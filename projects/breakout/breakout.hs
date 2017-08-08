{-# LANGUAGE OverloadedStrings #-}
  import Haste
  import Haste.Foreign
  import Haste.Prim (toJSStr)
  import Debug.Trace
  import Data.Typeable
  import Haste.Graphics.Canvas
  import Haste.DOM
  import Haste.Events
  import Data.IORef

  doItStr :: String -> Int
  doItStr x = length x

  doItInt :: Int -> Int
  doItInt x =  x

  doIt :: Int -> Int
  doIt x = 7

  -- width, height,ballRadius, paddleWidth, paddleHeight :: Double
  ballRadius, paddleWidth, paddleHeight :: Double
  -- note we init width and heigh in breakoutHsMain
  -- width = 500 -- width of canvas
  -- height = 600 -- height of canvas
  canvasWidth = 640
  canvasHeight = 480
  wallPos = (0, 0)
  wallDim = (canvasWidth, canvasHeight)

  -- For each side of the wall, associate it's "constant" value e.g the right side
  -- has a constant x and variable y, so associate the constant x.
  -- This is just to boilerplate code we use in several places.
  wallCoords :: [(Side, Double)]
  wallCoords = [
    (TopSide, snd wallPos),
    (BottomSide, (snd wallPos) + (snd wallDim)),
    (LeftSide, fst wallPos),
    (RightSide, (fst wallPos) + (fst wallDim)) ]

  wallTopSide = snd $ (filter (\x -> fst x == TopSide) wallCoords) !! 0
  wallBottomSide = snd $ (filter (\x -> fst x == BottomSide) wallCoords) !! 0
  wallLeftSide = snd $ (filter (\x -> fst x == LeftSide) wallCoords) !! 0
  wallRightSide = snd $ (filter (\x -> fst x == RightSide) wallCoords) !! 0

  -- Don't treat the wall as one object, but as basically four separate objects
  -- Each block is two points, from left to right and top to bottom.
  -- actully, just treat as a line for simplicity.
  wallLineTop = ((fst wallPos, snd wallPos), (fst wallPos + fst wallDim, snd wallPos))
  wallLineRight = (snd wallLineTop, (fst wallPos + fst wallDim, snd wallPos + snd wallDim))
  wallLineBottom = (fst wallLineTop, snd wallLineRight)
  wallLineLeft = (fst wallLineTop, fst wallLineBottom)

  ballRadius = 5 --radius of ball
  -- paddleHeight = 5 -- height of paddle
  paddleHeight = 15 -- height of paddle
  paddleWidth = 150 -- width of paddle
  paddleVx = 5
  -- halfWidth = width / 2 -- well, half the width
  -- halfHeight = height / 2 --also half the height
  -- cw :: Int
  type Vx = Double
  type Vy = Double

  data GameObj = Wall | Paddle | Brick | Ball | WallSide
    deriving (Show, Eq)

  data Side = TopSide | BottomSide | LeftSide | RightSide
    deriving (Show, Eq)

  type WallSide = Side

  -- this is for dynamic data only e.g data that can change on each tick.
  data GameState = GameState{
    ballPos :: Point, -- position of ball
    ballSpeed :: Point, -- how far will ball move in a single update
    paddlePos:: Double, -- start position of paddle on x axis
    score  :: Int
    -- wallPos :: Point, -- position of upper left
    -- wallDim :: Point -- width and height
  }

  initialState :: GameState
  initialState = GameState{
  -- ballPos = (20, 20),
  ballPos = (320, 478),
  -- ballSpeed = (8, 10),
  ballSpeed = (2, 3),
  paddlePos = (300 / 2) - 75, --position around center of canvas
  score = 0
  -- wallPos = (0, 0),
  -- wallDim = (canvasWidth, canvasHeight)
  }

  -- Note: this is called directly by main.js. it's the main Haskell entry point.
  breakoutHsMain :: IO ()
  breakoutHsMain =  do
    elems <- elemsByQS document "#canvas"
    Just canvas <- fromElem $ elems !! 0
    print $ doItInt 7
    getAttr canvas "width"
    -- canvasWidth :: String
    let abc = 7 + 1
    print $ "abc=" ++ show abc
    -- width <- do
    --   getAttr canvas "width"
    width <- getAttr canvas "width"
    print $ "width=" ++ width
    -- print $ doItStr $ width
    -- print $ doItInt $ (read width :: Int)
    -- convert from String to Int
    let canvasWidth = (read width :: Int)
    print $ "canvasWidth=" ++ show canvasWidth
    print $  "doItInt canvasWidth=" ++ (show $ doItInt  canvasWidth)

    canvasHeight <- do
      getAttr canvas "height"

    renderState canvas initialState
    stateRef <- newIORef $ initialState
    onEvent canvas KeyDown $ \keyData -> movePaddle keyData stateRef
    -- let distance = distBetween (0, 0) Wall 1 1
    state <- readIORef stateRef
    let distance = distBetween1 (20, 20) Wall state
    print $ "distance=" ++ show distance

    let wallHit = collisionTest (1000, 100) Wall
    print $ "wallHit1=" ++ show wallHit
    let wallHit2 = collisionTest (10, 100) Wall
    print $ "wallHit2=" ++ show wallHit2
    let wallHit3 = collisionTest (10, 1000) Wall
    print $ "wallHit3=" ++ show wallHit3
    -- let wallHit4 = collisionTest (-10, 100) Wall
    let wallHit4 = collisionTest (644, 20) Wall
    print $ "wallHit4=" ++ show wallHit4
    print $ "wallRightSide=" ++ show wallRightSide

    let collisionPoint = collisionWall (320, 481) 4 4
    print $ "collisionPoint=" ++ show collisionPoint

    let np = nextPos2 Ball state
    print $ "nextPos=" ++ show np
    -- let collisionPoint2 = collisionWall (644, 20) 4 1
    -- print $ "collisionPoint2=" ++ show collisionPoint2
    -- let collisionPoint3 = collisionWall (20, 20) 4 1
    -- print $ "collisionPoint3=" ++ show collisionPoint3
    -- let a = abc (400, 600)
    -- let b = def (400, 600) 1 1
    -- let rightWallCoords =
    -- print "hi"
    -- let nearestSide = nearestSide  (400, 600) 1 1
    -- print $ "nearestSide=" ++ show nearestSide
    -- animate  canvas stateRef

  -- wallShape :: Shape ()
  -- wallShape = do
  --   -- rect (0, 0) (canvasWidth - 0, canvasHeight - 0)
  --   rect (0, 0) (fst $ wallDim state, snd $ wallDim state)
  --
  -- wall :: Picture ()
  -- wall = stroke wallShape

  -- Draw the boundary wall
  wall :: Rect -> Picture ()
  wall (Rect x1 y1 x2 y2) = black $ do
    stroke $ rect (x1, y1) (x2, y2)

  -- wall pt = color (RGB 243 114 89) $ do
  --     fill $ circle pt ballRadius

  gamePicture :: GameState -> Picture ()
  gamePicture state = do
    ball $ ballPos state
    let x1 = paddlePos state -- paddle start position
        x2 = x1 + paddleWidth -- end position of paddle
    paddle $ Rect x1 460 x2 480 -- paddle
    -- wall $ Rect  (fst $ wallPos state) (snd $ wallPos state) (fst $ wallDim state) (snd $ wallDim state)
    wall $ Rect wallPosX wallPosY wallDimX wallDimY
    where
      wallPosX = fst wallPos
      wallPosY = snd wallPos
      wallDimX = fst wallDim
      wallDimY = snd wallDim
    -- wall $ Rect 0 0 canvasWidth canvasHeight
    -- wall $ Rect 0 0 canvasWidth  (snd $ wallDim state)

  renderState :: Canvas -> GameState -> IO ()
  renderState canvas state = render canvas $ do
    gamePicture state
    -- wall

  paddleShape :: Shape ()
  paddleShape = rect (-20, -10) (20, 10)

  white :: Picture () -> Picture ()
  white = color (RGB 255 255 255) -- or whichever color you like

  black :: Picture () -> Picture ()
  black = color (RGB 10 10 10)

  paddle :: Rect -> Picture ()
  paddle (Rect x1 y1 x2 y2) = white $ do
    fill $ rect (x1, y1) (x2, y2)

  movePaddle keyCode stateRef = do
    -- case fromIntegral keyCode of
    case keyCode of
      65 -> do
        atomicModifyIORef stateRef (\state -> ((state {paddlePos = (paddlePos state) - paddleVx}), ()))
      68 -> do
        atomicModifyIORef stateRef (\state -> ((state {paddlePos = (paddlePos state) + paddleVx}), ()))
      83 -> do
        atomicModifyIORef stateRef (\state -> ((state {paddlePos = (paddlePos state) + paddleVx}), ()))
      _ -> do
        writeLog "invalid key pressed"

  -- Draw a ball
  ball :: Point -> Picture ()
  ball pt = color (RGB 243 114 89) $ do
      fill $ circle pt ballRadius

  moveBall :: GameState -> GameState
  moveBall state = state {ballPos = (x + vx, y + vy)} --increment by vx and vy
    where
      (x, y)   = ballPos state
      (vx, vy) = ballSpeed state


  -- return the directional distance between two points.
  -- Vx and Vy provide the direction of the projectile
  -- TODO: consider passing all the state values as args, so you don't couple
  -- to the gameState e.g. this func could be used in other games.
  distBetween1 :: Point -> GameObj -> GameState-> Double
  -- distBetween p Wall state | trace ("wallBottomY - y=" ++ wallBottomY - y) False = undefined
  -- distBetween p Wall state | trace ("wallBottomX - x=" ++ show ((fst $ wallPos state) + (fst $ wallDim state)) - (fst p) ) False = undefined
  distBetween1 p Wall state | trace ("p=" ++ show  (snd p)) False=undefined
  distBetween1 p Wall state = sqrt $ (wallBottomY - y)**2 + (wallBottomX - x)**2
    where
      -- TODO: deal with case where vy =0
      x = fst p
      y = snd p
      vx = fst $ ballSpeed state
      vy = snd $ ballSpeed state
      theta = atan $ vx / vy
      -- wallBottomX = (fst $ wallPos state) + (fst $ wallDim state)
      -- wallBottomY = (snd $ wallPos state) + (snd $ wallDim state)
      wallBottomX = (fst wallPos) + (fst wallDim)
      wallBottomY = (snd wallPos) + (snd wallDim)
      -- trace ("wallBottomY" ++ show wallBottomY) False= undefined

  distBetweenWallSide :: Point -> Vx -> Vy -> WallSide -> Double
  distBetweenWallSide p vx vy BottomSide =
    let dy = y - wallBottomSide
        dx = dy / (tan theta)
    in
      sqrt $ (dx ** 2 + dy ** 2)
  -- vectorBetweenWall :: Point -> WallSide -> Double
  -- -- vectorBetweenWall p BottomSide = (x, y - wallBottomSide )
  -- vectorBetweenWall p BottomSide = (y - snd $ fst wallLineBottom)
    where
      x = fst p
      y = snd p
      theta = atan (vy / vx)

  vectBetweenWallSide :: Point -> Vx -> Vy -> WallSide -> Point
  vectBetweenWallSide p vx vy BottomSide =
    let dy = y - wallBottomSide
        dx = dy / (tan theta)
    in
      (dx, dy)
    where
      x = fst p
      y = snd p
      theta = atan (vy / vx)

  -- maybeSqrtX :: Maybe Point -> Maybe Double
  -- maybeSqrtX Nothing = Nothing
  -- maybeSqrtX x = sqrt $ fst x

  -- nextPos :: GameObj -> GameState -> Point
  -- nextPos Ball state =
  --   let vx = fst $ ballSpeed state
  --       vy = snd $ ballSpeed state
  --       p = ballPos state
  --       p' = (fst p + vx, snd p + vy)
  --       -- cp = do
  --       --   collisionWall p' vx vy
  --       cp = collisionWall p' vx vy
  --       -- jcp =Just $ Just cp
  --   in
  --     if (cp /= Nothing)
  --       then
  --         -- (5,5)
  --         -- let distToWall = sqrt $ ((fst cp - fst p) ** 2 ) + ((snd cp - snd p)) ** 2
  --
  --         -- let distToWall = do
  --         --                   fst cp
  --         let distToWall = maybeSqrtX cp
  --             vectLength = sqrt $ (vx **2 + vy ** 2)
  --             overShootRatio = distToWall / vectLength
  --         in
  --           (overShootRatio, 5)
  --       else
  --         (1,1)

  nextPos2 :: GameObj -> GameState -> Maybe Point
  nextPos2 Ball state =
    if collisionTest p' Wall
      then
        -- Just (0, 0)
        collisionWall p' vx vy
        -- Next: do all the ratio stuff
      else
        Just p'
    where
      vx = fst $ ballSpeed state
      vy = snd $ ballSpeed state
      p  = ballPos state
      p' = (fst p + vx, snd p + vy)
  -- nextPos2 Ball state = do
  --   let vx = fst $ ballSpeed state
  --   let vy = snd $ ballSpeed state
  --   -- collisionWall (ballPos state) (fst $ ballSpeed state) (snd $ ballSpeed state)
  --   let cp = collisionWall (ballPos state) vx vy
  --   let distToWall =
  --   return (0.0, 0.0)
    -- return $ Just $ Point 0.0 0.0
    -- return $ Just $ (0.0, 0.0)


  -- Note: we only call this if a (potential) collision is detected, so
  -- we know were always one vx or vy delta from hitting a wall.
  nearestSide :: Point -> Vx -> Vy -> Side
  -- nearestSide _ _ _ = Bottom
  nearestSide p vx vy
    -- upward to the right
    | (vx > 0) && (vy < 0) && ((y + vy) <= topSide)  = TopSide
    | (vx > 0) && (vy < 0) && ((y + vy) > topSide)  = RightSide
    -- upward to the left
    | (vx < 0) && (vy < 0) && ((y + vy) <= topSide)  = TopSide
    | (vx < 0) && (vy < 0) && ((y + vy) > topSide)  = LeftSide
    -- downward to the right
    | (vx > 0) && (vy > 0) && ((x + vx) >= rightSide)  = RightSide
    | (vx > 0) && (vy > 0) && ((x + vx) < rightSide)  = BottomSide
    -- downward to the left
    | (vx < 0) && (vy > 0) && ((x + vx) <= leftSide)  = LeftSide
    | (vx < 0) && (vy > 0) && ((x + vx) > leftSide)  = BottomSide
      where
        x = fst p
        y = snd p
        topSide = snd $ (filter (\x -> fst x == TopSide) wallCoords) !! 0
        bottomSide = snd $ (filter (\x -> fst x == BottomSide) wallCoords) !! 0
        leftSide = snd $ (filter (\x -> fst x == LeftSide) wallCoords) !! 0
        rightSide = snd $ (filter (\x -> fst x == RightSide) wallCoords) !! 0

  -- collisionTest :: Point -> GameObj -> Maybe Point
  collisionTest :: Point -> GameObj -> Bool
  collisionTest p Wall
    | x > wallRightSide = True
    | x < wallLeftSide = True
    | y > wallBottomSide = True
    | y < wallTopSide = True
    | otherwise = False
      where
        x = fst p
        y = snd p

    -- case of
    --   x > wallRightSide -> "case 1"
    --   y > wallBottomSide -> "case 2"
  -- this will return the position at which something hits the wall, even if the
  -- current point is beyond the wall (that's why we need Vx and Vy so we
  -- know where it came from)
  -- If a hit, return the collision point, otherwise return Nothing
  collisionWall :: Point -> Vx -> Vy -> Maybe Point
  -- collisionWall :: Point -> Vx -> Vy -> IO String
  -- collisionWall :: Int -> Vx -> Vy -> IO String
  -- collisionWall p vx vy | trace ("trace collisionWall px=" ++ show (fst  p)) False = undefined
  -- collisionWall p vx vy | trace ("trace collisionWall cw=" ++ show canvasWidth) False = undefined
  -- collisionWall p vx vy | trace ("collisionWall " ++ show vx) False = undefined
  collisionWall p vx vy | trace ("collisionWall " ++ show p) False = undefined
  collisionWall p vx vy | trace ("collisionWall: nearestSide= " ++ show (nearestSide  p vx vy)) False = undefined
  collisionWall p vx vy | trace ("collisionWall: distBetweenWallSide= " ++ show (distBetweenWallSide  p vx vy BottomSide)) False = undefined
  collisionWall p vx vy =
    if collisionTest p Wall
      then
        let nearSide = nearestSide p vx vy
        in
          case nearSide of
            TopSide -> Just (0.0,0)
            LeftSide -> Just (1.0,0)
            -- BottomSide -> Just (distBetweenWallSide p vx vy BottomSide,0)
            -- BottomSide -> Just $ vectBetweenWallSide p vx vy BottomSide
            -- BottomSide -> Just $ vectBetweenWallSide p vx vy BottomSide
            BottomSide -> Just $ (x - fst deltaVect, y - snd deltaVect)
              where
                deltaVect = vectBetweenWallSide p vx vy BottomSide
            RightSide -> Just (3.0,0)
          -- Just (0,0)
          -- | nearSide == BottomSide = Just (0,0)
      else
        Nothing
        -- | px > canvasWidth = Just (0,0)
        -- | py > canvasHeight = Just (0,0)
        -- | otherwise = Nothing
    where
      x = fst p
      y = snd p

  animate :: Canvas -> IORef GameState -> IO ()
  animate canvas stateRef = do
    state <- readIORef stateRef -- extract state from reference object
    renderState canvas state -- draw game picture
    atomicWriteIORef stateRef $ update state -- update state and rewrite state reference^
    let abc = collisionWall (ballPos state) (fst $ ballSpeed state) (snd $ ballSpeed state)
    print $ "abc=" ++  show abc
    let np = nextPos2 Ball state
    print $ "nextPos=" ++ show np

    -- setTimer (Once 10) $ animate canvas stateRef
    return ()
    where
      update = moveBall

  main = do
    export "breakoutHsMain" breakoutHsMain
