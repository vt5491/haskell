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
  import Data.Tuple
  -- import Data.Tuple.Select
  -- import Haste.Perch

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

  data GameStateType = BallPos | BallSpeed | PaddlePos | Score
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
  -- ballPos = (320, 478),
  ballPos = (120, 200),
  -- ballSpeed = (8, 10),
  -- ballSpeed = (2, 3),
  ballSpeed = (4, 4),
  paddlePos = (300 / 2) - 75, --position around center of canvas
  score = 0
  -- wallPos = (0, 0),
  -- wallDim = (canvasWidth, canvasHeight)
  }

  -- modifyGameState :: IORef GameState -> GameStateType -> IO ()
  -- modifyGameState stateRef PaddlePos =  atomicModifyIORef stateRef (\state -> ((state {paddlePos = (paddlePos state) - paddleVx}), ()))
  modifyStateRefPaddlePos :: IORef GameState -> Double -> IO ()
  modifyStateRefPaddlePos stateRef x =
    atomicModifyIORef stateRef (\state -> ((state {paddlePos = x}), ()))
    -- atomicWriteIORef stateRef (\state -> ((state {paddlePos = x}), ()))
    -- atomicModifyIORef stateRef (\state -> (( (paddlePos state) = x), ()))
    -- print $ "now in modifyStateRefPaddlePos"

  -- make stateRefGlobal a global
  -- stateRefGlobal :: IORef

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

    stateRef <- newIORef $ initialState
    state <- readIORef stateRef -- extract state from reference object
    print $ "paddlePos=" ++ show  (paddlePos state)
    let modifyPaddlePos = modifyStateRefPaddlePos stateRef
    modifyPaddlePos 120.0
    state <- readIORef stateRef
    -- let modifyGameStateByType = modifyGameState stateRef
    -- do
    -- atomicWriteIORef stateRef (modifyStateRefPaddlePos stateRef 30.0)
    -- atomicWriteIORef stateRef $ changeBallSpeed state (13,3) -- works
    -- atomicWriteIORef stateRef $ moveBall state -- update state and rewrite state reference^
    -- state <- readIORef stateRef
      -- return ()
    -- state <- readIORef stateRef
    print $ "paddlePos=" ++ show  (paddlePos state)
    print $ "ballSpeed=" ++ show  (ballSpeed state)
    print $ "ballPos=" ++ show  (ballPos state)
    -- print $ "paddlePos=" ++ paddlePos
    -- renderState canvas initialState
    renderState canvas state

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

    -- let np = nextPos Ball state stateRef
    -- atomicWriteIORef stateRef $ changeBallSpeed state (fst $ snd $ np, -1 * (snd $ ballSpeed state))
    -- state <- readIORef stateRef
    -- print $ "nextPos=" ++ show (fst np)
    -- print $ "ballSpeed=" ++ show (snd np)

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
        atomicModifyIORef stateRef
          (\state -> ((state {paddlePos = (paddlePos state) - paddleVx}), ()))
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

  changeBallSpeed :: GameState -> (Double, Double) -> GameState
  changeBallSpeed state speed = state {ballSpeed = speed}

  dist :: Point -> Point -> Double
  dist p1 p2 = sqrt ( (fst p2 - fst p1) ** 2 + (snd p2 - snd p1)** 2)
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

  -- nextPos :: GameObj -> GameState -> Maybe Point
  nextPos :: GameObj -> GameState -> IORef GameState ->  (Point, (Double, Double))
  -- nextPos Ball state | trace  ("dist=" ++ show (distBetweenWallSide (collisionWall p' vx vy) vx vy BottomSide)) False=undefined
  -- nextPos Ball state stateRef | trace  ("dist cp=" ++ show (dist p (collisionWall p' vx vy) )) False=undefined
  --   where vx = fst $ ballSpeed state
  --         vy = snd $ ballSpeed state
  --         p  = ballPos state
  --         p' = (fst p + vx, snd p + vy)
  -- nextPos Ball state stateRef| trace  ("dist p1, p1'=" ++ show (dist p p' )) False=undefined
  --   where vx = fst $ ballSpeed state
  --         vy = snd $ ballSpeed state
  --         p  = ballPos state
  --         p' = (fst p + vx, snd p + vy)
  nextPos Ball state stateRef =
    if collisionTest p' Wall
      then do
        -- p
        -- (0.0,0.0) :: Point
        -- tmp <- do
        --   return (7.0, 1.0)
          -- let tmp = atomicWriteIORef stateRef $ changeBallSpeed state (13,3)
          -- return (0.0, 0.0)
          -- return ()
        -- (0.0,0.0)
        -- do
        --   let tmp =atomicWriteIORef stateRef $ changeBallSpeed state (vx, -1 * vy)
        --   return (0,0)
        -- (hitPoint, (vx, -vy))
        (( (fst hitPoint), (snd hitPoint) - 4), (vx, -vy))
        -- atomicModifyIORef state (\state -> ((snd ballSpeed state) = -1 * (snd ballSpeed state)), ()))
        -- atomicModifyIORef state (\state -> ((state {ballSpeed = (fst $ ballSpeed state, snd $ ballSpeed state)}), ()))
        -- Just (0, 0)
        -- let collisionPoint = collisionWall p' vx vy
        -- let dist = distBetweenWallSide collisionPoint vx vy BottomSide
        -- return (0.0, 0.0)
        -- Next: do all the ratio stuff
        -- set new vx, vy

      else
        -- Just p'
        (p', (vx, vy))
    where vx = fst $ ballSpeed state
          vy = snd $ ballSpeed state
          p  = ballPos state
          p' = (fst p + vx, snd p + vy)
          hitPoint = collisionWall p' vx vy
          distToHitPoint = distBetweenWallSide hitPoint vx vy BottomSide
          ratio = distToHitPoint / sqrt (vx ** 2 + vy ** 2)
          -- tmp = do
          --   atomicWriteIORef stateRef $ changeBallSpeed state (vx, -1 * vy)

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
  -- If a hit, return the collision point, otherwise return the original point
  collisionWall :: Point -> Vx -> Vy ->  Point
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
            TopSide -> (0.0,0)
            LeftSide -> (1.0,0)
            BottomSide -> (x - fst deltaVect, y - snd deltaVect)
              where
                deltaVect = vectBetweenWallSide p vx vy BottomSide
            RightSide -> (3.0,0)
      else
        p
    where
      x = fst p
      y = snd p

  animate :: Canvas -> IORef GameState -> IO ()
  animate canvas stateRef = do
    state <- readIORef stateRef -- extract state from reference object
    renderState canvas state -- draw game picture
    -- atomicWriteIORef stateRef $ update state -- update state and rewrite state reference^
    -- let abc = collisionWall (ballPos state) (fst $ ballSpeed state) (snd $ ballSpeed state)
    -- print $ "abc=" ++  show abc
    let np = nextPos Ball state stateRef
    -- atomicWriteIORef stateRef $ changeBallSpeed state (fst $ snd $ np, 1 * (snd $ ballSpeed state))
    -- atomicWriteIORef stateRef $ changeBallSpeed state $ fst np
    atomicWriteIORef stateRef $ state {ballPos = fst np, ballSpeed = snd np}
    -- atomicWriteIORef stateRef $ state {ballSpeed = snd np}
    state <- readIORef stateRef
    print $ ("nextPos=" ++ (show $ fst np))
    print $ ("np.ballSpeed=" ++ (show $ snd np))

    setTimer (Once 10) $ animate canvas stateRef
    return ()
    where
      update = moveBall

  main = do
    export "breakoutHsMain" breakoutHsMain
