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

  data GameObj = Wall | Paddle | Brick | Ball
    deriving (Show, Eq)

  data Side = TopSide | BottomSide | LeftSide | RightSide
    deriving (Show, Eq)

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
  ballPos = (20, 20),
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
    let distance = distBetween (20, 20) Wall state
    print $ "distance=" ++ show distance
    -- let a = abc (400, 600)
    -- let b = def (400, 600) 1 1
    -- let rightWallCoords =
    print "hi"
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

  -- TODO: move up into the constants section
  -- For each side of the wall, associate it's "constant" value e.g the right side
  -- has a constant x and variable y, so associate the constant x.
  -- This is just to boilerplate code we use in several places.
  wallCoords :: [(Side, Double)]
  wallCoords = [
    (TopSide, snd wallPos),
    (BottomSide, (snd wallPos) + (snd wallDim)),
    (LeftSide, fst wallPos),
    (RightSide, (fst wallPos) + (fst wallDim)) ]
  -- return the directional distance between two points.
  -- Vx and Vy provide the direction of the projectile
  -- TODO: consider passing all the state values as args, so you don't couple
  -- to the gameState e.g. this func could be used in other games.
  distBetween :: Point -> GameObj -> GameState-> Double
  -- distBetween p Wall state | trace ("wallBottomY - y=" ++ wallBottomY - y) False = undefined
  -- distBetween p Wall state | trace ("wallBottomX - x=" ++ show ((fst $ wallPos state) + (fst $ wallDim state)) - (fst p) ) False = undefined
  distBetween p Wall state | trace ("p=" ++ show  (snd p)) False=undefined
  distBetween p Wall state = sqrt $ (wallBottomY - y)**2 + (wallBottomX - x)**2
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

  -- abc :: Point -> Side
  -- abc _ = Bottom
  --
  -- -- def :: Int -> Side
  -- def :: Point -> Vx -> Vy -> Side
  -- def _ _ _= Bottom

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

  -- this will return the position at which something hits the wall, even if the
  -- current point is beyond the wall (that's why we need Vx and Vy so we
  -- know where it came from)
  -- If a hit, return the collision point, otherwise return Nothing
  collisionWall :: Point -> Vx -> Vy -> Maybe Point
  -- collisionWall :: Point -> Vx -> Vy -> IO String
  -- collisionWall :: Int -> Vx -> Vy -> IO String
  -- collisionWall p vx vy | trace ("trace collisionWall px=" ++ show (fst  p)) False = undefined
  collisionWall p vx vy | trace ("trace collisionWall cw=" ++ show canvasWidth) False = undefined
  -- collisionWall _ _ _ = do
  --     print "collisionWall called"
  --     return "hello"
  -- collisionWall p vx vy | trace ("collisionWall " ++ show vx) False = undefined
  -- collisionWall p vx vy = Just (7,6)
  collisionWall p vx vy
        | px > canvasWidth = Just (0,0)
        | py > canvasHeight = Just (0,0)
        | otherwise = Nothing
    where
      px = fst p
      py = snd p

  animate :: Canvas -> IORef GameState -> IO ()
  animate canvas stateRef = do
    state <- readIORef stateRef -- extract state from reference object
    renderState canvas state -- draw game picture
    atomicWriteIORef stateRef $ update state -- update state and rewrite state reference^
    -- abc <- collisionWall (round (fst $ ballPos state) :: Int)  1 1
    -- let abc = collisionWall 1 1 1
    -- def <- abc
    -- print $ "abc=" ++ abc
    -- abc <- (collisionWall $ (ballPos state) $ fst $ ballSpeed state $ snd $ ballSpeed state)
    -- let Just abc = collisionWall (ballPos state) (fst $ ballSpeed state) (snd $ ballSpeed state)
    -- Just abc <- collisionWall (ballPos state) (fst $ ballSpeed state) (snd $ ballSpeed state)
    -- let abc = do
    let abc = collisionWall (ballPos state) (fst $ ballSpeed state) (snd $ ballSpeed state)
    print $ "abc=" ++  show abc
    setTimer (Once 10) $ animate canvas stateRef
    return ()
    where
      update = moveBall

  main = do
    export "breakoutHsMain" breakoutHsMain
