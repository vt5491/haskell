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

  data GameState = GameState{
    ballPos :: Point, -- position of ball
    ballSpeed :: Point, -- how far will ball move in a single update
    paddlePos:: Double, -- start position of paddle on x axis
    score  :: Int
  }

  initialState :: GameState
  initialState = GameState{
  ballPos = (20, 20),
  -- ballSpeed = (8, 10),
  ballSpeed = (2, 3),
  paddlePos = (300 / 2) - 75, --position around center of canvas
  score = 0
  }

  -- Note: this is called directly by main.js. it's the main Haskell entry point.
  breakoutHsMain :: IO ()
  breakoutHsMain =  do
    elems <- elemsByQS document "#canvas"
    Just canvas <- fromElem $ elems !! 0
    -- let canvasWidth =<<  getAttr canvas "width"
    -- writeLog "canvasWidth=" ++ canvasWidth
    -- let canvasWidth
    -- in  getAttr canvas "width"
    -- let cw =
    -- in
    -- width <- do
    --   getAttr canvas "width"
    -- cw <- getAttr canvas "width" -- works
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

    -- let cw = read (<- do
    --                     getAttr canvas "width" )
    --   :: Int
    -- let cw = read $ sm :: Int
    --   in
    --     sm <- do
    --             getAttr canvas "width"
    -- let cw = getAttr canvas "width"
    --     in

    -- print $ canvasWidth + 7
    canvasHeight <- do
      getAttr canvas "height"
    -- print canvasHeight
    -- writeLog width

    -- do
    --   writeLog "width=" ++ show 7
    renderState canvas initialState
    stateRef <- newIORef $ initialState
    onEvent canvas KeyDown $ \keyData -> movePaddle keyData stateRef
    animate  canvas stateRef

  gamePicture :: GameState -> Picture ()
  gamePicture state = do
    ball $ ballPos state
    let x1 = paddlePos state -- paddle start position
        x2 = x1 + paddleWidth -- end position of paddle
    paddle $ Rect x1 460 x2 480 -- paddle

  renderState :: Canvas -> GameState -> IO ()
  renderState canvas state = render canvas $ do
    gamePicture state

  paddleShape :: Shape ()
  paddleShape = rect (-20, -10) (20, 10)

  white :: Picture () -> Picture ()
  white = color (RGB 255 255 255) -- or whichever color you like

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
