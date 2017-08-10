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

  ballRadius, paddleWidth, paddleHeight :: Double
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
  paddleHeight = 15 -- height of paddle
  paddleWidth = 150 -- width of paddle
  paddleVx = 5
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
  }

  initialState :: GameState
  initialState = GameState{
  ballPos = (120, 200),
  ballSpeed = (4, 4),
  paddlePos = (300 / 2) - 75, --position around center of canvas
  score = 0
  }

  modifyStateRefPaddlePos :: IORef GameState -> Double -> IO ()
  modifyStateRefPaddlePos stateRef x =
    atomicModifyIORef stateRef (\state -> ((state {paddlePos = x}), ()))

  -- Note: this is called directly by main.js. it's the main Haskell entry point.
  breakoutHsMain :: IO ()
  breakoutHsMain =  do
    elems <- elemsByQS document "#canvas"
    Just canvas <- fromElem $ elems !! 0

    canvasHeight <- do
      getAttr canvas "height"

    stateRef <- newIORef $ initialState
    state <- readIORef stateRef -- extract state from reference object
    let modifyPaddlePos = modifyStateRefPaddlePos stateRef
    modifyPaddlePos 120.0
    state <- readIORef stateRef
    renderState canvas state

    onEvent canvas KeyDown $ \keyData -> movePaddle keyData stateRef
    state <- readIORef stateRef

    animate  canvas stateRef

  -- Draw the boundary wall
  wall :: Rect -> Picture ()
  wall (Rect x1 y1 x2 y2) = black $ do
    stroke $ rect (x1, y1) (x2, y2)

  gamePicture :: GameState -> Picture ()
  gamePicture state = do
    ball $ ballPos state
    let x1 = paddlePos state -- paddle start position
        x2 = x1 + paddleWidth -- end position of paddle
    paddle $ Rect x1 460 x2 480 -- paddle
    wall $ Rect wallPosX wallPosY wallDimX wallDimY
    where
      wallPosX = fst wallPos
      wallPosY = snd wallPos
      wallDimX = fst wallDim
      wallDimY = snd wallDim

  renderState :: Canvas -> GameState -> IO ()
  renderState canvas state = render canvas $ do
    gamePicture state

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

  distBetweenWallSide :: Point -> Vx -> Vy -> WallSide -> Double
  distBetweenWallSide p vx vy side =
    sqrt $ (dx ** 2 + dy ** 2)
    where
      vect = vectBetweenWallSide p vx vy side
      dx   = fst vect
      dy   = snd vect

  vectBetweenWallSide :: Point -> Vx -> Vy -> WallSide -> Point
  vectBetweenWallSide p vx vy side =
    case side of
      TopSide ->
        let dx = dy / (tan theta)
            dy = wallTopSide - y
        in
          (dx, dy)
      RightSide ->
        let dx = x - wallRightSide
            dy = dx * (tan theta)
        in
          (dx, dy)
      BottomSide ->
        let dx = dy / (tan theta)
            dy = y - wallBottomSide
        in
          (dx, dy)
      LeftSide ->
        let dx = x - wallLeftSide
            dy = dx * (tan theta)
        in
          (dx, dy)
      where
        x = fst p
        y = snd p
        theta = atan (vy / vx)

  nextPos :: GameObj -> GameState -> IORef GameState ->  (Point, (Double, Double))
  -- nextPos Ball state stateRef | trace  ("dist cp=" ++ show (dist p (collisionWall p' vx vy) )) False=undefined
  nextPos Ball state stateRef =
    if collisionTest p' Wall
      then
        let nearSide = nearestSide p vx vy
        in
          case nearSide of
            TopSide ->
              (( (fst hitPoint), (snd hitPoint) + 4), (vx, -vy))
            RightSide ->
              (( (fst hitPoint) - 4, (snd hitPoint)), (-vx, vy))
            BottomSide ->
              (( (fst hitPoint), (snd hitPoint) - 4), (vx, -vy))
            LeftSide ->
              (( (fst hitPoint), (snd hitPoint) - 4), (-vx, vy))
      else
        (p', (vx, vy))
    where vx = fst $ ballSpeed state
          vy = snd $ ballSpeed state
          p  = ballPos state
          p' = (fst p + vx, snd p + vy)
          hitPoint = collisionWall p' vx vy

  -- Note: we only call this if a (potential) collision is detected, so
  -- we know were always one vx or vy delta from hitting a wall.
  nearestSide :: Point -> Vx -> Vy -> Side
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

  -- this will return the position at which something hits the wall, even if the
  -- current point is beyond the wall (that's why we need Vx and Vy so we
  -- know where it came from)
  -- If a hit, return the collision point, otherwise return Nothing
  -- If a hit, return the collision point, otherwise return the original point
  collisionWall :: Point -> Vx -> Vy ->  Point
  collisionWall p vx vy =
    if collisionTest p Wall
      then
        let nearSide = nearestSide p vx vy
        in
          case nearSide of
            TopSide -> (x - fst deltaVect, y - snd deltaVect)
              where
                deltaVect = vectBetweenWallSide p vx vy TopSide
            RightSide -> (x - fst deltaVect, y - snd deltaVect)
              where
                deltaVect = vectBetweenWallSide p vx vy RightSide
            BottomSide -> (x - fst deltaVect, y - snd deltaVect)
              where
                deltaVect = vectBetweenWallSide p vx vy BottomSide
            LeftSide -> (x - fst deltaVect, y - snd deltaVect)
              where
                deltaVect = vectBetweenWallSide p vx vy LeftSide
      else
        p
    where
      x = fst p
      y = snd p

  animate :: Canvas -> IORef GameState -> IO ()
  animate canvas stateRef = do
    state <- readIORef stateRef -- extract state from reference object
    renderState canvas state -- draw game picture
    let np = nextPos Ball state stateRef
    atomicWriteIORef stateRef $ state {ballPos = fst np, ballSpeed = snd np}
    state <- readIORef stateRef

    setTimer (Once 10) $ animate canvas stateRef
    return ()
    where
      update = moveBall

  main = do
    export "breakoutHsMain" breakoutHsMain
