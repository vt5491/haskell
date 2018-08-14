module ToneDeaf where

import Data.Functor
import Data.Maybe
import Data.String
import Prelude

import Audio.WebAudio.AudioParam (getValue, setValue, setValueAtTime)
import Audio.WebAudio.BaseAudioContext (createGain, createOscillator, currentTime, destination, newAudioContext, resume, state, suspend)
import Audio.WebAudio.GainNode (gain)
import Audio.WebAudio.Oscillator (OscillatorType(..), frequency, setOscillatorType, startOscillator, stopOscillator)
import Audio.WebAudio.Types (AudioContext, GainNode, OscillatorNode, AudioContextState(..), connect)
import Control.Coroutine (Producer, Consumer, runProcess, pullFrom, await)
import Control.Coroutine.Aff (produce')
import Data.Array (filter, (..))
import Data.Newtype (wrap)
import Effect (Effect)
import Effect.Console (log)
import Web.DOM.Element (toEventTarget)
import Web.DOM.ParentNode (querySelector)
import Web.Event.Event (EventType(..), Event)
import Web.Event.EventTarget (EventTarget, addEventListener, eventListener)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toParentNode, toDocument)
import Web.HTML.HTMLElement (toElement, fromElement, className, HTMLElement)
import Web.HTML.Window (Window, document)
-- import Web.HTML.Window (Window)
-- import Web.HTML (window)
-- import Web.HTML.HTMLDocument (toParentNode)
-- import Web.HTML.Window (document)
-- import DOM (DOM)
-- import DOM.HTML (window)
-- import DOM.HTML.Types (HTMLElement, htmlElementToElement)
-- import DOM.HTML.Window (requestAnimationFrame)
-- import DOM.HTML.HTMLElement (getBoundingClientRect)
-- import DOM.Node.Types (elementToEventTarget)
-- import DOM.Event.EventTarget (addEventListener, eventListener)
-- import DOM.Event.MouseEvent (MouseEvent, eventToMouseEvent, clientX, clientY)
-- import DOM.Event.Types (Event, EventType(..), EventTarget)


-- import Data.Enum (Bounded)


sampleFreq :: Number
sampleFreq = 440.0

-- chromaticIntervals[0] = 1.000000;
-- chromaticIntervals[1] = 1.059463;
-- chromaticIntervals[2] = 1.122462;
-- chromaticIntervals[3] = 1.189207;
-- chromaticIntervals[4] = 1.259921;
-- chromaticIntervals[5] = 1.334839;
-- chromaticIntervals[6] = 1.414213;
-- chromaticIntervals[7] = 1.498307;
-- chromaticIntervals[8] = 1.587401;
-- chromaticIntervals[9] = 1.681792;
-- chromaticIntervals[10] = 1.781797;
-- chromaticIntervals[11] = 1.887748;

-- chromaticIntervals :: Int -> Number
-- chromaticIntervals 0  = 1.000000
-- chromaticIntervals 1  = 1.059463
-- chromaticIntervals 2  = 1.122462

chromaticMap :: ToneIndex -> Number
chromaticMap Zero  = 1.000000
chromaticMap One  = 1.059463
chromaticMap Two  = 1.122462
chromaticMap Three = 1.189207
chromaticMap Four = 1.259921
chromaticMap Five = 1.334839
chromaticMap Six = 1.414213
chromaticMap Seven = 1.498307
chromaticMap Eight = 1.587401
chromaticMap Nine = 1.681792
chromaticMap Ten = 1.781797
chromaticMap Eleven = 1.887748

chromaticIntervals :: ToneInterval -> Number
chromaticIntervals Tonic  = 1.000000
chromaticIntervals First  = 1.059463
chromaticIntervals Second  = 1.122462
chromaticIntervals MinThird = 1.189207
chromaticIntervals MajThird = 1.259921
chromaticIntervals Fourth = 1.334839
chromaticIntervals Diminished = 1.414213
chromaticIntervals Fifth = 1.498307
chromaticIntervals AugFifth = 1.587401
chromaticIntervals Sixth = 1.681792
chromaticIntervals MinSeventh = 1.781797
chromaticIntervals MajSeventh = 1.887748
-- data ToneInterval = 0 | 1 | 2 deriving (Enum)
-- data ToneInterval = Zero | One | Two deriving (Enum)
data ToneIndex = Zero | One | Two | Three | Four | Five
  | Six | Seven | Eight | Nine | Ten | Eleven

derive instance eqToneIndex :: Eq ToneIndex
derive instance ordToneIndex :: Ord ToneIndex

data ToneInterval = Tonic | First | Second | MinThird | MajThird | Fourth
  | Diminished | Fifth | AugFifth | Sixth | MinSeventh | MajSeventh

derive instance eqToneInterval :: Eq ToneInterval
derive instance ordToneInterval :: Ord ToneInterval
-- derive instance enumToneInterval :: Bounded ToneInterval

-- derive instance ti :: Enum
-- type ToneInterval = "abc" | "def"

-- data ModuleType2
--   = Regular
--   | Foreign
  -- deriving (Show, Eq, Ord)
beep :: Number -> Effect Unit
beep freq = do
  ctx <- newAudioContext
  osc <- createOscillator ctx
  setOscillatorType Sine osc
  log "ToneDeaf: now calling startOscillator"
  startOscillator 0.0 osc
  setValue freq =<< frequency osc
  connect osc =<< destination ctx
  stopOscillator 0.5 osc
  pure unit

-- getBtn :: String -> Effect Unit
getBtn ::  Effect Unit
getBtn = do
  log "ToneDeaf: now in getBtn"
  doc <- map toParentNode (window >>= document)
  -- doc <- map toParentNode (window >>= document)
  -- doc <- map toParentNode ( document)
  -- let doc = map toParentNode ( document)
  -- doc <-  map toParentNode $ document
  -- doc <- "hit"
  -- doc <- document window
  -- doc <- map toParentNode (htmlWindow >>= document)
  -- let doc :: Effect
  -- let doc :: Effect =<< (map toParentNode $ document)
  -- let doc =<< map toParentNode $  document
  -- doc <- toDocument document
  mbtn <- querySelector (wrap "#btn") doc
  -- mbtn <- querySelector "#btn" doc
  case mbtn of
    Nothing -> log "mbtn failed"
    Just btn -> do
      let mhtmlEl = fromElement btn
      case mhtmlEl of
        Nothing -> log "mhtml failed"
        Just htmlEl -> do
          let cn = className htmlEl
          -- log $ "cn=" <> map cn
          log $ "classname below:"
          cn >>= log
          -- "cn=" <> cn >>= log
          -- cn  do
          --   log cn
          -- addEventListener :: EventType -> EventListener -> Boolean -> EventTarget -> Effect Unit
          -- addEventListener (EventType "mousedown")
          -- (eventListener (emit <<< Left <<< EMouseMove)) false target
          -- eventListener :: forall a. (Event -> Effect a) -> Effect EventListener
          -- $ (eventListener (btnDownHandler))
          -- (eventListener (emit <<< Left <<< EMouseMove)) false target

          -- method 2
          evtListener <- (eventListener btnHandler2)
          -- addEventListener :: EventType -> EventListener -> Boolean -> EventTarget -> Effect Unit
          addEventListener
            (EventType "mousedown")
            -- (eventListener btnHandler3)
            evtListener
            false
            -- ((elementToEventTarget <<< htmlElementToElement) bodyHtmlElement)
            -- ((elementToEventTarget <<< htmlElementToElement) htmlEl)
            ((toEventTarget <<< toElement) htmlEl)
            -- htmlEl
          -- end method 2
          pure unit
      -- let cn = className htmlEl
      -- htmlEl <- fromElement button



      -- htmlEl <- button
      -- cn <- (fromElement htmlEl)
      pure unit

  -- button <- querySelector (wrap "#btn") doc
  -- case button of
  --   Nothing -> pure unit
  --   Just btn -> do
  --     let htmlEl = fromElement btn
  --     case htmlEl of
  --       Nothing -> pure unit
  --       Just he -> do
  --         let cn = className he
  --         -- log $ "cn=" <> map cn
  --         cn >>= log
  --         -- "cn=" <> cn >>= log
  --         log $ "abc"
  --         -- cn  do
  --         --   log cn
  --         pure unit
  --     -- let cn = className htmlEl
  --     -- htmlEl <- fromElement button
  --     -- htmlEl <- button
  --     -- cn <- (fromElement htmlEl)
  --     pure unit
  -- el <- button
  -- el do
  --   htmlEl <- fromElement el
  --   pure unit
  -- cn <- className $ (map fromElement el)
  -- case el of
  --   Nothing -> pure unit
  --   Just el -> do
  --     cn <- className el
  --     pure unit
  -- button do
  --   el <- button
  --   case el of
  --     Nothing -> pure unit
  --     Just el -> do
  --       cn <- className el
  --       pure unit
    -- cn <- className htmlEl
    -- pure unit
  -- cn2 <- className button
  -- let cn = getClassName button
  -- log $ "classname=" <> show cn
  -- do
    -- log $ "now in inner do" <> className  button
    -- let cn = map className ( map fromElement button )
    -- -- let cn = className ( fromElement button )
    -- let cn = (button >>= fromElement )
    -- pure cn
    -- log $ "now in inner do" <> map className ( map fromElement button )

  -- let unbox = button
  -- log $ "className=" <> button >>= getClassName
  -- className <*> button
  -- btnClass <- maybe "no-class" (\x -> x) $ className button
  -- btnClass <- maybe Element (\x -> x) button
  -- btnClass <- button >>= fromElement >>= className
  -- btnClass <- className <<= (button >>= fromElement)
  -- btnClass <- fromElement button >>= className
  -- btnClass <- button >>= fromElement >>= className
  -- log "btn-class=" <>
  -- button <- querySelector (wrap "#btn") =<< (map toParentNode $ document)
  -- button <- querySelector (wrap "#btn") document
  pure unit

-- getClassName :: Maybe HTMLElement -> String
-- getClassName e = map className  (map fromElement e)
-- note: the following actually compiles
-- getClassName e =  (map fromElement e)
-- getClassName e = className (map fromElement e)
-- getClassName Nothing = Nothing
-- getClassName (Just a) = className <*> a
-- getClassName elem = do
--   map className (map fromElement elem)

-- unboxMaybeElement :: Maybe Element -> HTMLElement
-- unboxMaybeElement Nothing = Nothing
-- unboxMaybeElement (Just a) = maybe (Element) (\x -> x) a

-- btnDownHandler :: Event -> Effect Unit
btnDownHandler e = log "btn pressed"

-- btnHandler2 :: forall e. Event -> GameEffect e Unit
-- btnHandler2 :: forall e. Event -> Effect e Unit
btnHandler2 :: Event -> Effect Unit
btnHandler2 a = do
  log "btn2 pressed"
  beep 880.0

btnHandler3 = 7
