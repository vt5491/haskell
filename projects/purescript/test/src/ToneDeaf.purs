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
import Web.Event.CustomEvent ( CustomEvent)
import Web.Event.Event (EventType(..), Event)
import Web.Event.EventTarget (EventTarget, addEventListener, dispatchEvent, eventListener)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toParentNode, toDocument)
import Web.HTML.HTMLElement (toElement, fromElement, className, HTMLElement)
import Web.DOM (Element)
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
  mbtn <- querySelector (wrap "#btn") doc
  case mbtn of
    Nothing -> log "mbtn failed"
    Just btn -> do
      let mhtmlEl = fromElement btn
      case mhtmlEl of
        Nothing -> log "mhtml failed"
        Just htmlEl -> do
          let cn = className htmlEl
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
          evtListener <- (eventListener btnHandler)
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
          vtEvtListener <- (eventListener vtEvtHandler)
          addEventListener
            (EventType "vtEvt")
            vtEvtListener
            false
            ((toEventTarget <<< toElement) htmlEl)
          pure unit
      pure unit

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
btnHandler :: Event -> Effect Unit
btnHandler e = do
  log "btn pressed"
  beep 890.0
  -- dispatchEvent :: Event -> EventTarget -> Effect Boolean
  -- let custEvt = customEvent $ EventType "vtEvt"
  let r = toneDeafJsDoIt 5
  log $ "btnHandler: r=" <> r
  -- TODO: how to create a new Event?
  -- let custEvt =  EventType "vtEvt"
  let custEvt = createVtEvt 1
  -- let w = toneDeafEvt custEvt
  -- let x = toneDeafAbc 5
  dispatchVtEvt custEvt
  -- dispatchVtEvt e
  -- let evtTgt = do
  -- evtTgt <- do
  --   doc <- map toParentNode (window >>= document)
  --   mBodyEl <- querySelector (wrap "body") doc
  --   case mBodyEl of
  --     Nothing -> log "mBodyEl failed"
  --     just bodyEl = pure bodyEl
  --
  -- dispatchEvent custEvt evtTgt
  pure unit

btnHandler3 = 7

vtEvtHandler :: Event -> Effect Unit
vtEvtHandler e = do
  log "vtEvtHandler entered"


-- getBodyEl :: Effect Unit
-- getBodyEl :: Maybe Element
-- getBodyEl = do
--   -- doc <- map toParentNode (window >>= document)
--   let doc = map toParentNode (window >>= document)
--   -- mEl <- querySelector (wrap "body") doc
--   -- mEl <- querySelector (wrap "body") doc
--   -- querySelector (wrap "body")  <<< (map  <<< toParentNode (window >>= document))
--   -- querySelector (wrap "body") $  doc
--   -- let mEl = (doc >>= querySelector (wrap "body"))
--   let mBodyEl = (doc >>= querySelector (wrap "body"))
--   -- pure <<< bodyEl
--   mBodyEl <- do
--     evtTgt <- Just mBodyEl
--     -- pure abc
--     let custEvt = EventType "vtEvt"
--     -- dispatchEvent :: Event -> EventTarget -> Effect Boolean
--     dispatchEvent custEvt evtTgt
--     -- Nothing
--     -- <<< mBodyEl
--     -- mBodyEl >>= HTMLElement
--     -- case mBodyEl of
--     --   Nothing -> Nothing
--     --   just el -> Just el
--   --   -- bodyEl
--   --   pure unit
--   -- pure bodyEl
--
--   -- mEl -> do
--   --   case mEl of
--   --     Nothing -> Nothing
--   --     Just el -> pure el
--   -- pure unit
--   Nothing
  -- Just abc

-- dispatchVtEvt :: Event -> Maybe Element
dispatchVtEvt :: Event -> Effect Unit
dispatchVtEvt e = do
  doc <- map toParentNode (window >>= document)
  -- mBodyEl <- querySelector (wrap "body") doc
  -- note: you *do* have to dispatch to the same element you put the listener on
  mBtnEl <- querySelector (wrap "#btn") doc
  -- mBodyEl <- do
    -- evtTgt <- Just mBodyEl
    -- let custEvt = EventType "vtEvt"
    -- dispatchEvent :: Event -> EventTarget -> Effect Boolean
    -- dispatchEvent e evtTgt
  case mBtnEl of
    Nothing -> log "mBodyEl is Nothing"
    -- Nothing -> pure unit
    Just btnEl -> do
      -- let rc = dispatchEvent e (toEventTarget bodyEl)
      rc <- dispatchEvent e (toEventTarget btnEl)
      -- rc -> do
      case rc of
        false -> log "bad rc"
        -- true -> pure unit
        true -> log "good rc"
      -- result <- do
      -- case mRc of
      --   Nothing -> log "fail"
      --   Just rc ->


  -- Nothing
  pure unit

foreign import createVtEvt :: Int -> Event
foreign import toneDeafJsDoIt :: Int -> String
-- foreign import debugIt :: Int -> String
foreign import toneDeafAbc :: Int -> String
foreign import toneDeafEvt :: Event -> String
