module Main where

import Prelude
import ToneDeaf
import UserMod

import Audio.WebAudio.AudioParam (getValue, setValue, setValueAtTime)
import Audio.WebAudio.BaseAudioContext (createGain, createOscillator, currentTime, destination, newAudioContext, resume, state, suspend)
import Audio.WebAudio.GainNode (gain)
import Audio.WebAudio.Oscillator (OscillatorType(..), frequency, setOscillatorType, startOscillator, stopOscillator)
import Audio.WebAudio.Types (AudioContext, GainNode, OscillatorNode, AudioContextState(..), connect)
import Data.Array (filter, (..))
import Effect (Effect)
import Effect.Console (log)
import Effect.Timer as T

-- main :: Effect Unit
-- main = do
--   let i = 1 ..2
--   let str = show vtVal
--   log str
--   log "Hello sailor2!"

  -- let result = show factors
  -- log factors
loopDo :: Array Int
loopDo = do
  i <- 1..5
  i <- 1..5
  pure i

-- main :: Effect Unit
-- main = do
--   log $ "hi" <> show loopDo
-- main :: forall eff. (Eff (wau :: WebAudio, dom :: DOM | eff) Unit)
-- main :: forall eff. (Effect (wau :: WebAudio, dom :: DOM | eff) Unit)
-- main :: Effect Unit
main = do
  -- getBtn "btn"
  let s = " world"
  let r = mainJsDoIt 5
  log $ "main: r=" <> r <> s
  void $ T.setTimeout 10 do
    log "timeout increment counter"
    getBtn

  beep 440.0
  beep 880.0

beep1 :: Number -> Effect Unit
beep1 freq = do
  -- ctx <- makeAudioContext
  ctx <- newAudioContext
  osc <- createOscillator ctx
  setOscillatorType Sine osc
  log "now calling startOscillator"
  startOscillator 0.0 osc
  -- user code
  -- osc.frequency.value <- 440 -- Hz
  -- setValue 440.0 $ frequency osc
  -- g <- createGain ctx
  -- let freq = sampleFreq
  -- setValue 440.0 =<< frequency osc
  setValue freq =<< frequency osc
  -- frequency osc <- 440.0
  -- do
  -- let x= setValue 440.0 $ frequency osc
    -- pure unit
  -- osc.connect(context.destination); -- connect it to the destination
  -- connect osc $ destination ctx
  -- connect destination ctx
  connect osc =<< destination ctx
  -- osc.start(); -- start the oscillator
  -- startOscillator 0.0 osc
  -- osc.stop(context.currentTime + 2); -- stop 2 seconds after the current time
  stopOscillator 1.0 osc
  pure unit

foreign import mainJsDoIt :: Int -> String
