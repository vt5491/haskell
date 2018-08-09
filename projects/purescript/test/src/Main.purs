module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)
-- import UserMod ((*))
import UserMod
import Data.Array (filter, (..))

-- import Audio.WebAudio.Types
-- import Audio.WebAudio.AudioContext
-- import Audio.WebAudio.AudioParam
-- -- import Audio.WebAudio.OscillatorNode
-- import Audio.WebAudio.Oscillator
-- import Audio.WebAudio.DestinationNode

import Audio.WebAudio.AudioParam (getValue, setValue, setValueAtTime)
import Audio.WebAudio.BaseAudioContext (createGain, createOscillator, currentTime, destination, newAudioContext, resume, state, suspend)
import Audio.WebAudio.GainNode (gain)
import Audio.WebAudio.Oscillator (OscillatorType(..), frequency, setOscillatorType, startOscillator, stopOscillator)
import Audio.WebAudio.Types (AudioContext, GainNode, OscillatorNode, AudioContextState(..), connect )

-- main :: Effect Unit
-- main = do
--   let i = 1 ..2
--   let str = show vtVal
--   log str
--   log "Hello sailor2!"

  -- let result = show factors
  -- log factors
-- main :: forall eff. (Eff (wau :: WebAudio, dom :: DOM | eff) Unit)
-- main :: forall eff. (Effect (wau :: WebAudio, dom :: DOM | eff) Unit)
main :: Effect Unit
main = do
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
  setValue 440.0 =<< frequency osc
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
