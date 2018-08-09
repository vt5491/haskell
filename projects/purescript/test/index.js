(function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
// shim for using process in browser
var process = module.exports = {};

// cached from whatever global is present so that test runners that stub it
// don't break things.  But we need to wrap it in a try catch in case it is
// wrapped in strict mode code which doesn't define any globals.  It's inside a
// function because try/catches deoptimize in certain engines.

var cachedSetTimeout;
var cachedClearTimeout;

function defaultSetTimout() {
    throw new Error('setTimeout has not been defined');
}
function defaultClearTimeout () {
    throw new Error('clearTimeout has not been defined');
}
(function () {
    try {
        if (typeof setTimeout === 'function') {
            cachedSetTimeout = setTimeout;
        } else {
            cachedSetTimeout = defaultSetTimout;
        }
    } catch (e) {
        cachedSetTimeout = defaultSetTimout;
    }
    try {
        if (typeof clearTimeout === 'function') {
            cachedClearTimeout = clearTimeout;
        } else {
            cachedClearTimeout = defaultClearTimeout;
        }
    } catch (e) {
        cachedClearTimeout = defaultClearTimeout;
    }
} ())
function runTimeout(fun) {
    if (cachedSetTimeout === setTimeout) {
        //normal enviroments in sane situations
        return setTimeout(fun, 0);
    }
    // if setTimeout wasn't available but was latter defined
    if ((cachedSetTimeout === defaultSetTimout || !cachedSetTimeout) && setTimeout) {
        cachedSetTimeout = setTimeout;
        return setTimeout(fun, 0);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedSetTimeout(fun, 0);
    } catch(e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't trust the global object when called normally
            return cachedSetTimeout.call(null, fun, 0);
        } catch(e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error
            return cachedSetTimeout.call(this, fun, 0);
        }
    }


}
function runClearTimeout(marker) {
    if (cachedClearTimeout === clearTimeout) {
        //normal enviroments in sane situations
        return clearTimeout(marker);
    }
    // if clearTimeout wasn't available but was latter defined
    if ((cachedClearTimeout === defaultClearTimeout || !cachedClearTimeout) && clearTimeout) {
        cachedClearTimeout = clearTimeout;
        return clearTimeout(marker);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedClearTimeout(marker);
    } catch (e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't  trust the global object when called normally
            return cachedClearTimeout.call(null, marker);
        } catch (e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error.
            // Some versions of I.E. have different rules for clearTimeout vs setTimeout
            return cachedClearTimeout.call(this, marker);
        }
    }



}
var queue = [];
var draining = false;
var currentQueue;
var queueIndex = -1;

function cleanUpNextTick() {
    if (!draining || !currentQueue) {
        return;
    }
    draining = false;
    if (currentQueue.length) {
        queue = currentQueue.concat(queue);
    } else {
        queueIndex = -1;
    }
    if (queue.length) {
        drainQueue();
    }
}

function drainQueue() {
    if (draining) {
        return;
    }
    var timeout = runTimeout(cleanUpNextTick);
    draining = true;

    var len = queue.length;
    while(len) {
        currentQueue = queue;
        queue = [];
        while (++queueIndex < len) {
            if (currentQueue) {
                currentQueue[queueIndex].run();
            }
        }
        queueIndex = -1;
        len = queue.length;
    }
    currentQueue = null;
    draining = false;
    runClearTimeout(timeout);
}

process.nextTick = function (fun) {
    var args = new Array(arguments.length - 1);
    if (arguments.length > 1) {
        for (var i = 1; i < arguments.length; i++) {
            args[i - 1] = arguments[i];
        }
    }
    queue.push(new Item(fun, args));
    if (queue.length === 1 && !draining) {
        runTimeout(drainQueue);
    }
};

// v8 likes predictible objects
function Item(fun, array) {
    this.fun = fun;
    this.array = array;
}
Item.prototype.run = function () {
    this.fun.apply(null, this.array);
};
process.title = 'browser';
process.browser = true;
process.env = {};
process.argv = [];
process.version = ''; // empty string to avoid regexp issues
process.versions = {};

function noop() {}

process.on = noop;
process.addListener = noop;
process.once = noop;
process.off = noop;
process.removeListener = noop;
process.removeAllListeners = noop;
process.emit = noop;
process.prependListener = noop;
process.prependOnceListener = noop;

process.listeners = function (name) { return [] }

process.binding = function (name) {
    throw new Error('process.binding is not supported');
};

process.cwd = function () { return '/' };
process.chdir = function (dir) {
    throw new Error('process.chdir is not supported');
};
process.umask = function() { return 0; };

},{}],2:[function(require,module,exports){
(function (setImmediate,clearImmediate){
var nextTick = require('process/browser.js').nextTick;
var apply = Function.prototype.apply;
var slice = Array.prototype.slice;
var immediateIds = {};
var nextImmediateId = 0;

// DOM APIs, for completeness

exports.setTimeout = function() {
  return new Timeout(apply.call(setTimeout, window, arguments), clearTimeout);
};
exports.setInterval = function() {
  return new Timeout(apply.call(setInterval, window, arguments), clearInterval);
};
exports.clearTimeout =
exports.clearInterval = function(timeout) { timeout.close(); };

function Timeout(id, clearFn) {
  this._id = id;
  this._clearFn = clearFn;
}
Timeout.prototype.unref = Timeout.prototype.ref = function() {};
Timeout.prototype.close = function() {
  this._clearFn.call(window, this._id);
};

// Does not start the time, just sets up the members needed.
exports.enroll = function(item, msecs) {
  clearTimeout(item._idleTimeoutId);
  item._idleTimeout = msecs;
};

exports.unenroll = function(item) {
  clearTimeout(item._idleTimeoutId);
  item._idleTimeout = -1;
};

exports._unrefActive = exports.active = function(item) {
  clearTimeout(item._idleTimeoutId);

  var msecs = item._idleTimeout;
  if (msecs >= 0) {
    item._idleTimeoutId = setTimeout(function onTimeout() {
      if (item._onTimeout)
        item._onTimeout();
    }, msecs);
  }
};

// That's not how node.js implements it but the exposed api is the same.
exports.setImmediate = typeof setImmediate === "function" ? setImmediate : function(fn) {
  var id = nextImmediateId++;
  var args = arguments.length < 2 ? false : slice.call(arguments, 1);

  immediateIds[id] = true;

  nextTick(function onNextTick() {
    if (immediateIds[id]) {
      // fn.call() is faster so we optimize for the common use-case
      // @see http://jsperf.com/call-apply-segu
      if (args) {
        fn.apply(null, args);
      } else {
        fn.call(null);
      }
      // Prevent ids from leaking
      exports.clearImmediate(id);
    }
  });

  return id;
};

exports.clearImmediate = typeof clearImmediate === "function" ? clearImmediate : function(id) {
  delete immediateIds[id];
};
}).call(this,require("timers").setImmediate,require("timers").clearImmediate)
},{"process/browser.js":1,"timers":2}],3:[function(require,module,exports){
/* jshint maxparams: false */
/* global exports, XMLHttpRequest */
"use strict";

// module Audio.WebAudio.AudioParam

exports.setValue = function(value) {
  return function(param) {
    return function() {
      param.value = value;
    };
  };
};


exports.getValue = function(param) {
  return function() {
    return param.value;
  };
};


exports.setValueAtTime = function(value) {
  return function(startTime) {
    return function(param) {
      return function() {
        param.setValueAtTime(value, startTime);
      };
    };
  };
};

exports.setTargetAtTime = function(value) {
  return function(startTime) {
    return function(timeConstant) {
      return function(param) {
        return function() {
          param.setTargetAtTime(value, startTime, timeConstant);
        };
      };
    };
  };
};


exports.linearRampToValueAtTime = function(value) {
  return function(endTime) {
    return function(param) {
      return function() {
        param.linearRampToValueAtTime(value, endTime);
      };
    };
  };
};


exports.exponentialRampToValueAtTime = function(value) {
  return function(endTime) {
    return function(param) {
      return function() {
        param.exponentialRampToValueAtTime(value, endTime);
      };
    };
  };
};


exports.cancelScheduledValues = function(startTime) {
  return function(param) {
    return function() {
      param.cancelScheduledValues(startTime);
    };
  };
};

},{}],4:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Audio_WebAudio_Types = require("../Audio.WebAudio.Types/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
module.exports = {
    setTargetAtTime: $foreign.setTargetAtTime,
    setValueAtTime: $foreign.setValueAtTime,
    getValue: $foreign.getValue,
    setValue: $foreign.setValue,
    linearRampToValueAtTime: $foreign.linearRampToValueAtTime,
    exponentialRampToValueAtTime: $foreign.exponentialRampToValueAtTime,
    cancelScheduledValues: $foreign.cancelScheduledValues
};

},{"../Audio.WebAudio.Types/index.js":12,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":3}],5:[function(require,module,exports){
/* jshint maxparams: false */
/* global exports, XMLHttpRequest */
"use strict";

// module Audio.WebAudio.AudioContext

exports.sampleRate = function(cx) {
  return function() {
    return cx.sampleRate;
  };
};

exports.currentTime = function(cx) {
  return function() {
    return cx.currentTime;
  };
};

exports._state = function(ctx) {
  return function() {
    return ctx.state;
  };
};

exports.suspend = function(ctx) {
  return function() {
    return ctx.suspend();
  };
};

exports.resume = function(ctx) {
  return function() {
    return ctx.resume();
  };
};

exports.decodeAudioData = function(cx) {
  return function(audioData) {
    return function(success) {
      return function(failure) {
        return function() {
          cx.decodeAudioData(audioData,
            function(data) {
              success(data)();
            },
            function(e) {
              failure(e.err);
            });
        };
      };
    };
  };
};

/* uncurrried version */
function _decodeAudioData (cx, audioData, onError, onSuccess) {
   cx.decodeAudioData(audioData, function (buff) {
     // console.log('buffer decoded OK ');
     onSuccess(buff);
    },
    function (e) {
      // console.log('buffer decode failed ');
      onError(e.err);
   });
};


exports.decodeAudioDataAsyncImpl = function(cx) {
  return function(audioData) {
    return function (onError, onSuccess) {
       _decodeAudioData (cx, audioData, onError, onSuccess);
       // Return a canceler, which is just another Aff effect.
       return function (cancelError, cancelerError, cancelerSuccess) {
         cancelerSuccess(); // invoke the success callback for the canceler
       };
    };
  };
};


exports.createBufferSource = function(cx) {
  return function() {
    return cx.createBufferSource();
  };
};

exports.createGain = function(ctx) {
  return function() {
    return ctx.createGain();
  };
};

exports.createOscillator = function(ctx) {
  return function() {
    return ctx.createOscillator();
  };
};

exports.createBiquadFilter = function(ctx) {
  return function() {
    return ctx.createBiquadFilter();
  };
};

exports.createDelay = function(ctx) {
  return function() {
    return ctx.createDelay();
  };
};

exports.createAnalyser = function(ctx) {
  return function() {
    return ctx.createAnalyser();
  };
};

exports.createStereoPanner = function(ctx) {
  return function() {
    return ctx.createStereoPanner();
  };
};

exports.createDynamicsCompressor = function(ctx) {
  return function() {
    return ctx.createDynamicsCompressor();
  };
};

exports.createConvolver = function(ctx) {
  return function() {
    return ctx.createConvolver();
  };
};

exports.newAudioContext = function() {
  return new (window.AudioContext || window.webkitAudioContext)();
};

},{}],6:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Audio_WebAudio_Types = require("../Audio.WebAudio.Types/index.js");
var Audio_WebAudio_Utils = require("../Audio.WebAudio.Utils/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_ArrayBuffer_Types = require("../Data.ArrayBuffer.Types/index.js");
var Data_Function = require("../Data.Function/index.js");
var Effect = require("../Effect/index.js");
var Effect_Aff = require("../Effect.Aff/index.js");
var Effect_Aff_Compat = require("../Effect.Aff.Compat/index.js");
var Prelude = require("../Prelude/index.js");
var state = function (ctx) {
    return function __do() {
        var v = $foreign._state(ctx)();
        if (v === "suspended") {
            return Audio_WebAudio_Types.SUSPENDED.value;
        };
        if (v === "running") {
            return Audio_WebAudio_Types.RUNNING.value;
        };
        if (v === "closed") {
            return Audio_WebAudio_Types.CLOSED.value;
        };
        return Audio_WebAudio_Types.CLOSED.value;
    };
};
var destination = Audio_WebAudio_Utils.unsafeGetProp("destination");
var decodeAudioDataAsync = function (ctx) {
    return function ($3) {
        return Effect_Aff_Compat.fromEffectFnAff($foreign.decodeAudioDataAsyncImpl(ctx)($3));
    };
};
module.exports = {
    destination: destination,
    state: state,
    decodeAudioDataAsync: decodeAudioDataAsync,
    newAudioContext: $foreign.newAudioContext,
    sampleRate: $foreign.sampleRate,
    currentTime: $foreign.currentTime,
    suspend: $foreign.suspend,
    resume: $foreign.resume,
    decodeAudioData: $foreign.decodeAudioData,
    createBufferSource: $foreign.createBufferSource,
    createGain: $foreign.createGain,
    createOscillator: $foreign.createOscillator,
    createAnalyser: $foreign.createAnalyser,
    createBiquadFilter: $foreign.createBiquadFilter,
    createConvolver: $foreign.createConvolver,
    createDelay: $foreign.createDelay,
    createDynamicsCompressor: $foreign.createDynamicsCompressor,
    createStereoPanner: $foreign.createStereoPanner
};

},{"../Audio.WebAudio.Types/index.js":12,"../Audio.WebAudio.Utils/index.js":14,"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Control.Semigroupoid/index.js":51,"../Data.ArrayBuffer.Types/index.js":64,"../Data.Function/index.js":95,"../Effect.Aff.Compat/index.js":170,"../Effect.Aff/index.js":172,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":5}],7:[function(require,module,exports){
/* jshint maxparams: false */
/* global exports, XMLHttpRequest */
"use strict";

// module Audio.WebAudio.GainNode

exports.gain = function(node) {
  return function() {
    return node.gain;
  };
};


},{}],8:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Audio_WebAudio_AudioParam = require("../Audio.WebAudio.AudioParam/index.js");
var Audio_WebAudio_Types = require("../Audio.WebAudio.Types/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var setGain = function (num) {
    return function (node) {
        return Control_Bind.bindFlipped(Effect.bindEffect)(Audio_WebAudio_AudioParam.setValue(num))($foreign.gain(node));
    };
};
module.exports = {
    setGain: setGain,
    gain: $foreign.gain
};

},{"../Audio.WebAudio.AudioParam/index.js":4,"../Audio.WebAudio.Types/index.js":12,"../Control.Bind/index.js":23,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":7}],9:[function(require,module,exports){
/* jshint maxparams: false */
/* global exports, XMLHttpRequest */
"use strict";

// module Audio.WebAudio.Oscillator

exports.startOscillator = function(when) {
  return function(n) {
    return function() {
      return n[n.start ? 'start' : 'noteOn'](when);
    };
  };
};


exports.stopOscillator = function(when) {
  return function(n) {
    return function() {
      return n[n.stop ? 'stop' : 'noteOff'](when);
    };
  };
};

},{}],10:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Audio_WebAudio_AudioParam = require("../Audio.WebAudio.AudioParam/index.js");
var Audio_WebAudio_Types = require("../Audio.WebAudio.Types/index.js");
var Audio_WebAudio_Utils = require("../Audio.WebAudio.Utils/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Show = require("../Data.Show/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var Sine = (function () {
    function Sine() {

    };
    Sine.value = new Sine();
    return Sine;
})();
var Square = (function () {
    function Square() {

    };
    Square.value = new Square();
    return Square;
})();
var Sawtooth = (function () {
    function Sawtooth() {

    };
    Sawtooth.value = new Sawtooth();
    return Sawtooth;
})();
var Triangle = (function () {
    function Triangle() {

    };
    Triangle.value = new Triangle();
    return Triangle;
})();
var Custom = (function () {
    function Custom() {

    };
    Custom.value = new Custom();
    return Custom;
})();
var readOscillatorType = function (v) {
    if (v === "sine") {
        return Sine.value;
    };
    if (v === "square") {
        return Square.value;
    };
    if (v === "sawtooth") {
        return Sawtooth.value;
    };
    if (v === "triangle") {
        return Triangle.value;
    };
    if (v === "custom") {
        return Custom.value;
    };
    return Sine.value;
};
var oscillatorTypeShow = new Data_Show.Show(function (v) {
    if (v instanceof Sine) {
        return "sine";
    };
    if (v instanceof Square) {
        return "square";
    };
    if (v instanceof Sawtooth) {
        return "sawtooth";
    };
    if (v instanceof Triangle) {
        return "triangle";
    };
    if (v instanceof Custom) {
        return "custom";
    };
    throw new Error("Failed pattern match at Audio.WebAudio.Oscillator line 18, column 1 - line 18, column 51: " + [ v.constructor.name ]);
});
var setOscillatorType = function (t) {
    return function (n) {
        return Audio_WebAudio_Utils.unsafeSetProp("type")(n)(Data_Show.show(oscillatorTypeShow)(t));
    };
};
var oscillatorType = function (n) {
    return Data_Functor.map(Effect.functorEffect)(readOscillatorType)(Audio_WebAudio_Utils.unsafeGetProp("type")(n));
};
var frequency = Audio_WebAudio_Utils.unsafeGetProp("frequency");
var setFrequency = function (num) {
    return function (node) {
        return Control_Bind.bindFlipped(Effect.bindEffect)(Audio_WebAudio_AudioParam.setValue(num))(frequency(node));
    };
};
var eqOscillatorType = new Data_Eq.Eq(function (x) {
    return function (y) {
        if (x instanceof Sine && y instanceof Sine) {
            return true;
        };
        if (x instanceof Square && y instanceof Square) {
            return true;
        };
        if (x instanceof Sawtooth && y instanceof Sawtooth) {
            return true;
        };
        if (x instanceof Triangle && y instanceof Triangle) {
            return true;
        };
        if (x instanceof Custom && y instanceof Custom) {
            return true;
        };
        return false;
    };
});
var ordOscillatorType = new Data_Ord.Ord(function () {
    return eqOscillatorType;
}, function (x) {
    return function (y) {
        if (x instanceof Sine && y instanceof Sine) {
            return Data_Ordering.EQ.value;
        };
        if (x instanceof Sine) {
            return Data_Ordering.LT.value;
        };
        if (y instanceof Sine) {
            return Data_Ordering.GT.value;
        };
        if (x instanceof Square && y instanceof Square) {
            return Data_Ordering.EQ.value;
        };
        if (x instanceof Square) {
            return Data_Ordering.LT.value;
        };
        if (y instanceof Square) {
            return Data_Ordering.GT.value;
        };
        if (x instanceof Sawtooth && y instanceof Sawtooth) {
            return Data_Ordering.EQ.value;
        };
        if (x instanceof Sawtooth) {
            return Data_Ordering.LT.value;
        };
        if (y instanceof Sawtooth) {
            return Data_Ordering.GT.value;
        };
        if (x instanceof Triangle && y instanceof Triangle) {
            return Data_Ordering.EQ.value;
        };
        if (x instanceof Triangle) {
            return Data_Ordering.LT.value;
        };
        if (y instanceof Triangle) {
            return Data_Ordering.GT.value;
        };
        if (x instanceof Custom && y instanceof Custom) {
            return Data_Ordering.EQ.value;
        };
        throw new Error("Failed pattern match at Audio.WebAudio.Oscillator line 34, column 8 - line 34, column 56: " + [ x.constructor.name, y.constructor.name ]);
    };
});
var detune = Audio_WebAudio_Utils.unsafeGetProp("detune");
var setDetune = function (num) {
    return function (node) {
        return Control_Bind.bindFlipped(Effect.bindEffect)(Audio_WebAudio_AudioParam.setValue(num))(detune(node));
    };
};
module.exports = {
    Sine: Sine,
    Square: Square,
    Sawtooth: Sawtooth,
    Triangle: Triangle,
    Custom: Custom,
    readOscillatorType: readOscillatorType,
    frequency: frequency,
    detune: detune,
    setFrequency: setFrequency,
    setDetune: setDetune,
    oscillatorType: oscillatorType,
    setOscillatorType: setOscillatorType,
    oscillatorTypeShow: oscillatorTypeShow,
    eqOscillatorType: eqOscillatorType,
    ordOscillatorType: ordOscillatorType,
    startOscillator: $foreign.startOscillator,
    stopOscillator: $foreign.stopOscillator
};

},{"../Audio.WebAudio.AudioParam/index.js":4,"../Audio.WebAudio.Types/index.js":12,"../Audio.WebAudio.Utils/index.js":14,"../Control.Bind/index.js":23,"../Data.Eq/index.js":86,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Show/index.js":141,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":9}],11:[function(require,module,exports){
"use strict";


exports.nodeConnect = function(_) {
  return function(_) {
    return function(source) {
      return function(sink) {
        return function() {
          source.connect(sink);
        };
      };
    };
  };
};

exports.nodeDisconnect = function(_) {
  return function(_) {
    return function(source) {
      return function(sink) {
        return function() {
          source.disconnect(sink);
        };
      };
    };
  };
};

exports.unsafeConnectParam = function(_) {
  return function(_) {
    return function(source) {
      return function(target) {
        return function(prop) {
          return function() {
            var value = target[prop];
            source.connect(value);
          };
        };
      };
    };
  };
};

},{}],12:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var Gain = (function () {
    function Gain(value0) {
        this.value0 = value0;
    };
    Gain.create = function (value0) {
        return new Gain(value0);
    };
    return Gain;
})();
var AudioBufferSource = (function () {
    function AudioBufferSource(value0) {
        this.value0 = value0;
    };
    AudioBufferSource.create = function (value0) {
        return new AudioBufferSource(value0);
    };
    return AudioBufferSource;
})();
var Oscillator = (function () {
    function Oscillator(value0) {
        this.value0 = value0;
    };
    Oscillator.create = function (value0) {
        return new Oscillator(value0);
    };
    return Oscillator;
})();
var BiquadFilter = (function () {
    function BiquadFilter(value0) {
        this.value0 = value0;
    };
    BiquadFilter.create = function (value0) {
        return new BiquadFilter(value0);
    };
    return BiquadFilter;
})();
var Delay = (function () {
    function Delay(value0) {
        this.value0 = value0;
    };
    Delay.create = function (value0) {
        return new Delay(value0);
    };
    return Delay;
})();
var Analyser = (function () {
    function Analyser(value0) {
        this.value0 = value0;
    };
    Analyser.create = function (value0) {
        return new Analyser(value0);
    };
    return Analyser;
})();
var StereoPanner = (function () {
    function StereoPanner(value0) {
        this.value0 = value0;
    };
    StereoPanner.create = function (value0) {
        return new StereoPanner(value0);
    };
    return StereoPanner;
})();
var DynamicsCompressor = (function () {
    function DynamicsCompressor(value0) {
        this.value0 = value0;
    };
    DynamicsCompressor.create = function (value0) {
        return new DynamicsCompressor(value0);
    };
    return DynamicsCompressor;
})();
var Convolver = (function () {
    function Convolver(value0) {
        this.value0 = value0;
    };
    Convolver.create = function (value0) {
        return new Convolver(value0);
    };
    return Convolver;
})();
var Destination = (function () {
    function Destination(value0) {
        this.value0 = value0;
    };
    Destination.create = function (value0) {
        return new Destination(value0);
    };
    return Destination;
})();
var SUSPENDED = (function () {
    function SUSPENDED() {

    };
    SUSPENDED.value = new SUSPENDED();
    return SUSPENDED;
})();
var RUNNING = (function () {
    function RUNNING() {

    };
    RUNNING.value = new RUNNING();
    return RUNNING;
})();
var CLOSED = (function () {
    function CLOSED() {

    };
    CLOSED.value = new CLOSED();
    return CLOSED;
})();
var BALANCED = (function () {
    function BALANCED() {

    };
    BALANCED.value = new BALANCED();
    return BALANCED;
})();
var INTERACTIVE = (function () {
    function INTERACTIVE() {

    };
    INTERACTIVE.value = new INTERACTIVE();
    return INTERACTIVE;
})();
var PLAYBACK = (function () {
    function PLAYBACK() {

    };
    PLAYBACK.value = new PLAYBACK();
    return PLAYBACK;
})();
var RawAudioNode = {};
var Connectable = function (connect, connectParam, disconnect) {
    this.connect = connect;
    this.connectParam = connectParam;
    this.disconnect = disconnect;
};
var showAudioContextState = new Data_Show.Show(function (v) {
    if (v instanceof SUSPENDED) {
        return "suspended";
    };
    if (v instanceof RUNNING) {
        return "running";
    };
    if (v instanceof CLOSED) {
        return "closed";
    };
    throw new Error("Failed pattern match at Audio.WebAudio.Types line 37, column 1 - line 37, column 57: " + [ v.constructor.name ]);
});
var showAudioContextPlaybackCategory = new Data_Show.Show(function (v) {
    if (v instanceof BALANCED) {
        return "balanced";
    };
    if (v instanceof INTERACTIVE) {
        return "interactive";
    };
    if (v instanceof PLAYBACK) {
        return "playback";
    };
    throw new Error("Failed pattern match at Audio.WebAudio.Types line 44, column 1 - line 44, column 79: " + [ v.constructor.name ]);
});
var eqAudioPlaybackCategory = new Data_Eq.Eq(function (x) {
    return function (y) {
        if (x instanceof BALANCED && y instanceof BALANCED) {
            return true;
        };
        if (x instanceof INTERACTIVE && y instanceof INTERACTIVE) {
            return true;
        };
        if (x instanceof PLAYBACK && y instanceof PLAYBACK) {
            return true;
        };
        return false;
    };
});
var eqAudioContextState = new Data_Eq.Eq(function (x) {
    return function (y) {
        if (x instanceof SUSPENDED && y instanceof SUSPENDED) {
            return true;
        };
        if (x instanceof RUNNING && y instanceof RUNNING) {
            return true;
        };
        if (x instanceof CLOSED && y instanceof CLOSED) {
            return true;
        };
        return false;
    };
});
var disconnect = function (dict) {
    return dict.disconnect;
};
var connectParam = function (dict) {
    return dict.connectParam;
};
var connect = function (dict) {
    return dict.connect;
};
var audioNodeStereoPannerNode = RawAudioNode;
var connectableStereoPannerNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeStereoPannerNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeStereoPannerNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeStereoPannerNode);
});
var audioNodeOscillatorNode = RawAudioNode;
var connectableOscillatorNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeOscillatorNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeOscillatorNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeOscillatorNode);
});
var audioNodeMediaElementAudioSourceNode = RawAudioNode;
var audioNodeGainNode = RawAudioNode;
var connectableGainNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeGainNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeGainNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeGainNode);
});
var audioNodeDynamicsCompressorNode = RawAudioNode;
var connectableDynamicsCompressorNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDynamicsCompressorNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeDynamicsCompressorNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeDynamicsCompressorNode);
});
var audioNodeDynamicsCConvolverNode = RawAudioNode;
var connectableConvolverNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDynamicsCConvolverNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeDynamicsCConvolverNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeDynamicsCConvolverNode);
});
var audioNodeDestinationNode = RawAudioNode;
var connectableDestinationNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDestinationNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeDestinationNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeDestinationNode);
});
var audioNodeDelayNode = RawAudioNode;
var connectableDelayNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDelayNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeDelayNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeDelayNode);
});
var audioNodeBiquadFilterNode = RawAudioNode;
var connectableBiquadFilterNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeBiquadFilterNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeBiquadFilterNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeBiquadFilterNode);
});
var audioNodeAudioBufferSourceNodeconnectParam = RawAudioNode;
var audioNodeAnalyserNode = RawAudioNode;
var connectableAnalyserNode = new Connectable(function (dictRawAudioNode) {
    return $foreign.nodeConnect(dictRawAudioNode)(audioNodeAnalyserNode);
}, function (dictRawAudioNode) {
    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeAnalyserNode);
}, function (dictRawAudioNode) {
    return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeAnalyserNode);
});
var connectableAudioNode = new Connectable(function (dictRawAudioNode) {
    return function (s) {
        return function (v) {
            if (v instanceof Gain) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeGainNode)(s)(v.value0);
            };
            if (v instanceof Oscillator) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeOscillatorNode)(s)(v.value0);
            };
            if (v instanceof BiquadFilter) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeBiquadFilterNode)(s)(v.value0);
            };
            if (v instanceof Delay) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDelayNode)(s)(v.value0);
            };
            if (v instanceof Analyser) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeAnalyserNode)(s)(v.value0);
            };
            if (v instanceof StereoPanner) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeStereoPannerNode)(s)(v.value0);
            };
            if (v instanceof DynamicsCompressor) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDynamicsCompressorNode)(s)(v.value0);
            };
            if (v instanceof Convolver) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDynamicsCConvolverNode)(s)(v.value0);
            };
            if (v instanceof Destination) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDestinationNode)(s)(v.value0);
            };
            return Control_Applicative.pure(Effect.applicativeEffect)(Data_Unit.unit);
        };
    };
}, function (dictRawAudioNode) {
    return function (s) {
        return function (v) {
            return function (p) {
                if (v instanceof Gain) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeGainNode)(s)(v.value0)(p);
                };
                if (v instanceof AudioBufferSource) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeAudioBufferSourceNodeconnectParam)(s)(v.value0)(p);
                };
                if (v instanceof Oscillator) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeOscillatorNode)(s)(v.value0)(p);
                };
                if (v instanceof BiquadFilter) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeBiquadFilterNode)(s)(v.value0)(p);
                };
                if (v instanceof Delay) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeDelayNode)(s)(v.value0)(p);
                };
                if (v instanceof Analyser) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeAnalyserNode)(s)(v.value0)(p);
                };
                if (v instanceof StereoPanner) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeStereoPannerNode)(s)(v.value0)(p);
                };
                if (v instanceof DynamicsCompressor) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeDynamicsCompressorNode)(s)(v.value0)(p);
                };
                if (v instanceof Convolver) {
                    return $foreign.unsafeConnectParam(dictRawAudioNode)(audioNodeDynamicsCConvolverNode)(s)(v.value0)(p);
                };
                if (v instanceof Destination) {
                    return Control_Applicative.pure(Effect.applicativeEffect)(Data_Unit.unit);
                };
                throw new Error("Failed pattern match at Audio.WebAudio.Types line 123, column 1 - line 123, column 55: " + [ s.constructor.name, v.constructor.name, p.constructor.name ]);
            };
        };
    };
}, function (dictRawAudioNode) {
    return function (s) {
        return function (v) {
            if (v instanceof Gain) {
                return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeGainNode)(s)(v.value0);
            };
            if (v instanceof Oscillator) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeOscillatorNode)(s)(v.value0);
            };
            if (v instanceof BiquadFilter) {
                return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeBiquadFilterNode)(s)(v.value0);
            };
            if (v instanceof Delay) {
                return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeDelayNode)(s)(v.value0);
            };
            if (v instanceof Analyser) {
                return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeAnalyserNode)(s)(v.value0);
            };
            if (v instanceof StereoPanner) {
                return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeStereoPannerNode)(s)(v.value0);
            };
            if (v instanceof DynamicsCompressor) {
                return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeDynamicsCompressorNode)(s)(v.value0);
            };
            if (v instanceof Convolver) {
                return $foreign.nodeDisconnect(dictRawAudioNode)(audioNodeDynamicsCConvolverNode)(s)(v.value0);
            };
            if (v instanceof Destination) {
                return $foreign.nodeConnect(dictRawAudioNode)(audioNodeDestinationNode)(s)(v.value0);
            };
            return Control_Applicative.pure(Effect.applicativeEffect)(Data_Unit.unit);
        };
    };
});
module.exports = {
    RawAudioNode: RawAudioNode,
    Connectable: Connectable,
    Gain: Gain,
    AudioBufferSource: AudioBufferSource,
    Oscillator: Oscillator,
    BiquadFilter: BiquadFilter,
    Delay: Delay,
    Analyser: Analyser,
    StereoPanner: StereoPanner,
    DynamicsCompressor: DynamicsCompressor,
    Convolver: Convolver,
    Destination: Destination,
    SUSPENDED: SUSPENDED,
    RUNNING: RUNNING,
    CLOSED: CLOSED,
    BALANCED: BALANCED,
    INTERACTIVE: INTERACTIVE,
    PLAYBACK: PLAYBACK,
    connect: connect,
    disconnect: disconnect,
    connectParam: connectParam,
    eqAudioContextState: eqAudioContextState,
    showAudioContextState: showAudioContextState,
    eqAudioPlaybackCategory: eqAudioPlaybackCategory,
    showAudioContextPlaybackCategory: showAudioContextPlaybackCategory,
    audioNodeAudioBufferSourceNodeconnectParam: audioNodeAudioBufferSourceNodeconnectParam,
    audioNodeMediaElementAudioSourceNode: audioNodeMediaElementAudioSourceNode,
    audioNodeGainNode: audioNodeGainNode,
    audioNodeDestinationNode: audioNodeDestinationNode,
    audioNodeOscillatorNode: audioNodeOscillatorNode,
    audioNodeBiquadFilterNode: audioNodeBiquadFilterNode,
    audioNodeDelayNode: audioNodeDelayNode,
    audioNodeAnalyserNode: audioNodeAnalyserNode,
    audioNodeStereoPannerNode: audioNodeStereoPannerNode,
    audioNodeDynamicsCompressorNode: audioNodeDynamicsCompressorNode,
    audioNodeDynamicsCConvolverNode: audioNodeDynamicsCConvolverNode,
    connectableGainNode: connectableGainNode,
    connectableOscillatorNode: connectableOscillatorNode,
    connectableBiquadFilterNode: connectableBiquadFilterNode,
    connectableDelayNode: connectableDelayNode,
    connectableAnalyserNode: connectableAnalyserNode,
    connectableStereoPannerNode: connectableStereoPannerNode,
    connectableDynamicsCompressorNode: connectableDynamicsCompressorNode,
    connectableConvolverNode: connectableConvolverNode,
    connectableDestinationNode: connectableDestinationNode,
    connectableAudioNode: connectableAudioNode
};

},{"../Control.Applicative/index.js":17,"../Data.Eq/index.js":86,"../Data.Show/index.js":141,"../Data.Unit/index.js":168,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":11}],13:[function(require,module,exports){
/* jshint maxparams: false */
/* global exports, XMLHttpRequest */
"use strict";

// module Audio.WebAudio.Utils


exports.unsafeSetProp = function(prop) {
  return function(obj) {
    return function(value) {
      return function() {
        obj[prop] = value;
      };
    };
  };
};


exports.unsafeGetProp = function(prop) {
  return function(obj) {
    return function() {
      return obj[prop];
    };
  };
};

},{}],14:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_ArrayBuffer_ArrayBuffer = require("../Data.ArrayBuffer.ArrayBuffer/index.js");
var Data_ArrayBuffer_DataView = require("../Data.ArrayBuffer.DataView/index.js");
var Data_ArrayBuffer_Typed = require("../Data.ArrayBuffer.Typed/index.js");
var Data_ArrayBuffer_Types = require("../Data.ArrayBuffer.Types/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var createUint8Buffer = function (len) {
    return Data_Functor.map(Effect.functorEffect)(function ($0) {
        return Data_ArrayBuffer_Typed.asUint8Array(Data_ArrayBuffer_DataView.whole($0));
    })(Data_ArrayBuffer_ArrayBuffer.create(len));
};
var createFloat32Buffer = function (len) {
    return Data_Functor.map(Effect.functorEffect)(function ($1) {
        return Data_ArrayBuffer_Typed.asFloat32Array(Data_ArrayBuffer_DataView.whole($1));
    })(Data_ArrayBuffer_ArrayBuffer.create(len));
};
module.exports = {
    createUint8Buffer: createUint8Buffer,
    createFloat32Buffer: createFloat32Buffer,
    unsafeGetProp: $foreign.unsafeGetProp,
    unsafeSetProp: $foreign.unsafeSetProp
};

},{"../Control.Semigroupoid/index.js":51,"../Data.ArrayBuffer.ArrayBuffer/index.js":59,"../Data.ArrayBuffer.DataView/index.js":61,"../Data.ArrayBuffer.Typed/index.js":63,"../Data.ArrayBuffer.Types/index.js":64,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":13}],15:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Functor = require("../Data.Functor/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Alt = function (Functor0, alt) {
    this.Functor0 = Functor0;
    this.alt = alt;
};
var altArray = new Alt(function () {
    return Data_Functor.functorArray;
}, Data_Semigroup.append(Data_Semigroup.semigroupArray));
var alt = function (dict) {
    return dict.alt;
};
module.exports = {
    Alt: Alt,
    alt: alt,
    altArray: altArray
};

},{"../Data.Functor/index.js":102,"../Data.Semigroup/index.js":137}],16:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Alternative = function (Applicative0, Plus1) {
    this.Applicative0 = Applicative0;
    this.Plus1 = Plus1;
};
var alternativeArray = new Alternative(function () {
    return Control_Applicative.applicativeArray;
}, function () {
    return Control_Plus.plusArray;
});
module.exports = {
    Alternative: Alternative,
    alternativeArray: alternativeArray
};

},{"../Control.Alt/index.js":15,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Plus/index.js":50,"../Data.Functor/index.js":102}],17:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Apply = require("../Control.Apply/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Applicative = function (Apply0, pure) {
    this.Apply0 = Apply0;
    this.pure = pure;
};
var pure = function (dict) {
    return dict.pure;
};
var unless = function (dictApplicative) {
    return function (v) {
        return function (v1) {
            if (!v) {
                return v1;
            };
            if (v) {
                return pure(dictApplicative)(Data_Unit.unit);
            };
            throw new Error("Failed pattern match at Control.Applicative line 62, column 1 - line 62, column 65: " + [ v.constructor.name, v1.constructor.name ]);
        };
    };
};
var when = function (dictApplicative) {
    return function (v) {
        return function (v1) {
            if (v) {
                return v1;
            };
            if (!v) {
                return pure(dictApplicative)(Data_Unit.unit);
            };
            throw new Error("Failed pattern match at Control.Applicative line 57, column 1 - line 57, column 63: " + [ v.constructor.name, v1.constructor.name ]);
        };
    };
};
var liftA1 = function (dictApplicative) {
    return function (f) {
        return function (a) {
            return Control_Apply.apply(dictApplicative.Apply0())(pure(dictApplicative)(f))(a);
        };
    };
};
var applicativeFn = new Applicative(function () {
    return Control_Apply.applyFn;
}, function (x) {
    return function (v) {
        return x;
    };
});
var applicativeArray = new Applicative(function () {
    return Control_Apply.applyArray;
}, function (x) {
    return [ x ];
});
module.exports = {
    Applicative: Applicative,
    pure: pure,
    liftA1: liftA1,
    unless: unless,
    when: when,
    applicativeFn: applicativeFn,
    applicativeArray: applicativeArray
};

},{"../Control.Apply/index.js":19,"../Data.Functor/index.js":102,"../Data.Unit/index.js":168}],18:[function(require,module,exports){
"use strict";

exports.arrayApply = function (fs) {
  return function (xs) {
    var l = fs.length;
    var k = xs.length;
    var result = new Array(l*k);
    var n = 0;
    for (var i = 0; i < l; i++) {
      var f = fs[i];
      for (var j = 0; j < k; j++) {
        result[n++] = f(xs[j]);
      }
    }
    return result;
  };
};

},{}],19:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Category = require("../Control.Category/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Apply = function (Functor0, apply) {
    this.Functor0 = Functor0;
    this.apply = apply;
};
var applyFn = new Apply(function () {
    return Data_Functor.functorFn;
}, function (f) {
    return function (g) {
        return function (x) {
            return f(x)(g(x));
        };
    };
});
var applyArray = new Apply(function () {
    return Data_Functor.functorArray;
}, $foreign.arrayApply);
var apply = function (dict) {
    return dict.apply;
};
var applyFirst = function (dictApply) {
    return function (a) {
        return function (b) {
            return apply(dictApply)(Data_Functor.map(dictApply.Functor0())(Data_Function["const"])(a))(b);
        };
    };
};
var applySecond = function (dictApply) {
    return function (a) {
        return function (b) {
            return apply(dictApply)(Data_Functor.map(dictApply.Functor0())(Data_Function["const"](Control_Category.identity(Control_Category.categoryFn)))(a))(b);
        };
    };
};
var lift2 = function (dictApply) {
    return function (f) {
        return function (a) {
            return function (b) {
                return apply(dictApply)(Data_Functor.map(dictApply.Functor0())(f)(a))(b);
            };
        };
    };
};
var lift3 = function (dictApply) {
    return function (f) {
        return function (a) {
            return function (b) {
                return function (c) {
                    return apply(dictApply)(apply(dictApply)(Data_Functor.map(dictApply.Functor0())(f)(a))(b))(c);
                };
            };
        };
    };
};
var lift4 = function (dictApply) {
    return function (f) {
        return function (a) {
            return function (b) {
                return function (c) {
                    return function (d) {
                        return apply(dictApply)(apply(dictApply)(apply(dictApply)(Data_Functor.map(dictApply.Functor0())(f)(a))(b))(c))(d);
                    };
                };
            };
        };
    };
};
var lift5 = function (dictApply) {
    return function (f) {
        return function (a) {
            return function (b) {
                return function (c) {
                    return function (d) {
                        return function (e) {
                            return apply(dictApply)(apply(dictApply)(apply(dictApply)(apply(dictApply)(Data_Functor.map(dictApply.Functor0())(f)(a))(b))(c))(d))(e);
                        };
                    };
                };
            };
        };
    };
};
module.exports = {
    Apply: Apply,
    apply: apply,
    applyFirst: applyFirst,
    applySecond: applySecond,
    lift2: lift2,
    lift3: lift3,
    lift4: lift4,
    lift5: lift5,
    applyFn: applyFn,
    applyArray: applyArray
};

},{"../Control.Category/index.js":24,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"./foreign.js":18}],20:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Biapply = require("../Control.Biapply/index.js");
var Biapplicative = function (Biapply0, bipure) {
    this.Biapply0 = Biapply0;
    this.bipure = bipure;
};
var bipure = function (dict) {
    return dict.bipure;
};
module.exports = {
    bipure: bipure,
    Biapplicative: Biapplicative
};

},{"../Control.Biapply/index.js":21}],21:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Function = require("../Data.Function/index.js");
var Biapply = function (Bifunctor0, biapply) {
    this.Bifunctor0 = Bifunctor0;
    this.biapply = biapply;
};
var biapply = function (dict) {
    return dict.biapply;
};
var biapplyFirst = function (dictBiapply) {
    return function (a) {
        return function (b) {
            return biapply(dictBiapply)(Control_Category.identity(Control_Category.categoryFn)(Data_Bifunctor.bimap(dictBiapply.Bifunctor0())(Data_Function["const"](Control_Category.identity(Control_Category.categoryFn)))(Data_Function["const"](Control_Category.identity(Control_Category.categoryFn))))(a))(b);
        };
    };
};
var biapplySecond = function (dictBiapply) {
    return function (a) {
        return function (b) {
            return biapply(dictBiapply)(Control_Category.identity(Control_Category.categoryFn)(Data_Bifunctor.bimap(dictBiapply.Bifunctor0())(Data_Function["const"])(Data_Function["const"]))(a))(b);
        };
    };
};
var bilift2 = function (dictBiapply) {
    return function (f) {
        return function (g) {
            return function (a) {
                return function (b) {
                    return biapply(dictBiapply)(Control_Category.identity(Control_Category.categoryFn)(Data_Bifunctor.bimap(dictBiapply.Bifunctor0())(f)(g))(a))(b);
                };
            };
        };
    };
};
var bilift3 = function (dictBiapply) {
    return function (f) {
        return function (g) {
            return function (a) {
                return function (b) {
                    return function (c) {
                        return biapply(dictBiapply)(biapply(dictBiapply)(Control_Category.identity(Control_Category.categoryFn)(Data_Bifunctor.bimap(dictBiapply.Bifunctor0())(f)(g))(a))(b))(c);
                    };
                };
            };
        };
    };
};
module.exports = {
    biapply: biapply,
    Biapply: Biapply,
    biapplyFirst: biapplyFirst,
    biapplySecond: biapplySecond,
    bilift2: bilift2,
    bilift3: bilift3
};

},{"../Control.Category/index.js":24,"../Data.Bifunctor/index.js":73,"../Data.Function/index.js":95}],22:[function(require,module,exports){
"use strict";

exports.arrayBind = function (arr) {
  return function (f) {
    var result = [];
    for (var i = 0, l = arr.length; i < l; i++) {
      Array.prototype.push.apply(result, f(arr[i]));
    }
    return result;
  };
};

},{}],23:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Bind = function (Apply0, bind) {
    this.Apply0 = Apply0;
    this.bind = bind;
};
var Discard = function (discard) {
    this.discard = discard;
};
var discard = function (dict) {
    return dict.discard;
};
var bindFn = new Bind(function () {
    return Control_Apply.applyFn;
}, function (m) {
    return function (f) {
        return function (x) {
            return f(m(x))(x);
        };
    };
});
var bindArray = new Bind(function () {
    return Control_Apply.applyArray;
}, $foreign.arrayBind);
var bind = function (dict) {
    return dict.bind;
};
var bindFlipped = function (dictBind) {
    return Data_Function.flip(bind(dictBind));
};
var composeKleisliFlipped = function (dictBind) {
    return function (f) {
        return function (g) {
            return function (a) {
                return bindFlipped(dictBind)(f)(g(a));
            };
        };
    };
};
var composeKleisli = function (dictBind) {
    return function (f) {
        return function (g) {
            return function (a) {
                return bind(dictBind)(f(a))(g);
            };
        };
    };
};
var discardUnit = new Discard(function (dictBind) {
    return bind(dictBind);
});
var ifM = function (dictBind) {
    return function (cond) {
        return function (t) {
            return function (f) {
                return bind(dictBind)(cond)(function (cond$prime) {
                    if (cond$prime) {
                        return t;
                    };
                    return f;
                });
            };
        };
    };
};
var join = function (dictBind) {
    return function (m) {
        return bind(dictBind)(m)(Control_Category.identity(Control_Category.categoryFn));
    };
};
module.exports = {
    Bind: Bind,
    bind: bind,
    bindFlipped: bindFlipped,
    Discard: Discard,
    discard: discard,
    join: join,
    composeKleisli: composeKleisli,
    composeKleisliFlipped: composeKleisliFlipped,
    ifM: ifM,
    bindFn: bindFn,
    bindArray: bindArray,
    discardUnit: discardUnit
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Unit/index.js":168,"./foreign.js":22}],24:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Category = function (Semigroupoid0, identity) {
    this.Semigroupoid0 = Semigroupoid0;
    this.identity = identity;
};
var identity = function (dict) {
    return dict.identity;
};
var categoryFn = new Category(function () {
    return Control_Semigroupoid.semigroupoidFn;
}, function (x) {
    return x;
});
module.exports = {
    Category: Category,
    identity: identity,
    categoryFn: categoryFn
};

},{"../Control.Semigroupoid/index.js":51}],25:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Extend = require("../Control.Extend/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Comonad = function (Extend0, extract) {
    this.Extend0 = Extend0;
    this.extract = extract;
};
var extract = function (dict) {
    return dict.extract;
};
module.exports = {
    Comonad: Comonad,
    extract: extract
};

},{"../Control.Extend/index.js":27,"../Data.Functor/index.js":102}],26:[function(require,module,exports){
"use strict";

exports.arrayExtend = function(f) {
  return function(xs) {
    return xs.map(function (_, i, xs) {
      return f(xs.slice(i));
    });
  };
};

},{}],27:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Category = require("../Control.Category/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Extend = function (Functor0, extend) {
    this.Functor0 = Functor0;
    this.extend = extend;
};
var extendFn = function (dictSemigroup) {
    return new Extend(function () {
        return Data_Functor.functorFn;
    }, function (f) {
        return function (g) {
            return function (w) {
                return f(function (w$prime) {
                    return g(Data_Semigroup.append(dictSemigroup)(w)(w$prime));
                });
            };
        };
    });
};
var extendArray = new Extend(function () {
    return Data_Functor.functorArray;
}, $foreign.arrayExtend);
var extend = function (dict) {
    return dict.extend;
};
var extendFlipped = function (dictExtend) {
    return function (w) {
        return function (f) {
            return extend(dictExtend)(f)(w);
        };
    };
};
var duplicate = function (dictExtend) {
    return extend(dictExtend)(Control_Category.identity(Control_Category.categoryFn));
};
var composeCoKleisliFlipped = function (dictExtend) {
    return function (f) {
        return function (g) {
            return function (w) {
                return f(extend(dictExtend)(g)(w));
            };
        };
    };
};
var composeCoKleisli = function (dictExtend) {
    return function (f) {
        return function (g) {
            return function (w) {
                return g(extend(dictExtend)(f)(w));
            };
        };
    };
};
module.exports = {
    Extend: Extend,
    extend: extend,
    extendFlipped: extendFlipped,
    composeCoKleisli: composeCoKleisli,
    composeCoKleisliFlipped: composeCoKleisliFlipped,
    duplicate: duplicate,
    extendFn: extendFn,
    extendArray: extendArray
};

},{"../Control.Category/index.js":24,"../Data.Functor/index.js":102,"../Data.Semigroup/index.js":137,"./foreign.js":26}],28:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Unit = require("../Data.Unit/index.js");
var Lazy = function (defer) {
    this.defer = defer;
};
var lazyUnit = new Lazy(function (v) {
    return Data_Unit.unit;
});
var lazyFn = new Lazy(function (f) {
    return function (x) {
        return f(Data_Unit.unit)(x);
    };
});
var defer = function (dict) {
    return dict.defer;
};
var fix = function (dictLazy) {
    return function (f) {
        var go = defer(dictLazy)(function (v) {
            return f(go);
        });
        return go;
    };
};
module.exports = {
    defer: defer,
    Lazy: Lazy,
    fix: fix,
    lazyFn: lazyFn,
    lazyUnit: lazyUnit
};

},{"../Data.Unit/index.js":168}],29:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Prelude = require("../Prelude/index.js");
var MonadCont = function (Monad0, callCC) {
    this.Monad0 = Monad0;
    this.callCC = callCC;
};
var callCC = function (dict) {
    return dict.callCC;
};
module.exports = {
    MonadCont: MonadCont,
    callCC: callCC
};

},{"../Prelude/index.js":195}],30:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Monad_Cont_Class = require("../Control.Monad.Cont.Class/index.js");
var Control_Monad_Reader_Class = require("../Control.Monad.Reader.Class/index.js");
var Control_Monad_State_Class = require("../Control.Monad.State.Class/index.js");
var Control_Monad_Trans_Class = require("../Control.Monad.Trans.Class/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Effect_Class = require("../Effect.Class/index.js");
var Prelude = require("../Prelude/index.js");
var ContT = function (x) {
    return x;
};
var withContT = function (f) {
    return function (v) {
        return function (k) {
            return v(f(k));
        };
    };
};
var runContT = function (v) {
    return function (k) {
        return v(k);
    };
};
var newtypeContT = new Data_Newtype.Newtype(function (n) {
    return n;
}, ContT);
var monadTransContT = new Control_Monad_Trans_Class.MonadTrans(function (dictMonad) {
    return function (m) {
        return function (k) {
            return Control_Bind.bind(dictMonad.Bind1())(m)(k);
        };
    };
});
var mapContT = function (f) {
    return function (v) {
        return function (k) {
            return f(v(k));
        };
    };
};
var functorContT = function (dictFunctor) {
    return new Data_Functor.Functor(function (f) {
        return function (v) {
            return function (k) {
                return v(function (a) {
                    return k(f(a));
                });
            };
        };
    });
};
var applyContT = function (dictApply) {
    return new Control_Apply.Apply(function () {
        return functorContT(dictApply.Functor0());
    }, function (v) {
        return function (v1) {
            return function (k) {
                return v(function (g) {
                    return v1(function (a) {
                        return k(g(a));
                    });
                });
            };
        };
    });
};
var bindContT = function (dictBind) {
    return new Control_Bind.Bind(function () {
        return applyContT(dictBind.Apply0());
    }, function (v) {
        return function (k) {
            return function (k$prime) {
                return v(function (a) {
                    var v1 = k(a);
                    return v1(k$prime);
                });
            };
        };
    });
};
var applicativeContT = function (dictApplicative) {
    return new Control_Applicative.Applicative(function () {
        return applyContT(dictApplicative.Apply0());
    }, function (a) {
        return function (k) {
            return k(a);
        };
    });
};
var monadContT = function (dictMonad) {
    return new Control_Monad.Monad(function () {
        return applicativeContT(dictMonad.Applicative0());
    }, function () {
        return bindContT(dictMonad.Bind1());
    });
};
var monadAskContT = function (dictMonadAsk) {
    return new Control_Monad_Reader_Class.MonadAsk(function () {
        return monadContT(dictMonadAsk.Monad0());
    }, Control_Monad_Trans_Class.lift(monadTransContT)(dictMonadAsk.Monad0())(Control_Monad_Reader_Class.ask(dictMonadAsk)));
};
var monadReaderContT = function (dictMonadReader) {
    return new Control_Monad_Reader_Class.MonadReader(function () {
        return monadAskContT(dictMonadReader.MonadAsk0());
    }, function (f) {
        return function (v) {
            return function (k) {
                return Control_Bind.bind(((dictMonadReader.MonadAsk0()).Monad0()).Bind1())(Control_Monad_Reader_Class.ask(dictMonadReader.MonadAsk0()))(function (v1) {
                    return Control_Monad_Reader_Class.local(dictMonadReader)(f)(v(function ($45) {
                        return Control_Monad_Reader_Class.local(dictMonadReader)(Data_Function["const"](v1))(k($45));
                    }));
                });
            };
        };
    });
};
var monadContContT = function (dictMonad) {
    return new Control_Monad_Cont_Class.MonadCont(function () {
        return monadContT(dictMonad);
    }, function (f) {
        return function (k) {
            var v = f(function (a) {
                return function (v1) {
                    return k(a);
                };
            });
            return v(k);
        };
    });
};
var monadEffectContT = function (dictMonadEffect) {
    return new Effect_Class.MonadEffect(function () {
        return monadContT(dictMonadEffect.Monad0());
    }, function ($46) {
        return Control_Monad_Trans_Class.lift(monadTransContT)(dictMonadEffect.Monad0())(Effect_Class.liftEffect(dictMonadEffect)($46));
    });
};
var monadStateContT = function (dictMonadState) {
    return new Control_Monad_State_Class.MonadState(function () {
        return monadContT(dictMonadState.Monad0());
    }, function ($47) {
        return Control_Monad_Trans_Class.lift(monadTransContT)(dictMonadState.Monad0())(Control_Monad_State_Class.state(dictMonadState)($47));
    });
};
module.exports = {
    ContT: ContT,
    runContT: runContT,
    mapContT: mapContT,
    withContT: withContT,
    newtypeContT: newtypeContT,
    monadContContT: monadContContT,
    functorContT: functorContT,
    applyContT: applyContT,
    applicativeContT: applicativeContT,
    bindContT: bindContT,
    monadContT: monadContT,
    monadTransContT: monadTransContT,
    monadEffectContT: monadEffectContT,
    monadAskContT: monadAskContT,
    monadReaderContT: monadReaderContT,
    monadStateContT: monadStateContT
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad.Cont.Class/index.js":29,"../Control.Monad.Reader.Class/index.js":34,"../Control.Monad.State.Class/index.js":41,"../Control.Monad.Trans.Class/index.js":42,"../Control.Monad/index.js":47,"../Control.Semigroupoid/index.js":51,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Newtype/index.js":121,"../Effect.Class/index.js":173,"../Prelude/index.js":195}],31:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var MonadThrow = function (Monad0, throwError) {
    this.Monad0 = Monad0;
    this.throwError = throwError;
};
var MonadError = function (MonadThrow0, catchError) {
    this.MonadThrow0 = MonadThrow0;
    this.catchError = catchError;
};
var throwError = function (dict) {
    return dict.throwError;
};
var monadThrowMaybe = new MonadThrow(function () {
    return Data_Maybe.monadMaybe;
}, Data_Function["const"](Data_Maybe.Nothing.value));
var monadThrowEither = new MonadThrow(function () {
    return Data_Either.monadEither;
}, Data_Either.Left.create);
var monadErrorMaybe = new MonadError(function () {
    return monadThrowMaybe;
}, function (v) {
    return function (v1) {
        if (v instanceof Data_Maybe.Nothing) {
            return v1(Data_Unit.unit);
        };
        if (v instanceof Data_Maybe.Just) {
            return new Data_Maybe.Just(v.value0);
        };
        throw new Error("Failed pattern match at Control.Monad.Error.Class line 76, column 1 - line 76, column 50: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var monadErrorEither = new MonadError(function () {
    return monadThrowEither;
}, function (v) {
    return function (v1) {
        if (v instanceof Data_Either.Left) {
            return v1(v.value0);
        };
        if (v instanceof Data_Either.Right) {
            return new Data_Either.Right(v.value0);
        };
        throw new Error("Failed pattern match at Control.Monad.Error.Class line 69, column 1 - line 69, column 53: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var catchError = function (dict) {
    return dict.catchError;
};
var catchJust = function (dictMonadError) {
    return function (p) {
        return function (act) {
            return function (handler) {
                var handle = function (e) {
                    var v = p(e);
                    if (v instanceof Data_Maybe.Nothing) {
                        return throwError(dictMonadError.MonadThrow0())(e);
                    };
                    if (v instanceof Data_Maybe.Just) {
                        return handler(v.value0);
                    };
                    throw new Error("Failed pattern match at Control.Monad.Error.Class line 54, column 5 - line 56, column 26: " + [ v.constructor.name ]);
                };
                return catchError(dictMonadError)(act)(handle);
            };
        };
    };
};
var $$try = function (dictMonadError) {
    return function (a) {
        return catchError(dictMonadError)(Data_Functor.map(((((dictMonadError.MonadThrow0()).Monad0()).Bind1()).Apply0()).Functor0())(Data_Either.Right.create)(a))(function ($21) {
            return Control_Applicative.pure(((dictMonadError.MonadThrow0()).Monad0()).Applicative0())(Data_Either.Left.create($21));
        });
    };
};
var withResource = function (dictMonadError) {
    return function (acquire) {
        return function (release) {
            return function (kleisli) {
                return Control_Bind.bind(((dictMonadError.MonadThrow0()).Monad0()).Bind1())(acquire)(function (v) {
                    return Control_Bind.bind(((dictMonadError.MonadThrow0()).Monad0()).Bind1())($$try(dictMonadError)(kleisli(v)))(function (v1) {
                        return Control_Bind.discard(Control_Bind.discardUnit)(((dictMonadError.MonadThrow0()).Monad0()).Bind1())(release(v))(function () {
                            return Data_Either.either(throwError(dictMonadError.MonadThrow0()))(Control_Applicative.pure(((dictMonadError.MonadThrow0()).Monad0()).Applicative0()))(v1);
                        });
                    });
                });
            };
        };
    };
};
module.exports = {
    catchError: catchError,
    throwError: throwError,
    MonadThrow: MonadThrow,
    MonadError: MonadError,
    catchJust: catchJust,
    "try": $$try,
    withResource: withResource,
    monadThrowEither: monadThrowEither,
    monadErrorEither: monadErrorEither,
    monadThrowMaybe: monadThrowMaybe,
    monadErrorMaybe: monadErrorMaybe
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Control.Semigroupoid/index.js":51,"../Data.Either/index.js":82,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Unit/index.js":168,"../Prelude/index.js":195}],32:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Monad_Cont_Class = require("../Control.Monad.Cont.Class/index.js");
var Control_Monad_Error_Class = require("../Control.Monad.Error.Class/index.js");
var Control_Monad_Reader_Class = require("../Control.Monad.Reader.Class/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Control_Monad_State_Class = require("../Control.Monad.State.Class/index.js");
var Control_Monad_Trans_Class = require("../Control.Monad.Trans.Class/index.js");
var Control_Monad_Writer_Class = require("../Control.Monad.Writer.Class/index.js");
var Control_MonadPlus = require("../Control.MonadPlus/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Effect_Class = require("../Effect.Class/index.js");
var Prelude = require("../Prelude/index.js");
var ExceptT = function (x) {
    return x;
};
var withExceptT = function (dictFunctor) {
    return function (f) {
        return function (v) {
            var mapLeft = function (v1) {
                return function (v2) {
                    if (v2 instanceof Data_Either.Right) {
                        return new Data_Either.Right(v2.value0);
                    };
                    if (v2 instanceof Data_Either.Left) {
                        return new Data_Either.Left(v1(v2.value0));
                    };
                    throw new Error("Failed pattern match at Control.Monad.Except.Trans line 42, column 3 - line 42, column 32: " + [ v1.constructor.name, v2.constructor.name ]);
                };
            };
            return ExceptT(Data_Functor.map(dictFunctor)(mapLeft(f))(v));
        };
    };
};
var runExceptT = function (v) {
    return v;
};
var newtypeExceptT = new Data_Newtype.Newtype(function (n) {
    return n;
}, ExceptT);
var monadTransExceptT = new Control_Monad_Trans_Class.MonadTrans(function (dictMonad) {
    return function (m) {
        return Control_Bind.bind(dictMonad.Bind1())(m)(function (v) {
            return Control_Applicative.pure(dictMonad.Applicative0())(new Data_Either.Right(v));
        });
    };
});
var mapExceptT = function (f) {
    return function (v) {
        return f(v);
    };
};
var functorExceptT = function (dictFunctor) {
    return new Data_Functor.Functor(function (f) {
        return mapExceptT(Data_Functor.map(dictFunctor)(Data_Functor.map(Data_Either.functorEither)(f)));
    });
};
var except = function (dictApplicative) {
    return function ($96) {
        return ExceptT(Control_Applicative.pure(dictApplicative)($96));
    };
};
var monadExceptT = function (dictMonad) {
    return new Control_Monad.Monad(function () {
        return applicativeExceptT(dictMonad);
    }, function () {
        return bindExceptT(dictMonad);
    });
};
var bindExceptT = function (dictMonad) {
    return new Control_Bind.Bind(function () {
        return applyExceptT(dictMonad);
    }, function (v) {
        return function (k) {
            return Control_Bind.bind(dictMonad.Bind1())(v)(Data_Either.either(function ($97) {
                return Control_Applicative.pure(dictMonad.Applicative0())(Data_Either.Left.create($97));
            })(function (a) {
                var v1 = k(a);
                return v1;
            }));
        };
    });
};
var applyExceptT = function (dictMonad) {
    return new Control_Apply.Apply(function () {
        return functorExceptT(((dictMonad.Bind1()).Apply0()).Functor0());
    }, Control_Monad.ap(monadExceptT(dictMonad)));
};
var applicativeExceptT = function (dictMonad) {
    return new Control_Applicative.Applicative(function () {
        return applyExceptT(dictMonad);
    }, function ($98) {
        return ExceptT(Control_Applicative.pure(dictMonad.Applicative0())(Data_Either.Right.create($98)));
    });
};
var monadAskExceptT = function (dictMonadAsk) {
    return new Control_Monad_Reader_Class.MonadAsk(function () {
        return monadExceptT(dictMonadAsk.Monad0());
    }, Control_Monad_Trans_Class.lift(monadTransExceptT)(dictMonadAsk.Monad0())(Control_Monad_Reader_Class.ask(dictMonadAsk)));
};
var monadReaderExceptT = function (dictMonadReader) {
    return new Control_Monad_Reader_Class.MonadReader(function () {
        return monadAskExceptT(dictMonadReader.MonadAsk0());
    }, function (f) {
        return mapExceptT(Control_Monad_Reader_Class.local(dictMonadReader)(f));
    });
};
var monadContExceptT = function (dictMonadCont) {
    return new Control_Monad_Cont_Class.MonadCont(function () {
        return monadExceptT(dictMonadCont.Monad0());
    }, function (f) {
        return ExceptT(Control_Monad_Cont_Class.callCC(dictMonadCont)(function (c) {
            var v = f(function (a) {
                return ExceptT(c(new Data_Either.Right(a)));
            });
            return v;
        }));
    });
};
var monadEffectExceptT = function (dictMonadEffect) {
    return new Effect_Class.MonadEffect(function () {
        return monadExceptT(dictMonadEffect.Monad0());
    }, function ($99) {
        return Control_Monad_Trans_Class.lift(monadTransExceptT)(dictMonadEffect.Monad0())(Effect_Class.liftEffect(dictMonadEffect)($99));
    });
};
var monadRecExceptT = function (dictMonadRec) {
    return new Control_Monad_Rec_Class.MonadRec(function () {
        return monadExceptT(dictMonadRec.Monad0());
    }, function (f) {
        return function ($100) {
            return ExceptT(Control_Monad_Rec_Class.tailRecM(dictMonadRec)(function (a) {
                return Control_Bind.bind((dictMonadRec.Monad0()).Bind1())((function () {
                    var v = f(a);
                    return v;
                })())(function (m$prime) {
                    return Control_Applicative.pure((dictMonadRec.Monad0()).Applicative0())((function () {
                        if (m$prime instanceof Data_Either.Left) {
                            return new Control_Monad_Rec_Class.Done(new Data_Either.Left(m$prime.value0));
                        };
                        if (m$prime instanceof Data_Either.Right && m$prime.value0 instanceof Control_Monad_Rec_Class.Loop) {
                            return new Control_Monad_Rec_Class.Loop(m$prime.value0.value0);
                        };
                        if (m$prime instanceof Data_Either.Right && m$prime.value0 instanceof Control_Monad_Rec_Class.Done) {
                            return new Control_Monad_Rec_Class.Done(new Data_Either.Right(m$prime.value0.value0));
                        };
                        throw new Error("Failed pattern match at Control.Monad.Except.Trans line 74, column 14 - line 77, column 43: " + [ m$prime.constructor.name ]);
                    })());
                });
            })($100));
        };
    });
};
var monadStateExceptT = function (dictMonadState) {
    return new Control_Monad_State_Class.MonadState(function () {
        return monadExceptT(dictMonadState.Monad0());
    }, function (f) {
        return Control_Monad_Trans_Class.lift(monadTransExceptT)(dictMonadState.Monad0())(Control_Monad_State_Class.state(dictMonadState)(f));
    });
};
var monadTellExceptT = function (dictMonadTell) {
    return new Control_Monad_Writer_Class.MonadTell(function () {
        return monadExceptT(dictMonadTell.Monad0());
    }, function ($101) {
        return Control_Monad_Trans_Class.lift(monadTransExceptT)(dictMonadTell.Monad0())(Control_Monad_Writer_Class.tell(dictMonadTell)($101));
    });
};
var monadWriterExceptT = function (dictMonadWriter) {
    return new Control_Monad_Writer_Class.MonadWriter(function () {
        return monadTellExceptT(dictMonadWriter.MonadTell0());
    }, mapExceptT(function (m) {
        return Control_Bind.bind(((dictMonadWriter.MonadTell0()).Monad0()).Bind1())(Control_Monad_Writer_Class.listen(dictMonadWriter)(m))(function (v) {
            return Control_Applicative.pure(((dictMonadWriter.MonadTell0()).Monad0()).Applicative0())(Data_Functor.map(Data_Either.functorEither)(function (r) {
                return new Data_Tuple.Tuple(r, v.value1);
            })(v.value0));
        });
    }), mapExceptT(function (m) {
        return Control_Monad_Writer_Class.pass(dictMonadWriter)(Control_Bind.bind(((dictMonadWriter.MonadTell0()).Monad0()).Bind1())(m)(function (v) {
            return Control_Applicative.pure(((dictMonadWriter.MonadTell0()).Monad0()).Applicative0())((function () {
                if (v instanceof Data_Either.Left) {
                    return new Data_Tuple.Tuple(new Data_Either.Left(v.value0), Control_Category.identity(Control_Category.categoryFn));
                };
                if (v instanceof Data_Either.Right) {
                    return new Data_Tuple.Tuple(new Data_Either.Right(v.value0.value0), v.value0.value1);
                };
                throw new Error("Failed pattern match at Control.Monad.Except.Trans line 136, column 10 - line 138, column 44: " + [ v.constructor.name ]);
            })());
        }));
    }));
};
var monadThrowExceptT = function (dictMonad) {
    return new Control_Monad_Error_Class.MonadThrow(function () {
        return monadExceptT(dictMonad);
    }, function ($102) {
        return ExceptT(Control_Applicative.pure(dictMonad.Applicative0())(Data_Either.Left.create($102)));
    });
};
var monadErrorExceptT = function (dictMonad) {
    return new Control_Monad_Error_Class.MonadError(function () {
        return monadThrowExceptT(dictMonad);
    }, function (v) {
        return function (k) {
            return Control_Bind.bind(dictMonad.Bind1())(v)(Data_Either.either(function (a) {
                var v1 = k(a);
                return v1;
            })(function ($103) {
                return Control_Applicative.pure(dictMonad.Applicative0())(Data_Either.Right.create($103));
            }));
        };
    });
};
var altExceptT = function (dictSemigroup) {
    return function (dictMonad) {
        return new Control_Alt.Alt(function () {
            return functorExceptT(((dictMonad.Bind1()).Apply0()).Functor0());
        }, function (v) {
            return function (v1) {
                return Control_Bind.bind(dictMonad.Bind1())(v)(function (v2) {
                    if (v2 instanceof Data_Either.Right) {
                        return Control_Applicative.pure(dictMonad.Applicative0())(new Data_Either.Right(v2.value0));
                    };
                    if (v2 instanceof Data_Either.Left) {
                        return Control_Bind.bind(dictMonad.Bind1())(v1)(function (v3) {
                            if (v3 instanceof Data_Either.Right) {
                                return Control_Applicative.pure(dictMonad.Applicative0())(new Data_Either.Right(v3.value0));
                            };
                            if (v3 instanceof Data_Either.Left) {
                                return Control_Applicative.pure(dictMonad.Applicative0())(new Data_Either.Left(Data_Semigroup.append(dictSemigroup)(v2.value0)(v3.value0)));
                            };
                            throw new Error("Failed pattern match at Control.Monad.Except.Trans line 86, column 9 - line 88, column 49: " + [ v3.constructor.name ]);
                        });
                    };
                    throw new Error("Failed pattern match at Control.Monad.Except.Trans line 82, column 5 - line 88, column 49: " + [ v2.constructor.name ]);
                });
            };
        });
    };
};
var plusExceptT = function (dictMonoid) {
    return function (dictMonad) {
        return new Control_Plus.Plus(function () {
            return altExceptT(dictMonoid.Semigroup0())(dictMonad);
        }, Control_Monad_Error_Class.throwError(monadThrowExceptT(dictMonad))(Data_Monoid.mempty(dictMonoid)));
    };
};
var alternativeExceptT = function (dictMonoid) {
    return function (dictMonad) {
        return new Control_Alternative.Alternative(function () {
            return applicativeExceptT(dictMonad);
        }, function () {
            return plusExceptT(dictMonoid)(dictMonad);
        });
    };
};
var monadZeroExceptT = function (dictMonoid) {
    return function (dictMonad) {
        return new Control_MonadZero.MonadZero(function () {
            return alternativeExceptT(dictMonoid)(dictMonad);
        }, function () {
            return monadExceptT(dictMonad);
        });
    };
};
var monadPlusExceptT = function (dictMonoid) {
    return function (dictMonad) {
        return new Control_MonadPlus.MonadPlus(function () {
            return monadZeroExceptT(dictMonoid)(dictMonad);
        });
    };
};
module.exports = {
    ExceptT: ExceptT,
    runExceptT: runExceptT,
    withExceptT: withExceptT,
    mapExceptT: mapExceptT,
    except: except,
    newtypeExceptT: newtypeExceptT,
    functorExceptT: functorExceptT,
    applyExceptT: applyExceptT,
    applicativeExceptT: applicativeExceptT,
    bindExceptT: bindExceptT,
    monadExceptT: monadExceptT,
    monadRecExceptT: monadRecExceptT,
    altExceptT: altExceptT,
    plusExceptT: plusExceptT,
    alternativeExceptT: alternativeExceptT,
    monadPlusExceptT: monadPlusExceptT,
    monadZeroExceptT: monadZeroExceptT,
    monadTransExceptT: monadTransExceptT,
    monadEffectExceptT: monadEffectExceptT,
    monadContExceptT: monadContExceptT,
    monadThrowExceptT: monadThrowExceptT,
    monadErrorExceptT: monadErrorExceptT,
    monadAskExceptT: monadAskExceptT,
    monadReaderExceptT: monadReaderExceptT,
    monadStateExceptT: monadStateExceptT,
    monadTellExceptT: monadTellExceptT,
    monadWriterExceptT: monadWriterExceptT
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Category/index.js":24,"../Control.Monad.Cont.Class/index.js":29,"../Control.Monad.Error.Class/index.js":31,"../Control.Monad.Reader.Class/index.js":34,"../Control.Monad.Rec.Class/index.js":36,"../Control.Monad.State.Class/index.js":41,"../Control.Monad.Trans.Class/index.js":42,"../Control.Monad.Writer.Class/index.js":43,"../Control.Monad/index.js":47,"../Control.MonadPlus/index.js":45,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Either/index.js":82,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Semigroup/index.js":137,"../Data.Tuple/index.js":160,"../Effect.Class/index.js":173,"../Prelude/index.js":195}],33:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Monad_Cont_Class = require("../Control.Monad.Cont.Class/index.js");
var Control_Monad_Error_Class = require("../Control.Monad.Error.Class/index.js");
var Control_Monad_Reader_Class = require("../Control.Monad.Reader.Class/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Control_Monad_State_Class = require("../Control.Monad.State.Class/index.js");
var Control_Monad_Trans_Class = require("../Control.Monad.Trans.Class/index.js");
var Control_Monad_Writer_Class = require("../Control.Monad.Writer.Class/index.js");
var Control_MonadPlus = require("../Control.MonadPlus/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Effect_Class = require("../Effect.Class/index.js");
var Prelude = require("../Prelude/index.js");
var MaybeT = function (x) {
    return x;
};
var runMaybeT = function (v) {
    return v;
};
var newtypeMaybeT = new Data_Newtype.Newtype(function (n) {
    return n;
}, MaybeT);
var monadTransMaybeT = new Control_Monad_Trans_Class.MonadTrans(function (dictMonad) {
    return function ($75) {
        return MaybeT(Control_Monad.liftM1(dictMonad)(Data_Maybe.Just.create)($75));
    };
});
var mapMaybeT = function (f) {
    return function (v) {
        return f(v);
    };
};
var functorMaybeT = function (dictFunctor) {
    return new Data_Functor.Functor(function (f) {
        return function (v) {
            return Data_Functor.map(dictFunctor)(Data_Functor.map(Data_Maybe.functorMaybe)(f))(v);
        };
    });
};
var monadMaybeT = function (dictMonad) {
    return new Control_Monad.Monad(function () {
        return applicativeMaybeT(dictMonad);
    }, function () {
        return bindMaybeT(dictMonad);
    });
};
var bindMaybeT = function (dictMonad) {
    return new Control_Bind.Bind(function () {
        return applyMaybeT(dictMonad);
    }, function (v) {
        return function (f) {
            return Control_Bind.bind(dictMonad.Bind1())(v)(function (v1) {
                if (v1 instanceof Data_Maybe.Nothing) {
                    return Control_Applicative.pure(dictMonad.Applicative0())(Data_Maybe.Nothing.value);
                };
                if (v1 instanceof Data_Maybe.Just) {
                    var v2 = f(v1.value0);
                    return v2;
                };
                throw new Error("Failed pattern match at Control.Monad.Maybe.Trans line 54, column 11 - line 56, column 42: " + [ v1.constructor.name ]);
            });
        };
    });
};
var applyMaybeT = function (dictMonad) {
    return new Control_Apply.Apply(function () {
        return functorMaybeT(((dictMonad.Bind1()).Apply0()).Functor0());
    }, Control_Monad.ap(monadMaybeT(dictMonad)));
};
var applicativeMaybeT = function (dictMonad) {
    return new Control_Applicative.Applicative(function () {
        return applyMaybeT(dictMonad);
    }, function ($76) {
        return MaybeT(Control_Applicative.pure(dictMonad.Applicative0())(Data_Maybe.Just.create($76)));
    });
};
var monadAskMaybeT = function (dictMonadAsk) {
    return new Control_Monad_Reader_Class.MonadAsk(function () {
        return monadMaybeT(dictMonadAsk.Monad0());
    }, Control_Monad_Trans_Class.lift(monadTransMaybeT)(dictMonadAsk.Monad0())(Control_Monad_Reader_Class.ask(dictMonadAsk)));
};
var monadReaderMaybeT = function (dictMonadReader) {
    return new Control_Monad_Reader_Class.MonadReader(function () {
        return monadAskMaybeT(dictMonadReader.MonadAsk0());
    }, function (f) {
        return mapMaybeT(Control_Monad_Reader_Class.local(dictMonadReader)(f));
    });
};
var monadContMaybeT = function (dictMonadCont) {
    return new Control_Monad_Cont_Class.MonadCont(function () {
        return monadMaybeT(dictMonadCont.Monad0());
    }, function (f) {
        return MaybeT(Control_Monad_Cont_Class.callCC(dictMonadCont)(function (c) {
            var v = f(function (a) {
                return MaybeT(c(new Data_Maybe.Just(a)));
            });
            return v;
        }));
    });
};
var monadEffectMaybe = function (dictMonadEffect) {
    return new Effect_Class.MonadEffect(function () {
        return monadMaybeT(dictMonadEffect.Monad0());
    }, function ($77) {
        return Control_Monad_Trans_Class.lift(monadTransMaybeT)(dictMonadEffect.Monad0())(Effect_Class.liftEffect(dictMonadEffect)($77));
    });
};
var monadRecMaybeT = function (dictMonadRec) {
    return new Control_Monad_Rec_Class.MonadRec(function () {
        return monadMaybeT(dictMonadRec.Monad0());
    }, function (f) {
        return function ($78) {
            return MaybeT(Control_Monad_Rec_Class.tailRecM(dictMonadRec)(function (a) {
                return Control_Bind.bind((dictMonadRec.Monad0()).Bind1())((function () {
                    var v = f(a);
                    return v;
                })())(function (m$prime) {
                    return Control_Applicative.pure((dictMonadRec.Monad0()).Applicative0())((function () {
                        if (m$prime instanceof Data_Maybe.Nothing) {
                            return new Control_Monad_Rec_Class.Done(Data_Maybe.Nothing.value);
                        };
                        if (m$prime instanceof Data_Maybe.Just && m$prime.value0 instanceof Control_Monad_Rec_Class.Loop) {
                            return new Control_Monad_Rec_Class.Loop(m$prime.value0.value0);
                        };
                        if (m$prime instanceof Data_Maybe.Just && m$prime.value0 instanceof Control_Monad_Rec_Class.Done) {
                            return new Control_Monad_Rec_Class.Done(new Data_Maybe.Just(m$prime.value0.value0));
                        };
                        throw new Error("Failed pattern match at Control.Monad.Maybe.Trans line 84, column 16 - line 87, column 43: " + [ m$prime.constructor.name ]);
                    })());
                });
            })($78));
        };
    });
};
var monadStateMaybeT = function (dictMonadState) {
    return new Control_Monad_State_Class.MonadState(function () {
        return monadMaybeT(dictMonadState.Monad0());
    }, function (f) {
        return Control_Monad_Trans_Class.lift(monadTransMaybeT)(dictMonadState.Monad0())(Control_Monad_State_Class.state(dictMonadState)(f));
    });
};
var monadTellMaybeT = function (dictMonadTell) {
    return new Control_Monad_Writer_Class.MonadTell(function () {
        return monadMaybeT(dictMonadTell.Monad0());
    }, function ($79) {
        return Control_Monad_Trans_Class.lift(monadTransMaybeT)(dictMonadTell.Monad0())(Control_Monad_Writer_Class.tell(dictMonadTell)($79));
    });
};
var monadWriterMaybeT = function (dictMonadWriter) {
    return new Control_Monad_Writer_Class.MonadWriter(function () {
        return monadTellMaybeT(dictMonadWriter.MonadTell0());
    }, mapMaybeT(function (m) {
        return Control_Bind.bind(((dictMonadWriter.MonadTell0()).Monad0()).Bind1())(Control_Monad_Writer_Class.listen(dictMonadWriter)(m))(function (v) {
            return Control_Applicative.pure(((dictMonadWriter.MonadTell0()).Monad0()).Applicative0())(Data_Functor.map(Data_Maybe.functorMaybe)(function (r) {
                return new Data_Tuple.Tuple(r, v.value1);
            })(v.value0));
        });
    }), mapMaybeT(function (m) {
        return Control_Monad_Writer_Class.pass(dictMonadWriter)(Control_Bind.bind(((dictMonadWriter.MonadTell0()).Monad0()).Bind1())(m)(function (v) {
            return Control_Applicative.pure(((dictMonadWriter.MonadTell0()).Monad0()).Applicative0())((function () {
                if (v instanceof Data_Maybe.Nothing) {
                    return new Data_Tuple.Tuple(Data_Maybe.Nothing.value, Control_Category.identity(Control_Category.categoryFn));
                };
                if (v instanceof Data_Maybe.Just) {
                    return new Data_Tuple.Tuple(new Data_Maybe.Just(v.value0.value0), v.value0.value1);
                };
                throw new Error("Failed pattern match at Control.Monad.Maybe.Trans line 121, column 10 - line 123, column 42: " + [ v.constructor.name ]);
            })());
        }));
    }));
};
var monadThrowMaybeT = function (dictMonadThrow) {
    return new Control_Monad_Error_Class.MonadThrow(function () {
        return monadMaybeT(dictMonadThrow.Monad0());
    }, function (e) {
        return Control_Monad_Trans_Class.lift(monadTransMaybeT)(dictMonadThrow.Monad0())(Control_Monad_Error_Class.throwError(dictMonadThrow)(e));
    });
};
var monadErrorMaybeT = function (dictMonadError) {
    return new Control_Monad_Error_Class.MonadError(function () {
        return monadThrowMaybeT(dictMonadError.MonadThrow0());
    }, function (v) {
        return function (h) {
            return MaybeT(Control_Monad_Error_Class.catchError(dictMonadError)(v)(function (a) {
                var v1 = h(a);
                return v1;
            }));
        };
    });
};
var altMaybeT = function (dictMonad) {
    return new Control_Alt.Alt(function () {
        return functorMaybeT(((dictMonad.Bind1()).Apply0()).Functor0());
    }, function (v) {
        return function (v1) {
            return Control_Bind.bind(dictMonad.Bind1())(v)(function (v2) {
                if (v2 instanceof Data_Maybe.Nothing) {
                    return v1;
                };
                return Control_Applicative.pure(dictMonad.Applicative0())(v2);
            });
        };
    });
};
var plusMaybeT = function (dictMonad) {
    return new Control_Plus.Plus(function () {
        return altMaybeT(dictMonad);
    }, Control_Applicative.pure(dictMonad.Applicative0())(Data_Maybe.Nothing.value));
};
var alternativeMaybeT = function (dictMonad) {
    return new Control_Alternative.Alternative(function () {
        return applicativeMaybeT(dictMonad);
    }, function () {
        return plusMaybeT(dictMonad);
    });
};
var monadZeroMaybeT = function (dictMonad) {
    return new Control_MonadZero.MonadZero(function () {
        return alternativeMaybeT(dictMonad);
    }, function () {
        return monadMaybeT(dictMonad);
    });
};
var monadPlusMaybeT = function (dictMonad) {
    return new Control_MonadPlus.MonadPlus(function () {
        return monadZeroMaybeT(dictMonad);
    });
};
module.exports = {
    MaybeT: MaybeT,
    runMaybeT: runMaybeT,
    mapMaybeT: mapMaybeT,
    newtypeMaybeT: newtypeMaybeT,
    functorMaybeT: functorMaybeT,
    applyMaybeT: applyMaybeT,
    applicativeMaybeT: applicativeMaybeT,
    bindMaybeT: bindMaybeT,
    monadMaybeT: monadMaybeT,
    monadTransMaybeT: monadTransMaybeT,
    altMaybeT: altMaybeT,
    plusMaybeT: plusMaybeT,
    alternativeMaybeT: alternativeMaybeT,
    monadPlusMaybeT: monadPlusMaybeT,
    monadZeroMaybeT: monadZeroMaybeT,
    monadRecMaybeT: monadRecMaybeT,
    monadEffectMaybe: monadEffectMaybe,
    monadContMaybeT: monadContMaybeT,
    monadThrowMaybeT: monadThrowMaybeT,
    monadErrorMaybeT: monadErrorMaybeT,
    monadAskMaybeT: monadAskMaybeT,
    monadReaderMaybeT: monadReaderMaybeT,
    monadStateMaybeT: monadStateMaybeT,
    monadTellMaybeT: monadTellMaybeT,
    monadWriterMaybeT: monadWriterMaybeT
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Category/index.js":24,"../Control.Monad.Cont.Class/index.js":29,"../Control.Monad.Error.Class/index.js":31,"../Control.Monad.Reader.Class/index.js":34,"../Control.Monad.Rec.Class/index.js":36,"../Control.Monad.State.Class/index.js":41,"../Control.Monad.Trans.Class/index.js":42,"../Control.Monad.Writer.Class/index.js":43,"../Control.Monad/index.js":47,"../Control.MonadPlus/index.js":45,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Newtype/index.js":121,"../Data.Tuple/index.js":160,"../Effect.Class/index.js":173,"../Prelude/index.js":195}],34:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Prelude = require("../Prelude/index.js");
var MonadAsk = function (Monad0, ask) {
    this.Monad0 = Monad0;
    this.ask = ask;
};
var MonadReader = function (MonadAsk0, local) {
    this.MonadAsk0 = MonadAsk0;
    this.local = local;
};
var monadAskFun = new MonadAsk(function () {
    return Control_Monad.monadFn;
}, Control_Category.identity(Control_Category.categoryFn));
var monadReaderFun = new MonadReader(function () {
    return monadAskFun;
}, Control_Semigroupoid.composeFlipped(Control_Semigroupoid.semigroupoidFn));
var local = function (dict) {
    return dict.local;
};
var ask = function (dict) {
    return dict.ask;
};
var asks = function (dictMonadAsk) {
    return function (f) {
        return Data_Functor.map((((dictMonadAsk.Monad0()).Bind1()).Apply0()).Functor0())(f)(ask(dictMonadAsk));
    };
};
module.exports = {
    ask: ask,
    local: local,
    MonadAsk: MonadAsk,
    asks: asks,
    MonadReader: MonadReader,
    monadAskFun: monadAskFun,
    monadReaderFun: monadReaderFun
};

},{"../Control.Category/index.js":24,"../Control.Monad/index.js":47,"../Control.Semigroupoid/index.js":51,"../Data.Functor/index.js":102,"../Prelude/index.js":195}],35:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Monad_Cont_Class = require("../Control.Monad.Cont.Class/index.js");
var Control_Monad_Error_Class = require("../Control.Monad.Error.Class/index.js");
var Control_Monad_Reader_Class = require("../Control.Monad.Reader.Class/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Control_Monad_State_Class = require("../Control.Monad.State.Class/index.js");
var Control_Monad_Trans_Class = require("../Control.Monad.Trans.Class/index.js");
var Control_Monad_Writer_Class = require("../Control.Monad.Writer.Class/index.js");
var Control_MonadPlus = require("../Control.MonadPlus/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Distributive = require("../Data.Distributive/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Effect_Class = require("../Effect.Class/index.js");
var Prelude = require("../Prelude/index.js");
var ReaderT = function (x) {
    return x;
};
var withReaderT = function (f) {
    return function (v) {
        return function ($66) {
            return v(f($66));
        };
    };
};
var runReaderT = function (v) {
    return v;
};
var newtypeReaderT = new Data_Newtype.Newtype(function (n) {
    return n;
}, ReaderT);
var monadTransReaderT = new Control_Monad_Trans_Class.MonadTrans(function (dictMonad) {
    return function ($67) {
        return ReaderT(Data_Function["const"]($67));
    };
});
var mapReaderT = function (f) {
    return function (v) {
        return function ($68) {
            return f(v($68));
        };
    };
};
var functorReaderT = function (dictFunctor) {
    return new Data_Functor.Functor(function ($69) {
        return mapReaderT(Data_Functor.map(dictFunctor)($69));
    });
};
var distributiveReaderT = function (dictDistributive) {
    return new Data_Distributive.Distributive(function () {
        return functorReaderT(dictDistributive.Functor0());
    }, function (dictFunctor) {
        return function (f) {
            return function ($70) {
                return Data_Distributive.distribute(distributiveReaderT(dictDistributive))(dictFunctor)(Data_Functor.map(dictFunctor)(f)($70));
            };
        };
    }, function (dictFunctor) {
        return function (a) {
            return function (e) {
                return Data_Distributive.collect(dictDistributive)(dictFunctor)(function (r) {
                    return r(e);
                })(a);
            };
        };
    });
};
var applyReaderT = function (dictApply) {
    return new Control_Apply.Apply(function () {
        return functorReaderT(dictApply.Functor0());
    }, function (v) {
        return function (v1) {
            return function (r) {
                return Control_Apply.apply(dictApply)(v(r))(v1(r));
            };
        };
    });
};
var bindReaderT = function (dictBind) {
    return new Control_Bind.Bind(function () {
        return applyReaderT(dictBind.Apply0());
    }, function (v) {
        return function (k) {
            return function (r) {
                return Control_Bind.bind(dictBind)(v(r))(function (a) {
                    var v1 = k(a);
                    return v1(r);
                });
            };
        };
    });
};
var semigroupReaderT = function (dictApply) {
    return function (dictSemigroup) {
        return new Data_Semigroup.Semigroup(Control_Apply.lift2(applyReaderT(dictApply))(Data_Semigroup.append(dictSemigroup)));
    };
};
var applicativeReaderT = function (dictApplicative) {
    return new Control_Applicative.Applicative(function () {
        return applyReaderT(dictApplicative.Apply0());
    }, function ($71) {
        return ReaderT(Data_Function["const"](Control_Applicative.pure(dictApplicative)($71)));
    });
};
var monadReaderT = function (dictMonad) {
    return new Control_Monad.Monad(function () {
        return applicativeReaderT(dictMonad.Applicative0());
    }, function () {
        return bindReaderT(dictMonad.Bind1());
    });
};
var monadAskReaderT = function (dictMonad) {
    return new Control_Monad_Reader_Class.MonadAsk(function () {
        return monadReaderT(dictMonad);
    }, Control_Applicative.pure(dictMonad.Applicative0()));
};
var monadReaderReaderT = function (dictMonad) {
    return new Control_Monad_Reader_Class.MonadReader(function () {
        return monadAskReaderT(dictMonad);
    }, withReaderT);
};
var monadContReaderT = function (dictMonadCont) {
    return new Control_Monad_Cont_Class.MonadCont(function () {
        return monadReaderT(dictMonadCont.Monad0());
    }, function (f) {
        return function (r) {
            return Control_Monad_Cont_Class.callCC(dictMonadCont)(function (c) {
                var v = f(function ($72) {
                    return ReaderT(Data_Function["const"](c($72)));
                });
                return v(r);
            });
        };
    });
};
var monadEffectReader = function (dictMonadEffect) {
    return new Effect_Class.MonadEffect(function () {
        return monadReaderT(dictMonadEffect.Monad0());
    }, function ($73) {
        return Control_Monad_Trans_Class.lift(monadTransReaderT)(dictMonadEffect.Monad0())(Effect_Class.liftEffect(dictMonadEffect)($73));
    });
};
var monadRecReaderT = function (dictMonadRec) {
    return new Control_Monad_Rec_Class.MonadRec(function () {
        return monadReaderT(dictMonadRec.Monad0());
    }, function (k) {
        return function (a) {
            var k$prime = function (r) {
                return function (a$prime) {
                    var v = k(a$prime);
                    return Control_Bind.bindFlipped((dictMonadRec.Monad0()).Bind1())(Control_Applicative.pure((dictMonadRec.Monad0()).Applicative0()))(v(r));
                };
            };
            return function (r) {
                return Control_Monad_Rec_Class.tailRecM(dictMonadRec)(k$prime(r))(a);
            };
        };
    });
};
var monadStateReaderT = function (dictMonadState) {
    return new Control_Monad_State_Class.MonadState(function () {
        return monadReaderT(dictMonadState.Monad0());
    }, function ($74) {
        return Control_Monad_Trans_Class.lift(monadTransReaderT)(dictMonadState.Monad0())(Control_Monad_State_Class.state(dictMonadState)($74));
    });
};
var monadTellReaderT = function (dictMonadTell) {
    return new Control_Monad_Writer_Class.MonadTell(function () {
        return monadReaderT(dictMonadTell.Monad0());
    }, function ($75) {
        return Control_Monad_Trans_Class.lift(monadTransReaderT)(dictMonadTell.Monad0())(Control_Monad_Writer_Class.tell(dictMonadTell)($75));
    });
};
var monadWriterReaderT = function (dictMonadWriter) {
    return new Control_Monad_Writer_Class.MonadWriter(function () {
        return monadTellReaderT(dictMonadWriter.MonadTell0());
    }, mapReaderT(Control_Monad_Writer_Class.listen(dictMonadWriter)), mapReaderT(Control_Monad_Writer_Class.pass(dictMonadWriter)));
};
var monadThrowReaderT = function (dictMonadThrow) {
    return new Control_Monad_Error_Class.MonadThrow(function () {
        return monadReaderT(dictMonadThrow.Monad0());
    }, function ($76) {
        return Control_Monad_Trans_Class.lift(monadTransReaderT)(dictMonadThrow.Monad0())(Control_Monad_Error_Class.throwError(dictMonadThrow)($76));
    });
};
var monadErrorReaderT = function (dictMonadError) {
    return new Control_Monad_Error_Class.MonadError(function () {
        return monadThrowReaderT(dictMonadError.MonadThrow0());
    }, function (v) {
        return function (h) {
            return function (r) {
                return Control_Monad_Error_Class.catchError(dictMonadError)(v(r))(function (e) {
                    var v1 = h(e);
                    return v1(r);
                });
            };
        };
    });
};
var monoidReaderT = function (dictApplicative) {
    return function (dictMonoid) {
        return new Data_Monoid.Monoid(function () {
            return semigroupReaderT(dictApplicative.Apply0())(dictMonoid.Semigroup0());
        }, Control_Applicative.pure(applicativeReaderT(dictApplicative))(Data_Monoid.mempty(dictMonoid)));
    };
};
var altReaderT = function (dictAlt) {
    return new Control_Alt.Alt(function () {
        return functorReaderT(dictAlt.Functor0());
    }, function (v) {
        return function (v1) {
            return function (r) {
                return Control_Alt.alt(dictAlt)(v(r))(v1(r));
            };
        };
    });
};
var plusReaderT = function (dictPlus) {
    return new Control_Plus.Plus(function () {
        return altReaderT(dictPlus.Alt0());
    }, Data_Function["const"](Control_Plus.empty(dictPlus)));
};
var alternativeReaderT = function (dictAlternative) {
    return new Control_Alternative.Alternative(function () {
        return applicativeReaderT(dictAlternative.Applicative0());
    }, function () {
        return plusReaderT(dictAlternative.Plus1());
    });
};
var monadZeroReaderT = function (dictMonadZero) {
    return new Control_MonadZero.MonadZero(function () {
        return alternativeReaderT(dictMonadZero.Alternative1());
    }, function () {
        return monadReaderT(dictMonadZero.Monad0());
    });
};
var monadPlusReaderT = function (dictMonadPlus) {
    return new Control_MonadPlus.MonadPlus(function () {
        return monadZeroReaderT(dictMonadPlus.MonadZero0());
    });
};
module.exports = {
    ReaderT: ReaderT,
    runReaderT: runReaderT,
    withReaderT: withReaderT,
    mapReaderT: mapReaderT,
    newtypeReaderT: newtypeReaderT,
    functorReaderT: functorReaderT,
    applyReaderT: applyReaderT,
    applicativeReaderT: applicativeReaderT,
    altReaderT: altReaderT,
    plusReaderT: plusReaderT,
    alternativeReaderT: alternativeReaderT,
    bindReaderT: bindReaderT,
    monadReaderT: monadReaderT,
    monadZeroReaderT: monadZeroReaderT,
    semigroupReaderT: semigroupReaderT,
    monoidReaderT: monoidReaderT,
    monadPlusReaderT: monadPlusReaderT,
    monadTransReaderT: monadTransReaderT,
    monadEffectReader: monadEffectReader,
    monadContReaderT: monadContReaderT,
    monadThrowReaderT: monadThrowReaderT,
    monadErrorReaderT: monadErrorReaderT,
    monadAskReaderT: monadAskReaderT,
    monadReaderReaderT: monadReaderReaderT,
    monadStateReaderT: monadStateReaderT,
    monadTellReaderT: monadTellReaderT,
    monadWriterReaderT: monadWriterReaderT,
    distributiveReaderT: distributiveReaderT,
    monadRecReaderT: monadRecReaderT
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad.Cont.Class/index.js":29,"../Control.Monad.Error.Class/index.js":31,"../Control.Monad.Reader.Class/index.js":34,"../Control.Monad.Rec.Class/index.js":36,"../Control.Monad.State.Class/index.js":41,"../Control.Monad.Trans.Class/index.js":42,"../Control.Monad.Writer.Class/index.js":43,"../Control.Monad/index.js":47,"../Control.MonadPlus/index.js":45,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Distributive/index.js":80,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Semigroup/index.js":137,"../Effect.Class/index.js":173,"../Prelude/index.js":195}],36:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Identity = require("../Data.Identity/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Effect = require("../Effect/index.js");
var Effect_Ref = require("../Effect.Ref/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var Loop = (function () {
    function Loop(value0) {
        this.value0 = value0;
    };
    Loop.create = function (value0) {
        return new Loop(value0);
    };
    return Loop;
})();
var Done = (function () {
    function Done(value0) {
        this.value0 = value0;
    };
    Done.create = function (value0) {
        return new Done(value0);
    };
    return Done;
})();
var MonadRec = function (Monad0, tailRecM) {
    this.Monad0 = Monad0;
    this.tailRecM = tailRecM;
};
var tailRecM = function (dict) {
    return dict.tailRecM;
};
var tailRecM2 = function (dictMonadRec) {
    return function (f) {
        return function (a) {
            return function (b) {
                return tailRecM(dictMonadRec)(function (o) {
                    return f(o.a)(o.b);
                })({
                    a: a,
                    b: b
                });
            };
        };
    };
};
var tailRecM3 = function (dictMonadRec) {
    return function (f) {
        return function (a) {
            return function (b) {
                return function (c) {
                    return tailRecM(dictMonadRec)(function (o) {
                        return f(o.a)(o.b)(o.c);
                    })({
                        a: a,
                        b: b,
                        c: c
                    });
                };
            };
        };
    };
};
var tailRec = function (f) {
    var go = function ($copy_v) {
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(v) {
            if (v instanceof Loop) {
                $copy_v = f(v.value0);
                return;
            };
            if (v instanceof Done) {
                $tco_done = true;
                return v.value0;
            };
            throw new Error("Failed pattern match at Control.Monad.Rec.Class line 91, column 3 - line 91, column 25: " + [ v.constructor.name ]);
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($copy_v);
        };
        return $tco_result;
    };
    return function ($53) {
        return go(f($53));
    };
};
var monadRecMaybe = new MonadRec(function () {
    return Data_Maybe.monadMaybe;
}, function (f) {
    return function (a0) {
        var g = function (v) {
            if (v instanceof Data_Maybe.Nothing) {
                return new Done(Data_Maybe.Nothing.value);
            };
            if (v instanceof Data_Maybe.Just && v.value0 instanceof Loop) {
                return new Loop(f(v.value0.value0));
            };
            if (v instanceof Data_Maybe.Just && v.value0 instanceof Done) {
                return new Done(new Data_Maybe.Just(v.value0.value0));
            };
            throw new Error("Failed pattern match at Control.Monad.Rec.Class line 127, column 7 - line 127, column 31: " + [ v.constructor.name ]);
        };
        return tailRec(g)(f(a0));
    };
});
var monadRecIdentity = new MonadRec(function () {
    return Data_Identity.monadIdentity;
}, function (f) {
    var runIdentity = function (v) {
        return v;
    };
    return function ($54) {
        return Data_Identity.Identity(tailRec(function ($55) {
            return runIdentity(f($55));
        })($54));
    };
});
var monadRecFunction = new MonadRec(function () {
    return Control_Monad.monadFn;
}, function (f) {
    return function (a0) {
        return function (e) {
            return tailRec(function (a) {
                return f(a)(e);
            })(a0);
        };
    };
});
var monadRecEither = new MonadRec(function () {
    return Data_Either.monadEither;
}, function (f) {
    return function (a0) {
        var g = function (v) {
            if (v instanceof Data_Either.Left) {
                return new Done(new Data_Either.Left(v.value0));
            };
            if (v instanceof Data_Either.Right && v.value0 instanceof Loop) {
                return new Loop(f(v.value0.value0));
            };
            if (v instanceof Data_Either.Right && v.value0 instanceof Done) {
                return new Done(new Data_Either.Right(v.value0.value0));
            };
            throw new Error("Failed pattern match at Control.Monad.Rec.Class line 119, column 7 - line 119, column 33: " + [ v.constructor.name ]);
        };
        return tailRec(g)(f(a0));
    };
});
var monadRecEffect = new MonadRec(function () {
    return Effect.monadEffect;
}, function (f) {
    return function (a) {
        var fromDone = function (v) {
            var $__unused = function (dictPartial1) {
                return function ($dollar19) {
                    return $dollar19;
                };
            };
            return $__unused()((function () {
                if (v instanceof Done) {
                    return v.value0;
                };
                throw new Error("Failed pattern match at Control.Monad.Rec.Class line 111, column 30 - line 111, column 44: " + [ v.constructor.name ]);
            })());
        };
        return function __do() {
            var v = Control_Bind.bindFlipped(Effect.bindEffect)(Effect_Ref["new"])(f(a))();
            (function () {
                while (!(function __do() {
                    var v1 = Effect_Ref.read(v)();
                    if (v1 instanceof Loop) {
                        var v2 = f(v1.value0)();
                        var v3 = Effect_Ref.write(v2)(v)();
                        return false;
                    };
                    if (v1 instanceof Done) {
                        return true;
                    };
                    throw new Error("Failed pattern match at Control.Monad.Rec.Class line 102, column 22 - line 107, column 28: " + [ v1.constructor.name ]);
                })()) {

                };
                return {};
            })();
            return Data_Functor.map(Effect.functorEffect)(fromDone)(Effect_Ref.read(v))();
        };
    };
});
var functorStep = new Data_Functor.Functor(function (f) {
    return function (m) {
        if (m instanceof Loop) {
            return new Loop(m.value0);
        };
        if (m instanceof Done) {
            return new Done(f(m.value0));
        };
        throw new Error("Failed pattern match at Control.Monad.Rec.Class line 25, column 8 - line 25, column 48: " + [ m.constructor.name ]);
    };
});
var forever = function (dictMonadRec) {
    return function (ma) {
        return tailRecM(dictMonadRec)(function (u) {
            return Data_Functor.voidRight((((dictMonadRec.Monad0()).Bind1()).Apply0()).Functor0())(new Loop(u))(ma);
        })(Data_Unit.unit);
    };
};
var bifunctorStep = new Data_Bifunctor.Bifunctor(function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof Loop) {
                return new Loop(v(v2.value0));
            };
            if (v2 instanceof Done) {
                return new Done(v1(v2.value0));
            };
            throw new Error("Failed pattern match at Control.Monad.Rec.Class line 27, column 1 - line 27, column 41: " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
});
module.exports = {
    Loop: Loop,
    Done: Done,
    MonadRec: MonadRec,
    tailRec: tailRec,
    tailRecM: tailRecM,
    tailRecM2: tailRecM2,
    tailRecM3: tailRecM3,
    forever: forever,
    functorStep: functorStep,
    bifunctorStep: bifunctorStep,
    monadRecIdentity: monadRecIdentity,
    monadRecEffect: monadRecEffect,
    monadRecFunction: monadRecFunction,
    monadRecEither: monadRecEither,
    monadRecMaybe: monadRecMaybe
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Control.Semigroupoid/index.js":51,"../Data.Bifunctor/index.js":73,"../Data.Either/index.js":82,"../Data.Functor/index.js":102,"../Data.Identity/index.js":105,"../Data.Maybe/index.js":112,"../Data.Unit/index.js":168,"../Effect.Ref/index.js":179,"../Effect/index.js":185,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195}],37:[function(require,module,exports){
"use strict";

exports.map_ = function (f) {
  return function (a) {
    return function () {
      return f(a());
    };
  };
};

exports.pure_ = function (a) {
  return function () {
    return a;
  };
};

exports.bind_ = function (a) {
  return function (f) {
    return function () {
      return f(a())();
    };
  };
};

exports.run = function (f) {
  return f();
};

exports["while"] = function (f) {
  return function (a) {
    return function () {
      while (f()) {
        a();
      }
    };
  };
};

exports["for"] = function (lo) {
  return function (hi) {
    return function (f) {
      return function () {
        for (var i = lo; i < hi; i++) {
          f(i)();
        }
      };
    };
  };
};

exports.foreach = function (as) {
  return function (f) {
    return function () {
      for (var i = 0, l = as.length; i < l; i++) {
        f(as[i])();
      }
    };
  };
};

exports.new = function (val) {
  return function () {
    return { value: val };
  };
};

exports.read = function (ref) {
  return function () {
    return ref.value;
  };
};

exports["modify'"] = function (f) {
  return function (ref) {
    return function () {
      var t = f(ref.value);
      ref.value = t.state;
      return t.value;
    };
  };
};

exports.write = function (a) {
  return function (ref) {
    return function () {
      return ref.value = a; // eslint-disable-line no-return-assign
    };
  };
};

},{}],38:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var modify = function (f) {
    return $foreign["modify'"](function (s) {
        var s$prime = f(s);
        return {
            state: s$prime,
            value: s$prime
        };
    });
};
var functorST = new Data_Functor.Functor($foreign.map_);
var monadST = new Control_Monad.Monad(function () {
    return applicativeST;
}, function () {
    return bindST;
});
var bindST = new Control_Bind.Bind(function () {
    return applyST;
}, $foreign.bind_);
var applyST = new Control_Apply.Apply(function () {
    return functorST;
}, Control_Monad.ap(monadST));
var applicativeST = new Control_Applicative.Applicative(function () {
    return applyST;
}, $foreign.pure_);
var monadRecST = new Control_Monad_Rec_Class.MonadRec(function () {
    return monadST;
}, function (f) {
    return function (a) {
        var isLooping = function (v) {
            if (v instanceof Control_Monad_Rec_Class.Loop) {
                return true;
            };
            return false;
        };
        var fromDone = function (v) {
            var $__unused = function (dictPartial1) {
                return function ($dollar6) {
                    return $dollar6;
                };
            };
            return $__unused()((function () {
                if (v instanceof Control_Monad_Rec_Class.Done) {
                    return v.value0;
                };
                throw new Error("Failed pattern match at Control.Monad.ST.Internal line 54, column 32 - line 54, column 46: " + [ v.constructor.name ]);
            })());
        };
        return Control_Bind.bind(bindST)(Control_Bind.bindFlipped(bindST)($foreign["new"])(f(a)))(function (v) {
            return Control_Bind.discard(Control_Bind.discardUnit)(bindST)($foreign["while"](Data_Functor.map(functorST)(isLooping)($foreign.read(v)))(Control_Bind.bind(bindST)($foreign.read(v))(function (v1) {
                if (v1 instanceof Control_Monad_Rec_Class.Loop) {
                    return Control_Bind.bind(bindST)(f(v1.value0))(function (v2) {
                        return Data_Functor["void"](functorST)($foreign.write(v2)(v));
                    });
                };
                if (v1 instanceof Control_Monad_Rec_Class.Done) {
                    return Control_Applicative.pure(applicativeST)(Data_Unit.unit);
                };
                throw new Error("Failed pattern match at Control.Monad.ST.Internal line 46, column 18 - line 50, column 28: " + [ v1.constructor.name ]);
            })))(function () {
                return Data_Functor.map(functorST)(fromDone)($foreign.read(v));
            });
        });
    };
});
module.exports = {
    modify: modify,
    functorST: functorST,
    applyST: applyST,
    applicativeST: applicativeST,
    bindST: bindST,
    monadST: monadST,
    monadRecST: monadRecST,
    map_: $foreign.map_,
    pure_: $foreign.pure_,
    bind_: $foreign.bind_,
    run: $foreign.run,
    "while": $foreign["while"],
    "for": $foreign["for"],
    foreach: $foreign.foreach,
    "new": $foreign["new"],
    read: $foreign.read,
    "modify'": $foreign["modify'"],
    write: $foreign.write
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad.Rec.Class/index.js":36,"../Control.Monad/index.js":47,"../Data.Functor/index.js":102,"../Data.Unit/index.js":168,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195,"./foreign.js":37}],39:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Monad_ST_Internal = require("../Control.Monad.ST.Internal/index.js");
module.exports = {};

},{"../Control.Monad.ST.Internal/index.js":38}],40:[function(require,module,exports){
arguments[4][39][0].apply(exports,arguments)
},{"../Control.Monad.ST.Internal/index.js":38,"dup":39}],41:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var MonadState = function (Monad0, state) {
    this.Monad0 = Monad0;
    this.state = state;
};
var state = function (dict) {
    return dict.state;
};
var put = function (dictMonadState) {
    return function (s) {
        return state(dictMonadState)(function (v) {
            return new Data_Tuple.Tuple(Data_Unit.unit, s);
        });
    };
};
var modify_ = function (dictMonadState) {
    return function (f) {
        return state(dictMonadState)(function (s) {
            return new Data_Tuple.Tuple(Data_Unit.unit, f(s));
        });
    };
};
var modify = function (dictMonadState) {
    return function (f) {
        return state(dictMonadState)(function (s) {
            var s$prime = f(s);
            return new Data_Tuple.Tuple(s$prime, s$prime);
        });
    };
};
var gets = function (dictMonadState) {
    return function (f) {
        return state(dictMonadState)(function (s) {
            return new Data_Tuple.Tuple(f(s), s);
        });
    };
};
var get = function (dictMonadState) {
    return state(dictMonadState)(function (s) {
        return new Data_Tuple.Tuple(s, s);
    });
};
module.exports = {
    state: state,
    MonadState: MonadState,
    get: get,
    gets: gets,
    put: put,
    modify: modify,
    modify_: modify_
};

},{"../Data.Tuple/index.js":160,"../Data.Unit/index.js":168,"../Prelude/index.js":195}],42:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Prelude = require("../Prelude/index.js");
var MonadTrans = function (lift) {
    this.lift = lift;
};
var lift = function (dict) {
    return dict.lift;
};
module.exports = {
    lift: lift,
    MonadTrans: MonadTrans
};

},{"../Prelude/index.js":195}],43:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Prelude = require("../Prelude/index.js");
var MonadTell = function (Monad0, tell) {
    this.Monad0 = Monad0;
    this.tell = tell;
};
var MonadWriter = function (MonadTell0, listen, pass) {
    this.MonadTell0 = MonadTell0;
    this.listen = listen;
    this.pass = pass;
};
var tell = function (dict) {
    return dict.tell;
};
var pass = function (dict) {
    return dict.pass;
};
var listen = function (dict) {
    return dict.listen;
};
var listens = function (dictMonadWriter) {
    return function (f) {
        return function (m) {
            return Control_Bind.bind(((dictMonadWriter.MonadTell0()).Monad0()).Bind1())(listen(dictMonadWriter)(m))(function (v) {
                return Control_Applicative.pure(((dictMonadWriter.MonadTell0()).Monad0()).Applicative0())(new Data_Tuple.Tuple(v.value0, f(v.value1)));
            });
        };
    };
};
var censor = function (dictMonadWriter) {
    return function (f) {
        return function (m) {
            return pass(dictMonadWriter)(Control_Bind.bind(((dictMonadWriter.MonadTell0()).Monad0()).Bind1())(m)(function (v) {
                return Control_Applicative.pure(((dictMonadWriter.MonadTell0()).Monad0()).Applicative0())(new Data_Tuple.Tuple(v, f));
            }));
        };
    };
};
module.exports = {
    listen: listen,
    pass: pass,
    tell: tell,
    MonadTell: MonadTell,
    MonadWriter: MonadWriter,
    listens: listens,
    censor: censor
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Data.Function/index.js":95,"../Data.Tuple/index.js":160,"../Prelude/index.js":195}],44:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Monad_Cont_Class = require("../Control.Monad.Cont.Class/index.js");
var Control_Monad_Error_Class = require("../Control.Monad.Error.Class/index.js");
var Control_Monad_Reader_Class = require("../Control.Monad.Reader.Class/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Control_Monad_State_Class = require("../Control.Monad.State.Class/index.js");
var Control_Monad_Trans_Class = require("../Control.Monad.Trans.Class/index.js");
var Control_Monad_Writer_Class = require("../Control.Monad.Writer.Class/index.js");
var Control_MonadPlus = require("../Control.MonadPlus/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Effect_Class = require("../Effect.Class/index.js");
var Prelude = require("../Prelude/index.js");
var WriterT = function (x) {
    return x;
};
var runWriterT = function (v) {
    return v;
};
var newtypeWriterT = new Data_Newtype.Newtype(function (n) {
    return n;
}, WriterT);
var monadTransWriterT = function (dictMonoid) {
    return new Control_Monad_Trans_Class.MonadTrans(function (dictMonad) {
        return function (m) {
            return Control_Bind.bind(dictMonad.Bind1())(m)(function (v) {
                return Control_Applicative.pure(dictMonad.Applicative0())(new Data_Tuple.Tuple(v, Data_Monoid.mempty(dictMonoid)));
            });
        };
    });
};
var mapWriterT = function (f) {
    return function (v) {
        return f(v);
    };
};
var functorWriterT = function (dictFunctor) {
    return new Data_Functor.Functor(function (f) {
        return mapWriterT(Data_Functor.map(dictFunctor)(function (v) {
            return new Data_Tuple.Tuple(f(v.value0), v.value1);
        }));
    });
};
var execWriterT = function (dictFunctor) {
    return function (v) {
        return Data_Functor.map(dictFunctor)(Data_Tuple.snd)(v);
    };
};
var applyWriterT = function (dictSemigroup) {
    return function (dictApply) {
        return new Control_Apply.Apply(function () {
            return functorWriterT(dictApply.Functor0());
        }, function (v) {
            return function (v1) {
                var k = function (v3) {
                    return function (v4) {
                        return new Data_Tuple.Tuple(v3.value0(v4.value0), Data_Semigroup.append(dictSemigroup)(v3.value1)(v4.value1));
                    };
                };
                return Control_Apply.apply(dictApply)(Data_Functor.map(dictApply.Functor0())(k)(v))(v1);
            };
        });
    };
};
var bindWriterT = function (dictSemigroup) {
    return function (dictBind) {
        return new Control_Bind.Bind(function () {
            return applyWriterT(dictSemigroup)(dictBind.Apply0());
        }, function (v) {
            return function (k) {
                return WriterT(Control_Bind.bind(dictBind)(v)(function (v1) {
                    var v2 = k(v1.value0);
                    return Data_Functor.map((dictBind.Apply0()).Functor0())(function (v3) {
                        return new Data_Tuple.Tuple(v3.value0, Data_Semigroup.append(dictSemigroup)(v1.value1)(v3.value1));
                    })(v2);
                }));
            };
        });
    };
};
var applicativeWriterT = function (dictMonoid) {
    return function (dictApplicative) {
        return new Control_Applicative.Applicative(function () {
            return applyWriterT(dictMonoid.Semigroup0())(dictApplicative.Apply0());
        }, function (a) {
            return WriterT(Control_Applicative.pure(dictApplicative)(new Data_Tuple.Tuple(a, Data_Monoid.mempty(dictMonoid))));
        });
    };
};
var monadWriterT = function (dictMonoid) {
    return function (dictMonad) {
        return new Control_Monad.Monad(function () {
            return applicativeWriterT(dictMonoid)(dictMonad.Applicative0());
        }, function () {
            return bindWriterT(dictMonoid.Semigroup0())(dictMonad.Bind1());
        });
    };
};
var monadAskWriterT = function (dictMonoid) {
    return function (dictMonadAsk) {
        return new Control_Monad_Reader_Class.MonadAsk(function () {
            return monadWriterT(dictMonoid)(dictMonadAsk.Monad0());
        }, Control_Monad_Trans_Class.lift(monadTransWriterT(dictMonoid))(dictMonadAsk.Monad0())(Control_Monad_Reader_Class.ask(dictMonadAsk)));
    };
};
var monadReaderWriterT = function (dictMonoid) {
    return function (dictMonadReader) {
        return new Control_Monad_Reader_Class.MonadReader(function () {
            return monadAskWriterT(dictMonoid)(dictMonadReader.MonadAsk0());
        }, function (f) {
            return mapWriterT(Control_Monad_Reader_Class.local(dictMonadReader)(f));
        });
    };
};
var monadContWriterT = function (dictMonoid) {
    return function (dictMonadCont) {
        return new Control_Monad_Cont_Class.MonadCont(function () {
            return monadWriterT(dictMonoid)(dictMonadCont.Monad0());
        }, function (f) {
            return WriterT(Control_Monad_Cont_Class.callCC(dictMonadCont)(function (c) {
                var v = f(function (a) {
                    return WriterT(c(new Data_Tuple.Tuple(a, Data_Monoid.mempty(dictMonoid))));
                });
                return v;
            }));
        });
    };
};
var monadEffectWriter = function (dictMonoid) {
    return function (dictMonadEffect) {
        return new Effect_Class.MonadEffect(function () {
            return monadWriterT(dictMonoid)(dictMonadEffect.Monad0());
        }, function ($123) {
            return Control_Monad_Trans_Class.lift(monadTransWriterT(dictMonoid))(dictMonadEffect.Monad0())(Effect_Class.liftEffect(dictMonadEffect)($123));
        });
    };
};
var monadRecWriterT = function (dictMonoid) {
    return function (dictMonadRec) {
        return new Control_Monad_Rec_Class.MonadRec(function () {
            return monadWriterT(dictMonoid)(dictMonadRec.Monad0());
        }, function (f) {
            return function (a) {
                var f$prime = function (v) {
                    return Control_Bind.bind((dictMonadRec.Monad0()).Bind1())((function () {
                        var v1 = f(v.value0);
                        return v1;
                    })())(function (v1) {
                        return Control_Applicative.pure((dictMonadRec.Monad0()).Applicative0())((function () {
                            if (v1.value0 instanceof Control_Monad_Rec_Class.Loop) {
                                return new Control_Monad_Rec_Class.Loop(new Data_Tuple.Tuple(v1.value0.value0, Data_Semigroup.append(dictMonoid.Semigroup0())(v.value1)(v1.value1)));
                            };
                            if (v1.value0 instanceof Control_Monad_Rec_Class.Done) {
                                return new Control_Monad_Rec_Class.Done(new Data_Tuple.Tuple(v1.value0.value0, Data_Semigroup.append(dictMonoid.Semigroup0())(v.value1)(v1.value1)));
                            };
                            throw new Error("Failed pattern match at Control.Monad.Writer.Trans line 83, column 16 - line 85, column 47: " + [ v1.value0.constructor.name ]);
                        })());
                    });
                };
                return WriterT(Control_Monad_Rec_Class.tailRecM(dictMonadRec)(f$prime)(new Data_Tuple.Tuple(a, Data_Monoid.mempty(dictMonoid))));
            };
        });
    };
};
var monadStateWriterT = function (dictMonoid) {
    return function (dictMonadState) {
        return new Control_Monad_State_Class.MonadState(function () {
            return monadWriterT(dictMonoid)(dictMonadState.Monad0());
        }, function (f) {
            return Control_Monad_Trans_Class.lift(monadTransWriterT(dictMonoid))(dictMonadState.Monad0())(Control_Monad_State_Class.state(dictMonadState)(f));
        });
    };
};
var monadTellWriterT = function (dictMonoid) {
    return function (dictMonad) {
        return new Control_Monad_Writer_Class.MonadTell(function () {
            return monadWriterT(dictMonoid)(dictMonad);
        }, function ($124) {
            return WriterT(Control_Applicative.pure(dictMonad.Applicative0())(Data_Tuple.Tuple.create(Data_Unit.unit)($124)));
        });
    };
};
var monadWriterWriterT = function (dictMonoid) {
    return function (dictMonad) {
        return new Control_Monad_Writer_Class.MonadWriter(function () {
            return monadTellWriterT(dictMonoid)(dictMonad);
        }, function (v) {
            return Control_Bind.bind(dictMonad.Bind1())(v)(function (v1) {
                return Control_Applicative.pure(dictMonad.Applicative0())(new Data_Tuple.Tuple(new Data_Tuple.Tuple(v1.value0, v1.value1), v1.value1));
            });
        }, function (v) {
            return Control_Bind.bind(dictMonad.Bind1())(v)(function (v1) {
                return Control_Applicative.pure(dictMonad.Applicative0())(new Data_Tuple.Tuple(v1.value0.value0, v1.value0.value1(v1.value1)));
            });
        });
    };
};
var monadThrowWriterT = function (dictMonoid) {
    return function (dictMonadThrow) {
        return new Control_Monad_Error_Class.MonadThrow(function () {
            return monadWriterT(dictMonoid)(dictMonadThrow.Monad0());
        }, function (e) {
            return Control_Monad_Trans_Class.lift(monadTransWriterT(dictMonoid))(dictMonadThrow.Monad0())(Control_Monad_Error_Class.throwError(dictMonadThrow)(e));
        });
    };
};
var monadErrorWriterT = function (dictMonoid) {
    return function (dictMonadError) {
        return new Control_Monad_Error_Class.MonadError(function () {
            return monadThrowWriterT(dictMonoid)(dictMonadError.MonadThrow0());
        }, function (v) {
            return function (h) {
                return WriterT(Control_Monad_Error_Class.catchError(dictMonadError)(v)(function (e) {
                    var v1 = h(e);
                    return v1;
                }));
            };
        });
    };
};
var altWriterT = function (dictAlt) {
    return new Control_Alt.Alt(function () {
        return functorWriterT(dictAlt.Functor0());
    }, function (v) {
        return function (v1) {
            return Control_Alt.alt(dictAlt)(v)(v1);
        };
    });
};
var plusWriterT = function (dictPlus) {
    return new Control_Plus.Plus(function () {
        return altWriterT(dictPlus.Alt0());
    }, Control_Plus.empty(dictPlus));
};
var alternativeWriterT = function (dictMonoid) {
    return function (dictAlternative) {
        return new Control_Alternative.Alternative(function () {
            return applicativeWriterT(dictMonoid)(dictAlternative.Applicative0());
        }, function () {
            return plusWriterT(dictAlternative.Plus1());
        });
    };
};
var monadZeroWriterT = function (dictMonoid) {
    return function (dictMonadZero) {
        return new Control_MonadZero.MonadZero(function () {
            return alternativeWriterT(dictMonoid)(dictMonadZero.Alternative1());
        }, function () {
            return monadWriterT(dictMonoid)(dictMonadZero.Monad0());
        });
    };
};
var monadPlusWriterT = function (dictMonoid) {
    return function (dictMonadPlus) {
        return new Control_MonadPlus.MonadPlus(function () {
            return monadZeroWriterT(dictMonoid)(dictMonadPlus.MonadZero0());
        });
    };
};
module.exports = {
    WriterT: WriterT,
    runWriterT: runWriterT,
    execWriterT: execWriterT,
    mapWriterT: mapWriterT,
    newtypeWriterT: newtypeWriterT,
    functorWriterT: functorWriterT,
    applyWriterT: applyWriterT,
    applicativeWriterT: applicativeWriterT,
    altWriterT: altWriterT,
    plusWriterT: plusWriterT,
    alternativeWriterT: alternativeWriterT,
    bindWriterT: bindWriterT,
    monadWriterT: monadWriterT,
    monadRecWriterT: monadRecWriterT,
    monadZeroWriterT: monadZeroWriterT,
    monadPlusWriterT: monadPlusWriterT,
    monadTransWriterT: monadTransWriterT,
    monadEffectWriter: monadEffectWriter,
    monadContWriterT: monadContWriterT,
    monadThrowWriterT: monadThrowWriterT,
    monadErrorWriterT: monadErrorWriterT,
    monadAskWriterT: monadAskWriterT,
    monadReaderWriterT: monadReaderWriterT,
    monadStateWriterT: monadStateWriterT,
    monadTellWriterT: monadTellWriterT,
    monadWriterWriterT: monadWriterWriterT
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad.Cont.Class/index.js":29,"../Control.Monad.Error.Class/index.js":31,"../Control.Monad.Reader.Class/index.js":34,"../Control.Monad.Rec.Class/index.js":36,"../Control.Monad.State.Class/index.js":41,"../Control.Monad.Trans.Class/index.js":42,"../Control.Monad.Writer.Class/index.js":43,"../Control.Monad/index.js":47,"../Control.MonadPlus/index.js":45,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Semigroup/index.js":137,"../Data.Tuple/index.js":160,"../Data.Unit/index.js":168,"../Effect.Class/index.js":173,"../Prelude/index.js":195}],45:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var MonadPlus = function (MonadZero0) {
    this.MonadZero0 = MonadZero0;
};
var monadPlusArray = new MonadPlus(function () {
    return Control_MonadZero.monadZeroArray;
});
module.exports = {
    MonadPlus: MonadPlus,
    monadPlusArray: monadPlusArray
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Data.Functor/index.js":102}],46:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var MonadZero = function (Alternative1, Monad0) {
    this.Alternative1 = Alternative1;
    this.Monad0 = Monad0;
};
var monadZeroArray = new MonadZero(function () {
    return Control_Alternative.alternativeArray;
}, function () {
    return Control_Monad.monadArray;
});
var guard = function (dictMonadZero) {
    return function (v) {
        if (v) {
            return Control_Applicative.pure((dictMonadZero.Alternative1()).Applicative0())(Data_Unit.unit);
        };
        if (!v) {
            return Control_Plus.empty((dictMonadZero.Alternative1()).Plus1());
        };
        throw new Error("Failed pattern match at Control.MonadZero line 54, column 1 - line 54, column 52: " + [ v.constructor.name ]);
    };
};
module.exports = {
    MonadZero: MonadZero,
    guard: guard,
    monadZeroArray: monadZeroArray
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Control.Plus/index.js":50,"../Data.Functor/index.js":102,"../Data.Unit/index.js":168}],47:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Monad = function (Applicative0, Bind1) {
    this.Applicative0 = Applicative0;
    this.Bind1 = Bind1;
};
var whenM = function (dictMonad) {
    return function (mb) {
        return function (m) {
            return Control_Bind.bind(dictMonad.Bind1())(mb)(function (v) {
                return Control_Applicative.when(dictMonad.Applicative0())(v)(m);
            });
        };
    };
};
var unlessM = function (dictMonad) {
    return function (mb) {
        return function (m) {
            return Control_Bind.bind(dictMonad.Bind1())(mb)(function (v) {
                return Control_Applicative.unless(dictMonad.Applicative0())(v)(m);
            });
        };
    };
};
var monadFn = new Monad(function () {
    return Control_Applicative.applicativeFn;
}, function () {
    return Control_Bind.bindFn;
});
var monadArray = new Monad(function () {
    return Control_Applicative.applicativeArray;
}, function () {
    return Control_Bind.bindArray;
});
var liftM1 = function (dictMonad) {
    return function (f) {
        return function (a) {
            return Control_Bind.bind(dictMonad.Bind1())(a)(function (v) {
                return Control_Applicative.pure(dictMonad.Applicative0())(f(v));
            });
        };
    };
};
var ap = function (dictMonad) {
    return function (f) {
        return function (a) {
            return Control_Bind.bind(dictMonad.Bind1())(f)(function (v) {
                return Control_Bind.bind(dictMonad.Bind1())(a)(function (v1) {
                    return Control_Applicative.pure(dictMonad.Applicative0())(v(v1));
                });
            });
        };
    };
};
module.exports = {
    Monad: Monad,
    liftM1: liftM1,
    ap: ap,
    whenM: whenM,
    unlessM: unlessM,
    monadFn: monadFn,
    monadArray: monadArray
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Data.Functor/index.js":102,"../Data.Unit/index.js":168}],48:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad_Cont_Trans = require("../Control.Monad.Cont.Trans/index.js");
var Control_Monad_Except_Trans = require("../Control.Monad.Except.Trans/index.js");
var Control_Monad_Maybe_Trans = require("../Control.Monad.Maybe.Trans/index.js");
var Control_Monad_Reader_Trans = require("../Control.Monad.Reader.Trans/index.js");
var Control_Monad_Writer_Trans = require("../Control.Monad.Writer.Trans/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_Compose = require("../Data.Functor.Compose/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Effect_Class = require("../Effect.Class/index.js");
var Effect_Ref = require("../Effect.Ref/index.js");
var Prelude = require("../Prelude/index.js");
var ParCont = function (x) {
    return x;
};
var Parallel = function (Applicative1, Monad0, parallel, sequential) {
    this.Applicative1 = Applicative1;
    this.Monad0 = Monad0;
    this.parallel = parallel;
    this.sequential = sequential;
};
var sequential = function (dict) {
    return dict.sequential;
};
var parallel = function (dict) {
    return dict.parallel;
};
var newtypeParCont = new Data_Newtype.Newtype(function (n) {
    return n;
}, ParCont);
var monadParWriterT = function (dictMonoid) {
    return function (dictParallel) {
        return new Parallel(function () {
            return Control_Monad_Writer_Trans.applicativeWriterT(dictMonoid)(dictParallel.Applicative1());
        }, function () {
            return Control_Monad_Writer_Trans.monadWriterT(dictMonoid)(dictParallel.Monad0());
        }, Control_Monad_Writer_Trans.mapWriterT(parallel(dictParallel)), Control_Monad_Writer_Trans.mapWriterT(sequential(dictParallel)));
    };
};
var monadParReaderT = function (dictParallel) {
    return new Parallel(function () {
        return Control_Monad_Reader_Trans.applicativeReaderT(dictParallel.Applicative1());
    }, function () {
        return Control_Monad_Reader_Trans.monadReaderT(dictParallel.Monad0());
    }, Control_Monad_Reader_Trans.mapReaderT(parallel(dictParallel)), Control_Monad_Reader_Trans.mapReaderT(sequential(dictParallel)));
};
var monadParMaybeT = function (dictParallel) {
    return new Parallel(function () {
        return Data_Functor_Compose.applicativeCompose(dictParallel.Applicative1())(Data_Maybe.applicativeMaybe);
    }, function () {
        return Control_Monad_Maybe_Trans.monadMaybeT(dictParallel.Monad0());
    }, function (v) {
        return parallel(dictParallel)(v);
    }, function (v) {
        return sequential(dictParallel)(v);
    });
};
var monadParExceptT = function (dictParallel) {
    return new Parallel(function () {
        return Data_Functor_Compose.applicativeCompose(dictParallel.Applicative1())(Data_Either.applicativeEither);
    }, function () {
        return Control_Monad_Except_Trans.monadExceptT(dictParallel.Monad0());
    }, function (v) {
        return parallel(dictParallel)(v);
    }, function (v) {
        return sequential(dictParallel)(v);
    });
};
var monadParParCont = function (dictMonadEffect) {
    return new Parallel(function () {
        return applicativeParCont(dictMonadEffect);
    }, function () {
        return Control_Monad_Cont_Trans.monadContT(dictMonadEffect.Monad0());
    }, ParCont, function (v) {
        return v;
    });
};
var functorParCont = function (dictMonadEffect) {
    return new Data_Functor.Functor(function (f) {
        return function ($54) {
            return parallel(monadParParCont(dictMonadEffect))(Data_Functor.map(Control_Monad_Cont_Trans.functorContT((((dictMonadEffect.Monad0()).Bind1()).Apply0()).Functor0()))(f)(sequential(monadParParCont(dictMonadEffect))($54)));
        };
    });
};
var applyParCont = function (dictMonadEffect) {
    return new Control_Apply.Apply(function () {
        return functorParCont(dictMonadEffect);
    }, function (v) {
        return function (v1) {
            return ParCont(function (k) {
                return Control_Bind.bind((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref["new"](Data_Maybe.Nothing.value)))(function (v2) {
                    return Control_Bind.bind((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref["new"](Data_Maybe.Nothing.value)))(function (v3) {
                        return Control_Bind.discard(Control_Bind.discardUnit)((dictMonadEffect.Monad0()).Bind1())(Control_Monad_Cont_Trans.runContT(v)(function (a) {
                            return Control_Bind.bind((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.read(v3)))(function (v4) {
                                if (v4 instanceof Data_Maybe.Nothing) {
                                    return Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.write(new Data_Maybe.Just(a))(v2));
                                };
                                if (v4 instanceof Data_Maybe.Just) {
                                    return k(a(v4.value0));
                                };
                                throw new Error("Failed pattern match at Control.Parallel.Class line 71, column 7 - line 73, column 26: " + [ v4.constructor.name ]);
                            });
                        }))(function () {
                            return Control_Monad_Cont_Trans.runContT(v1)(function (b) {
                                return Control_Bind.bind((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.read(v2)))(function (v4) {
                                    if (v4 instanceof Data_Maybe.Nothing) {
                                        return Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.write(new Data_Maybe.Just(b))(v3));
                                    };
                                    if (v4 instanceof Data_Maybe.Just) {
                                        return k(v4.value0(b));
                                    };
                                    throw new Error("Failed pattern match at Control.Parallel.Class line 77, column 7 - line 79, column 26: " + [ v4.constructor.name ]);
                                });
                            });
                        });
                    });
                });
            });
        };
    });
};
var applicativeParCont = function (dictMonadEffect) {
    return new Control_Applicative.Applicative(function () {
        return applyParCont(dictMonadEffect);
    }, function ($55) {
        return parallel(monadParParCont(dictMonadEffect))(Control_Applicative.pure(Control_Monad_Cont_Trans.applicativeContT((dictMonadEffect.Monad0()).Applicative0()))($55));
    });
};
var altParCont = function (dictMonadEffect) {
    return new Control_Alt.Alt(function () {
        return functorParCont(dictMonadEffect);
    }, function (v) {
        return function (v1) {
            return ParCont(function (k) {
                return Control_Bind.bind((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref["new"](false)))(function (v2) {
                    return Control_Bind.discard(Control_Bind.discardUnit)((dictMonadEffect.Monad0()).Bind1())(Control_Monad_Cont_Trans.runContT(v)(function (a) {
                        return Control_Bind.bind((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.read(v2)))(function (v3) {
                            if (v3) {
                                return Control_Applicative.pure((dictMonadEffect.Monad0()).Applicative0())(Data_Unit.unit);
                            };
                            return Control_Bind.discard(Control_Bind.discardUnit)((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.write(true)(v2)))(function () {
                                return k(a);
                            });
                        });
                    }))(function () {
                        return Control_Monad_Cont_Trans.runContT(v1)(function (a) {
                            return Control_Bind.bind((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.read(v2)))(function (v3) {
                                if (v3) {
                                    return Control_Applicative.pure((dictMonadEffect.Monad0()).Applicative0())(Data_Unit.unit);
                                };
                                return Control_Bind.discard(Control_Bind.discardUnit)((dictMonadEffect.Monad0()).Bind1())(Effect_Class.liftEffect(dictMonadEffect)(Effect_Ref.write(true)(v2)))(function () {
                                    return k(a);
                                });
                            });
                        });
                    });
                });
            });
        };
    });
};
var plusParCont = function (dictMonadEffect) {
    return new Control_Plus.Plus(function () {
        return altParCont(dictMonadEffect);
    }, ParCont(function (v) {
        return Control_Applicative.pure((dictMonadEffect.Monad0()).Applicative0())(Data_Unit.unit);
    }));
};
var alternativeParCont = function (dictMonadEffect) {
    return new Control_Alternative.Alternative(function () {
        return applicativeParCont(dictMonadEffect);
    }, function () {
        return plusParCont(dictMonadEffect);
    });
};
module.exports = {
    parallel: parallel,
    sequential: sequential,
    Parallel: Parallel,
    ParCont: ParCont,
    monadParExceptT: monadParExceptT,
    monadParReaderT: monadParReaderT,
    monadParWriterT: monadParWriterT,
    monadParMaybeT: monadParMaybeT,
    newtypeParCont: newtypeParCont,
    functorParCont: functorParCont,
    applyParCont: applyParCont,
    applicativeParCont: applicativeParCont,
    altParCont: altParCont,
    plusParCont: plusParCont,
    alternativeParCont: alternativeParCont,
    monadParParCont: monadParParCont
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad.Cont.Trans/index.js":30,"../Control.Monad.Except.Trans/index.js":32,"../Control.Monad.Maybe.Trans/index.js":33,"../Control.Monad.Reader.Trans/index.js":35,"../Control.Monad.Writer.Trans/index.js":44,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Either/index.js":82,"../Data.Function/index.js":95,"../Data.Functor.Compose/index.js":97,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Newtype/index.js":121,"../Data.Unit/index.js":168,"../Effect.Class/index.js":173,"../Effect.Ref/index.js":179,"../Prelude/index.js":195}],49:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Parallel_Class = require("../Control.Parallel.Class/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Prelude = require("../Prelude/index.js");
var parTraverse_ = function (dictParallel) {
    return function (dictFoldable) {
        return function (f) {
            return function ($17) {
                return Control_Parallel_Class.sequential(dictParallel)(Data_Foldable.traverse_(dictParallel.Applicative1())(dictFoldable)(function ($18) {
                    return Control_Parallel_Class.parallel(dictParallel)(f($18));
                })($17));
            };
        };
    };
};
var parTraverse = function (dictParallel) {
    return function (dictTraversable) {
        return function (f) {
            return function ($19) {
                return Control_Parallel_Class.sequential(dictParallel)(Data_Traversable.traverse(dictTraversable)(dictParallel.Applicative1())(function ($20) {
                    return Control_Parallel_Class.parallel(dictParallel)(f($20));
                })($19));
            };
        };
    };
};
var parSequence_ = function (dictParallel) {
    return function (dictFoldable) {
        return parTraverse_(dictParallel)(dictFoldable)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var parSequence = function (dictParallel) {
    return function (dictTraversable) {
        return parTraverse(dictParallel)(dictTraversable)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var parOneOfMap = function (dictParallel) {
    return function (dictAlternative) {
        return function (dictFoldable) {
            return function (dictFunctor) {
                return function (f) {
                    return function ($21) {
                        return Control_Parallel_Class.sequential(dictParallel)(Data_Foldable.oneOfMap(dictFoldable)(dictAlternative.Plus1())(function ($22) {
                            return Control_Parallel_Class.parallel(dictParallel)(f($22));
                        })($21));
                    };
                };
            };
        };
    };
};
var parOneOf = function (dictParallel) {
    return function (dictAlternative) {
        return function (dictFoldable) {
            return function (dictFunctor) {
                return function ($23) {
                    return Control_Parallel_Class.sequential(dictParallel)(Data_Foldable.oneOfMap(dictFoldable)(dictAlternative.Plus1())(Control_Parallel_Class.parallel(dictParallel))($23));
                };
            };
        };
    };
};
var parApply = function (dictParallel) {
    return function (mf) {
        return function (ma) {
            return Control_Parallel_Class.sequential(dictParallel)(Control_Apply.apply((dictParallel.Applicative1()).Apply0())(Control_Parallel_Class.parallel(dictParallel)(mf))(Control_Parallel_Class.parallel(dictParallel)(ma)));
        };
    };
};
module.exports = {
    parApply: parApply,
    parTraverse: parTraverse,
    parTraverse_: parTraverse_,
    parSequence: parSequence,
    parSequence_: parSequence_,
    parOneOf: parOneOf,
    parOneOfMap: parOneOfMap
};

},{"../Control.Alternative/index.js":16,"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Control.Parallel.Class/index.js":48,"../Control.Semigroupoid/index.js":51,"../Data.Foldable/index.js":92,"../Data.Traversable/index.js":159,"../Prelude/index.js":195}],50:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Plus = function (Alt0, empty) {
    this.Alt0 = Alt0;
    this.empty = empty;
};
var plusArray = new Plus(function () {
    return Control_Alt.altArray;
}, [  ]);
var empty = function (dict) {
    return dict.empty;
};
module.exports = {
    Plus: Plus,
    empty: empty,
    plusArray: plusArray
};

},{"../Control.Alt/index.js":15,"../Data.Functor/index.js":102}],51:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Semigroupoid = function (compose) {
    this.compose = compose;
};
var semigroupoidFn = new Semigroupoid(function (f) {
    return function (g) {
        return function (x) {
            return f(g(x));
        };
    };
});
var compose = function (dict) {
    return dict.compose;
};
var composeFlipped = function (dictSemigroupoid) {
    return function (f) {
        return function (g) {
            return compose(dictSemigroupoid)(g)(f);
        };
    };
};
module.exports = {
    compose: compose,
    Semigroupoid: Semigroupoid,
    composeFlipped: composeFlipped,
    semigroupoidFn: semigroupoidFn
};

},{}],52:[function(require,module,exports){
"use strict";

exports.fold1Impl = function (f) {
  return function (xs) {
    var acc = xs[0];
    var len = xs.length;
    for (var i = 1; i < len; i++) {
      acc = f(acc)(xs[i]);
    }
    return acc;
  };
};

exports.traverse1Impl = function () {
  function Cont(fn) {
    this.fn = fn;
  }

  var emptyList = {};

  var ConsCell = function (head, tail) {
    this.head = head;
    this.tail = tail;
  };

  function finalCell(head) {
    return new ConsCell(head, emptyList);
  }

  function consList(x) {
    return function (xs) {
      return new ConsCell(x, xs);
    };
  }

  function listToArray(list) {
    var arr = [];
    var xs = list;
    while (xs !== emptyList) {
      arr.push(xs.head);
      xs = xs.tail;
    }
    return arr;
  }

  return function (apply) {
    return function (map) {
      return function (f) {
        var buildFrom = function (x, ys) {
          return apply(map(consList)(f(x)))(ys);
        };

        var go = function (acc, currentLen, xs) {
          if (currentLen === 0) {
            return acc;
          } else {
            var last = xs[currentLen - 1];
            return new Cont(function () {
              var built = go(buildFrom(last, acc), currentLen - 1, xs);
              return built;
            });
          }
        };

        return function (array) {
          var acc = map(finalCell)(f(array[array.length - 1]));
          var result = go(acc, array.length - 1, array);
          while (result instanceof Cont) {
            result = result.fn();
          }

          return map(listToArray)(result);
        };
      };
    };
  };
}();

},{}],53:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Alt = require("../Control.Alt/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_FoldableWithIndex = require("../Data.FoldableWithIndex/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_FunctorWithIndex = require("../Data.FunctorWithIndex/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semigroup_Foldable = require("../Data.Semigroup.Foldable/index.js");
var Data_Semigroup_Traversable = require("../Data.Semigroup.Traversable/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Data_TraversableWithIndex = require("../Data.TraversableWithIndex/index.js");
var Data_Unfoldable1 = require("../Data.Unfoldable1/index.js");
var Prelude = require("../Prelude/index.js");
var NonEmptyArray = function (x) {
    return x;
};
var unfoldable1NonEmptyArray = Data_Unfoldable1.unfoldable1Array;
var traversableWithIndexNonEmptyArray = Data_TraversableWithIndex.traversableWithIndexArray;
var traversableNonEmptyArray = Data_Traversable.traversableArray;
var showNonEmptyArray = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(NonEmptyArray " + (Data_Show.show(Data_Show.showArray(dictShow))(v) + ")");
    });
};
var semigroupNonEmptyArray = Data_Semigroup.semigroupArray;
var ordNonEmptyArray = function (dictOrd) {
    return Data_Ord.ordArray(dictOrd);
};
var ord1NonEmptyArray = Data_Ord.ord1Array;
var monadNonEmptyArray = Control_Monad.monadArray;
var functorWithIndexNonEmptyArray = Data_FunctorWithIndex.functorWithIndexArray;
var functorNonEmptyArray = Data_Functor.functorArray;
var foldableWithIndexNonEmptyArray = Data_FoldableWithIndex.foldableWithIndexArray;
var foldableNonEmptyArray = Data_Foldable.foldableArray;
var foldable1NonEmptyArray = new Data_Semigroup_Foldable.Foldable1(function () {
    return foldableNonEmptyArray;
}, function (dictSemigroup) {
    return $foreign.fold1Impl(Data_Semigroup.append(dictSemigroup));
}, function (dictSemigroup) {
    return Data_Semigroup_Foldable.foldMap1Default(foldable1NonEmptyArray)(functorNonEmptyArray)(dictSemigroup);
});
var traversable1NonEmptyArray = new Data_Semigroup_Traversable.Traversable1(function () {
    return foldable1NonEmptyArray;
}, function () {
    return traversableNonEmptyArray;
}, function (dictApply) {
    return Data_Semigroup_Traversable.sequence1Default(traversable1NonEmptyArray)(dictApply);
}, function (dictApply) {
    return $foreign.traverse1Impl(Control_Apply.apply(dictApply))(Data_Functor.map(dictApply.Functor0()));
});
var eqNonEmptyArray = function (dictEq) {
    return Data_Eq.eqArray(dictEq);
};
var eq1NonEmptyArray = Data_Eq.eq1Array;
var bindNonEmptyArray = Control_Bind.bindArray;
var applyNonEmptyArray = Control_Apply.applyArray;
var applicativeNonEmptyArray = Control_Applicative.applicativeArray;
var altNonEmptyArray = Control_Alt.altArray;
module.exports = {
    showNonEmptyArray: showNonEmptyArray,
    eqNonEmptyArray: eqNonEmptyArray,
    eq1NonEmptyArray: eq1NonEmptyArray,
    ordNonEmptyArray: ordNonEmptyArray,
    ord1NonEmptyArray: ord1NonEmptyArray,
    semigroupNonEmptyArray: semigroupNonEmptyArray,
    functorNonEmptyArray: functorNonEmptyArray,
    functorWithIndexNonEmptyArray: functorWithIndexNonEmptyArray,
    foldableNonEmptyArray: foldableNonEmptyArray,
    foldableWithIndexNonEmptyArray: foldableWithIndexNonEmptyArray,
    foldable1NonEmptyArray: foldable1NonEmptyArray,
    unfoldable1NonEmptyArray: unfoldable1NonEmptyArray,
    traversableNonEmptyArray: traversableNonEmptyArray,
    traversableWithIndexNonEmptyArray: traversableWithIndexNonEmptyArray,
    traversable1NonEmptyArray: traversable1NonEmptyArray,
    applyNonEmptyArray: applyNonEmptyArray,
    applicativeNonEmptyArray: applicativeNonEmptyArray,
    bindNonEmptyArray: bindNonEmptyArray,
    monadNonEmptyArray: monadNonEmptyArray,
    altNonEmptyArray: altNonEmptyArray
};

},{"../Control.Alt/index.js":15,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.FoldableWithIndex/index.js":90,"../Data.Functor/index.js":102,"../Data.FunctorWithIndex/index.js":100,"../Data.Ord/index.js":128,"../Data.Semigroup.Foldable/index.js":133,"../Data.Semigroup.Traversable/index.js":135,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Data.Traversable/index.js":159,"../Data.TraversableWithIndex/index.js":157,"../Data.Unfoldable1/index.js":164,"../Prelude/index.js":195,"./foreign.js":52}],54:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Lazy = require("../Control.Lazy/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Array = require("../Data.Array/index.js");
var Data_Array_NonEmpty_Internal = require("../Data.Array.NonEmpty.Internal/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_NonEmpty = require("../Data.NonEmpty/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semigroup_Foldable = require("../Data.Semigroup.Foldable/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unfoldable = require("../Data.Unfoldable/index.js");
var Data_Unfoldable1 = require("../Data.Unfoldable1/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var Unsafe_Coerce = require("../Unsafe.Coerce/index.js");
var unsafeFromArrayF = Unsafe_Coerce.unsafeCoerce;
var unsafeFromArray = Unsafe_Coerce.unsafeCoerce;
var toArray = Unsafe_Coerce.unsafeCoerce;
var unionBy$prime = function (eq) {
    return function (xs) {
        return function ($39) {
            return unsafeFromArray(Data_Array.unionBy(eq)(toArray(xs))($39));
        };
    };
};
var union$prime = function (dictEq) {
    return unionBy$prime(Data_Eq.eq(dictEq));
};
var unionBy = function (eq) {
    return function (xs) {
        return function ($40) {
            return unionBy$prime(eq)(xs)(toArray($40));
        };
    };
};
var union = function (dictEq) {
    return unionBy(Data_Eq.eq(dictEq));
};
var unzip = function ($41) {
    return Data_Bifunctor.bimap(Data_Tuple.bifunctorTuple)(unsafeFromArray)(unsafeFromArray)(Data_Array.unzip(toArray($41)));
};
var updateAt = function (i) {
    return function (x) {
        return function ($42) {
            return unsafeFromArrayF(Data_Array.updateAt(i)(x)(toArray($42)));
        };
    };
};
var zip = function (xs) {
    return function (ys) {
        return unsafeFromArray(Data_Array.zip(toArray(xs))(toArray(ys)));
    };
};
var zipWith = function (f) {
    return function (xs) {
        return function (ys) {
            return unsafeFromArray(Data_Array.zipWith(f)(toArray(xs))(toArray(ys)));
        };
    };
};
var zipWithA = function (dictApplicative) {
    return function (f) {
        return function (xs) {
            return function (ys) {
                return unsafeFromArrayF(Data_Array.zipWithA(dictApplicative)(f)(toArray(xs))(toArray(ys)));
            };
        };
    };
};
var some = function (dictAlternative) {
    return function (dictLazy) {
        return function ($43) {
            return unsafeFromArrayF(Data_Array.some(dictAlternative)(dictLazy)($43));
        };
    };
};
var snoc$prime = function (xs) {
    return function (x) {
        return unsafeFromArray(Data_Array.snoc(xs)(x));
    };
};
var snoc = function (xs) {
    return function (x) {
        return unsafeFromArray(Data_Array.snoc(toArray(xs))(x));
    };
};
var singleton = function ($44) {
    return unsafeFromArray(Data_Array.singleton($44));
};
var replicate = function (i) {
    return function (x) {
        return unsafeFromArray(Data_Array.replicate(Data_Ord.max(Data_Ord.ordInt)(1)(i))(x));
    };
};
var range = function (x) {
    return function (y) {
        return unsafeFromArray(Data_Array.range(x)(y));
    };
};
var modifyAt = function (i) {
    return function (f) {
        return function ($45) {
            return unsafeFromArrayF(Data_Array.modifyAt(i)(f)(toArray($45)));
        };
    };
};
var intersectBy$prime = function (eq) {
    return function (xs) {
        return Data_Array.intersectBy(eq)(toArray(xs));
    };
};
var intersectBy = function (eq) {
    return function (xs) {
        return function ($46) {
            return intersectBy$prime(eq)(xs)(toArray($46));
        };
    };
};
var intersect$prime = function (dictEq) {
    return intersectBy$prime(Data_Eq.eq(dictEq));
};
var intersect = function (dictEq) {
    return intersectBy(Data_Eq.eq(dictEq));
};
var insertAt = function (i) {
    return function (x) {
        return function ($47) {
            return unsafeFromArrayF(Data_Array.insertAt(i)(x)(toArray($47)));
        };
    };
};
var fromFoldable1 = function (dictFoldable1) {
    return function ($48) {
        return unsafeFromArray(Data_Array.fromFoldable(dictFoldable1.Foldable0())($48));
    };
};
var fromArray = function (xs) {
    if (Data_Array.length(xs) > 0) {
        return new Data_Maybe.Just(unsafeFromArray(xs));
    };
    if (Data_Boolean.otherwise) {
        return Data_Maybe.Nothing.value;
    };
    throw new Error("Failed pattern match at Data.Array.NonEmpty line 134, column 1 - line 134, column 58: " + [ xs.constructor.name ]);
};
var fromFoldable = function (dictFoldable) {
    return function ($49) {
        return fromArray(Data_Array.fromFoldable(dictFoldable)($49));
    };
};
var difference$prime = function (dictEq) {
    return function (xs) {
        return Data_Array.difference(dictEq)(toArray(xs));
    };
};
var cons$prime = function (x) {
    return function (xs) {
        return unsafeFromArray(Data_Array.cons(x)(xs));
    };
};
var fromNonEmpty = function (v) {
    return cons$prime(v.value0)(v.value1);
};
var concatMap = Data_Function.flip(Control_Bind.bind(Data_Array_NonEmpty_Internal.bindNonEmptyArray));
var concat = function ($50) {
    return unsafeFromArray(Data_Array.concat(toArray(Data_Functor.map(Data_Array_NonEmpty_Internal.functorNonEmptyArray)(toArray)($50))));
};
var appendArray = function (xs) {
    return function (ys) {
        return unsafeFromArray(Data_Semigroup.append(Data_Semigroup.semigroupArray)(toArray(xs))(ys));
    };
};
var alterAt = function (i) {
    return function (f) {
        return function ($51) {
            return Data_Array.alterAt(i)(f)(toArray($51));
        };
    };
};
var adaptMaybe = function (f) {
    return function ($52) {
        return Data_Maybe.fromJust()(f(toArray($52)));
    };
};
var head = adaptMaybe(Data_Array.head);
var init = adaptMaybe(Data_Array.init);
var last = adaptMaybe(Data_Array.last);
var tail = adaptMaybe(Data_Array.tail);
var uncons = adaptMaybe(Data_Array.uncons);
var toNonEmpty = function ($53) {
    return (function (v) {
        return new Data_NonEmpty.NonEmpty(v.head, v.tail);
    })(uncons($53));
};
var unsnoc = adaptMaybe(Data_Array.unsnoc);
var adaptAny = function (f) {
    return function ($54) {
        return f(toArray($54));
    };
};
var catMaybes = adaptAny(Data_Array.catMaybes);
var $$delete = function (dictEq) {
    return function (x) {
        return adaptAny(Data_Array["delete"](dictEq)(x));
    };
};
var deleteAt = function (i) {
    return adaptAny(Data_Array.deleteAt(i));
};
var deleteBy = function (f) {
    return function (x) {
        return adaptAny(Data_Array.deleteBy(f)(x));
    };
};
var difference = function (dictEq) {
    return function (xs) {
        return adaptAny(difference$prime(dictEq)(xs));
    };
};
var drop = function (i) {
    return adaptAny(Data_Array.drop(i));
};
var dropEnd = function (i) {
    return adaptAny(Data_Array.dropEnd(i));
};
var dropWhile = function (f) {
    return adaptAny(Data_Array.dropWhile(f));
};
var elemIndex = function (dictEq) {
    return function (x) {
        return adaptAny(Data_Array.elemIndex(dictEq)(x));
    };
};
var elemLastIndex = function (dictEq) {
    return function (x) {
        return adaptAny(Data_Array.elemLastIndex(dictEq)(x));
    };
};
var filter = function (f) {
    return adaptAny(Data_Array.filter(f));
};
var filterA = function (dictApplicative) {
    return function (f) {
        return adaptAny(Data_Array.filterA(dictApplicative)(f));
    };
};
var findIndex = function (x) {
    return adaptAny(Data_Array.findIndex(x));
};
var findLastIndex = function (x) {
    return adaptAny(Data_Array.findLastIndex(x));
};
var foldM = function (dictMonad) {
    return function (f) {
        return function (acc) {
            return adaptAny(Data_Array.foldM(dictMonad)(f)(acc));
        };
    };
};
var foldRecM = function (dictMonadRec) {
    return function (f) {
        return function (acc) {
            return adaptAny(Data_Array.foldRecM(dictMonadRec)(f)(acc));
        };
    };
};
var index = adaptAny(Data_Array.index);
var length = adaptAny(Data_Array.length);
var mapMaybe = function (f) {
    return adaptAny(Data_Array.mapMaybe(f));
};
var partition = function (f) {
    return adaptAny(Data_Array.partition(f));
};
var slice = function (start) {
    return function (end) {
        return adaptAny(Data_Array.slice(start)(end));
    };
};
var span = function (f) {
    return adaptAny(Data_Array.span(f));
};
var take = function (i) {
    return adaptAny(Data_Array.take(i));
};
var takeEnd = function (i) {
    return adaptAny(Data_Array.takeEnd(i));
};
var takeWhile = function (f) {
    return adaptAny(Data_Array.takeWhile(f));
};
var toUnfoldable = function (dictUnfoldable) {
    return adaptAny(Data_Array.toUnfoldable(dictUnfoldable));
};
var unsafeAdapt = function (f) {
    return function ($55) {
        return unsafeFromArray(adaptAny(f)($55));
    };
};
var cons = function (x) {
    return unsafeAdapt(Data_Array.cons(x));
};
var insert = function (dictOrd) {
    return function (x) {
        return unsafeAdapt(Data_Array.insert(dictOrd)(x));
    };
};
var insertBy = function (f) {
    return function (x) {
        return unsafeAdapt(Data_Array.insertBy(f)(x));
    };
};
var modifyAtIndices = function (dictFoldable) {
    return function (is) {
        return function (f) {
            return unsafeAdapt(Data_Array.modifyAtIndices(dictFoldable)(is)(f));
        };
    };
};
var nub = function (dictOrd) {
    return unsafeAdapt(Data_Array.nub(dictOrd));
};
var nubBy = function (f) {
    return unsafeAdapt(Data_Array.nubBy(f));
};
var nubByEq = function (f) {
    return unsafeAdapt(Data_Array.nubByEq(f));
};
var nubEq = function (dictEq) {
    return unsafeAdapt(Data_Array.nubEq(dictEq));
};
var reverse = unsafeAdapt(Data_Array.reverse);
var sort = function (dictOrd) {
    return unsafeAdapt(Data_Array.sort(dictOrd));
};
var sortBy = function (f) {
    return unsafeAdapt(Data_Array.sortBy(f));
};
var sortWith = function (dictOrd) {
    return function (f) {
        return unsafeAdapt(Data_Array.sortWith(dictOrd)(f));
    };
};
var updateAtIndices = function (dictFoldable) {
    return function (pairs) {
        return unsafeAdapt(Data_Array.updateAtIndices(dictFoldable)(pairs));
    };
};
var unsafeIndex = function (dictPartial) {
    return adaptAny(Data_Array.unsafeIndex(dictPartial));
};
var toUnfoldable1 = function (dictUnfoldable1) {
    return function (xs) {
        var len = length(xs);
        var f = function (i) {
            return Data_Tuple.Tuple.create(unsafeIndex()(xs)(i))((function () {
                var $38 = i < (len - 1 | 0);
                if ($38) {
                    return new Data_Maybe.Just(i + 1 | 0);
                };
                return Data_Maybe.Nothing.value;
            })());
        };
        return Data_Unfoldable1.unfoldr1(dictUnfoldable1)(f)(0);
    };
};
module.exports = {
    fromArray: fromArray,
    fromNonEmpty: fromNonEmpty,
    toArray: toArray,
    toNonEmpty: toNonEmpty,
    fromFoldable: fromFoldable,
    fromFoldable1: fromFoldable1,
    toUnfoldable: toUnfoldable,
    toUnfoldable1: toUnfoldable1,
    singleton: singleton,
    range: range,
    replicate: replicate,
    some: some,
    length: length,
    cons: cons,
    "cons'": cons$prime,
    snoc: snoc,
    "snoc'": snoc$prime,
    appendArray: appendArray,
    insert: insert,
    insertBy: insertBy,
    head: head,
    last: last,
    tail: tail,
    init: init,
    uncons: uncons,
    unsnoc: unsnoc,
    index: index,
    elemIndex: elemIndex,
    elemLastIndex: elemLastIndex,
    findIndex: findIndex,
    findLastIndex: findLastIndex,
    insertAt: insertAt,
    deleteAt: deleteAt,
    updateAt: updateAt,
    updateAtIndices: updateAtIndices,
    modifyAt: modifyAt,
    modifyAtIndices: modifyAtIndices,
    alterAt: alterAt,
    reverse: reverse,
    concat: concat,
    concatMap: concatMap,
    filter: filter,
    partition: partition,
    filterA: filterA,
    mapMaybe: mapMaybe,
    catMaybes: catMaybes,
    sort: sort,
    sortBy: sortBy,
    sortWith: sortWith,
    slice: slice,
    take: take,
    takeEnd: takeEnd,
    takeWhile: takeWhile,
    drop: drop,
    dropEnd: dropEnd,
    dropWhile: dropWhile,
    span: span,
    nub: nub,
    nubBy: nubBy,
    nubEq: nubEq,
    nubByEq: nubByEq,
    union: union,
    "union'": union$prime,
    unionBy: unionBy,
    "unionBy'": unionBy$prime,
    "delete": $$delete,
    deleteBy: deleteBy,
    difference: difference,
    "difference'": difference$prime,
    intersect: intersect,
    "intersect'": intersect$prime,
    intersectBy: intersectBy,
    "intersectBy'": intersectBy$prime,
    zipWith: zipWith,
    zipWithA: zipWithA,
    zip: zip,
    unzip: unzip,
    foldM: foldM,
    foldRecM: foldRecM,
    unsafeIndex: unsafeIndex
};

},{"../Control.Alternative/index.js":16,"../Control.Bind/index.js":23,"../Control.Lazy/index.js":28,"../Control.Monad.Rec.Class/index.js":36,"../Control.Semigroupoid/index.js":51,"../Data.Array.NonEmpty.Internal/index.js":53,"../Data.Array/index.js":66,"../Data.Bifunctor/index.js":73,"../Data.Boolean/index.js":76,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.NonEmpty/index.js":122,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Semigroup.Foldable/index.js":133,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Tuple/index.js":160,"../Data.Unfoldable/index.js":166,"../Data.Unfoldable1/index.js":164,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195,"../Unsafe.Coerce/index.js":202}],55:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad_ST = require("../Control.Monad.ST/index.js");
var Control_Monad_ST_Internal = require("../Control.Monad.ST.Internal/index.js");
var Control_Monad_ST_Ref = require("../Control.Monad.ST.Ref/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Array_ST = require("../Data.Array.ST/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Prelude = require("../Prelude/index.js");
var Iterator = (function () {
    function Iterator(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Iterator.create = function (value0) {
        return function (value1) {
            return new Iterator(value0, value1);
        };
    };
    return Iterator;
})();
var peek = function (v) {
    return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Control_Monad_ST_Internal.read(v.value1))(function (v1) {
        return Control_Applicative.pure(Control_Monad_ST_Internal.applicativeST)(v.value0(v1));
    });
};
var next = function (v) {
    return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Control_Monad_ST_Internal.read(v.value1))(function (v1) {
        return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Control_Monad_ST_Internal.modify(function (v2) {
            return v2 + 1 | 0;
        })(v.value1))(function (v2) {
            return Control_Applicative.pure(Control_Monad_ST_Internal.applicativeST)(v.value0(v1));
        });
    });
};
var pushWhile = function (p) {
    return function (iter) {
        return function (array) {
            return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Control_Monad_ST_Internal["new"](false))(function (v) {
                return Control_Monad_ST_Internal["while"](Data_Functor.map(Control_Monad_ST_Internal.functorST)(Data_HeytingAlgebra.not(Data_HeytingAlgebra.heytingAlgebraBoolean))(Control_Monad_ST_Internal.read(v)))(Control_Bind.bind(Control_Monad_ST_Internal.bindST)(peek(iter))(function (v1) {
                    if (v1 instanceof Data_Maybe.Just && p(v1.value0)) {
                        return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.push(v1.value0)(array))(function (v2) {
                            return Data_Functor["void"](Control_Monad_ST_Internal.functorST)(next(iter));
                        });
                    };
                    return Data_Functor["void"](Control_Monad_ST_Internal.functorST)(Control_Monad_ST_Internal.write(true)(v));
                }));
            });
        };
    };
};
var pushAll = pushWhile(Data_Function["const"](true));
var iterator = function (f) {
    return Data_Functor.map(Control_Monad_ST_Internal.functorST)(Iterator.create(f))(Control_Monad_ST_Internal["new"](0));
};
var iterate = function (iter) {
    return function (f) {
        return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Control_Monad_ST_Internal["new"](false))(function (v) {
            return Control_Monad_ST_Internal["while"](Data_Functor.map(Control_Monad_ST_Internal.functorST)(Data_HeytingAlgebra.not(Data_HeytingAlgebra.heytingAlgebraBoolean))(Control_Monad_ST_Internal.read(v)))(Control_Bind.bind(Control_Monad_ST_Internal.bindST)(next(iter))(function (v1) {
                if (v1 instanceof Data_Maybe.Just) {
                    return f(v1.value0);
                };
                if (v1 instanceof Data_Maybe.Nothing) {
                    return Data_Functor["void"](Control_Monad_ST_Internal.functorST)(Control_Monad_ST_Internal.write(true)(v));
                };
                throw new Error("Failed pattern match at Data.Array.ST.Iterator line 42, column 5 - line 44, column 47: " + [ v1.constructor.name ]);
            }));
        });
    };
};
var exhausted = function ($27) {
    return Data_Functor.map(Control_Monad_ST_Internal.functorST)(Data_Maybe.isNothing)(peek($27));
};
module.exports = {
    iterator: iterator,
    iterate: iterate,
    next: next,
    peek: peek,
    exhausted: exhausted,
    pushWhile: pushWhile,
    pushAll: pushAll
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Control.Monad.ST.Internal/index.js":38,"../Control.Monad.ST.Ref/index.js":39,"../Control.Monad.ST/index.js":40,"../Control.Semigroupoid/index.js":51,"../Data.Array.ST/index.js":57,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Maybe/index.js":112,"../Data.Semiring/index.js":139,"../Prelude/index.js":195}],56:[function(require,module,exports){
"use strict";

exports.empty = function () {
  return [];
};

exports.peekImpl = function (just) {
  return function (nothing) {
    return function (i) {
      return function (xs) {
        return function () {
          return i >= 0 && i < xs.length ? just(xs[i]) : nothing;
        };
      };
    };
  };
};

exports.poke = function (i) {
  return function (a) {
    return function (xs) {
      return function () {
        var ret = i >= 0 && i < xs.length;
        if (ret) xs[i] = a;
        return ret;
      };
    };
  };
};

exports.pushAll = function (as) {
  return function (xs) {
    return function () {
      return xs.push.apply(xs, as);
    };
  };
};

exports.splice = function (i) {
  return function (howMany) {
    return function (bs) {
      return function (xs) {
        return function () {
          return xs.splice.apply(xs, [i, howMany].concat(bs));
        };
      };
    };
  };
};

exports.copyImpl = function (xs) {
  return function () {
    return xs.slice();
  };
};

exports.sortByImpl = function (comp) {
  return function (xs) {
    return function () {
      return xs.sort(function (x, y) {
        return comp(x)(y);
      });
    };
  };
};

exports.toAssocArray = function (xs) {
  return function () {
    var n = xs.length;
    var as = new Array(n);
    for (var i = 0; i < n; i++) as[i] = { value: xs[i], index: i };
    return as;
  };
};

},{}],57:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad_ST = require("../Control.Monad.ST/index.js");
var Control_Monad_ST_Internal = require("../Control.Monad.ST.Internal/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Prelude = require("../Prelude/index.js");
var Unsafe_Coerce = require("../Unsafe.Coerce/index.js");
var unsafeThaw = function ($11) {
    return Control_Applicative.pure(Control_Monad_ST_Internal.applicativeST)($11);
};
var unsafeFreeze = function ($12) {
    return Control_Applicative.pure(Control_Monad_ST_Internal.applicativeST)($12);
};
var thaw = $foreign.copyImpl;
var withArray = function (f) {
    return function (xs) {
        return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(thaw(xs))(function (v) {
            return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(f(v))(function (v1) {
                return unsafeFreeze(v);
            });
        });
    };
};
var sortBy = function (comp) {
    var comp$prime = function (x) {
        return function (y) {
            var v = comp(x)(y);
            if (v instanceof Data_Ordering.GT) {
                return 1;
            };
            if (v instanceof Data_Ordering.EQ) {
                return 0;
            };
            if (v instanceof Data_Ordering.LT) {
                return -1 | 0;
            };
            throw new Error("Failed pattern match at Data.Array.ST line 85, column 15 - line 90, column 1: " + [ v.constructor.name ]);
        };
    };
    return $foreign.sortByImpl(comp$prime);
};
var sortWith = function (dictOrd) {
    return function (f) {
        return sortBy(Data_Ord.comparing(dictOrd)(f));
    };
};
var sort = function (dictOrd) {
    return sortBy(Data_Ord.compare(dictOrd));
};
var push = function (a) {
    return $foreign.pushAll([ a ]);
};
var peek = $foreign.peekImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var modify = function (i) {
    return function (f) {
        return function (xs) {
            return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(peek(i)(xs))(function (v) {
                if (v instanceof Data_Maybe.Just) {
                    return $foreign.poke(i)(f(v.value0))(xs);
                };
                if (v instanceof Data_Maybe.Nothing) {
                    return Control_Applicative.pure(Control_Monad_ST_Internal.applicativeST)(false);
                };
                throw new Error("Failed pattern match at Data.Array.ST line 147, column 3 - line 149, column 26: " + [ v.constructor.name ]);
            });
        };
    };
};
var freeze = $foreign.copyImpl;
module.exports = {
    withArray: withArray,
    peek: peek,
    push: push,
    modify: modify,
    sort: sort,
    sortBy: sortBy,
    sortWith: sortWith,
    freeze: freeze,
    thaw: thaw,
    unsafeFreeze: unsafeFreeze,
    unsafeThaw: unsafeThaw,
    empty: $foreign.empty,
    poke: $foreign.poke,
    pushAll: $foreign.pushAll,
    splice: $foreign.splice,
    toAssocArray: $foreign.toAssocArray
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Control.Monad.ST.Internal/index.js":38,"../Control.Monad.ST/index.js":40,"../Control.Semigroupoid/index.js":51,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Prelude/index.js":195,"../Unsafe.Coerce/index.js":202,"./foreign.js":56}],58:[function(require,module,exports){
"use strict";

// module Data.ArrayBuffer.ArrayBuffer

exports.create = function(s) {
  return function () {
    return new ArrayBuffer(s);
  };
};

exports.byteLength = function(a) {
  return a.byteLength;
};

exports.sliceImpl = function(s, e, a) {
  return function () {
    return a.slice(s, e);
  };
};

exports.fromArray = function(s) {
  return (new Uint8Array(s)).buffer;
};

exports.fromIntArray = function(s) {
  return (new Uint8Array(s)).buffer;
};

exports.fromString = function(s) {
  var buf = new ArrayBuffer(s.length*2);
  var bufView = new Uint16Array(buf);
  for (var i=0, strLen=s.length; i<strLen; i++) {
    bufView[i] = s.charCodeAt(i);
  }
 return buf;
};

exports.decodeToStringImpl = function(just, nothing, buffer) {
  try {
    return just(String.fromCharCode.apply(null, new Uint16Array(buffer)));
  }
  catch (e) {
    return nothing;
  }
};

},{}],59:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_ArrayBuffer_Types = require("../Data.ArrayBuffer.Types/index.js");
var Data_Function_Uncurried = require("../Data.Function.Uncurried/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Effect = require("../Effect/index.js");
var slice = Data_Function_Uncurried.runFn3($foreign.sliceImpl);
var decodeToString = Data_Function_Uncurried.runFn3($foreign.decodeToStringImpl)(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
module.exports = {
    slice: slice,
    decodeToString: decodeToString,
    create: $foreign.create,
    byteLength: $foreign.byteLength,
    fromArray: $foreign.fromArray,
    fromIntArray: $foreign.fromIntArray,
    fromString: $foreign.fromString
};

},{"../Data.ArrayBuffer.Types/index.js":64,"../Data.Function.Uncurried/index.js":94,"../Data.Maybe/index.js":112,"../Effect/index.js":185,"./foreign.js":58}],60:[function(require,module,exports){
"use strict";

// module Data.ArrayBuffer.DataView


exports.whole = function(b) {
  return new DataView(b);
}

exports.sliceImpl = function(just, nothing, s, l, b) {
  return ((s + l)>>>0) <= b.byteLength ? just(new DataView(b, s, l)) : nothing;
}

exports.buffer = function(v) {
  return v.buffer;
}

exports.byteOffset = function(v) {
  return v.byteOffset;
}

exports.byteLength = function(v) {
  return v.byteLength;
}

exports.getterImpl = function(just, nothing, s, l, e, v, o) {
  return function() {
    return ((o + l)>>>0) <= v.byteLength? just(v[s].call(v,o,e)) : nothing;
  };
}

exports.setter = function(s) {
  return function(e) {
    return function(v) {
      var f = v[s];
      return function(n) {
        return function(o) {
            return function() {
            f.call(v,o,n,e);
          };
        };
      };
    };
  };
}

},{}],61:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_ArrayBuffer_Types = require("../Data.ArrayBuffer.Types/index.js");
var Data_Function_Uncurried = require("../Data.Function.Uncurried/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_UInt = require("../Data.UInt/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var slice = Data_Function_Uncurried.runFn5($foreign.sliceImpl)(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var setUint8 = $foreign.setter("setUint8")(false);
var setUint32le = $foreign.setter("setUint32")(true);
var setUint32be = $foreign.setter("setUint32")(false);
var setUint16le = $foreign.setter("setUint16")(true);
var setUint16be = $foreign.setter("setUint16")(false);
var setInt8 = $foreign.setter("setInt8")(false);
var setInt32le = $foreign.setter("setInt32")(true);
var setInt32be = $foreign.setter("setInt32")(false);
var setInt16le = $foreign.setter("setInt16")(true);
var setInt16be = $foreign.setter("setInt16")(false);
var setFloat64le = $foreign.setter("setFloat64")(true);
var setFloat64be = $foreign.setter("setFloat64")(false);
var setFloat32le = $foreign.setter("setFloat32")(true);
var setFloat32be = $foreign.setter("setFloat32")(false);
var getter = Data_Function_Uncurried.runFn7($foreign.getterImpl)(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var getUint8 = getter("getUint8")(1)(false);
var getUint32le = getter("getUint32")(4)(true);
var getUint32be = getter("getUint32")(4)(false);
var getUint16le = getter("getUint16")(2)(true);
var getUint16be = getter("getUint16")(2)(false);
var getInt8 = getter("getInt8")(1)(false);
var getInt32le = getter("getInt32")(4)(true);
var getInt32be = getter("getInt32")(4)(false);
var getInt16le = getter("getInt16")(2)(true);
var getInt16be = getter("getInt16")(2)(false);
var getFloat64le = getter("getFloat64")(8)(true);
var getFloat64be = getter("getFloat64")(8)(false);
var getFloat32le = getter("getFloat32")(4)(true);
var getFloat32be = getter("getFloat32")(4)(false);
module.exports = {
    slice: slice,
    getInt8: getInt8,
    getInt16be: getInt16be,
    getInt32be: getInt32be,
    getUint8: getUint8,
    getUint16be: getUint16be,
    getUint32be: getUint32be,
    getFloat32be: getFloat32be,
    getFloat64be: getFloat64be,
    getInt16le: getInt16le,
    getInt32le: getInt32le,
    getUint16le: getUint16le,
    getUint32le: getUint32le,
    getFloat32le: getFloat32le,
    getFloat64le: getFloat64le,
    setInt8: setInt8,
    setInt16be: setInt16be,
    setInt32be: setInt32be,
    setUint8: setUint8,
    setUint16be: setUint16be,
    setUint32be: setUint32be,
    setFloat32be: setFloat32be,
    setFloat64be: setFloat64be,
    setInt16le: setInt16le,
    setInt32le: setInt32le,
    setUint16le: setUint16le,
    setUint32le: setUint32le,
    setFloat32le: setFloat32le,
    setFloat64le: setFloat64le,
    whole: $foreign.whole,
    buffer: $foreign.buffer,
    byteOffset: $foreign.byteOffset,
    byteLength: $foreign.byteLength
};

},{"../Data.ArrayBuffer.Types/index.js":64,"../Data.Function.Uncurried/index.js":94,"../Data.Maybe/index.js":112,"../Data.UInt/index.js":162,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":60}],62:[function(require,module,exports){
"use strict";

// module Data.ArrayBuffer.Typed

exports.asInt8Array = function(v) {
  return new Int8Array(v.buffer, v.byteOffset, v.byteLength);
}

exports.asInt16Array = function(v) {
  return new Int16Array(v.buffer, v.byteOffset, v.byteLength >>> 1);
}

exports.asInt32Array = function(v) {
  return new Int32Array(v.buffer, v.byteOffset, v.byteLength >>> 2);
}

exports.asUint8Array = function(v) {
  return new Uint8Array(v.buffer, v.byteOffset, v.byteLength);
}

exports.asUint16Array = function(v) {
  return new Uint16Array(v.buffer, v.byteOffset, v.byteLength >>> 1);
}

exports.asUint32Array = function(v) {
  return new Uint32Array(v.buffer, v.byteOffset, v.byteLength >>> 2);
}

exports.asUint8ClampedArray = function(v) {
  return new Uint8ClampedArray(v.buffer, v.byteOffset, v.byteLength);
}

exports.asFloat32Array = function(v) {
  return new Float32Array(v.buffer, v.byteOffset, v.byteLength >>> 2);
}

exports.asFloat64Array = function(v) {
  return new Float64Array(v.buffer, v.byteOffset, v.byteLength >>> 3);
}

exports.dataView = function(a) {
  return a;
}

exports.setImpl = function(ra, off, a) {
  return function() {
    a.set(ra, off);
  };
}

exports.unsafeAtImpl = function(a, i) {
  return function() {
   return a[i];
  };
}

exports.hasIndexImpl = function(a, i) {
  return i in a;
}

exports.toArray = function(a) {
  var l = a.length;
  var ret = new Array(l);
  for (var i = 0; i < l; i++)
    ret[i] = a[i];
  return ret;
}

exports.toIntArray = function(a) {
  var l = a.length;
  var ret = new Array(l);
  for (var i = 0; i < l; i++)
    ret[i] = a[i] | 0;
  return ret;
}

},{}],63:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Data_ArrayBuffer_Types = require("../Data.ArrayBuffer.Types/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Function_Uncurried = require("../Data.Function.Uncurried/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var unsafeAt = Data_Function_Uncurried.runFn2($foreign.unsafeAtImpl);
var set = Data_Function_Uncurried.runFn3($foreign.setImpl);
var hasIndex = Data_Function_Uncurried.runFn2($foreign.hasIndexImpl);
var at = function (a) {
    return function (n) {
        var $1 = hasIndex(a)(n);
        if ($1) {
            return function __do() {
                var v = unsafeAt(a)(n)();
                return new Data_Maybe.Just(v);
            };
        };
        return Control_Applicative.pure(Effect.applicativeEffect)(Data_Maybe.Nothing.value);
    };
};
module.exports = {
    set: set,
    unsafeAt: unsafeAt,
    hasIndex: hasIndex,
    at: at,
    asInt8Array: $foreign.asInt8Array,
    asInt16Array: $foreign.asInt16Array,
    asInt32Array: $foreign.asInt32Array,
    asUint8Array: $foreign.asUint8Array,
    asUint16Array: $foreign.asUint16Array,
    asUint32Array: $foreign.asUint32Array,
    asUint8ClampedArray: $foreign.asUint8ClampedArray,
    asFloat32Array: $foreign.asFloat32Array,
    asFloat64Array: $foreign.asFloat64Array,
    dataView: $foreign.dataView,
    toArray: $foreign.toArray,
    toIntArray: $foreign.toIntArray
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Data.ArrayBuffer.Types/index.js":64,"../Data.Function.Uncurried/index.js":94,"../Data.Function/index.js":95,"../Data.Maybe/index.js":112,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":62}],64:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
module.exports = {};

},{}],65:[function(require,module,exports){
"use strict";

//------------------------------------------------------------------------------
// Array creation --------------------------------------------------------------
//------------------------------------------------------------------------------

exports.range = function (start) {
  return function (end) {
    var step = start > end ? -1 : 1;
    var result = new Array(step * (end - start) + 1);
    var i = start, n = 0;
    while (i !== end) {
      result[n++] = i;
      i += step;
    }
    result[n] = i;
    return result;
  };
};

var replicate = function (count) {
  return function (value) {
    if (count < 1) {
      return [];
    }
    var result = new Array(count);
    return result.fill(value);
  };
};

var replicatePolyfill = function (count) {
  return function (value) {
    var result = [];
    var n = 0;
    for (var i = 0; i < count; i++) {
      result[n++] = value;
    }
    return result;
  };
};

// In browsers that have Array.prototype.fill we use it, as it's faster.
exports.replicate = typeof Array.prototype.fill === "function" ? replicate : replicatePolyfill;

exports.fromFoldableImpl = (function () {
  function Cons(head, tail) {
    this.head = head;
    this.tail = tail;
  }
  var emptyList = {};

  function curryCons(head) {
    return function (tail) {
      return new Cons(head, tail);
    };
  }

  function listToArray(list) {
    var result = [];
    var count = 0;
    var xs = list;
    while (xs !== emptyList) {
      result[count++] = xs.head;
      xs = xs.tail;
    }
    return result;
  }

  return function (foldr) {
    return function (xs) {
      return listToArray(foldr(curryCons)(emptyList)(xs));
    };
  };
})();

//------------------------------------------------------------------------------
// Array size ------------------------------------------------------------------
//------------------------------------------------------------------------------

exports.length = function (xs) {
  return xs.length;
};

//------------------------------------------------------------------------------
// Extending arrays ------------------------------------------------------------
//------------------------------------------------------------------------------

exports.cons = function (e) {
  return function (l) {
    return [e].concat(l);
  };
};

exports.snoc = function (l) {
  return function (e) {
    var l1 = l.slice();
    l1.push(e);
    return l1;
  };
};

//------------------------------------------------------------------------------
// Non-indexed reads -----------------------------------------------------------
//------------------------------------------------------------------------------

exports["uncons'"] = function (empty) {
  return function (next) {
    return function (xs) {
      return xs.length === 0 ? empty({}) : next(xs[0])(xs.slice(1));
    };
  };
};

//------------------------------------------------------------------------------
// Indexed operations ----------------------------------------------------------
//------------------------------------------------------------------------------

exports.indexImpl = function (just) {
  return function (nothing) {
    return function (xs) {
      return function (i) {
        return i < 0 || i >= xs.length ? nothing :  just(xs[i]);
      };
    };
  };
};

exports.findIndexImpl = function (just) {
  return function (nothing) {
    return function (f) {
      return function (xs) {
        for (var i = 0, l = xs.length; i < l; i++) {
          if (f(xs[i])) return just(i);
        }
        return nothing;
      };
    };
  };
};

exports.findLastIndexImpl = function (just) {
  return function (nothing) {
    return function (f) {
      return function (xs) {
        for (var i = xs.length - 1; i >= 0; i--) {
          if (f(xs[i])) return just(i);
        }
        return nothing;
      };
    };
  };
};

exports._insertAt = function (just) {
  return function (nothing) {
    return function (i) {
      return function (a) {
        return function (l) {
          if (i < 0 || i > l.length) return nothing;
          var l1 = l.slice();
          l1.splice(i, 0, a);
          return just(l1);
        };
      };
    };
  };
};

exports._deleteAt = function (just) {
  return function (nothing) {
    return function (i) {
      return function (l) {
        if (i < 0 || i >= l.length) return nothing;
        var l1 = l.slice();
        l1.splice(i, 1);
        return just(l1);
      };
    };
  };
};

exports._updateAt = function (just) {
  return function (nothing) {
    return function (i) {
      return function (a) {
        return function (l) {
          if (i < 0 || i >= l.length) return nothing;
          var l1 = l.slice();
          l1[i] = a;
          return just(l1);
        };
      };
    };
  };
};

//------------------------------------------------------------------------------
// Transformations -------------------------------------------------------------
//------------------------------------------------------------------------------

exports.reverse = function (l) {
  return l.slice().reverse();
};

exports.concat = function (xss) {
  if (xss.length <= 10000) {
    // This method is faster, but it crashes on big arrays.
    // So we use it when can and fallback to simple variant otherwise.
    return Array.prototype.concat.apply([], xss);
  }

  var result = [];
  for (var i = 0, l = xss.length; i < l; i++) {
    var xs = xss[i];
    for (var j = 0, m = xs.length; j < m; j++) {
      result.push(xs[j]);
    }
  }
  return result;
};

exports.filter = function (f) {
  return function (xs) {
    return xs.filter(f);
  };
};

exports.partition = function (f) {
  return function (xs) {
    var yes = [];
    var no  = [];
    for (var i = 0; i < xs.length; i++) {
      var x = xs[i];
      if (f(x))
        yes.push(x);
      else
        no.push(x);
    }
    return { yes: yes, no: no };
  };
};

//------------------------------------------------------------------------------
// Sorting ---------------------------------------------------------------------
//------------------------------------------------------------------------------

exports.sortImpl = function (f) {
  return function (l) {
    return l.slice().sort(function (x, y) {
      return f(x)(y);
    });
  };
};

//------------------------------------------------------------------------------
// Subarrays -------------------------------------------------------------------
//------------------------------------------------------------------------------

exports.slice = function (s) {
  return function (e) {
    return function (l) {
      return l.slice(s, e);
    };
  };
};

exports.take = function (n) {
  return function (l) {
    return n < 1 ? [] : l.slice(0, n);
  };
};

exports.drop = function (n) {
  return function (l) {
    return n < 1 ? l : l.slice(n);
  };
};

//------------------------------------------------------------------------------
// Zipping ---------------------------------------------------------------------
//------------------------------------------------------------------------------

exports.zipWith = function (f) {
  return function (xs) {
    return function (ys) {
      var l = xs.length < ys.length ? xs.length : ys.length;
      var result = new Array(l);
      for (var i = 0; i < l; i++) {
        result[i] = f(xs[i])(ys[i]);
      }
      return result;
    };
  };
};

//------------------------------------------------------------------------------
// Partial ---------------------------------------------------------------------
//------------------------------------------------------------------------------

exports.unsafeIndexImpl = function (xs) {
  return function (n) {
    return xs[n];
  };
};

},{}],66:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Lazy = require("../Control.Lazy/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Control_Monad_ST = require("../Control.Monad.ST/index.js");
var Control_Monad_ST_Internal = require("../Control.Monad.ST.Internal/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Array_NonEmpty_Internal = require("../Data.Array.NonEmpty.Internal/index.js");
var Data_Array_ST = require("../Data.Array.ST/index.js");
var Data_Array_ST_Iterator = require("../Data.Array.ST.Iterator/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unfoldable = require("../Data.Unfoldable/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var Unsafe_Coerce = require("../Unsafe.Coerce/index.js");
var zipWithA = function (dictApplicative) {
    return function (f) {
        return function (xs) {
            return function (ys) {
                return Data_Traversable.sequence(Data_Traversable.traversableArray)(dictApplicative)($foreign.zipWith(f)(xs)(ys));
            };
        };
    };
};
var zip = $foreign.zipWith(Data_Tuple.Tuple.create);
var updateAtIndices = function (dictFoldable) {
    return function (us) {
        return function (xs) {
            return Control_Monad_ST_Internal.run(Data_Array_ST.withArray(function (res) {
                return Data_Foldable.traverse_(Control_Monad_ST_Internal.applicativeST)(dictFoldable)(function (v) {
                    return Data_Array_ST.poke(v.value0)(v.value1)(res);
                })(us);
            })(xs));
        };
    };
};
var updateAt = $foreign._updateAt(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var unsafeIndex = function (dictPartial) {
    return $foreign.unsafeIndexImpl;
};
var uncons = $foreign["uncons'"](Data_Function["const"](Data_Maybe.Nothing.value))(function (x) {
    return function (xs) {
        return new Data_Maybe.Just({
            head: x,
            tail: xs
        });
    };
});
var toUnfoldable = function (dictUnfoldable) {
    return function (xs) {
        var len = $foreign.length(xs);
        var f = function (i) {
            if (i < len) {
                return new Data_Maybe.Just(new Data_Tuple.Tuple(unsafeIndex()(xs)(i), i + 1 | 0));
            };
            if (Data_Boolean.otherwise) {
                return Data_Maybe.Nothing.value;
            };
            throw new Error("Failed pattern match at Data.Array line 143, column 3 - line 145, column 26: " + [ i.constructor.name ]);
        };
        return Data_Unfoldable.unfoldr(dictUnfoldable)(f)(0);
    };
};
var takeEnd = function (n) {
    return function (xs) {
        return $foreign.drop($foreign.length(xs) - n | 0)(xs);
    };
};
var tail = $foreign["uncons'"](Data_Function["const"](Data_Maybe.Nothing.value))(function (v) {
    return function (xs) {
        return new Data_Maybe.Just(xs);
    };
});
var sortBy = function (comp) {
    return function (xs) {
        var comp$prime = function (x) {
            return function (y) {
                var v = comp(x)(y);
                if (v instanceof Data_Ordering.GT) {
                    return 1;
                };
                if (v instanceof Data_Ordering.EQ) {
                    return 0;
                };
                if (v instanceof Data_Ordering.LT) {
                    return -1 | 0;
                };
                throw new Error("Failed pattern match at Data.Array line 702, column 15 - line 707, column 1: " + [ v.constructor.name ]);
            };
        };
        return $foreign.sortImpl(comp$prime)(xs);
    };
};
var sortWith = function (dictOrd) {
    return function (f) {
        return sortBy(Data_Ord.comparing(dictOrd)(f));
    };
};
var sort = function (dictOrd) {
    return function (xs) {
        return sortBy(Data_Ord.compare(dictOrd))(xs);
    };
};
var singleton = function (a) {
    return [ a ];
};
var $$null = function (xs) {
    return $foreign.length(xs) === 0;
};
var nubByEq = function (eq) {
    return function (xs) {
        var v = uncons(xs);
        if (v instanceof Data_Maybe.Just) {
            return $foreign.cons(v.value0.head)(nubByEq(eq)($foreign.filter(function (y) {
                return !eq(v.value0.head)(y);
            })(v.value0.tail)));
        };
        if (v instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Data.Array line 929, column 3 - line 931, column 18: " + [ v.constructor.name ]);
    };
};
var nubEq = function (dictEq) {
    return nubByEq(Data_Eq.eq(dictEq));
};
var modifyAtIndices = function (dictFoldable) {
    return function (is) {
        return function (f) {
            return function (xs) {
                return Control_Monad_ST_Internal.run(Data_Array_ST.withArray(function (res) {
                    return Data_Foldable.traverse_(Control_Monad_ST_Internal.applicativeST)(dictFoldable)(function (i) {
                        return Data_Array_ST.modify(i)(f)(res);
                    })(is);
                })(xs));
            };
        };
    };
};
var mapWithIndex = function (f) {
    return function (xs) {
        return $foreign.zipWith(f)($foreign.range(0)($foreign.length(xs) - 1 | 0))(xs);
    };
};
var some = function (dictAlternative) {
    return function (dictLazy) {
        return function (v) {
            return Control_Apply.apply((dictAlternative.Applicative0()).Apply0())(Data_Functor.map(((dictAlternative.Plus1()).Alt0()).Functor0())($foreign.cons)(v))(Control_Lazy.defer(dictLazy)(function (v1) {
                return many(dictAlternative)(dictLazy)(v);
            }));
        };
    };
};
var many = function (dictAlternative) {
    return function (dictLazy) {
        return function (v) {
            return Control_Alt.alt((dictAlternative.Plus1()).Alt0())(some(dictAlternative)(dictLazy)(v))(Control_Applicative.pure(dictAlternative.Applicative0())([  ]));
        };
    };
};
var insertAt = $foreign._insertAt(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var init = function (xs) {
    if ($$null(xs)) {
        return Data_Maybe.Nothing.value;
    };
    if (Data_Boolean.otherwise) {
        return new Data_Maybe.Just($foreign.slice(0)($foreign.length(xs) - 1 | 0)(xs));
    };
    throw new Error("Failed pattern match at Data.Array line 323, column 1 - line 323, column 45: " + [ xs.constructor.name ]);
};
var index = $foreign.indexImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var last = function (xs) {
    return index(xs)($foreign.length(xs) - 1 | 0);
};
var unsnoc = function (xs) {
    return Control_Apply.apply(Data_Maybe.applyMaybe)(Data_Functor.map(Data_Maybe.functorMaybe)(function (v) {
        return function (v1) {
            return {
                init: v,
                last: v1
            };
        };
    })(init(xs)))(last(xs));
};
var modifyAt = function (i) {
    return function (f) {
        return function (xs) {
            var go = function (x) {
                return updateAt(i)(f(x))(xs);
            };
            return Data_Maybe.maybe(Data_Maybe.Nothing.value)(go)(index(xs)(i));
        };
    };
};
var span = function (p) {
    return function (arr) {
        var go = function ($copy_i) {
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(i) {
                var v = index(arr)(i);
                if (v instanceof Data_Maybe.Just) {
                    var $75 = p(v.value0);
                    if ($75) {
                        $copy_i = i + 1 | 0;
                        return;
                    };
                    $tco_done = true;
                    return new Data_Maybe.Just(i);
                };
                if (v instanceof Data_Maybe.Nothing) {
                    $tco_done = true;
                    return Data_Maybe.Nothing.value;
                };
                throw new Error("Failed pattern match at Data.Array line 834, column 5 - line 836, column 25: " + [ v.constructor.name ]);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($copy_i);
            };
            return $tco_result;
        };
        var breakIndex = go(0);
        if (breakIndex instanceof Data_Maybe.Just && breakIndex.value0 === 0) {
            return {
                init: [  ],
                rest: arr
            };
        };
        if (breakIndex instanceof Data_Maybe.Just) {
            return {
                init: $foreign.slice(0)(breakIndex.value0)(arr),
                rest: $foreign.slice(breakIndex.value0)($foreign.length(arr))(arr)
            };
        };
        if (breakIndex instanceof Data_Maybe.Nothing) {
            return {
                init: arr,
                rest: [  ]
            };
        };
        throw new Error("Failed pattern match at Data.Array line 821, column 3 - line 827, column 30: " + [ breakIndex.constructor.name ]);
    };
};
var takeWhile = function (p) {
    return function (xs) {
        return (span(p)(xs)).init;
    };
};
var unzip = function (xs) {
    return Control_Monad_ST_Internal.run(Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.empty)(function (v) {
        return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.empty)(function (v1) {
            return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST_Iterator.iterator(function (v2) {
                return index(xs)(v2);
            }))(function (v2) {
                return Control_Bind.discard(Control_Bind.discardUnit)(Control_Monad_ST_Internal.bindST)(Data_Array_ST_Iterator.iterate(v2)(function (v3) {
                    return Control_Bind.discard(Control_Bind.discardUnit)(Control_Monad_ST_Internal.bindST)(Data_Functor["void"](Control_Monad_ST_Internal.functorST)(Data_Array_ST.push(v3.value0)(v)))(function () {
                        return Data_Functor["void"](Control_Monad_ST_Internal.functorST)(Data_Array_ST.push(v3.value1)(v1));
                    });
                }))(function () {
                    return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.unsafeFreeze(v))(function (v3) {
                        return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.unsafeFreeze(v1))(function (v4) {
                            return Control_Applicative.pure(Control_Monad_ST_Internal.applicativeST)(new Data_Tuple.Tuple(v3, v4));
                        });
                    });
                });
            });
        });
    }));
};
var head = function (xs) {
    return index(xs)(0);
};
var nubBy = function (comp) {
    return function (xs) {
        var indexedAndSorted = sortBy(function (x) {
            return function (y) {
                return comp(Data_Tuple.snd(x))(Data_Tuple.snd(y));
            };
        })(mapWithIndex(Data_Tuple.Tuple.create)(xs));
        var v = head(indexedAndSorted);
        if (v instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        if (v instanceof Data_Maybe.Just) {
            return Data_Functor.map(Data_Functor.functorArray)(Data_Tuple.snd)(sortWith(Data_Ord.ordInt)(Data_Tuple.fst)(Control_Monad_ST_Internal.run(Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.unsafeThaw(singleton(v.value0)))(function (v1) {
                return Control_Bind.discard(Control_Bind.discardUnit)(Control_Monad_ST_Internal.bindST)(Control_Monad_ST_Internal.foreach(indexedAndSorted)(function (v2) {
                    return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Functor.map(Control_Monad_ST_Internal.functorST)(function ($111) {
                        return Data_Tuple.snd((function ($112) {
                            return Data_Maybe.fromJust()(last($112));
                        })($111));
                    })(Data_Array_ST.unsafeFreeze(v1)))(function (v3) {
                        return Control_Applicative.when(Control_Monad_ST_Internal.applicativeST)(Data_Eq.notEq(Data_Ordering.eqOrdering)(comp(v3)(v2.value1))(Data_Ordering.EQ.value))(Data_Functor["void"](Control_Monad_ST_Internal.functorST)(Data_Array_ST.push(v2)(v1)));
                    });
                }))(function () {
                    return Data_Array_ST.unsafeFreeze(v1);
                });
            }))));
        };
        throw new Error("Failed pattern match at Data.Array line 903, column 17 - line 911, column 29: " + [ v.constructor.name ]);
    };
};
var nub = function (dictOrd) {
    return nubBy(Data_Ord.compare(dictOrd));
};
var groupBy = function (op) {
    return function (xs) {
        return Control_Monad_ST_Internal.run(Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.empty)(function (v) {
            return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST_Iterator.iterator(function (v1) {
                return index(xs)(v1);
            }))(function (v1) {
                return Control_Bind.discard(Control_Bind.discardUnit)(Control_Monad_ST_Internal.bindST)(Data_Array_ST_Iterator.iterate(v1)(function (x) {
                    return Data_Functor["void"](Control_Monad_ST_Internal.functorST)(Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.empty)(function (v2) {
                        return Control_Bind.discard(Control_Bind.discardUnit)(Control_Monad_ST_Internal.bindST)(Data_Array_ST_Iterator.pushWhile(op(x))(v1)(v2))(function () {
                            return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.push(x)(v2))(function (v3) {
                                return Control_Bind.bind(Control_Monad_ST_Internal.bindST)(Data_Array_ST.unsafeFreeze(v2))(function (v4) {
                                    return Data_Array_ST.push(v4)(v);
                                });
                            });
                        });
                    }));
                }))(function () {
                    return Data_Array_ST.unsafeFreeze(v);
                });
            });
        }));
    };
};
var group = function (dictEq) {
    return function (xs) {
        return groupBy(Data_Eq.eq(dictEq))(xs);
    };
};
var group$prime = function (dictOrd) {
    return function ($113) {
        return group(dictOrd.Eq0())(sort(dictOrd)($113));
    };
};
var fromFoldable = function (dictFoldable) {
    return $foreign.fromFoldableImpl(Data_Foldable.foldr(dictFoldable));
};
var foldRecM = function (dictMonadRec) {
    return function (f) {
        return function (a) {
            return function (array) {
                var go = function (res) {
                    return function (i) {
                        if (i >= $foreign.length(array)) {
                            return Control_Applicative.pure((dictMonadRec.Monad0()).Applicative0())(new Control_Monad_Rec_Class.Done(res));
                        };
                        if (Data_Boolean.otherwise) {
                            return Control_Bind.bind((dictMonadRec.Monad0()).Bind1())(f(res)(unsafeIndex()(array)(i)))(function (v) {
                                return Control_Applicative.pure((dictMonadRec.Monad0()).Applicative0())(new Control_Monad_Rec_Class.Loop({
                                    a: v,
                                    b: i + 1 | 0
                                }));
                            });
                        };
                        throw new Error("Failed pattern match at Data.Array line 1098, column 3 - line 1102, column 42: " + [ res.constructor.name, i.constructor.name ]);
                    };
                };
                return Control_Monad_Rec_Class.tailRecM2(dictMonadRec)(go)(a)(0);
            };
        };
    };
};
var foldM = function (dictMonad) {
    return function (f) {
        return function (a) {
            return $foreign["uncons'"](function (v) {
                return Control_Applicative.pure(dictMonad.Applicative0())(a);
            })(function (b) {
                return function (bs) {
                    return Control_Bind.bind(dictMonad.Bind1())(f(a)(b))(function (a$prime) {
                        return foldM(dictMonad)(f)(a$prime)(bs);
                    });
                };
            });
        };
    };
};
var findLastIndex = $foreign.findLastIndexImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var insertBy = function (cmp) {
    return function (x) {
        return function (ys) {
            var i = Data_Maybe.maybe(0)(function (v) {
                return v + 1 | 0;
            })(findLastIndex(function (y) {
                return Data_Eq.eq(Data_Ordering.eqOrdering)(cmp(x)(y))(Data_Ordering.GT.value);
            })(ys));
            return Data_Maybe.fromJust()(insertAt(i)(x)(ys));
        };
    };
};
var insert = function (dictOrd) {
    return insertBy(Data_Ord.compare(dictOrd));
};
var findIndex = $foreign.findIndexImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var intersectBy = function (eq) {
    return function (xs) {
        return function (ys) {
            return $foreign.filter(function (x) {
                return Data_Maybe.isJust(findIndex(eq(x))(ys));
            })(xs);
        };
    };
};
var intersect = function (dictEq) {
    return intersectBy(Data_Eq.eq(dictEq));
};
var elemLastIndex = function (dictEq) {
    return function (x) {
        return findLastIndex(function (v) {
            return Data_Eq.eq(dictEq)(v)(x);
        });
    };
};
var elemIndex = function (dictEq) {
    return function (x) {
        return findIndex(function (v) {
            return Data_Eq.eq(dictEq)(v)(x);
        });
    };
};
var dropWhile = function (p) {
    return function (xs) {
        return (span(p)(xs)).rest;
    };
};
var dropEnd = function (n) {
    return function (xs) {
        return $foreign.take($foreign.length(xs) - n | 0)(xs);
    };
};
var deleteAt = $foreign._deleteAt(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var deleteBy = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2.length === 0) {
                return [  ];
            };
            return Data_Maybe.maybe(v2)(function (i) {
                return Data_Maybe.fromJust()(deleteAt(i)(v2));
            })(findIndex(v(v1))(v2));
        };
    };
};
var unionBy = function (eq) {
    return function (xs) {
        return function (ys) {
            return Data_Semigroup.append(Data_Semigroup.semigroupArray)(xs)(Data_Foldable.foldl(Data_Foldable.foldableArray)(Data_Function.flip(deleteBy(eq)))(nubByEq(eq)(ys))(xs));
        };
    };
};
var union = function (dictEq) {
    return unionBy(Data_Eq.eq(dictEq));
};
var $$delete = function (dictEq) {
    return deleteBy(Data_Eq.eq(dictEq));
};
var difference = function (dictEq) {
    return Data_Foldable.foldr(Data_Foldable.foldableArray)($$delete(dictEq));
};
var concatMap = Data_Function.flip(Control_Bind.bind(Control_Bind.bindArray));
var mapMaybe = function (f) {
    return concatMap(function ($114) {
        return Data_Maybe.maybe([  ])(singleton)(f($114));
    });
};
var filterA = function (dictApplicative) {
    return function (p) {
        return function ($115) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(mapMaybe(function (v) {
                if (v.value1) {
                    return new Data_Maybe.Just(v.value0);
                };
                return Data_Maybe.Nothing.value;
            }))(Data_Traversable.traverse(Data_Traversable.traversableArray)(dictApplicative)(function (x) {
                return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Tuple.Tuple.create(x))(p(x));
            })($115));
        };
    };
};
var catMaybes = mapMaybe(Control_Category.identity(Control_Category.categoryFn));
var alterAt = function (i) {
    return function (f) {
        return function (xs) {
            var go = function (x) {
                var v = f(x);
                if (v instanceof Data_Maybe.Nothing) {
                    return deleteAt(i)(xs);
                };
                if (v instanceof Data_Maybe.Just) {
                    return updateAt(i)(v.value0)(xs);
                };
                throw new Error("Failed pattern match at Data.Array line 544, column 10 - line 546, column 32: " + [ v.constructor.name ]);
            };
            return Data_Maybe.maybe(Data_Maybe.Nothing.value)(go)(index(xs)(i));
        };
    };
};
module.exports = {
    fromFoldable: fromFoldable,
    toUnfoldable: toUnfoldable,
    singleton: singleton,
    some: some,
    many: many,
    "null": $$null,
    insert: insert,
    insertBy: insertBy,
    head: head,
    last: last,
    tail: tail,
    init: init,
    uncons: uncons,
    unsnoc: unsnoc,
    index: index,
    elemIndex: elemIndex,
    elemLastIndex: elemLastIndex,
    findIndex: findIndex,
    findLastIndex: findLastIndex,
    insertAt: insertAt,
    deleteAt: deleteAt,
    updateAt: updateAt,
    updateAtIndices: updateAtIndices,
    modifyAt: modifyAt,
    modifyAtIndices: modifyAtIndices,
    alterAt: alterAt,
    concatMap: concatMap,
    filterA: filterA,
    mapMaybe: mapMaybe,
    catMaybes: catMaybes,
    mapWithIndex: mapWithIndex,
    sort: sort,
    sortBy: sortBy,
    sortWith: sortWith,
    takeEnd: takeEnd,
    takeWhile: takeWhile,
    dropEnd: dropEnd,
    dropWhile: dropWhile,
    span: span,
    group: group,
    "group'": group$prime,
    groupBy: groupBy,
    nub: nub,
    nubEq: nubEq,
    nubBy: nubBy,
    nubByEq: nubByEq,
    union: union,
    unionBy: unionBy,
    "delete": $$delete,
    deleteBy: deleteBy,
    difference: difference,
    intersect: intersect,
    intersectBy: intersectBy,
    zipWithA: zipWithA,
    zip: zip,
    unzip: unzip,
    foldM: foldM,
    foldRecM: foldRecM,
    unsafeIndex: unsafeIndex,
    range: $foreign.range,
    replicate: $foreign.replicate,
    length: $foreign.length,
    cons: $foreign.cons,
    snoc: $foreign.snoc,
    reverse: $foreign.reverse,
    concat: $foreign.concat,
    filter: $foreign.filter,
    partition: $foreign.partition,
    slice: $foreign.slice,
    take: $foreign.take,
    drop: $foreign.drop,
    zipWith: $foreign.zipWith
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Category/index.js":24,"../Control.Lazy/index.js":28,"../Control.Monad.Rec.Class/index.js":36,"../Control.Monad.ST.Internal/index.js":38,"../Control.Monad.ST/index.js":40,"../Control.Semigroupoid/index.js":51,"../Data.Array.NonEmpty.Internal/index.js":53,"../Data.Array.ST.Iterator/index.js":55,"../Data.Array.ST/index.js":57,"../Data.Boolean/index.js":76,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Traversable/index.js":159,"../Data.Tuple/index.js":160,"../Data.Unfoldable/index.js":166,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195,"../Unsafe.Coerce/index.js":202,"./foreign.js":65}],67:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Bifunctor_Clown = require("../Data.Bifunctor.Clown/index.js");
var Data_Bifunctor_Flip = require("../Data.Bifunctor.Flip/index.js");
var Data_Bifunctor_Joker = require("../Data.Bifunctor.Joker/index.js");
var Data_Bifunctor_Product = require("../Data.Bifunctor.Product/index.js");
var Data_Bifunctor_Wrap = require("../Data.Bifunctor.Wrap/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Endo = require("../Data.Monoid.Endo/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var Bifoldable = function (bifoldMap, bifoldl, bifoldr) {
    this.bifoldMap = bifoldMap;
    this.bifoldl = bifoldl;
    this.bifoldr = bifoldr;
};
var bifoldr = function (dict) {
    return dict.bifoldr;
};
var bitraverse_ = function (dictBifoldable) {
    return function (dictApplicative) {
        return function (f) {
            return function (g) {
                return bifoldr(dictBifoldable)(function ($97) {
                    return Control_Apply.applySecond(dictApplicative.Apply0())(f($97));
                })(function ($98) {
                    return Control_Apply.applySecond(dictApplicative.Apply0())(g($98));
                })(Control_Applicative.pure(dictApplicative)(Data_Unit.unit));
            };
        };
    };
};
var bifor_ = function (dictBifoldable) {
    return function (dictApplicative) {
        return function (t) {
            return function (f) {
                return function (g) {
                    return bitraverse_(dictBifoldable)(dictApplicative)(f)(g)(t);
                };
            };
        };
    };
};
var bisequence_ = function (dictBifoldable) {
    return function (dictApplicative) {
        return bitraverse_(dictBifoldable)(dictApplicative)(Control_Category.identity(Control_Category.categoryFn))(Control_Category.identity(Control_Category.categoryFn));
    };
};
var bifoldl = function (dict) {
    return dict.bifoldl;
};
var bifoldableJoker = function (dictFoldable) {
    return new Bifoldable(function (dictMonoid) {
        return function (v) {
            return function (r) {
                return function (v1) {
                    return Data_Foldable.foldMap(dictFoldable)(dictMonoid)(r)(v1);
                };
            };
        };
    }, function (v) {
        return function (r) {
            return function (u) {
                return function (v1) {
                    return Data_Foldable.foldl(dictFoldable)(r)(u)(v1);
                };
            };
        };
    }, function (v) {
        return function (r) {
            return function (u) {
                return function (v1) {
                    return Data_Foldable.foldr(dictFoldable)(r)(u)(v1);
                };
            };
        };
    });
};
var bifoldableClown = function (dictFoldable) {
    return new Bifoldable(function (dictMonoid) {
        return function (l) {
            return function (v) {
                return function (v1) {
                    return Data_Foldable.foldMap(dictFoldable)(dictMonoid)(l)(v1);
                };
            };
        };
    }, function (l) {
        return function (v) {
            return function (u) {
                return function (v1) {
                    return Data_Foldable.foldl(dictFoldable)(l)(u)(v1);
                };
            };
        };
    }, function (l) {
        return function (v) {
            return function (u) {
                return function (v1) {
                    return Data_Foldable.foldr(dictFoldable)(l)(u)(v1);
                };
            };
        };
    });
};
var bifoldMapDefaultR = function (dictBifoldable) {
    return function (dictMonoid) {
        return function (f) {
            return function (g) {
                return bifoldr(dictBifoldable)(function ($99) {
                    return Data_Semigroup.append(dictMonoid.Semigroup0())(f($99));
                })(function ($100) {
                    return Data_Semigroup.append(dictMonoid.Semigroup0())(g($100));
                })(Data_Monoid.mempty(dictMonoid));
            };
        };
    };
};
var bifoldMapDefaultL = function (dictBifoldable) {
    return function (dictMonoid) {
        return function (f) {
            return function (g) {
                return bifoldl(dictBifoldable)(function (m) {
                    return function (a) {
                        return Data_Semigroup.append(dictMonoid.Semigroup0())(m)(f(a));
                    };
                })(function (m) {
                    return function (b) {
                        return Data_Semigroup.append(dictMonoid.Semigroup0())(m)(g(b));
                    };
                })(Data_Monoid.mempty(dictMonoid));
            };
        };
    };
};
var bifoldMap = function (dict) {
    return dict.bifoldMap;
};
var bifoldableFlip = function (dictBifoldable) {
    return new Bifoldable(function (dictMonoid) {
        return function (r) {
            return function (l) {
                return function (v) {
                    return bifoldMap(dictBifoldable)(dictMonoid)(l)(r)(v);
                };
            };
        };
    }, function (r) {
        return function (l) {
            return function (u) {
                return function (v) {
                    return bifoldl(dictBifoldable)(l)(r)(u)(v);
                };
            };
        };
    }, function (r) {
        return function (l) {
            return function (u) {
                return function (v) {
                    return bifoldr(dictBifoldable)(l)(r)(u)(v);
                };
            };
        };
    });
};
var bifoldableWrap = function (dictBifoldable) {
    return new Bifoldable(function (dictMonoid) {
        return function (l) {
            return function (r) {
                return function (v) {
                    return bifoldMap(dictBifoldable)(dictMonoid)(l)(r)(v);
                };
            };
        };
    }, function (l) {
        return function (r) {
            return function (u) {
                return function (v) {
                    return bifoldl(dictBifoldable)(l)(r)(u)(v);
                };
            };
        };
    }, function (l) {
        return function (r) {
            return function (u) {
                return function (v) {
                    return bifoldr(dictBifoldable)(l)(r)(u)(v);
                };
            };
        };
    });
};
var bifoldlDefault = function (dictBifoldable) {
    return function (f) {
        return function (g) {
            return function (z) {
                return function (p) {
                    return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(Data_Newtype.unwrap(Data_Newtype.newtypeDual)(bifoldMap(dictBifoldable)(Data_Monoid_Dual.monoidDual(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn)))(function ($101) {
                        return Data_Monoid_Dual.Dual(Data_Monoid_Endo.Endo(Data_Function.flip(f)($101)));
                    })(function ($102) {
                        return Data_Monoid_Dual.Dual(Data_Monoid_Endo.Endo(Data_Function.flip(g)($102)));
                    })(p)))(z);
                };
            };
        };
    };
};
var bifoldrDefault = function (dictBifoldable) {
    return function (f) {
        return function (g) {
            return function (z) {
                return function (p) {
                    return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(bifoldMap(dictBifoldable)(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn))(function ($103) {
                        return Data_Monoid_Endo.Endo(f($103));
                    })(function ($104) {
                        return Data_Monoid_Endo.Endo(g($104));
                    })(p))(z);
                };
            };
        };
    };
};
var bifoldableProduct = function (dictBifoldable) {
    return function (dictBifoldable1) {
        return new Bifoldable(function (dictMonoid) {
            return function (l) {
                return function (r) {
                    return function (v) {
                        return Data_Semigroup.append(dictMonoid.Semigroup0())(bifoldMap(dictBifoldable)(dictMonoid)(l)(r)(v.value0))(bifoldMap(dictBifoldable1)(dictMonoid)(l)(r)(v.value1));
                    };
                };
            };
        }, function (l) {
            return function (r) {
                return function (u) {
                    return function (m) {
                        return bifoldlDefault(bifoldableProduct(dictBifoldable)(dictBifoldable1))(l)(r)(u)(m);
                    };
                };
            };
        }, function (l) {
            return function (r) {
                return function (u) {
                    return function (m) {
                        return bifoldrDefault(bifoldableProduct(dictBifoldable)(dictBifoldable1))(l)(r)(u)(m);
                    };
                };
            };
        });
    };
};
var bifold = function (dictBifoldable) {
    return function (dictMonoid) {
        return bifoldMap(dictBifoldable)(dictMonoid)(Control_Category.identity(Control_Category.categoryFn))(Control_Category.identity(Control_Category.categoryFn));
    };
};
var biany = function (dictBifoldable) {
    return function (dictBooleanAlgebra) {
        return function (p) {
            return function (q) {
                return function ($105) {
                    return Data_Newtype.unwrap(Data_Newtype.newtypeDisj)(bifoldMap(dictBifoldable)(Data_Monoid_Disj.monoidDisj(dictBooleanAlgebra.HeytingAlgebra0()))(function ($106) {
                        return Data_Monoid_Disj.Disj(p($106));
                    })(function ($107) {
                        return Data_Monoid_Disj.Disj(q($107));
                    })($105));
                };
            };
        };
    };
};
var biall = function (dictBifoldable) {
    return function (dictBooleanAlgebra) {
        return function (p) {
            return function (q) {
                return function ($108) {
                    return Data_Newtype.unwrap(Data_Newtype.newtypeConj)(bifoldMap(dictBifoldable)(Data_Monoid_Conj.monoidConj(dictBooleanAlgebra.HeytingAlgebra0()))(function ($109) {
                        return Data_Monoid_Conj.Conj(p($109));
                    })(function ($110) {
                        return Data_Monoid_Conj.Conj(q($110));
                    })($108));
                };
            };
        };
    };
};
module.exports = {
    bifoldMap: bifoldMap,
    bifoldl: bifoldl,
    bifoldr: bifoldr,
    Bifoldable: Bifoldable,
    bifoldrDefault: bifoldrDefault,
    bifoldlDefault: bifoldlDefault,
    bifoldMapDefaultR: bifoldMapDefaultR,
    bifoldMapDefaultL: bifoldMapDefaultL,
    bifold: bifold,
    bitraverse_: bitraverse_,
    bifor_: bifor_,
    bisequence_: bisequence_,
    biany: biany,
    biall: biall,
    bifoldableClown: bifoldableClown,
    bifoldableJoker: bifoldableJoker,
    bifoldableFlip: bifoldableFlip,
    bifoldableProduct: bifoldableProduct,
    bifoldableWrap: bifoldableWrap
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Control.Semigroupoid/index.js":51,"../Data.Bifunctor.Clown/index.js":68,"../Data.Bifunctor.Flip/index.js":69,"../Data.Bifunctor.Joker/index.js":70,"../Data.Bifunctor.Product/index.js":71,"../Data.Bifunctor.Wrap/index.js":72,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Endo/index.js":117,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Semigroup/index.js":137,"../Data.Unit/index.js":168,"../Prelude/index.js":195}],68:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Biapplicative = require("../Control.Biapplicative/index.js");
var Control_Biapply = require("../Control.Biapply/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Clown = function (x) {
    return x;
};
var showClown = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Clown " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var ordClown = function (dictOrd) {
    return dictOrd;
};
var newtypeClown = new Data_Newtype.Newtype(function (n) {
    return n;
}, Clown);
var functorClown = new Data_Functor.Functor(function (v) {
    return function (v1) {
        return v1;
    };
});
var eqClown = function (dictEq) {
    return dictEq;
};
var bifunctorClown = function (dictFunctor) {
    return new Data_Bifunctor.Bifunctor(function (f) {
        return function (v) {
            return function (v1) {
                return Data_Functor.map(dictFunctor)(f)(v1);
            };
        };
    });
};
var biapplyClown = function (dictApply) {
    return new Control_Biapply.Biapply(function () {
        return bifunctorClown(dictApply.Functor0());
    }, function (v) {
        return function (v1) {
            return Control_Apply.apply(dictApply)(v)(v1);
        };
    });
};
var biapplicativeClown = function (dictApplicative) {
    return new Control_Biapplicative.Biapplicative(function () {
        return biapplyClown(dictApplicative.Apply0());
    }, function (a) {
        return function (v) {
            return Control_Applicative.pure(dictApplicative)(a);
        };
    });
};
module.exports = {
    Clown: Clown,
    newtypeClown: newtypeClown,
    eqClown: eqClown,
    ordClown: ordClown,
    showClown: showClown,
    functorClown: functorClown,
    bifunctorClown: bifunctorClown,
    biapplyClown: biapplyClown,
    biapplicativeClown: biapplicativeClown
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Biapplicative/index.js":20,"../Control.Biapply/index.js":21,"../Data.Bifunctor/index.js":73,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],69:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Biapplicative = require("../Control.Biapplicative/index.js");
var Control_Biapply = require("../Control.Biapply/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Flip = function (x) {
    return x;
};
var showFlip = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Flip " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var ordFlip = function (dictOrd) {
    return dictOrd;
};
var newtypeFlip = new Data_Newtype.Newtype(function (n) {
    return n;
}, Flip);
var functorFlip = function (dictBifunctor) {
    return new Data_Functor.Functor(function (f) {
        return function (v) {
            return Data_Bifunctor.lmap(dictBifunctor)(f)(v);
        };
    });
};
var eqFlip = function (dictEq) {
    return dictEq;
};
var bifunctorFlip = function (dictBifunctor) {
    return new Data_Bifunctor.Bifunctor(function (f) {
        return function (g) {
            return function (v) {
                return Data_Bifunctor.bimap(dictBifunctor)(g)(f)(v);
            };
        };
    });
};
var biapplyFlip = function (dictBiapply) {
    return new Control_Biapply.Biapply(function () {
        return bifunctorFlip(dictBiapply.Bifunctor0());
    }, function (v) {
        return function (v1) {
            return Control_Biapply.biapply(dictBiapply)(v)(v1);
        };
    });
};
var biapplicativeFlip = function (dictBiapplicative) {
    return new Control_Biapplicative.Biapplicative(function () {
        return biapplyFlip(dictBiapplicative.Biapply0());
    }, function (a) {
        return function (b) {
            return Control_Biapplicative.bipure(dictBiapplicative)(b)(a);
        };
    });
};
module.exports = {
    Flip: Flip,
    newtypeFlip: newtypeFlip,
    eqFlip: eqFlip,
    ordFlip: ordFlip,
    showFlip: showFlip,
    functorFlip: functorFlip,
    bifunctorFlip: bifunctorFlip,
    biapplyFlip: biapplyFlip,
    biapplicativeFlip: biapplicativeFlip
};

},{"../Control.Biapplicative/index.js":20,"../Control.Biapply/index.js":21,"../Data.Bifunctor/index.js":73,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],70:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Biapplicative = require("../Control.Biapplicative/index.js");
var Control_Biapply = require("../Control.Biapply/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Joker = function (x) {
    return x;
};
var showJoker = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Joker " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var ordJoker = function (dictOrd) {
    return dictOrd;
};
var newtypeJoker = new Data_Newtype.Newtype(function (n) {
    return n;
}, Joker);
var functorJoker = function (dictFunctor) {
    return new Data_Functor.Functor(function (g) {
        return function (v) {
            return Data_Functor.map(dictFunctor)(g)(v);
        };
    });
};
var eqJoker = function (dictEq) {
    return dictEq;
};
var bifunctorJoker = function (dictFunctor) {
    return new Data_Bifunctor.Bifunctor(function (v) {
        return function (g) {
            return function (v1) {
                return Data_Functor.map(dictFunctor)(g)(v1);
            };
        };
    });
};
var biapplyJoker = function (dictApply) {
    return new Control_Biapply.Biapply(function () {
        return bifunctorJoker(dictApply.Functor0());
    }, function (v) {
        return function (v1) {
            return Control_Apply.apply(dictApply)(v)(v1);
        };
    });
};
var biapplicativeJoker = function (dictApplicative) {
    return new Control_Biapplicative.Biapplicative(function () {
        return biapplyJoker(dictApplicative.Apply0());
    }, function (v) {
        return function (b) {
            return Control_Applicative.pure(dictApplicative)(b);
        };
    });
};
module.exports = {
    Joker: Joker,
    newtypeJoker: newtypeJoker,
    eqJoker: eqJoker,
    ordJoker: ordJoker,
    showJoker: showJoker,
    functorJoker: functorJoker,
    bifunctorJoker: bifunctorJoker,
    biapplyJoker: biapplyJoker,
    biapplicativeJoker: biapplicativeJoker
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Biapplicative/index.js":20,"../Control.Biapply/index.js":21,"../Data.Bifunctor/index.js":73,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],71:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Biapplicative = require("../Control.Biapplicative/index.js");
var Control_Biapply = require("../Control.Biapply/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Product = (function () {
    function Product(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Product.create = function (value0) {
        return function (value1) {
            return new Product(value0, value1);
        };
    };
    return Product;
})();
var showProduct = function (dictShow) {
    return function (dictShow1) {
        return new Data_Show.Show(function (v) {
            return "(Product " + (Data_Show.show(dictShow)(v.value0) + (" " + (Data_Show.show(dictShow1)(v.value1) + ")")));
        });
    };
};
var eqProduct = function (dictEq) {
    return function (dictEq1) {
        return new Data_Eq.Eq(function (x) {
            return function (y) {
                return Data_Eq.eq(dictEq)(x.value0)(y.value0) && Data_Eq.eq(dictEq1)(x.value1)(y.value1);
            };
        });
    };
};
var ordProduct = function (dictOrd) {
    return function (dictOrd1) {
        return new Data_Ord.Ord(function () {
            return eqProduct(dictOrd.Eq0())(dictOrd1.Eq0());
        }, function (x) {
            return function (y) {
                var v = Data_Ord.compare(dictOrd)(x.value0)(y.value0);
                if (v instanceof Data_Ordering.LT) {
                    return Data_Ordering.LT.value;
                };
                if (v instanceof Data_Ordering.GT) {
                    return Data_Ordering.GT.value;
                };
                return Data_Ord.compare(dictOrd1)(x.value1)(y.value1);
            };
        });
    };
};
var bifunctorProduct = function (dictBifunctor) {
    return function (dictBifunctor1) {
        return new Data_Bifunctor.Bifunctor(function (f) {
            return function (g) {
                return function (v) {
                    return new Product(Data_Bifunctor.bimap(dictBifunctor)(f)(g)(v.value0), Data_Bifunctor.bimap(dictBifunctor1)(f)(g)(v.value1));
                };
            };
        });
    };
};
var biapplyProduct = function (dictBiapply) {
    return function (dictBiapply1) {
        return new Control_Biapply.Biapply(function () {
            return bifunctorProduct(dictBiapply.Bifunctor0())(dictBiapply1.Bifunctor0());
        }, function (v) {
            return function (v1) {
                return new Product(Control_Biapply.biapply(dictBiapply)(v.value0)(v1.value0), Control_Biapply.biapply(dictBiapply1)(v.value1)(v1.value1));
            };
        });
    };
};
var biapplicativeProduct = function (dictBiapplicative) {
    return function (dictBiapplicative1) {
        return new Control_Biapplicative.Biapplicative(function () {
            return biapplyProduct(dictBiapplicative.Biapply0())(dictBiapplicative1.Biapply0());
        }, function (a) {
            return function (b) {
                return new Product(Control_Biapplicative.bipure(dictBiapplicative)(a)(b), Control_Biapplicative.bipure(dictBiapplicative1)(a)(b));
            };
        });
    };
};
module.exports = {
    Product: Product,
    eqProduct: eqProduct,
    ordProduct: ordProduct,
    showProduct: showProduct,
    bifunctorProduct: bifunctorProduct,
    biapplyProduct: biapplyProduct,
    biapplicativeProduct: biapplicativeProduct
};

},{"../Control.Biapplicative/index.js":20,"../Control.Biapply/index.js":21,"../Data.Bifunctor/index.js":73,"../Data.Eq/index.js":86,"../Data.HeytingAlgebra/index.js":104,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],72:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Biapplicative = require("../Control.Biapplicative/index.js");
var Control_Biapply = require("../Control.Biapply/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Wrap = function (x) {
    return x;
};
var showWrap = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Wrap " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var ordWrap = function (dictOrd) {
    return dictOrd;
};
var newtypeWrap = new Data_Newtype.Newtype(function (n) {
    return n;
}, Wrap);
var functorWrap = function (dictBifunctor) {
    return new Data_Functor.Functor(function (f) {
        return function (v) {
            return Data_Bifunctor.rmap(dictBifunctor)(f)(v);
        };
    });
};
var eqWrap = function (dictEq) {
    return dictEq;
};
var bifunctorWrap = function (dictBifunctor) {
    return new Data_Bifunctor.Bifunctor(function (f) {
        return function (g) {
            return function (v) {
                return Data_Bifunctor.bimap(dictBifunctor)(f)(g)(v);
            };
        };
    });
};
var biapplyWrap = function (dictBiapply) {
    return new Control_Biapply.Biapply(function () {
        return bifunctorWrap(dictBiapply.Bifunctor0());
    }, function (v) {
        return function (v1) {
            return Control_Biapply.biapply(dictBiapply)(v)(v1);
        };
    });
};
var biapplicativeWrap = function (dictBiapplicative) {
    return new Control_Biapplicative.Biapplicative(function () {
        return biapplyWrap(dictBiapplicative.Biapply0());
    }, function (a) {
        return function (b) {
            return Control_Biapplicative.bipure(dictBiapplicative)(a)(b);
        };
    });
};
module.exports = {
    Wrap: Wrap,
    newtypeWrap: newtypeWrap,
    eqWrap: eqWrap,
    ordWrap: ordWrap,
    showWrap: showWrap,
    functorWrap: functorWrap,
    bifunctorWrap: bifunctorWrap,
    biapplyWrap: biapplyWrap,
    biapplicativeWrap: biapplicativeWrap
};

},{"../Control.Biapplicative/index.js":20,"../Control.Biapply/index.js":21,"../Data.Bifunctor/index.js":73,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],73:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Bifunctor = function (bimap) {
    this.bimap = bimap;
};
var bimap = function (dict) {
    return dict.bimap;
};
var lmap = function (dictBifunctor) {
    return function (f) {
        return bimap(dictBifunctor)(f)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var rmap = function (dictBifunctor) {
    return bimap(dictBifunctor)(Control_Category.identity(Control_Category.categoryFn));
};
module.exports = {
    bimap: bimap,
    Bifunctor: Bifunctor,
    lmap: lmap,
    rmap: rmap
};

},{"../Control.Category/index.js":24}],74:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Data_Bifoldable = require("../Data.Bifoldable/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Bifunctor_Clown = require("../Data.Bifunctor.Clown/index.js");
var Data_Bifunctor_Flip = require("../Data.Bifunctor.Flip/index.js");
var Data_Bifunctor_Joker = require("../Data.Bifunctor.Joker/index.js");
var Data_Bifunctor_Product = require("../Data.Bifunctor.Product/index.js");
var Data_Bifunctor_Wrap = require("../Data.Bifunctor.Wrap/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Prelude = require("../Prelude/index.js");
var Bitraversable = function (Bifoldable1, Bifunctor0, bisequence, bitraverse) {
    this.Bifoldable1 = Bifoldable1;
    this.Bifunctor0 = Bifunctor0;
    this.bisequence = bisequence;
    this.bitraverse = bitraverse;
};
var bitraverse = function (dict) {
    return dict.bitraverse;
};
var lfor = function (dictBitraversable) {
    return function (dictApplicative) {
        return function (t) {
            return function (f) {
                return bitraverse(dictBitraversable)(dictApplicative)(f)(Control_Applicative.pure(dictApplicative))(t);
            };
        };
    };
};
var ltraverse = function (dictBitraversable) {
    return function (dictApplicative) {
        return function (f) {
            return bitraverse(dictBitraversable)(dictApplicative)(f)(Control_Applicative.pure(dictApplicative));
        };
    };
};
var rfor = function (dictBitraversable) {
    return function (dictApplicative) {
        return function (t) {
            return function (f) {
                return bitraverse(dictBitraversable)(dictApplicative)(Control_Applicative.pure(dictApplicative))(f)(t);
            };
        };
    };
};
var rtraverse = function (dictBitraversable) {
    return function (dictApplicative) {
        return bitraverse(dictBitraversable)(dictApplicative)(Control_Applicative.pure(dictApplicative));
    };
};
var bitraversableJoker = function (dictTraversable) {
    return new Bitraversable(function () {
        return Data_Bifoldable.bifoldableJoker(dictTraversable.Foldable1());
    }, function () {
        return Data_Bifunctor_Joker.bifunctorJoker(dictTraversable.Functor0());
    }, function (dictApplicative) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Joker.Joker)(Data_Traversable.sequence(dictTraversable)(dictApplicative)(v));
        };
    }, function (dictApplicative) {
        return function (v) {
            return function (r) {
                return function (v1) {
                    return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Joker.Joker)(Data_Traversable.traverse(dictTraversable)(dictApplicative)(r)(v1));
                };
            };
        };
    });
};
var bitraversableClown = function (dictTraversable) {
    return new Bitraversable(function () {
        return Data_Bifoldable.bifoldableClown(dictTraversable.Foldable1());
    }, function () {
        return Data_Bifunctor_Clown.bifunctorClown(dictTraversable.Functor0());
    }, function (dictApplicative) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Clown.Clown)(Data_Traversable.sequence(dictTraversable)(dictApplicative)(v));
        };
    }, function (dictApplicative) {
        return function (l) {
            return function (v) {
                return function (v1) {
                    return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Clown.Clown)(Data_Traversable.traverse(dictTraversable)(dictApplicative)(l)(v1));
                };
            };
        };
    });
};
var bisequenceDefault = function (dictBitraversable) {
    return function (dictApplicative) {
        return bitraverse(dictBitraversable)(dictApplicative)(Control_Category.identity(Control_Category.categoryFn))(Control_Category.identity(Control_Category.categoryFn));
    };
};
var bisequence = function (dict) {
    return dict.bisequence;
};
var bitraversableFlip = function (dictBitraversable) {
    return new Bitraversable(function () {
        return Data_Bifoldable.bifoldableFlip(dictBitraversable.Bifoldable1());
    }, function () {
        return Data_Bifunctor_Flip.bifunctorFlip(dictBitraversable.Bifunctor0());
    }, function (dictApplicative) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Flip.Flip)(bisequence(dictBitraversable)(dictApplicative)(v));
        };
    }, function (dictApplicative) {
        return function (r) {
            return function (l) {
                return function (v) {
                    return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Flip.Flip)(bitraverse(dictBitraversable)(dictApplicative)(l)(r)(v));
                };
            };
        };
    });
};
var bitraversableProduct = function (dictBitraversable) {
    return function (dictBitraversable1) {
        return new Bitraversable(function () {
            return Data_Bifoldable.bifoldableProduct(dictBitraversable.Bifoldable1())(dictBitraversable1.Bifoldable1());
        }, function () {
            return Data_Bifunctor_Product.bifunctorProduct(dictBitraversable.Bifunctor0())(dictBitraversable1.Bifunctor0());
        }, function (dictApplicative) {
            return function (v) {
                return Control_Apply.apply(dictApplicative.Apply0())(Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Product.Product.create)(bisequence(dictBitraversable)(dictApplicative)(v.value0)))(bisequence(dictBitraversable1)(dictApplicative)(v.value1));
            };
        }, function (dictApplicative) {
            return function (l) {
                return function (r) {
                    return function (v) {
                        return Control_Apply.apply(dictApplicative.Apply0())(Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Product.Product.create)(bitraverse(dictBitraversable)(dictApplicative)(l)(r)(v.value0)))(bitraverse(dictBitraversable1)(dictApplicative)(l)(r)(v.value1));
                    };
                };
            };
        });
    };
};
var bitraversableWrap = function (dictBitraversable) {
    return new Bitraversable(function () {
        return Data_Bifoldable.bifoldableWrap(dictBitraversable.Bifoldable1());
    }, function () {
        return Data_Bifunctor_Wrap.bifunctorWrap(dictBitraversable.Bifunctor0());
    }, function (dictApplicative) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Wrap.Wrap)(bisequence(dictBitraversable)(dictApplicative)(v));
        };
    }, function (dictApplicative) {
        return function (l) {
            return function (r) {
                return function (v) {
                    return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Bifunctor_Wrap.Wrap)(bitraverse(dictBitraversable)(dictApplicative)(l)(r)(v));
                };
            };
        };
    });
};
var bitraverseDefault = function (dictBitraversable) {
    return function (dictApplicative) {
        return function (f) {
            return function (g) {
                return function (t) {
                    return bisequence(dictBitraversable)(dictApplicative)(Data_Bifunctor.bimap(dictBitraversable.Bifunctor0())(f)(g)(t));
                };
            };
        };
    };
};
var bifor = function (dictBitraversable) {
    return function (dictApplicative) {
        return function (t) {
            return function (f) {
                return function (g) {
                    return bitraverse(dictBitraversable)(dictApplicative)(f)(g)(t);
                };
            };
        };
    };
};
module.exports = {
    Bitraversable: Bitraversable,
    bitraverse: bitraverse,
    bisequence: bisequence,
    bitraverseDefault: bitraverseDefault,
    bisequenceDefault: bisequenceDefault,
    ltraverse: ltraverse,
    rtraverse: rtraverse,
    bifor: bifor,
    lfor: lfor,
    rfor: rfor,
    bitraversableClown: bitraversableClown,
    bitraversableJoker: bitraversableJoker,
    bitraversableFlip: bitraversableFlip,
    bitraversableProduct: bitraversableProduct,
    bitraversableWrap: bitraversableWrap
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Data.Bifoldable/index.js":67,"../Data.Bifunctor.Clown/index.js":68,"../Data.Bifunctor.Flip/index.js":69,"../Data.Bifunctor.Joker/index.js":70,"../Data.Bifunctor.Product/index.js":71,"../Data.Bifunctor.Wrap/index.js":72,"../Data.Bifunctor/index.js":73,"../Data.Functor/index.js":102,"../Data.Traversable/index.js":159,"../Prelude/index.js":195}],75:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var BooleanAlgebra = function (HeytingAlgebra0) {
    this.HeytingAlgebra0 = HeytingAlgebra0;
};
var BooleanAlgebraRecord = function (HeytingAlgebraRecord0) {
    this.HeytingAlgebraRecord0 = HeytingAlgebraRecord0;
};
var booleanAlgebraUnit = new BooleanAlgebra(function () {
    return Data_HeytingAlgebra.heytingAlgebraUnit;
});
var booleanAlgebraRecordNil = new BooleanAlgebraRecord(function () {
    return Data_HeytingAlgebra.heytingAlgebraRecordNil;
});
var booleanAlgebraRecordCons = function (dictIsSymbol) {
    return function (dictCons) {
        return function (dictBooleanAlgebraRecord) {
            return function (dictBooleanAlgebra) {
                return new BooleanAlgebraRecord(function () {
                    return Data_HeytingAlgebra.heytingAlgebraRecordCons(dictIsSymbol)(dictCons)(dictBooleanAlgebraRecord.HeytingAlgebraRecord0())(dictBooleanAlgebra.HeytingAlgebra0());
                });
            };
        };
    };
};
var booleanAlgebraRecord = function (dictRowToList) {
    return function (dictBooleanAlgebraRecord) {
        return new BooleanAlgebra(function () {
            return Data_HeytingAlgebra.heytingAlgebraRecord(dictRowToList)(dictBooleanAlgebraRecord.HeytingAlgebraRecord0());
        });
    };
};
var booleanAlgebraFn = function (dictBooleanAlgebra) {
    return new BooleanAlgebra(function () {
        return Data_HeytingAlgebra.heytingAlgebraFunction(dictBooleanAlgebra.HeytingAlgebra0());
    });
};
var booleanAlgebraBoolean = new BooleanAlgebra(function () {
    return Data_HeytingAlgebra.heytingAlgebraBoolean;
});
module.exports = {
    BooleanAlgebra: BooleanAlgebra,
    BooleanAlgebraRecord: BooleanAlgebraRecord,
    booleanAlgebraBoolean: booleanAlgebraBoolean,
    booleanAlgebraUnit: booleanAlgebraUnit,
    booleanAlgebraFn: booleanAlgebraFn,
    booleanAlgebraRecord: booleanAlgebraRecord,
    booleanAlgebraRecordNil: booleanAlgebraRecordNil,
    booleanAlgebraRecordCons: booleanAlgebraRecordCons
};

},{"../Data.HeytingAlgebra/index.js":104,"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168}],76:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var otherwise = true;
module.exports = {
    otherwise: otherwise
};

},{}],77:[function(require,module,exports){
"use strict";

exports.topInt = 2147483647;
exports.bottomInt = -2147483648;

exports.topChar = String.fromCharCode(65535);
exports.bottomChar = String.fromCharCode(0);

exports.topNumber = Number.POSITIVE_INFINITY;
exports.bottomNumber = Number.NEGATIVE_INFINITY;

},{}],78:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Bounded = function (Ord0, bottom, top) {
    this.Ord0 = Ord0;
    this.bottom = bottom;
    this.top = top;
};
var top = function (dict) {
    return dict.top;
};
var boundedUnit = new Bounded(function () {
    return Data_Ord.ordUnit;
}, Data_Unit.unit, Data_Unit.unit);
var boundedOrdering = new Bounded(function () {
    return Data_Ord.ordOrdering;
}, Data_Ordering.LT.value, Data_Ordering.GT.value);
var boundedNumber = new Bounded(function () {
    return Data_Ord.ordNumber;
}, $foreign.bottomNumber, $foreign.topNumber);
var boundedInt = new Bounded(function () {
    return Data_Ord.ordInt;
}, $foreign.bottomInt, $foreign.topInt);
var boundedChar = new Bounded(function () {
    return Data_Ord.ordChar;
}, $foreign.bottomChar, $foreign.topChar);
var boundedBoolean = new Bounded(function () {
    return Data_Ord.ordBoolean;
}, false, true);
var bottom = function (dict) {
    return dict.bottom;
};
module.exports = {
    Bounded: Bounded,
    bottom: bottom,
    top: top,
    boundedBoolean: boundedBoolean,
    boundedInt: boundedInt,
    boundedChar: boundedChar,
    boundedOrdering: boundedOrdering,
    boundedUnit: boundedUnit,
    boundedNumber: boundedNumber
};

},{"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Unit/index.js":168,"./foreign.js":77}],79:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var CommutativeRing = function (Ring0) {
    this.Ring0 = Ring0;
};
var CommutativeRingRecord = function (RingRecord0) {
    this.RingRecord0 = RingRecord0;
};
var commutativeRingUnit = new CommutativeRing(function () {
    return Data_Ring.ringUnit;
});
var commutativeRingRecordNil = new CommutativeRingRecord(function () {
    return Data_Ring.ringRecordNil;
});
var commutativeRingRecordCons = function (dictIsSymbol) {
    return function (dictCons) {
        return function (dictCommutativeRingRecord) {
            return function (dictCommutativeRing) {
                return new CommutativeRingRecord(function () {
                    return Data_Ring.ringRecordCons(dictIsSymbol)(dictCons)(dictCommutativeRingRecord.RingRecord0())(dictCommutativeRing.Ring0());
                });
            };
        };
    };
};
var commutativeRingRecord = function (dictRowToList) {
    return function (dictCommutativeRingRecord) {
        return new CommutativeRing(function () {
            return Data_Ring.ringRecord(dictRowToList)(dictCommutativeRingRecord.RingRecord0());
        });
    };
};
var commutativeRingNumber = new CommutativeRing(function () {
    return Data_Ring.ringNumber;
});
var commutativeRingInt = new CommutativeRing(function () {
    return Data_Ring.ringInt;
});
var commutativeRingFn = function (dictCommutativeRing) {
    return new CommutativeRing(function () {
        return Data_Ring.ringFn(dictCommutativeRing.Ring0());
    });
};
module.exports = {
    CommutativeRing: CommutativeRing,
    CommutativeRingRecord: CommutativeRingRecord,
    commutativeRingInt: commutativeRingInt,
    commutativeRingNumber: commutativeRingNumber,
    commutativeRingUnit: commutativeRingUnit,
    commutativeRingFn: commutativeRingFn,
    commutativeRingRecord: commutativeRingRecord,
    commutativeRingRecordNil: commutativeRingRecordNil,
    commutativeRingRecordCons: commutativeRingRecordCons
};

},{"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139,"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168}],80:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Identity = require("../Data.Identity/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Prelude = require("../Prelude/index.js");
var Distributive = function (Functor0, collect, distribute) {
    this.Functor0 = Functor0;
    this.collect = collect;
    this.distribute = distribute;
};
var distributiveIdentity = new Distributive(function () {
    return Data_Identity.functorIdentity;
}, function (dictFunctor) {
    return function (f) {
        return function ($11) {
            return Data_Identity.Identity(Data_Functor.map(dictFunctor)(function ($12) {
                return Data_Newtype.unwrap(Data_Identity.newtypeIdentity)(f($12));
            })($11));
        };
    };
}, function (dictFunctor) {
    return function ($13) {
        return Data_Identity.Identity(Data_Functor.map(dictFunctor)(Data_Newtype.unwrap(Data_Identity.newtypeIdentity))($13));
    };
});
var distribute = function (dict) {
    return dict.distribute;
};
var distributiveFunction = new Distributive(function () {
    return Data_Functor.functorFn;
}, function (dictFunctor) {
    return function (f) {
        return function ($14) {
            return distribute(distributiveFunction)(dictFunctor)(Data_Functor.map(dictFunctor)(f)($14));
        };
    };
}, function (dictFunctor) {
    return function (a) {
        return function (e) {
            return Data_Functor.map(dictFunctor)(function (v) {
                return v(e);
            })(a);
        };
    };
});
var cotraverse = function (dictDistributive) {
    return function (dictFunctor) {
        return function (f) {
            return function ($15) {
                return Data_Functor.map(dictDistributive.Functor0())(f)(distribute(dictDistributive)(dictFunctor)($15));
            };
        };
    };
};
var collectDefault = function (dictDistributive) {
    return function (dictFunctor) {
        return function (f) {
            return function ($16) {
                return distribute(dictDistributive)(dictFunctor)(Data_Functor.map(dictFunctor)(f)($16));
            };
        };
    };
};
var collect = function (dict) {
    return dict.collect;
};
var distributeDefault = function (dictDistributive) {
    return function (dictFunctor) {
        return collect(dictDistributive)(dictFunctor)(Control_Category.identity(Control_Category.categoryFn));
    };
};
module.exports = {
    collect: collect,
    distribute: distribute,
    Distributive: Distributive,
    distributeDefault: distributeDefault,
    collectDefault: collectDefault,
    cotraverse: cotraverse,
    distributiveIdentity: distributiveIdentity,
    distributiveFunction: distributiveFunction
};

},{"../Control.Category/index.js":24,"../Control.Semigroupoid/index.js":51,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Identity/index.js":105,"../Data.Newtype/index.js":121,"../Prelude/index.js":195}],81:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var DivisionRing = function (Ring0, recip) {
    this.Ring0 = Ring0;
    this.recip = recip;
};
var recip = function (dict) {
    return dict.recip;
};
var rightDiv = function (dictDivisionRing) {
    return function (a) {
        return function (b) {
            return Data_Semiring.mul((dictDivisionRing.Ring0()).Semiring0())(a)(recip(dictDivisionRing)(b));
        };
    };
};
var leftDiv = function (dictDivisionRing) {
    return function (a) {
        return function (b) {
            return Data_Semiring.mul((dictDivisionRing.Ring0()).Semiring0())(recip(dictDivisionRing)(b))(a);
        };
    };
};
var divisionringNumber = new DivisionRing(function () {
    return Data_Ring.ringNumber;
}, function (x) {
    return 1.0 / x;
});
module.exports = {
    DivisionRing: DivisionRing,
    recip: recip,
    leftDiv: leftDiv,
    rightDiv: rightDiv,
    divisionringNumber: divisionringNumber
};

},{"../Data.EuclideanRing/index.js":88,"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139}],82:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Extend = require("../Control.Extend/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Bifoldable = require("../Data.Bifoldable/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Bitraversable = require("../Data.Bitraversable/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_Invariant = require("../Data.Functor.Invariant/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Prelude = require("../Prelude/index.js");
var Left = (function () {
    function Left(value0) {
        this.value0 = value0;
    };
    Left.create = function (value0) {
        return new Left(value0);
    };
    return Left;
})();
var Right = (function () {
    function Right(value0) {
        this.value0 = value0;
    };
    Right.create = function (value0) {
        return new Right(value0);
    };
    return Right;
})();
var showEither = function (dictShow) {
    return function (dictShow1) {
        return new Data_Show.Show(function (v) {
            if (v instanceof Left) {
                return "(Left " + (Data_Show.show(dictShow)(v.value0) + ")");
            };
            if (v instanceof Right) {
                return "(Right " + (Data_Show.show(dictShow1)(v.value0) + ")");
            };
            throw new Error("Failed pattern match at Data.Either line 157, column 1 - line 157, column 61: " + [ v.constructor.name ]);
        });
    };
};
var note$prime = function (f) {
    return Data_Maybe["maybe'"](function ($171) {
        return Left.create(f($171));
    })(Right.create);
};
var note = function (a) {
    return Data_Maybe.maybe(new Left(a))(Right.create);
};
var functorEither = new Data_Functor.Functor(function (f) {
    return function (m) {
        if (m instanceof Left) {
            return new Left(m.value0);
        };
        if (m instanceof Right) {
            return new Right(f(m.value0));
        };
        throw new Error("Failed pattern match at Data.Either line 35, column 8 - line 35, column 52: " + [ m.constructor.name ]);
    };
});
var invariantEither = new Data_Functor_Invariant.Invariant(Data_Functor_Invariant.imapF(functorEither));
var fromRight = function (dictPartial) {
    return function (v) {
        var $__unused = function (dictPartial1) {
            return function ($dollar63) {
                return $dollar63;
            };
        };
        return $__unused(dictPartial)((function () {
            if (v instanceof Right) {
                return v.value0;
            };
            throw new Error("Failed pattern match at Data.Either line 243, column 1 - line 243, column 52: " + [ v.constructor.name ]);
        })());
    };
};
var fromLeft = function (dictPartial) {
    return function (v) {
        var $__unused = function (dictPartial1) {
            return function ($dollar67) {
                return $dollar67;
            };
        };
        return $__unused(dictPartial)((function () {
            if (v instanceof Left) {
                return v.value0;
            };
            throw new Error("Failed pattern match at Data.Either line 238, column 1 - line 238, column 51: " + [ v.constructor.name ]);
        })());
    };
};
var foldableEither = new Data_Foldable.Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            if (v instanceof Left) {
                return Data_Monoid.mempty(dictMonoid);
            };
            if (v instanceof Right) {
                return f(v.value0);
            };
            throw new Error("Failed pattern match at Data.Either line 181, column 1 - line 181, column 47: " + [ f.constructor.name, v.constructor.name ]);
        };
    };
}, function (v) {
    return function (z) {
        return function (v1) {
            if (v1 instanceof Left) {
                return z;
            };
            if (v1 instanceof Right) {
                return v(z)(v1.value0);
            };
            throw new Error("Failed pattern match at Data.Either line 181, column 1 - line 181, column 47: " + [ v.constructor.name, z.constructor.name, v1.constructor.name ]);
        };
    };
}, function (v) {
    return function (z) {
        return function (v1) {
            if (v1 instanceof Left) {
                return z;
            };
            if (v1 instanceof Right) {
                return v(v1.value0)(z);
            };
            throw new Error("Failed pattern match at Data.Either line 181, column 1 - line 181, column 47: " + [ v.constructor.name, z.constructor.name, v1.constructor.name ]);
        };
    };
});
var traversableEither = new Data_Traversable.Traversable(function () {
    return foldableEither;
}, function () {
    return functorEither;
}, function (dictApplicative) {
    return function (v) {
        if (v instanceof Left) {
            return Control_Applicative.pure(dictApplicative)(new Left(v.value0));
        };
        if (v instanceof Right) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Right.create)(v.value0);
        };
        throw new Error("Failed pattern match at Data.Either line 197, column 1 - line 197, column 53: " + [ v.constructor.name ]);
    };
}, function (dictApplicative) {
    return function (v) {
        return function (v1) {
            if (v1 instanceof Left) {
                return Control_Applicative.pure(dictApplicative)(new Left(v1.value0));
            };
            if (v1 instanceof Right) {
                return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Right.create)(v(v1.value0));
            };
            throw new Error("Failed pattern match at Data.Either line 197, column 1 - line 197, column 53: " + [ v.constructor.name, v1.constructor.name ]);
        };
    };
});
var extendEither = new Control_Extend.Extend(function () {
    return functorEither;
}, function (v) {
    return function (v1) {
        if (v1 instanceof Left) {
            return new Left(v1.value0);
        };
        return new Right(v(v1));
    };
});
var eqEither = function (dictEq) {
    return function (dictEq1) {
        return new Data_Eq.Eq(function (x) {
            return function (y) {
                if (x instanceof Left && y instanceof Left) {
                    return Data_Eq.eq(dictEq)(x.value0)(y.value0);
                };
                if (x instanceof Right && y instanceof Right) {
                    return Data_Eq.eq(dictEq1)(x.value0)(y.value0);
                };
                return false;
            };
        });
    };
};
var ordEither = function (dictOrd) {
    return function (dictOrd1) {
        return new Data_Ord.Ord(function () {
            return eqEither(dictOrd.Eq0())(dictOrd1.Eq0());
        }, function (x) {
            return function (y) {
                if (x instanceof Left && y instanceof Left) {
                    return Data_Ord.compare(dictOrd)(x.value0)(y.value0);
                };
                if (x instanceof Left) {
                    return Data_Ordering.LT.value;
                };
                if (y instanceof Left) {
                    return Data_Ordering.GT.value;
                };
                if (x instanceof Right && y instanceof Right) {
                    return Data_Ord.compare(dictOrd1)(x.value0)(y.value0);
                };
                throw new Error("Failed pattern match at Data.Either line 173, column 8 - line 173, column 64: " + [ x.constructor.name, y.constructor.name ]);
            };
        });
    };
};
var eq1Either = function (dictEq) {
    return new Data_Eq.Eq1(function (dictEq1) {
        return Data_Eq.eq(eqEither(dictEq)(dictEq1));
    });
};
var ord1Either = function (dictOrd) {
    return new Data_Ord.Ord1(function () {
        return eq1Either(dictOrd.Eq0());
    }, function (dictOrd1) {
        return Data_Ord.compare(ordEither(dictOrd)(dictOrd1));
    });
};
var either = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof Left) {
                return v(v2.value0);
            };
            if (v2 instanceof Right) {
                return v1(v2.value0);
            };
            throw new Error("Failed pattern match at Data.Either line 220, column 1 - line 220, column 64: " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};
var hush = either(Data_Function["const"](Data_Maybe.Nothing.value))(Data_Maybe.Just.create);
var isLeft = either(Data_Function["const"](true))(Data_Function["const"](false));
var isRight = either(Data_Function["const"](false))(Data_Function["const"](true));
var choose = function (dictAlt) {
    return function (a) {
        return function (b) {
            return Control_Alt.alt(dictAlt)(Data_Functor.map(dictAlt.Functor0())(Left.create)(a))(Data_Functor.map(dictAlt.Functor0())(Right.create)(b));
        };
    };
};
var boundedEither = function (dictBounded) {
    return function (dictBounded1) {
        return new Data_Bounded.Bounded(function () {
            return ordEither(dictBounded.Ord0())(dictBounded1.Ord0());
        }, new Left(Data_Bounded.bottom(dictBounded)), new Right(Data_Bounded.top(dictBounded1)));
    };
};
var bifunctorEither = new Data_Bifunctor.Bifunctor(function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof Left) {
                return new Left(v(v2.value0));
            };
            if (v2 instanceof Right) {
                return new Right(v1(v2.value0));
            };
            throw new Error("Failed pattern match at Data.Either line 40, column 1 - line 40, column 45: " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
});
var bifoldableEither = new Data_Bifoldable.Bifoldable(function (dictMonoid) {
    return function (v) {
        return function (v1) {
            return function (v2) {
                if (v2 instanceof Left) {
                    return v(v2.value0);
                };
                if (v2 instanceof Right) {
                    return v1(v2.value0);
                };
                throw new Error("Failed pattern match at Data.Either line 189, column 1 - line 189, column 47: " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
            };
        };
    };
}, function (v) {
    return function (v1) {
        return function (z) {
            return function (v2) {
                if (v2 instanceof Left) {
                    return v(z)(v2.value0);
                };
                if (v2 instanceof Right) {
                    return v1(z)(v2.value0);
                };
                throw new Error("Failed pattern match at Data.Either line 189, column 1 - line 189, column 47: " + [ v.constructor.name, v1.constructor.name, z.constructor.name, v2.constructor.name ]);
            };
        };
    };
}, function (v) {
    return function (v1) {
        return function (z) {
            return function (v2) {
                if (v2 instanceof Left) {
                    return v(v2.value0)(z);
                };
                if (v2 instanceof Right) {
                    return v1(v2.value0)(z);
                };
                throw new Error("Failed pattern match at Data.Either line 189, column 1 - line 189, column 47: " + [ v.constructor.name, v1.constructor.name, z.constructor.name, v2.constructor.name ]);
            };
        };
    };
});
var bitraversableEither = new Data_Bitraversable.Bitraversable(function () {
    return bifoldableEither;
}, function () {
    return bifunctorEither;
}, function (dictApplicative) {
    return function (v) {
        if (v instanceof Left) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Left.create)(v.value0);
        };
        if (v instanceof Right) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Right.create)(v.value0);
        };
        throw new Error("Failed pattern match at Data.Either line 203, column 1 - line 203, column 53: " + [ v.constructor.name ]);
    };
}, function (dictApplicative) {
    return function (v) {
        return function (v1) {
            return function (v2) {
                if (v2 instanceof Left) {
                    return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Left.create)(v(v2.value0));
                };
                if (v2 instanceof Right) {
                    return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Right.create)(v1(v2.value0));
                };
                throw new Error("Failed pattern match at Data.Either line 203, column 1 - line 203, column 53: " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
            };
        };
    };
});
var applyEither = new Control_Apply.Apply(function () {
    return functorEither;
}, function (v) {
    return function (v1) {
        if (v instanceof Left) {
            return new Left(v.value0);
        };
        if (v instanceof Right) {
            return Data_Functor.map(functorEither)(v.value0)(v1);
        };
        throw new Error("Failed pattern match at Data.Either line 76, column 1 - line 76, column 41: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var bindEither = new Control_Bind.Bind(function () {
    return applyEither;
}, either(function (e) {
    return function (v) {
        return new Left(e);
    };
})(function (a) {
    return function (f) {
        return f(a);
    };
}));
var semigroupEither = function (dictSemigroup) {
    return new Data_Semigroup.Semigroup(function (x) {
        return function (y) {
            return Control_Apply.apply(applyEither)(Data_Functor.map(functorEither)(Data_Semigroup.append(dictSemigroup))(x))(y);
        };
    });
};
var applicativeEither = new Control_Applicative.Applicative(function () {
    return applyEither;
}, Right.create);
var monadEither = new Control_Monad.Monad(function () {
    return applicativeEither;
}, function () {
    return bindEither;
});
var altEither = new Control_Alt.Alt(function () {
    return functorEither;
}, function (v) {
    return function (v1) {
        if (v instanceof Left) {
            return v1;
        };
        return v;
    };
});
module.exports = {
    Left: Left,
    Right: Right,
    either: either,
    choose: choose,
    isLeft: isLeft,
    isRight: isRight,
    fromLeft: fromLeft,
    fromRight: fromRight,
    note: note,
    "note'": note$prime,
    hush: hush,
    functorEither: functorEither,
    invariantEither: invariantEither,
    bifunctorEither: bifunctorEither,
    applyEither: applyEither,
    applicativeEither: applicativeEither,
    altEither: altEither,
    bindEither: bindEither,
    monadEither: monadEither,
    extendEither: extendEither,
    showEither: showEither,
    eqEither: eqEither,
    eq1Either: eq1Either,
    ordEither: ordEither,
    ord1Either: ord1Either,
    boundedEither: boundedEither,
    foldableEither: foldableEither,
    bifoldableEither: bifoldableEither,
    traversableEither: traversableEither,
    bitraversableEither: bitraversableEither,
    semigroupEither: semigroupEither
};

},{"../Control.Alt/index.js":15,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Extend/index.js":27,"../Control.Monad/index.js":47,"../Control.Semigroupoid/index.js":51,"../Data.Bifoldable/index.js":67,"../Data.Bifunctor/index.js":73,"../Data.Bitraversable/index.js":74,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Functor.Invariant/index.js":98,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Data.Traversable/index.js":159,"../Prelude/index.js":195}],83:[function(require,module,exports){
"use strict";

exports.toCharCode = function (c) {
  return c.charCodeAt(0);
};

exports.fromCharCode = function (c) {
  return String.fromCharCode(c);
};

},{}],84:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_MonadPlus = require("../Control.MonadPlus/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unfoldable = require("../Data.Unfoldable/index.js");
var Data_Unfoldable1 = require("../Data.Unfoldable1/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var Cardinality = function (x) {
    return x;
};
var Enum = function (Ord0, pred, succ) {
    this.Ord0 = Ord0;
    this.pred = pred;
    this.succ = succ;
};
var BoundedEnum = function (Bounded0, Enum1, cardinality, fromEnum, toEnum) {
    this.Bounded0 = Bounded0;
    this.Enum1 = Enum1;
    this.cardinality = cardinality;
    this.fromEnum = fromEnum;
    this.toEnum = toEnum;
};
var toEnum = function (dict) {
    return dict.toEnum;
};
var succ = function (dict) {
    return dict.succ;
};
var upFromIncluding = function (dictEnum) {
    return function (dictUnfoldable1) {
        return Data_Unfoldable1.unfoldr1(dictUnfoldable1)(Control_Apply.apply(Control_Apply.applyFn)(Data_Tuple.Tuple.create)(succ(dictEnum)));
    };
};
var showCardinality = new Data_Show.Show(function (v) {
    return "(Cardinality " + (Data_Show.show(Data_Show.showInt)(v) + ")");
});
var pred = function (dict) {
    return dict.pred;
};
var ordCardinality = Data_Ord.ordInt;
var newtypeCardinality = new Data_Newtype.Newtype(function (n) {
    return n;
}, Cardinality);
var fromEnum = function (dict) {
    return dict.fromEnum;
};
var toEnumWithDefaults = function (dictBoundedEnum) {
    return function (low) {
        return function (high) {
            return function (x) {
                var v = toEnum(dictBoundedEnum)(x);
                if (v instanceof Data_Maybe.Just) {
                    return v.value0;
                };
                if (v instanceof Data_Maybe.Nothing) {
                    var $51 = x < fromEnum(dictBoundedEnum)(Data_Bounded.bottom(dictBoundedEnum.Bounded0()));
                    if ($51) {
                        return low;
                    };
                    return high;
                };
                throw new Error("Failed pattern match at Data.Enum line 158, column 33 - line 160, column 62: " + [ v.constructor.name ]);
            };
        };
    };
};
var eqCardinality = Data_Eq.eqInt;
var enumUnit = new Enum(function () {
    return Data_Ord.ordUnit;
}, Data_Function["const"](Data_Maybe.Nothing.value), Data_Function["const"](Data_Maybe.Nothing.value));
var enumTuple = function (dictEnum) {
    return function (dictBoundedEnum) {
        return new Enum(function () {
            return Data_Tuple.ordTuple(dictEnum.Ord0())((dictBoundedEnum.Enum1()).Ord0());
        }, function (v) {
            return Data_Maybe.maybe(Data_Functor.map(Data_Maybe.functorMaybe)(Data_Function.flip(Data_Tuple.Tuple.create)(Data_Bounded.top(dictBoundedEnum.Bounded0())))(pred(dictEnum)(v.value0)))(function ($86) {
                return Data_Maybe.Just.create(Data_Tuple.Tuple.create(v.value0)($86));
            })(pred(dictBoundedEnum.Enum1())(v.value1));
        }, function (v) {
            return Data_Maybe.maybe(Data_Functor.map(Data_Maybe.functorMaybe)(Data_Function.flip(Data_Tuple.Tuple.create)(Data_Bounded.bottom(dictBoundedEnum.Bounded0())))(succ(dictEnum)(v.value0)))(function ($87) {
                return Data_Maybe.Just.create(Data_Tuple.Tuple.create(v.value0)($87));
            })(succ(dictBoundedEnum.Enum1())(v.value1));
        });
    };
};
var enumOrdering = new Enum(function () {
    return Data_Ord.ordOrdering;
}, function (v) {
    if (v instanceof Data_Ordering.LT) {
        return Data_Maybe.Nothing.value;
    };
    if (v instanceof Data_Ordering.EQ) {
        return new Data_Maybe.Just(Data_Ordering.LT.value);
    };
    if (v instanceof Data_Ordering.GT) {
        return new Data_Maybe.Just(Data_Ordering.EQ.value);
    };
    throw new Error("Failed pattern match at Data.Enum line 72, column 1 - line 72, column 39: " + [ v.constructor.name ]);
}, function (v) {
    if (v instanceof Data_Ordering.LT) {
        return new Data_Maybe.Just(Data_Ordering.EQ.value);
    };
    if (v instanceof Data_Ordering.EQ) {
        return new Data_Maybe.Just(Data_Ordering.GT.value);
    };
    if (v instanceof Data_Ordering.GT) {
        return Data_Maybe.Nothing.value;
    };
    throw new Error("Failed pattern match at Data.Enum line 72, column 1 - line 72, column 39: " + [ v.constructor.name ]);
});
var enumMaybe = function (dictBoundedEnum) {
    return new Enum(function () {
        return Data_Maybe.ordMaybe((dictBoundedEnum.Enum1()).Ord0());
    }, function (v) {
        if (v instanceof Data_Maybe.Nothing) {
            return Data_Maybe.Nothing.value;
        };
        if (v instanceof Data_Maybe.Just) {
            return new Data_Maybe.Just(pred(dictBoundedEnum.Enum1())(v.value0));
        };
        throw new Error("Failed pattern match at Data.Enum line 80, column 1 - line 80, column 54: " + [ v.constructor.name ]);
    }, function (v) {
        if (v instanceof Data_Maybe.Nothing) {
            return new Data_Maybe.Just(new Data_Maybe.Just(Data_Bounded.bottom(dictBoundedEnum.Bounded0())));
        };
        if (v instanceof Data_Maybe.Just) {
            return Data_Functor.map(Data_Maybe.functorMaybe)(Data_Maybe.Just.create)(succ(dictBoundedEnum.Enum1())(v.value0));
        };
        throw new Error("Failed pattern match at Data.Enum line 80, column 1 - line 80, column 54: " + [ v.constructor.name ]);
    });
};
var enumInt = new Enum(function () {
    return Data_Ord.ordInt;
}, function (n) {
    var $64 = n > Data_Bounded.bottom(Data_Bounded.boundedInt);
    if ($64) {
        return new Data_Maybe.Just(n - 1 | 0);
    };
    return Data_Maybe.Nothing.value;
}, function (n) {
    var $65 = n < Data_Bounded.top(Data_Bounded.boundedInt);
    if ($65) {
        return new Data_Maybe.Just(n + 1 | 0);
    };
    return Data_Maybe.Nothing.value;
});
var enumFromTo = function (dictEnum) {
    return function (dictUnfoldable1) {
        var go = function (step) {
            return function (op) {
                return function (to) {
                    return function (a) {
                        return new Data_Tuple.Tuple(a, Control_Bind.bind(Data_Maybe.bindMaybe)(step(a))(function (a$prime) {
                            return Data_Functor.voidLeft(Data_Maybe.functorMaybe)(Control_MonadZero.guard(Data_Maybe.monadZeroMaybe)(op(a$prime)(to)))(a$prime);
                        }));
                    };
                };
            };
        };
        return function (v) {
            return function (v1) {
                if (Data_Eq.eq((dictEnum.Ord0()).Eq0())(v)(v1)) {
                    return Data_Unfoldable1.singleton(dictUnfoldable1)(v);
                };
                if (Data_Ord.lessThan(dictEnum.Ord0())(v)(v1)) {
                    return Data_Unfoldable1.unfoldr1(dictUnfoldable1)(go(succ(dictEnum))(Data_Ord.lessThanOrEq(dictEnum.Ord0()))(v1))(v);
                };
                if (Data_Boolean.otherwise) {
                    return Data_Unfoldable1.unfoldr1(dictUnfoldable1)(go(pred(dictEnum))(Data_Ord.greaterThanOrEq(dictEnum.Ord0()))(v1))(v);
                };
                throw new Error("Failed pattern match at Data.Enum line 183, column 14 - line 187, column 51: " + [ v.constructor.name, v1.constructor.name ]);
            };
        };
    };
};
var enumFromThenTo = function (dictUnfoldable) {
    return function (dictFunctor) {
        return function (dictBoundedEnum) {
            var go = function (step) {
                return function (to) {
                    return function (e) {
                        if (e <= to) {
                            return new Data_Maybe.Just(new Data_Tuple.Tuple(e, e + step | 0));
                        };
                        if (Data_Boolean.otherwise) {
                            return Data_Maybe.Nothing.value;
                        };
                        throw new Error("Failed pattern match at Data.Enum line 214, column 5 - line 216, column 28: " + [ step.constructor.name, to.constructor.name, e.constructor.name ]);
                    };
                };
            };
            return function (a) {
                return function (b) {
                    return function (c) {
                        var c$prime = fromEnum(dictBoundedEnum)(c);
                        var b$prime = fromEnum(dictBoundedEnum)(b);
                        var a$prime = fromEnum(dictBoundedEnum)(a);
                        return Data_Functor.map(dictFunctor)(function ($88) {
                            return Data_Maybe.fromJust()(toEnum(dictBoundedEnum)($88));
                        })(Data_Unfoldable.unfoldr(dictUnfoldable)(go(b$prime - a$prime | 0)(c$prime))(a$prime));
                    };
                };
            };
        };
    };
};
var enumEither = function (dictBoundedEnum) {
    return function (dictBoundedEnum1) {
        return new Enum(function () {
            return Data_Either.ordEither((dictBoundedEnum.Enum1()).Ord0())((dictBoundedEnum1.Enum1()).Ord0());
        }, function (v) {
            if (v instanceof Data_Either.Left) {
                return Data_Maybe.maybe(Data_Maybe.Nothing.value)(function ($89) {
                    return Data_Maybe.Just.create(Data_Either.Left.create($89));
                })(pred(dictBoundedEnum.Enum1())(v.value0));
            };
            if (v instanceof Data_Either.Right) {
                return Data_Maybe.maybe(new Data_Maybe.Just(new Data_Either.Left(Data_Bounded.top(dictBoundedEnum.Bounded0()))))(function ($90) {
                    return Data_Maybe.Just.create(Data_Either.Right.create($90));
                })(pred(dictBoundedEnum1.Enum1())(v.value0));
            };
            throw new Error("Failed pattern match at Data.Enum line 86, column 1 - line 86, column 75: " + [ v.constructor.name ]);
        }, function (v) {
            if (v instanceof Data_Either.Left) {
                return Data_Maybe.maybe(new Data_Maybe.Just(new Data_Either.Right(Data_Bounded.bottom(dictBoundedEnum1.Bounded0()))))(function ($91) {
                    return Data_Maybe.Just.create(Data_Either.Left.create($91));
                })(succ(dictBoundedEnum.Enum1())(v.value0));
            };
            if (v instanceof Data_Either.Right) {
                return Data_Maybe.maybe(Data_Maybe.Nothing.value)(function ($92) {
                    return Data_Maybe.Just.create(Data_Either.Right.create($92));
                })(succ(dictBoundedEnum1.Enum1())(v.value0));
            };
            throw new Error("Failed pattern match at Data.Enum line 86, column 1 - line 86, column 75: " + [ v.constructor.name ]);
        });
    };
};
var enumBoolean = new Enum(function () {
    return Data_Ord.ordBoolean;
}, function (v) {
    if (v) {
        return new Data_Maybe.Just(false);
    };
    return Data_Maybe.Nothing.value;
}, function (v) {
    if (!v) {
        return new Data_Maybe.Just(true);
    };
    return Data_Maybe.Nothing.value;
});
var downFromIncluding = function (dictEnum) {
    return function (dictUnfoldable1) {
        return Data_Unfoldable1.unfoldr1(dictUnfoldable1)(Control_Apply.apply(Control_Apply.applyFn)(Data_Tuple.Tuple.create)(pred(dictEnum)));
    };
};
var diag = function (a) {
    return new Data_Tuple.Tuple(a, a);
};
var downFrom = function (dictEnum) {
    return function (dictUnfoldable) {
        return Data_Unfoldable.unfoldr(dictUnfoldable)(function ($93) {
            return Data_Functor.map(Data_Maybe.functorMaybe)(diag)(pred(dictEnum)($93));
        });
    };
};
var upFrom = function (dictEnum) {
    return function (dictUnfoldable) {
        return Data_Unfoldable.unfoldr(dictUnfoldable)(function ($94) {
            return Data_Functor.map(Data_Maybe.functorMaybe)(diag)(succ(dictEnum)($94));
        });
    };
};
var defaultToEnum = function (dictBounded) {
    return function (dictEnum) {
        return function (n) {
            if (n < 0) {
                return Data_Maybe.Nothing.value;
            };
            if (n === 0) {
                return new Data_Maybe.Just(Data_Bounded.bottom(dictBounded));
            };
            if (Data_Boolean.otherwise) {
                return Control_Bind.bind(Data_Maybe.bindMaybe)(defaultToEnum(dictBounded)(dictEnum)(n - 1 | 0))(succ(dictEnum));
            };
            throw new Error("Failed pattern match at Data.Enum line 281, column 1 - line 281, column 65: " + [ n.constructor.name ]);
        };
    };
};
var defaultSucc = function (toEnum$prime) {
    return function (fromEnum$prime) {
        return function (a) {
            return toEnum$prime(fromEnum$prime(a) + 1 | 0);
        };
    };
};
var defaultPred = function (toEnum$prime) {
    return function (fromEnum$prime) {
        return function (a) {
            return toEnum$prime(fromEnum$prime(a) - 1 | 0);
        };
    };
};
var defaultFromEnum = function (dictEnum) {
    return function ($95) {
        return Data_Maybe.maybe(0)(function (prd) {
            return defaultFromEnum(dictEnum)(prd) + 1 | 0;
        })(pred(dictEnum)($95));
    };
};
var defaultCardinality = function (dictBounded) {
    return function (dictEnum) {
        var defaultCardinality$prime = function (i) {
            return function ($96) {
                return Data_Maybe.maybe(i)(defaultCardinality$prime(i + 1 | 0))(succ(dictEnum)($96));
            };
        };
        return Cardinality(defaultCardinality$prime(1)(Data_Bounded.bottom(dictBounded)));
    };
};
var charToEnum = function (v) {
    if (v >= Data_Bounded.bottom(Data_Bounded.boundedInt) && v <= Data_Bounded.top(Data_Bounded.boundedInt)) {
        return new Data_Maybe.Just($foreign.fromCharCode(v));
    };
    return Data_Maybe.Nothing.value;
};
var enumChar = new Enum(function () {
    return Data_Ord.ordChar;
}, defaultPred(charToEnum)($foreign.toCharCode), defaultSucc(charToEnum)($foreign.toCharCode));
var cardinality = function (dict) {
    return dict.cardinality;
};
var boundedEnumUnit = new BoundedEnum(function () {
    return Data_Bounded.boundedUnit;
}, function () {
    return enumUnit;
}, 1, Data_Function["const"](0), function (v) {
    if (v === 0) {
        return new Data_Maybe.Just(Data_Unit.unit);
    };
    return Data_Maybe.Nothing.value;
});
var boundedEnumOrdering = new BoundedEnum(function () {
    return Data_Bounded.boundedOrdering;
}, function () {
    return enumOrdering;
}, 3, function (v) {
    if (v instanceof Data_Ordering.LT) {
        return 0;
    };
    if (v instanceof Data_Ordering.EQ) {
        return 1;
    };
    if (v instanceof Data_Ordering.GT) {
        return 2;
    };
    throw new Error("Failed pattern match at Data.Enum line 137, column 1 - line 137, column 53: " + [ v.constructor.name ]);
}, function (v) {
    if (v === 0) {
        return new Data_Maybe.Just(Data_Ordering.LT.value);
    };
    if (v === 1) {
        return new Data_Maybe.Just(Data_Ordering.EQ.value);
    };
    if (v === 2) {
        return new Data_Maybe.Just(Data_Ordering.GT.value);
    };
    return Data_Maybe.Nothing.value;
});
var boundedEnumChar = new BoundedEnum(function () {
    return Data_Bounded.boundedChar;
}, function () {
    return enumChar;
}, $foreign.toCharCode(Data_Bounded.top(Data_Bounded.boundedChar)) - $foreign.toCharCode(Data_Bounded.bottom(Data_Bounded.boundedChar)) | 0, $foreign.toCharCode, charToEnum);
var boundedEnumBoolean = new BoundedEnum(function () {
    return Data_Bounded.boundedBoolean;
}, function () {
    return enumBoolean;
}, 2, function (v) {
    if (!v) {
        return 0;
    };
    if (v) {
        return 1;
    };
    throw new Error("Failed pattern match at Data.Enum line 118, column 1 - line 118, column 51: " + [ v.constructor.name ]);
}, function (v) {
    if (v === 0) {
        return new Data_Maybe.Just(false);
    };
    if (v === 1) {
        return new Data_Maybe.Just(true);
    };
    return Data_Maybe.Nothing.value;
});
module.exports = {
    Enum: Enum,
    succ: succ,
    pred: pred,
    BoundedEnum: BoundedEnum,
    cardinality: cardinality,
    toEnum: toEnum,
    fromEnum: fromEnum,
    toEnumWithDefaults: toEnumWithDefaults,
    Cardinality: Cardinality,
    enumFromTo: enumFromTo,
    enumFromThenTo: enumFromThenTo,
    upFrom: upFrom,
    upFromIncluding: upFromIncluding,
    downFrom: downFrom,
    downFromIncluding: downFromIncluding,
    defaultSucc: defaultSucc,
    defaultPred: defaultPred,
    defaultCardinality: defaultCardinality,
    defaultToEnum: defaultToEnum,
    defaultFromEnum: defaultFromEnum,
    enumBoolean: enumBoolean,
    enumInt: enumInt,
    enumChar: enumChar,
    enumUnit: enumUnit,
    enumOrdering: enumOrdering,
    enumMaybe: enumMaybe,
    enumEither: enumEither,
    enumTuple: enumTuple,
    boundedEnumBoolean: boundedEnumBoolean,
    boundedEnumChar: boundedEnumChar,
    boundedEnumUnit: boundedEnumUnit,
    boundedEnumOrdering: boundedEnumOrdering,
    newtypeCardinality: newtypeCardinality,
    eqCardinality: eqCardinality,
    ordCardinality: ordCardinality,
    showCardinality: showCardinality
};

},{"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.MonadPlus/index.js":45,"../Control.MonadZero/index.js":46,"../Control.Semigroupoid/index.js":51,"../Data.Boolean/index.js":76,"../Data.Bounded/index.js":78,"../Data.Either/index.js":82,"../Data.Eq/index.js":86,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Maybe/index.js":112,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Data.Tuple/index.js":160,"../Data.Unfoldable/index.js":166,"../Data.Unfoldable1/index.js":164,"../Data.Unit/index.js":168,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195,"./foreign.js":83}],85:[function(require,module,exports){
"use strict";

exports.refEq = function (r1) {
  return function (r2) {
    return r1 === r2;
  };
};

exports.eqArrayImpl = function (f) {
  return function (xs) {
    return function (ys) {
      if (xs === ys) return true;
      if (xs.length !== ys.length) return false;
      for (var i = 0; i < xs.length; i++) {
        if (!f(xs[i])(ys[i])) return false;
      }
      return true;
    };
  };
};

},{}],86:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Data_Void = require("../Data.Void/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var Eq = function (eq) {
    this.eq = eq;
};
var Eq1 = function (eq1) {
    this.eq1 = eq1;
};
var EqRecord = function (eqRecord) {
    this.eqRecord = eqRecord;
};
var eqVoid = new Eq(function (v) {
    return function (v1) {
        return true;
    };
});
var eqUnit = new Eq(function (v) {
    return function (v1) {
        return true;
    };
});
var eqString = new Eq($foreign.refEq);
var eqRowNil = new EqRecord(function (v) {
    return function (v1) {
        return function (v2) {
            return true;
        };
    };
});
var eqRecord = function (dict) {
    return dict.eqRecord;
};
var eqRec = function (dictRowToList) {
    return function (dictEqRecord) {
        return new Eq(eqRecord(dictEqRecord)(Type_Data_RowList.RLProxy.value));
    };
};
var eqNumber = new Eq($foreign.refEq);
var eqInt = new Eq($foreign.refEq);
var eqChar = new Eq($foreign.refEq);
var eqBoolean = new Eq($foreign.refEq);
var eq1 = function (dict) {
    return dict.eq1;
};
var eq = function (dict) {
    return dict.eq;
};
var eqArray = function (dictEq) {
    return new Eq($foreign.eqArrayImpl(eq(dictEq)));
};
var eq1Array = new Eq1(function (dictEq) {
    return eq(eqArray(dictEq));
});
var eqRowCons = function (dictEqRecord) {
    return function (dictCons) {
        return function (dictIsSymbol) {
            return function (dictEq) {
                return new EqRecord(function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = eqRecord(dictEqRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var get = Record_Unsafe.unsafeGet(key);
                            return eq(dictEq)(get(ra))(get(rb)) && tail;
                        };
                    };
                });
            };
        };
    };
};
var notEq = function (dictEq) {
    return function (x) {
        return function (y) {
            return eq(eqBoolean)(eq(dictEq)(x)(y))(false);
        };
    };
};
var notEq1 = function (dictEq1) {
    return function (dictEq) {
        return function (x) {
            return function (y) {
                return eq(eqBoolean)(eq1(dictEq1)(dictEq)(x)(y))(false);
            };
        };
    };
};
module.exports = {
    Eq: Eq,
    eq: eq,
    notEq: notEq,
    Eq1: Eq1,
    eq1: eq1,
    notEq1: notEq1,
    EqRecord: EqRecord,
    eqRecord: eqRecord,
    eqBoolean: eqBoolean,
    eqInt: eqInt,
    eqNumber: eqNumber,
    eqChar: eqChar,
    eqString: eqString,
    eqUnit: eqUnit,
    eqVoid: eqVoid,
    eqArray: eqArray,
    eqRec: eqRec,
    eq1Array: eq1Array,
    eqRowNil: eqRowNil,
    eqRowCons: eqRowCons
};

},{"../Data.HeytingAlgebra/index.js":104,"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168,"../Data.Void/index.js":169,"../Record.Unsafe/index.js":197,"../Type.Data.RowList/index.js":198,"./foreign.js":85}],87:[function(require,module,exports){
"use strict";

exports.intDegree = function (x) {
  return Math.min(Math.abs(x), 2147483647);
};

// See the Euclidean definition in
// https://en.m.wikipedia.org/wiki/Modulo_operation.
exports.intDiv = function (x) {
  return function (y) {
    if (y === 0) return 0;
    return y > 0 ? Math.floor(x / y) : -Math.floor(x / -y);
  };
};

exports.intMod = function (x) {
  return function (y) {
    if (y === 0) return 0;
    var yy = Math.abs(y);
    return ((x % yy) + yy) % yy;
  };
};

exports.numDiv = function (n1) {
  return function (n2) {
    return n1 / n2;
  };
};

},{}],88:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_BooleanAlgebra = require("../Data.BooleanAlgebra/index.js");
var Data_CommutativeRing = require("../Data.CommutativeRing/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var EuclideanRing = function (CommutativeRing0, degree, div, mod) {
    this.CommutativeRing0 = CommutativeRing0;
    this.degree = degree;
    this.div = div;
    this.mod = mod;
};
var mod = function (dict) {
    return dict.mod;
};
var gcd = function ($copy_dictEq) {
    return function ($copy_dictEuclideanRing) {
        return function ($copy_a) {
            return function ($copy_b) {
                var $tco_var_dictEq = $copy_dictEq;
                var $tco_var_dictEuclideanRing = $copy_dictEuclideanRing;
                var $tco_var_a = $copy_a;
                var $tco_done = false;
                var $tco_result;
                function $tco_loop(dictEq, dictEuclideanRing, a, b) {
                    var $7 = Data_Eq.eq(dictEq)(b)(Data_Semiring.zero(((dictEuclideanRing.CommutativeRing0()).Ring0()).Semiring0()));
                    if ($7) {
                        $tco_done = true;
                        return a;
                    };
                    $tco_var_dictEq = dictEq;
                    $tco_var_dictEuclideanRing = dictEuclideanRing;
                    $tco_var_a = b;
                    $copy_b = mod(dictEuclideanRing)(a)(b);
                    return;
                };
                while (!$tco_done) {
                    $tco_result = $tco_loop($tco_var_dictEq, $tco_var_dictEuclideanRing, $tco_var_a, $copy_b);
                };
                return $tco_result;
            };
        };
    };
};
var euclideanRingNumber = new EuclideanRing(function () {
    return Data_CommutativeRing.commutativeRingNumber;
}, function (v) {
    return 1;
}, $foreign.numDiv, function (v) {
    return function (v1) {
        return 0.0;
    };
});
var euclideanRingInt = new EuclideanRing(function () {
    return Data_CommutativeRing.commutativeRingInt;
}, $foreign.intDegree, $foreign.intDiv, $foreign.intMod);
var div = function (dict) {
    return dict.div;
};
var lcm = function (dictEq) {
    return function (dictEuclideanRing) {
        return function (a) {
            return function (b) {
                var $8 = Data_Eq.eq(dictEq)(a)(Data_Semiring.zero(((dictEuclideanRing.CommutativeRing0()).Ring0()).Semiring0())) || Data_Eq.eq(dictEq)(b)(Data_Semiring.zero(((dictEuclideanRing.CommutativeRing0()).Ring0()).Semiring0()));
                if ($8) {
                    return Data_Semiring.zero(((dictEuclideanRing.CommutativeRing0()).Ring0()).Semiring0());
                };
                return div(dictEuclideanRing)(Data_Semiring.mul(((dictEuclideanRing.CommutativeRing0()).Ring0()).Semiring0())(a)(b))(gcd(dictEq)(dictEuclideanRing)(a)(b));
            };
        };
    };
};
var degree = function (dict) {
    return dict.degree;
};
module.exports = {
    EuclideanRing: EuclideanRing,
    degree: degree,
    div: div,
    mod: mod,
    gcd: gcd,
    lcm: lcm,
    euclideanRingInt: euclideanRingInt,
    euclideanRingNumber: euclideanRingNumber
};

},{"../Data.BooleanAlgebra/index.js":75,"../Data.CommutativeRing/index.js":79,"../Data.Eq/index.js":86,"../Data.HeytingAlgebra/index.js":104,"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139,"./foreign.js":87}],89:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_CommutativeRing = require("../Data.CommutativeRing/index.js");
var Data_DivisionRing = require("../Data.DivisionRing/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Field = function (DivisionRing1, EuclideanRing0) {
    this.DivisionRing1 = DivisionRing1;
    this.EuclideanRing0 = EuclideanRing0;
};
var field = function (dictEuclideanRing) {
    return function (dictDivisionRing) {
        return new Field(function () {
            return dictDivisionRing;
        }, function () {
            return dictEuclideanRing;
        });
    };
};
module.exports = {
    Field: Field,
    field: field
};

},{"../Data.CommutativeRing/index.js":79,"../Data.DivisionRing/index.js":81,"../Data.EuclideanRing/index.js":88,"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139}],90:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_FunctorWithIndex = require("../Data.FunctorWithIndex/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Maybe_First = require("../Data.Maybe.First/index.js");
var Data_Maybe_Last = require("../Data.Maybe.Last/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Monoid_Additive = require("../Data.Monoid.Additive/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Endo = require("../Data.Monoid.Endo/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var Tuple = (function () {
    function Tuple(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Tuple.create = function (value0) {
        return function (value1) {
            return new Tuple(value0, value1);
        };
    };
    return Tuple;
})();
var FoldableWithIndex = function (Foldable0, foldMapWithIndex, foldlWithIndex, foldrWithIndex) {
    this.Foldable0 = Foldable0;
    this.foldMapWithIndex = foldMapWithIndex;
    this.foldlWithIndex = foldlWithIndex;
    this.foldrWithIndex = foldrWithIndex;
};
var foldrWithIndex = function (dict) {
    return dict.foldrWithIndex;
};
var traverseWithIndex_ = function (dictApplicative) {
    return function (dictFoldableWithIndex) {
        return function (f) {
            return foldrWithIndex(dictFoldableWithIndex)(function (i) {
                return function ($46) {
                    return Control_Apply.applySecond(dictApplicative.Apply0())(f(i)($46));
                };
            })(Control_Applicative.pure(dictApplicative)(Data_Unit.unit));
        };
    };
};
var forWithIndex_ = function (dictApplicative) {
    return function (dictFoldableWithIndex) {
        return Data_Function.flip(traverseWithIndex_(dictApplicative)(dictFoldableWithIndex));
    };
};
var foldrDefault = function (dictFoldableWithIndex) {
    return function (f) {
        return foldrWithIndex(dictFoldableWithIndex)(Data_Function["const"](f));
    };
};
var foldlWithIndex = function (dict) {
    return dict.foldlWithIndex;
};
var foldlDefault = function (dictFoldableWithIndex) {
    return function (f) {
        return foldlWithIndex(dictFoldableWithIndex)(Data_Function["const"](f));
    };
};
var foldableWithIndexMultiplicative = new FoldableWithIndex(function () {
    return Data_Foldable.foldableMultiplicative;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableMultiplicative)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableMultiplicative)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableMultiplicative)(f(Data_Unit.unit));
});
var foldableWithIndexMaybe = new FoldableWithIndex(function () {
    return Data_Foldable.foldableMaybe;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableMaybe)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableMaybe)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableMaybe)(f(Data_Unit.unit));
});
var foldableWithIndexLast = new FoldableWithIndex(function () {
    return Data_Foldable.foldableLast;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableLast)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableLast)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableLast)(f(Data_Unit.unit));
});
var foldableWithIndexFirst = new FoldableWithIndex(function () {
    return Data_Foldable.foldableFirst;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableFirst)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableFirst)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableFirst)(f(Data_Unit.unit));
});
var foldableWithIndexDual = new FoldableWithIndex(function () {
    return Data_Foldable.foldableDual;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableDual)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableDual)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableDual)(f(Data_Unit.unit));
});
var foldableWithIndexDisj = new FoldableWithIndex(function () {
    return Data_Foldable.foldableDisj;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableDisj)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableDisj)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableDisj)(f(Data_Unit.unit));
});
var foldableWithIndexConj = new FoldableWithIndex(function () {
    return Data_Foldable.foldableConj;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableConj)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableConj)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableConj)(f(Data_Unit.unit));
});
var foldableWithIndexAdditive = new FoldableWithIndex(function () {
    return Data_Foldable.foldableAdditive;
}, function (dictMonoid) {
    return function (f) {
        return Data_Foldable.foldMap(Data_Foldable.foldableAdditive)(dictMonoid)(f(Data_Unit.unit));
    };
}, function (f) {
    return Data_Foldable.foldl(Data_Foldable.foldableAdditive)(f(Data_Unit.unit));
}, function (f) {
    return Data_Foldable.foldr(Data_Foldable.foldableAdditive)(f(Data_Unit.unit));
});
var foldWithIndexM = function (dictFoldableWithIndex) {
    return function (dictMonad) {
        return function (f) {
            return function (a0) {
                return foldlWithIndex(dictFoldableWithIndex)(function (i) {
                    return function (ma) {
                        return function (b) {
                            return Control_Bind.bind(dictMonad.Bind1())(ma)(Data_Function.flip(f(i))(b));
                        };
                    };
                })(Control_Applicative.pure(dictMonad.Applicative0())(a0));
            };
        };
    };
};
var foldMapWithIndexDefaultR = function (dictFoldableWithIndex) {
    return function (dictMonoid) {
        return function (f) {
            return foldrWithIndex(dictFoldableWithIndex)(function (i) {
                return function (x) {
                    return function (acc) {
                        return Data_Semigroup.append(dictMonoid.Semigroup0())(f(i)(x))(acc);
                    };
                };
            })(Data_Monoid.mempty(dictMonoid));
        };
    };
};
var foldableWithIndexArray = new FoldableWithIndex(function () {
    return Data_Foldable.foldableArray;
}, function (dictMonoid) {
    return foldMapWithIndexDefaultR(foldableWithIndexArray)(dictMonoid);
}, function (f) {
    return function (z) {
        return function ($47) {
            return Data_Foldable.foldl(Data_Foldable.foldableArray)(function (y) {
                return function (v) {
                    return f(v.value0)(y)(v.value1);
                };
            })(z)(Data_FunctorWithIndex.mapWithIndex(Data_FunctorWithIndex.functorWithIndexArray)(Tuple.create)($47));
        };
    };
}, function (f) {
    return function (z) {
        return function ($48) {
            return Data_Foldable.foldr(Data_Foldable.foldableArray)(function (v) {
                return function (y) {
                    return f(v.value0)(v.value1)(y);
                };
            })(z)(Data_FunctorWithIndex.mapWithIndex(Data_FunctorWithIndex.functorWithIndexArray)(Tuple.create)($48));
        };
    };
});
var foldMapWithIndexDefaultL = function (dictFoldableWithIndex) {
    return function (dictMonoid) {
        return function (f) {
            return foldlWithIndex(dictFoldableWithIndex)(function (i) {
                return function (acc) {
                    return function (x) {
                        return Data_Semigroup.append(dictMonoid.Semigroup0())(acc)(f(i)(x));
                    };
                };
            })(Data_Monoid.mempty(dictMonoid));
        };
    };
};
var foldMapWithIndex = function (dict) {
    return dict.foldMapWithIndex;
};
var foldlWithIndexDefault = function (dictFoldableWithIndex) {
    return function (c) {
        return function (u) {
            return function (xs) {
                return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(Data_Newtype.unwrap(Data_Newtype.newtypeDual)(foldMapWithIndex(dictFoldableWithIndex)(Data_Monoid_Dual.monoidDual(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn)))(function (i) {
                    return function ($49) {
                        return Data_Monoid_Dual.Dual(Data_Monoid_Endo.Endo(Data_Function.flip(c(i))($49)));
                    };
                })(xs)))(u);
            };
        };
    };
};
var foldrWithIndexDefault = function (dictFoldableWithIndex) {
    return function (c) {
        return function (u) {
            return function (xs) {
                return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(foldMapWithIndex(dictFoldableWithIndex)(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn))(function (i) {
                    return function ($50) {
                        return Data_Monoid_Endo.Endo(c(i)($50));
                    };
                })(xs))(u);
            };
        };
    };
};
var surroundMapWithIndex = function (dictFoldableWithIndex) {
    return function (dictSemigroup) {
        return function (d) {
            return function (t) {
                return function (f) {
                    var joined = function (i) {
                        return function (a) {
                            return function (m) {
                                return Data_Semigroup.append(dictSemigroup)(d)(Data_Semigroup.append(dictSemigroup)(t(i)(a))(m));
                            };
                        };
                    };
                    return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(foldMapWithIndex(dictFoldableWithIndex)(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn))(joined)(f))(d);
                };
            };
        };
    };
};
var foldMapDefault = function (dictFoldableWithIndex) {
    return function (dictMonoid) {
        return function (f) {
            return foldMapWithIndex(dictFoldableWithIndex)(dictMonoid)(Data_Function["const"](f));
        };
    };
};
var findWithIndex = function (dictFoldableWithIndex) {
    return function (p) {
        var go = function (v) {
            return function (v1) {
                return function (v2) {
                    if (v1 instanceof Data_Maybe.Nothing && p(v)(v2)) {
                        return new Data_Maybe.Just({
                            index: v,
                            value: v2
                        });
                    };
                    return v1;
                };
            };
        };
        return foldlWithIndex(dictFoldableWithIndex)(go)(Data_Maybe.Nothing.value);
    };
};
var anyWithIndex = function (dictFoldableWithIndex) {
    return function (dictHeytingAlgebra) {
        return function (t) {
            return function ($51) {
                return Data_Newtype.unwrap(Data_Newtype.newtypeDisj)(foldMapWithIndex(dictFoldableWithIndex)(Data_Monoid_Disj.monoidDisj(dictHeytingAlgebra))(function (i) {
                    return function ($52) {
                        return Data_Monoid_Disj.Disj(t(i)($52));
                    };
                })($51));
            };
        };
    };
};
var allWithIndex = function (dictFoldableWithIndex) {
    return function (dictHeytingAlgebra) {
        return function (t) {
            return function ($53) {
                return Data_Newtype.unwrap(Data_Newtype.newtypeConj)(foldMapWithIndex(dictFoldableWithIndex)(Data_Monoid_Conj.monoidConj(dictHeytingAlgebra))(function (i) {
                    return function ($54) {
                        return Data_Monoid_Conj.Conj(t(i)($54));
                    };
                })($53));
            };
        };
    };
};
module.exports = {
    FoldableWithIndex: FoldableWithIndex,
    foldrWithIndex: foldrWithIndex,
    foldlWithIndex: foldlWithIndex,
    foldMapWithIndex: foldMapWithIndex,
    foldrWithIndexDefault: foldrWithIndexDefault,
    foldlWithIndexDefault: foldlWithIndexDefault,
    foldMapWithIndexDefaultR: foldMapWithIndexDefaultR,
    foldMapWithIndexDefaultL: foldMapWithIndexDefaultL,
    foldWithIndexM: foldWithIndexM,
    traverseWithIndex_: traverseWithIndex_,
    forWithIndex_: forWithIndex_,
    surroundMapWithIndex: surroundMapWithIndex,
    allWithIndex: allWithIndex,
    anyWithIndex: anyWithIndex,
    findWithIndex: findWithIndex,
    foldrDefault: foldrDefault,
    foldlDefault: foldlDefault,
    foldMapDefault: foldMapDefault,
    foldableWithIndexArray: foldableWithIndexArray,
    foldableWithIndexMaybe: foldableWithIndexMaybe,
    foldableWithIndexFirst: foldableWithIndexFirst,
    foldableWithIndexLast: foldableWithIndexLast,
    foldableWithIndexAdditive: foldableWithIndexAdditive,
    foldableWithIndexDual: foldableWithIndexDual,
    foldableWithIndexDisj: foldableWithIndexDisj,
    foldableWithIndexConj: foldableWithIndexConj,
    foldableWithIndexMultiplicative: foldableWithIndexMultiplicative
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Category/index.js":24,"../Control.Semigroupoid/index.js":51,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.FunctorWithIndex/index.js":100,"../Data.Maybe.First/index.js":110,"../Data.Maybe.Last/index.js":111,"../Data.Maybe/index.js":112,"../Data.Monoid.Additive/index.js":113,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Endo/index.js":117,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Semigroup/index.js":137,"../Data.Unit/index.js":168,"../Prelude/index.js":195}],91:[function(require,module,exports){
"use strict";

exports.foldrArray = function (f) {
  return function (init) {
    return function (xs) {
      var acc = init;
      var len = xs.length;
      for (var i = len - 1; i >= 0; i--) {
        acc = f(xs[i])(acc);
      }
      return acc;
    };
  };
};

exports.foldlArray = function (f) {
  return function (init) {
    return function (xs) {
      var acc = init;
      var len = xs.length;
      for (var i = 0; i < len; i++) {
        acc = f(acc)(xs[i]);
      }
      return acc;
    };
  };
};

},{}],92:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Alt = require("../Control.Alt/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Maybe_First = require("../Data.Maybe.First/index.js");
var Data_Maybe_Last = require("../Data.Maybe.Last/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Monoid_Additive = require("../Data.Monoid.Additive/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Endo = require("../Data.Monoid.Endo/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var Foldable = function (foldMap, foldl, foldr) {
    this.foldMap = foldMap;
    this.foldl = foldl;
    this.foldr = foldr;
};
var foldr = function (dict) {
    return dict.foldr;
};
var indexr = function (dictFoldable) {
    return function (idx) {
        var go = function (a) {
            return function (cursor) {
                if (cursor.elem instanceof Data_Maybe.Just) {
                    return cursor;
                };
                var $106 = cursor.pos === idx;
                if ($106) {
                    return {
                        elem: new Data_Maybe.Just(a),
                        pos: cursor.pos
                    };
                };
                return {
                    pos: cursor.pos + 1 | 0,
                    elem: cursor.elem
                };
            };
        };
        return function ($193) {
            return (function (v) {
                return v.elem;
            })(foldr(dictFoldable)(go)({
                elem: Data_Maybe.Nothing.value,
                pos: 0
            })($193));
        };
    };
};
var $$null = function (dictFoldable) {
    return foldr(dictFoldable)(function (v) {
        return function (v1) {
            return false;
        };
    })(true);
};
var oneOf = function (dictFoldable) {
    return function (dictPlus) {
        return foldr(dictFoldable)(Control_Alt.alt(dictPlus.Alt0()))(Control_Plus.empty(dictPlus));
    };
};
var oneOfMap = function (dictFoldable) {
    return function (dictPlus) {
        return function (f) {
            return foldr(dictFoldable)(function ($194) {
                return Control_Alt.alt(dictPlus.Alt0())(f($194));
            })(Control_Plus.empty(dictPlus));
        };
    };
};
var traverse_ = function (dictApplicative) {
    return function (dictFoldable) {
        return function (f) {
            return foldr(dictFoldable)(function ($195) {
                return Control_Apply.applySecond(dictApplicative.Apply0())(f($195));
            })(Control_Applicative.pure(dictApplicative)(Data_Unit.unit));
        };
    };
};
var for_ = function (dictApplicative) {
    return function (dictFoldable) {
        return Data_Function.flip(traverse_(dictApplicative)(dictFoldable));
    };
};
var sequence_ = function (dictApplicative) {
    return function (dictFoldable) {
        return traverse_(dictApplicative)(dictFoldable)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var foldl = function (dict) {
    return dict.foldl;
};
var indexl = function (dictFoldable) {
    return function (idx) {
        var go = function (cursor) {
            return function (a) {
                if (cursor.elem instanceof Data_Maybe.Just) {
                    return cursor;
                };
                var $109 = cursor.pos === idx;
                if ($109) {
                    return {
                        elem: new Data_Maybe.Just(a),
                        pos: cursor.pos
                    };
                };
                return {
                    pos: cursor.pos + 1 | 0,
                    elem: cursor.elem
                };
            };
        };
        return function ($196) {
            return (function (v) {
                return v.elem;
            })(foldl(dictFoldable)(go)({
                elem: Data_Maybe.Nothing.value,
                pos: 0
            })($196));
        };
    };
};
var intercalate = function (dictFoldable) {
    return function (dictMonoid) {
        return function (sep) {
            return function (xs) {
                var go = function (v) {
                    return function (x) {
                        if (v.init) {
                            return {
                                init: false,
                                acc: x
                            };
                        };
                        return {
                            init: false,
                            acc: Data_Semigroup.append(dictMonoid.Semigroup0())(v.acc)(Data_Semigroup.append(dictMonoid.Semigroup0())(sep)(x))
                        };
                    };
                };
                return (foldl(dictFoldable)(go)({
                    init: true,
                    acc: Data_Monoid.mempty(dictMonoid)
                })(xs)).acc;
            };
        };
    };
};
var length = function (dictFoldable) {
    return function (dictSemiring) {
        return foldl(dictFoldable)(function (c) {
            return function (v) {
                return Data_Semiring.add(dictSemiring)(Data_Semiring.one(dictSemiring))(c);
            };
        })(Data_Semiring.zero(dictSemiring));
    };
};
var maximumBy = function (dictFoldable) {
    return function (cmp) {
        var max$prime = function (v) {
            return function (v1) {
                if (v instanceof Data_Maybe.Nothing) {
                    return new Data_Maybe.Just(v1);
                };
                if (v instanceof Data_Maybe.Just) {
                    return new Data_Maybe.Just((function () {
                        var $116 = Data_Eq.eq(Data_Ordering.eqOrdering)(cmp(v.value0)(v1))(Data_Ordering.GT.value);
                        if ($116) {
                            return v.value0;
                        };
                        return v1;
                    })());
                };
                throw new Error("Failed pattern match at Data.Foldable line 376, column 3 - line 376, column 27: " + [ v.constructor.name, v1.constructor.name ]);
            };
        };
        return foldl(dictFoldable)(max$prime)(Data_Maybe.Nothing.value);
    };
};
var maximum = function (dictOrd) {
    return function (dictFoldable) {
        return maximumBy(dictFoldable)(Data_Ord.compare(dictOrd));
    };
};
var minimumBy = function (dictFoldable) {
    return function (cmp) {
        var min$prime = function (v) {
            return function (v1) {
                if (v instanceof Data_Maybe.Nothing) {
                    return new Data_Maybe.Just(v1);
                };
                if (v instanceof Data_Maybe.Just) {
                    return new Data_Maybe.Just((function () {
                        var $120 = Data_Eq.eq(Data_Ordering.eqOrdering)(cmp(v.value0)(v1))(Data_Ordering.LT.value);
                        if ($120) {
                            return v.value0;
                        };
                        return v1;
                    })());
                };
                throw new Error("Failed pattern match at Data.Foldable line 389, column 3 - line 389, column 27: " + [ v.constructor.name, v1.constructor.name ]);
            };
        };
        return foldl(dictFoldable)(min$prime)(Data_Maybe.Nothing.value);
    };
};
var minimum = function (dictOrd) {
    return function (dictFoldable) {
        return minimumBy(dictFoldable)(Data_Ord.compare(dictOrd));
    };
};
var product = function (dictFoldable) {
    return function (dictSemiring) {
        return foldl(dictFoldable)(Data_Semiring.mul(dictSemiring))(Data_Semiring.one(dictSemiring));
    };
};
var sum = function (dictFoldable) {
    return function (dictSemiring) {
        return foldl(dictFoldable)(Data_Semiring.add(dictSemiring))(Data_Semiring.zero(dictSemiring));
    };
};
var foldableMultiplicative = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(v)(z);
        };
    };
});
var foldableMaybe = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            if (v instanceof Data_Maybe.Nothing) {
                return Data_Monoid.mempty(dictMonoid);
            };
            if (v instanceof Data_Maybe.Just) {
                return f(v.value0);
            };
            throw new Error("Failed pattern match at Data.Foldable line 129, column 1 - line 129, column 41: " + [ f.constructor.name, v.constructor.name ]);
        };
    };
}, function (v) {
    return function (z) {
        return function (v1) {
            if (v1 instanceof Data_Maybe.Nothing) {
                return z;
            };
            if (v1 instanceof Data_Maybe.Just) {
                return v(z)(v1.value0);
            };
            throw new Error("Failed pattern match at Data.Foldable line 129, column 1 - line 129, column 41: " + [ v.constructor.name, z.constructor.name, v1.constructor.name ]);
        };
    };
}, function (v) {
    return function (z) {
        return function (v1) {
            if (v1 instanceof Data_Maybe.Nothing) {
                return z;
            };
            if (v1 instanceof Data_Maybe.Just) {
                return v(v1.value0)(z);
            };
            throw new Error("Failed pattern match at Data.Foldable line 129, column 1 - line 129, column 41: " + [ v.constructor.name, z.constructor.name, v1.constructor.name ]);
        };
    };
});
var foldableDual = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(v)(z);
        };
    };
});
var foldableDisj = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(v)(z);
        };
    };
});
var foldableConj = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(v)(z);
        };
    };
});
var foldableAdditive = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(v)(z);
        };
    };
});
var foldMapDefaultR = function (dictFoldable) {
    return function (dictMonoid) {
        return function (f) {
            return foldr(dictFoldable)(function (x) {
                return function (acc) {
                    return Data_Semigroup.append(dictMonoid.Semigroup0())(f(x))(acc);
                };
            })(Data_Monoid.mempty(dictMonoid));
        };
    };
};
var foldableArray = new Foldable(function (dictMonoid) {
    return foldMapDefaultR(foldableArray)(dictMonoid);
}, $foreign.foldlArray, $foreign.foldrArray);
var foldMapDefaultL = function (dictFoldable) {
    return function (dictMonoid) {
        return function (f) {
            return foldl(dictFoldable)(function (acc) {
                return function (x) {
                    return Data_Semigroup.append(dictMonoid.Semigroup0())(acc)(f(x));
                };
            })(Data_Monoid.mempty(dictMonoid));
        };
    };
};
var foldMap = function (dict) {
    return dict.foldMap;
};
var foldableFirst = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return foldMap(foldableMaybe)(dictMonoid)(f)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return foldl(foldableMaybe)(f)(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return foldr(foldableMaybe)(f)(z)(v);
        };
    };
});
var foldableLast = new Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return foldMap(foldableMaybe)(dictMonoid)(f)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return foldl(foldableMaybe)(f)(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return foldr(foldableMaybe)(f)(z)(v);
        };
    };
});
var foldlDefault = function (dictFoldable) {
    return function (c) {
        return function (u) {
            return function (xs) {
                return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(Data_Newtype.unwrap(Data_Newtype.newtypeDual)(foldMap(dictFoldable)(Data_Monoid_Dual.monoidDual(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn)))(function ($197) {
                    return Data_Monoid_Dual.Dual(Data_Monoid_Endo.Endo(Data_Function.flip(c)($197)));
                })(xs)))(u);
            };
        };
    };
};
var foldrDefault = function (dictFoldable) {
    return function (c) {
        return function (u) {
            return function (xs) {
                return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(foldMap(dictFoldable)(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn))(function ($198) {
                    return Data_Monoid_Endo.Endo(c($198));
                })(xs))(u);
            };
        };
    };
};
var surroundMap = function (dictFoldable) {
    return function (dictSemigroup) {
        return function (d) {
            return function (t) {
                return function (f) {
                    var joined = function (a) {
                        return function (m) {
                            return Data_Semigroup.append(dictSemigroup)(d)(Data_Semigroup.append(dictSemigroup)(t(a))(m));
                        };
                    };
                    return Data_Newtype.unwrap(Data_Newtype.newtypeEndo)(foldMap(dictFoldable)(Data_Monoid_Endo.monoidEndo(Control_Category.categoryFn))(joined)(f))(d);
                };
            };
        };
    };
};
var surround = function (dictFoldable) {
    return function (dictSemigroup) {
        return function (d) {
            return surroundMap(dictFoldable)(dictSemigroup)(d)(Control_Category.identity(Control_Category.categoryFn));
        };
    };
};
var foldM = function (dictFoldable) {
    return function (dictMonad) {
        return function (f) {
            return function (a0) {
                return foldl(dictFoldable)(function (ma) {
                    return function (b) {
                        return Control_Bind.bind(dictMonad.Bind1())(ma)(Data_Function.flip(f)(b));
                    };
                })(Control_Applicative.pure(dictMonad.Applicative0())(a0));
            };
        };
    };
};
var fold = function (dictFoldable) {
    return function (dictMonoid) {
        return foldMap(dictFoldable)(dictMonoid)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var findMap = function (dictFoldable) {
    return function (p) {
        var go = function (v) {
            return function (v1) {
                if (v instanceof Data_Maybe.Nothing) {
                    return p(v1);
                };
                return v;
            };
        };
        return foldl(dictFoldable)(go)(Data_Maybe.Nothing.value);
    };
};
var find = function (dictFoldable) {
    return function (p) {
        var go = function (v) {
            return function (v1) {
                if (v instanceof Data_Maybe.Nothing && p(v1)) {
                    return new Data_Maybe.Just(v1);
                };
                return v;
            };
        };
        return foldl(dictFoldable)(go)(Data_Maybe.Nothing.value);
    };
};
var any = function (dictFoldable) {
    return function (dictHeytingAlgebra) {
        return Data_Newtype.alaF(Data_Functor.functorFn)(Data_Functor.functorFn)(Data_Newtype.newtypeDisj)(Data_Newtype.newtypeDisj)(Data_Monoid_Disj.Disj)(foldMap(dictFoldable)(Data_Monoid_Disj.monoidDisj(dictHeytingAlgebra)));
    };
};
var elem = function (dictFoldable) {
    return function (dictEq) {
        return function ($199) {
            return any(dictFoldable)(Data_HeytingAlgebra.heytingAlgebraBoolean)(Data_Eq.eq(dictEq)($199));
        };
    };
};
var notElem = function (dictFoldable) {
    return function (dictEq) {
        return function (x) {
            return function ($200) {
                return !elem(dictFoldable)(dictEq)(x)($200);
            };
        };
    };
};
var or = function (dictFoldable) {
    return function (dictHeytingAlgebra) {
        return any(dictFoldable)(dictHeytingAlgebra)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var all = function (dictFoldable) {
    return function (dictHeytingAlgebra) {
        return Data_Newtype.alaF(Data_Functor.functorFn)(Data_Functor.functorFn)(Data_Newtype.newtypeConj)(Data_Newtype.newtypeConj)(Data_Monoid_Conj.Conj)(foldMap(dictFoldable)(Data_Monoid_Conj.monoidConj(dictHeytingAlgebra)));
    };
};
var and = function (dictFoldable) {
    return function (dictHeytingAlgebra) {
        return all(dictFoldable)(dictHeytingAlgebra)(Control_Category.identity(Control_Category.categoryFn));
    };
};
module.exports = {
    Foldable: Foldable,
    foldr: foldr,
    foldl: foldl,
    foldMap: foldMap,
    foldrDefault: foldrDefault,
    foldlDefault: foldlDefault,
    foldMapDefaultL: foldMapDefaultL,
    foldMapDefaultR: foldMapDefaultR,
    fold: fold,
    foldM: foldM,
    traverse_: traverse_,
    for_: for_,
    sequence_: sequence_,
    oneOf: oneOf,
    oneOfMap: oneOfMap,
    intercalate: intercalate,
    surroundMap: surroundMap,
    surround: surround,
    and: and,
    or: or,
    all: all,
    any: any,
    sum: sum,
    product: product,
    elem: elem,
    notElem: notElem,
    indexl: indexl,
    indexr: indexr,
    find: find,
    findMap: findMap,
    maximum: maximum,
    maximumBy: maximumBy,
    minimum: minimum,
    minimumBy: minimumBy,
    "null": $$null,
    length: length,
    foldableArray: foldableArray,
    foldableMaybe: foldableMaybe,
    foldableFirst: foldableFirst,
    foldableLast: foldableLast,
    foldableAdditive: foldableAdditive,
    foldableDual: foldableDual,
    foldableDisj: foldableDisj,
    foldableConj: foldableConj,
    foldableMultiplicative: foldableMultiplicative
};

},{"../Control.Alt/index.js":15,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Category/index.js":24,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Eq/index.js":86,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Maybe.First/index.js":110,"../Data.Maybe.Last/index.js":111,"../Data.Maybe/index.js":112,"../Data.Monoid.Additive/index.js":113,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Endo/index.js":117,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Unit/index.js":168,"../Prelude/index.js":195,"./foreign.js":91}],93:[function(require,module,exports){
"use strict";

// module Data.Function.Uncurried

exports.mkFn0 = function (fn) {
  return function () {
    return fn({});
  };
};

exports.mkFn2 = function (fn) {
  /* jshint maxparams: 2 */
  return function (a, b) {
    return fn(a)(b);
  };
};

exports.mkFn3 = function (fn) {
  /* jshint maxparams: 3 */
  return function (a, b, c) {
    return fn(a)(b)(c);
  };
};

exports.mkFn4 = function (fn) {
  /* jshint maxparams: 4 */
  return function (a, b, c, d) {
    return fn(a)(b)(c)(d);
  };
};

exports.mkFn5 = function (fn) {
  /* jshint maxparams: 5 */
  return function (a, b, c, d, e) {
    return fn(a)(b)(c)(d)(e);
  };
};

exports.mkFn6 = function (fn) {
  /* jshint maxparams: 6 */
  return function (a, b, c, d, e, f) {
    return fn(a)(b)(c)(d)(e)(f);
  };
};

exports.mkFn7 = function (fn) {
  /* jshint maxparams: 7 */
  return function (a, b, c, d, e, f, g) {
    return fn(a)(b)(c)(d)(e)(f)(g);
  };
};

exports.mkFn8 = function (fn) {
  /* jshint maxparams: 8 */
  return function (a, b, c, d, e, f, g, h) {
    return fn(a)(b)(c)(d)(e)(f)(g)(h);
  };
};

exports.mkFn9 = function (fn) {
  /* jshint maxparams: 9 */
  return function (a, b, c, d, e, f, g, h, i) {
    return fn(a)(b)(c)(d)(e)(f)(g)(h)(i);
  };
};

exports.mkFn10 = function (fn) {
  /* jshint maxparams: 10 */
  return function (a, b, c, d, e, f, g, h, i, j) {
    return fn(a)(b)(c)(d)(e)(f)(g)(h)(i)(j);
  };
};

exports.runFn0 = function (fn) {
  return fn();
};

exports.runFn2 = function (fn) {
  return function (a) {
    return function (b) {
      return fn(a, b);
    };
  };
};

exports.runFn3 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return fn(a, b, c);
      };
    };
  };
};

exports.runFn4 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return function (d) {
          return fn(a, b, c, d);
        };
      };
    };
  };
};

exports.runFn5 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return function (d) {
          return function (e) {
            return fn(a, b, c, d, e);
          };
        };
      };
    };
  };
};

exports.runFn6 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return function (d) {
          return function (e) {
            return function (f) {
              return fn(a, b, c, d, e, f);
            };
          };
        };
      };
    };
  };
};

exports.runFn7 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return function (d) {
          return function (e) {
            return function (f) {
              return function (g) {
                return fn(a, b, c, d, e, f, g);
              };
            };
          };
        };
      };
    };
  };
};

exports.runFn8 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return function (d) {
          return function (e) {
            return function (f) {
              return function (g) {
                return function (h) {
                  return fn(a, b, c, d, e, f, g, h);
                };
              };
            };
          };
        };
      };
    };
  };
};

exports.runFn9 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return function (d) {
          return function (e) {
            return function (f) {
              return function (g) {
                return function (h) {
                  return function (i) {
                    return fn(a, b, c, d, e, f, g, h, i);
                  };
                };
              };
            };
          };
        };
      };
    };
  };
};

exports.runFn10 = function (fn) {
  return function (a) {
    return function (b) {
      return function (c) {
        return function (d) {
          return function (e) {
            return function (f) {
              return function (g) {
                return function (h) {
                  return function (i) {
                    return function (j) {
                      return fn(a, b, c, d, e, f, g, h, i, j);
                    };
                  };
                };
              };
            };
          };
        };
      };
    };
  };
};

},{}],94:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Unit = require("../Data.Unit/index.js");
var runFn1 = function (f) {
    return f;
};
var mkFn1 = function (f) {
    return f;
};
module.exports = {
    mkFn1: mkFn1,
    runFn1: runFn1,
    mkFn0: $foreign.mkFn0,
    mkFn2: $foreign.mkFn2,
    mkFn3: $foreign.mkFn3,
    mkFn4: $foreign.mkFn4,
    mkFn5: $foreign.mkFn5,
    mkFn6: $foreign.mkFn6,
    mkFn7: $foreign.mkFn7,
    mkFn8: $foreign.mkFn8,
    mkFn9: $foreign.mkFn9,
    mkFn10: $foreign.mkFn10,
    runFn0: $foreign.runFn0,
    runFn2: $foreign.runFn2,
    runFn3: $foreign.runFn3,
    runFn4: $foreign.runFn4,
    runFn5: $foreign.runFn5,
    runFn6: $foreign.runFn6,
    runFn7: $foreign.runFn7,
    runFn8: $foreign.runFn8,
    runFn9: $foreign.runFn9,
    runFn10: $foreign.runFn10
};

},{"../Data.Unit/index.js":168,"./foreign.js":93}],95:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var on = function (f) {
    return function (g) {
        return function (x) {
            return function (y) {
                return f(g(x))(g(y));
            };
        };
    };
};
var flip = function (f) {
    return function (b) {
        return function (a) {
            return f(a)(b);
        };
    };
};
var $$const = function (a) {
    return function (v) {
        return a;
    };
};
var applyN = function (f) {
    var go = function ($copy_n) {
        return function ($copy_acc) {
            var $tco_var_n = $copy_n;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(n, acc) {
                if (n <= 0) {
                    $tco_done = true;
                    return acc;
                };
                if (Data_Boolean.otherwise) {
                    $tco_var_n = n - 1 | 0;
                    $copy_acc = f(acc);
                    return;
                };
                throw new Error("Failed pattern match at Data.Function line 94, column 3 - line 96, column 37: " + [ n.constructor.name, acc.constructor.name ]);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_n, $copy_acc);
            };
            return $tco_result;
        };
    };
    return go;
};
var applyFlipped = function (x) {
    return function (f) {
        return f(x);
    };
};
var apply = function (f) {
    return function (x) {
        return f(x);
    };
};
module.exports = {
    flip: flip,
    "const": $$const,
    apply: apply,
    applyFlipped: applyFlipped,
    applyN: applyN,
    on: on
};

},{"../Control.Category/index.js":24,"../Data.Boolean/index.js":76,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131}],96:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Comonad = require("../Control.Comonad/index.js");
var Control_Extend = require("../Control.Extend/index.js");
var Control_Lazy = require("../Control.Lazy/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_MonadPlus = require("../Control.MonadPlus/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Prelude = require("../Prelude/index.js");
var Unsafe_Coerce = require("../Unsafe.Coerce/index.js");
var App = function (x) {
    return x;
};
var traversableApp = function (dictTraversable) {
    return dictTraversable;
};
var showApp = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(App " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupApp = function (dictApply) {
    return function (dictSemigroup) {
        return new Data_Semigroup.Semigroup(function (v) {
            return function (v1) {
                return Control_Apply.lift2(dictApply)(Data_Semigroup.append(dictSemigroup))(v)(v1);
            };
        });
    };
};
var plusApp = function (dictPlus) {
    return dictPlus;
};
var newtypeApp = new Data_Newtype.Newtype(function (n) {
    return n;
}, App);
var monoidApp = function (dictApplicative) {
    return function (dictMonoid) {
        return new Data_Monoid.Monoid(function () {
            return semigroupApp(dictApplicative.Apply0())(dictMonoid.Semigroup0());
        }, Control_Applicative.pure(dictApplicative)(Data_Monoid.mempty(dictMonoid)));
    };
};
var monadZeroApp = function (dictMonadZero) {
    return dictMonadZero;
};
var monadPlusApp = function (dictMonadPlus) {
    return dictMonadPlus;
};
var monadApp = function (dictMonad) {
    return dictMonad;
};
var lazyApp = function (dictLazy) {
    return dictLazy;
};
var hoistLowerApp = Unsafe_Coerce.unsafeCoerce;
var hoistLiftApp = Unsafe_Coerce.unsafeCoerce;
var hoistApp = function (f) {
    return function (v) {
        return f(v);
    };
};
var functorApp = function (dictFunctor) {
    return dictFunctor;
};
var foldableApp = function (dictFoldable) {
    return dictFoldable;
};
var extendApp = function (dictExtend) {
    return dictExtend;
};
var eqApp = function (dictEq1) {
    return function (dictEq) {
        return new Data_Eq.Eq(function (x) {
            return function (y) {
                return Data_Eq.eq1(dictEq1)(dictEq)(x)(y);
            };
        });
    };
};
var ordApp = function (dictOrd1) {
    return function (dictOrd) {
        return new Data_Ord.Ord(function () {
            return eqApp(dictOrd1.Eq10())(dictOrd.Eq0());
        }, function (x) {
            return function (y) {
                return Data_Ord.compare1(dictOrd1)(dictOrd)(x)(y);
            };
        });
    };
};
var eq1App = function (dictEq1) {
    return new Data_Eq.Eq1(function (dictEq) {
        return Data_Eq.eq(eqApp(dictEq1)(dictEq));
    });
};
var ord1App = function (dictOrd1) {
    return new Data_Ord.Ord1(function () {
        return eq1App(dictOrd1.Eq10());
    }, function (dictOrd) {
        return Data_Ord.compare(ordApp(dictOrd1)(dictOrd));
    });
};
var comonadApp = function (dictComonad) {
    return dictComonad;
};
var bindApp = function (dictBind) {
    return dictBind;
};
var applyApp = function (dictApply) {
    return dictApply;
};
var applicativeApp = function (dictApplicative) {
    return dictApplicative;
};
var alternativeApp = function (dictAlternative) {
    return dictAlternative;
};
var altApp = function (dictAlt) {
    return dictAlt;
};
module.exports = {
    App: App,
    hoistApp: hoistApp,
    hoistLiftApp: hoistLiftApp,
    hoistLowerApp: hoistLowerApp,
    newtypeApp: newtypeApp,
    eqApp: eqApp,
    eq1App: eq1App,
    ordApp: ordApp,
    ord1App: ord1App,
    showApp: showApp,
    semigroupApp: semigroupApp,
    monoidApp: monoidApp,
    functorApp: functorApp,
    applyApp: applyApp,
    applicativeApp: applicativeApp,
    bindApp: bindApp,
    monadApp: monadApp,
    altApp: altApp,
    plusApp: plusApp,
    alternativeApp: alternativeApp,
    monadZeroApp: monadZeroApp,
    monadPlusApp: monadPlusApp,
    lazyApp: lazyApp,
    foldableApp: foldableApp,
    traversableApp: traversableApp,
    extendApp: extendApp,
    comonadApp: comonadApp
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Comonad/index.js":25,"../Control.Extend/index.js":27,"../Control.Lazy/index.js":28,"../Control.Monad/index.js":47,"../Control.MonadPlus/index.js":45,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Data.Traversable/index.js":159,"../Prelude/index.js":195,"../Unsafe.Coerce/index.js":202}],97:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_App = require("../Data.Functor.App/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Prelude = require("../Prelude/index.js");
var Compose = function (x) {
    return x;
};
var showCompose = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Compose " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var newtypeCompose = new Data_Newtype.Newtype(function (n) {
    return n;
}, Compose);
var functorCompose = function (dictFunctor) {
    return function (dictFunctor1) {
        return new Data_Functor.Functor(function (f) {
            return function (v) {
                return Compose(Data_Functor.map(dictFunctor)(Data_Functor.map(dictFunctor1)(f))(v));
            };
        });
    };
};
var foldableCompose = function (dictFoldable) {
    return function (dictFoldable1) {
        return new Data_Foldable.Foldable(function (dictMonoid) {
            return function (f) {
                return function (v) {
                    return Data_Foldable.foldMap(dictFoldable)(dictMonoid)(Data_Foldable.foldMap(dictFoldable1)(dictMonoid)(f))(v);
                };
            };
        }, function (f) {
            return function (i) {
                return function (v) {
                    return Data_Foldable.foldl(dictFoldable)(Data_Foldable.foldl(dictFoldable1)(f))(i)(v);
                };
            };
        }, function (f) {
            return function (i) {
                return function (v) {
                    return Data_Foldable.foldr(dictFoldable)(Data_Function.flip(Data_Foldable.foldr(dictFoldable1)(f)))(i)(v);
                };
            };
        });
    };
};
var traversableCompose = function (dictTraversable) {
    return function (dictTraversable1) {
        return new Data_Traversable.Traversable(function () {
            return foldableCompose(dictTraversable.Foldable1())(dictTraversable1.Foldable1());
        }, function () {
            return functorCompose(dictTraversable.Functor0())(dictTraversable1.Functor0());
        }, function (dictApplicative) {
            return Data_Traversable.traverse(traversableCompose(dictTraversable)(dictTraversable1))(dictApplicative)(Control_Category.identity(Control_Category.categoryFn));
        }, function (dictApplicative) {
            return function (f) {
                return function (v) {
                    return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Compose)(Data_Traversable.traverse(dictTraversable)(dictApplicative)(Data_Traversable.traverse(dictTraversable1)(dictApplicative)(f))(v));
                };
            };
        });
    };
};
var eqCompose = function (dictEq1) {
    return function (dictEq11) {
        return function (dictEq) {
            return new Data_Eq.Eq(function (v) {
                return function (v1) {
                    return Data_Eq.eq1(dictEq1)(Data_Functor_App.eqApp(dictEq11)(dictEq))(Data_Functor_App.hoistLiftApp(v))(Data_Functor_App.hoistLiftApp(v1));
                };
            });
        };
    };
};
var ordCompose = function (dictOrd1) {
    return function (dictOrd11) {
        return function (dictOrd) {
            return new Data_Ord.Ord(function () {
                return eqCompose(dictOrd1.Eq10())(dictOrd11.Eq10())(dictOrd.Eq0());
            }, function (v) {
                return function (v1) {
                    return Data_Ord.compare1(dictOrd1)(Data_Functor_App.ordApp(dictOrd11)(dictOrd))(Data_Functor_App.hoistLiftApp(v))(Data_Functor_App.hoistLiftApp(v1));
                };
            });
        };
    };
};
var eq1Compose = function (dictEq1) {
    return function (dictEq11) {
        return new Data_Eq.Eq1(function (dictEq) {
            return Data_Eq.eq(eqCompose(dictEq1)(dictEq11)(dictEq));
        });
    };
};
var ord1Compose = function (dictOrd1) {
    return function (dictOrd11) {
        return new Data_Ord.Ord1(function () {
            return eq1Compose(dictOrd1.Eq10())(dictOrd11.Eq10());
        }, function (dictOrd) {
            return Data_Ord.compare(ordCompose(dictOrd1)(dictOrd11)(dictOrd));
        });
    };
};
var bihoistCompose = function (dictFunctor) {
    return function (natF) {
        return function (natG) {
            return function (v) {
                return natF(Data_Functor.map(dictFunctor)(natG)(v));
            };
        };
    };
};
var applyCompose = function (dictApply) {
    return function (dictApply1) {
        return new Control_Apply.Apply(function () {
            return functorCompose(dictApply.Functor0())(dictApply1.Functor0());
        }, function (v) {
            return function (v1) {
                return Compose(Control_Apply.apply(dictApply)(Data_Functor.map(dictApply.Functor0())(Control_Apply.apply(dictApply1))(v))(v1));
            };
        });
    };
};
var applicativeCompose = function (dictApplicative) {
    return function (dictApplicative1) {
        return new Control_Applicative.Applicative(function () {
            return applyCompose(dictApplicative.Apply0())(dictApplicative1.Apply0());
        }, function ($75) {
            return Compose(Control_Applicative.pure(dictApplicative)(Control_Applicative.pure(dictApplicative1)($75)));
        });
    };
};
var altCompose = function (dictAlt) {
    return function (dictFunctor) {
        return new Control_Alt.Alt(function () {
            return functorCompose(dictAlt.Functor0())(dictFunctor);
        }, function (v) {
            return function (v1) {
                return Compose(Control_Alt.alt(dictAlt)(v)(v1));
            };
        });
    };
};
var plusCompose = function (dictPlus) {
    return function (dictFunctor) {
        return new Control_Plus.Plus(function () {
            return altCompose(dictPlus.Alt0())(dictFunctor);
        }, Control_Plus.empty(dictPlus));
    };
};
var alternativeCompose = function (dictAlternative) {
    return function (dictApplicative) {
        return new Control_Alternative.Alternative(function () {
            return applicativeCompose(dictAlternative.Applicative0())(dictApplicative);
        }, function () {
            return plusCompose(dictAlternative.Plus1())((dictApplicative.Apply0()).Functor0());
        });
    };
};
module.exports = {
    Compose: Compose,
    bihoistCompose: bihoistCompose,
    newtypeCompose: newtypeCompose,
    eqCompose: eqCompose,
    eq1Compose: eq1Compose,
    ordCompose: ordCompose,
    ord1Compose: ord1Compose,
    showCompose: showCompose,
    functorCompose: functorCompose,
    applyCompose: applyCompose,
    applicativeCompose: applicativeCompose,
    foldableCompose: foldableCompose,
    traversableCompose: traversableCompose,
    altCompose: altCompose,
    plusCompose: plusCompose,
    alternativeCompose: alternativeCompose
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Functor.App/index.js":96,"../Data.Functor/index.js":102,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Data.Traversable/index.js":159,"../Prelude/index.js":195}],98:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid_Additive = require("../Data.Monoid.Additive/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Endo = require("../Data.Monoid.Endo/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Invariant = function (imap) {
    this.imap = imap;
};
var invariantMultiplicative = new Invariant(function (f) {
    return function (v) {
        return function (v1) {
            return f(v1);
        };
    };
});
var invariantEndo = new Invariant(function (ab) {
    return function (ba) {
        return function (v) {
            return function ($31) {
                return ab(v(ba($31)));
            };
        };
    };
});
var invariantDual = new Invariant(function (f) {
    return function (v) {
        return function (v1) {
            return f(v1);
        };
    };
});
var invariantDisj = new Invariant(function (f) {
    return function (v) {
        return function (v1) {
            return f(v1);
        };
    };
});
var invariantConj = new Invariant(function (f) {
    return function (v) {
        return function (v1) {
            return f(v1);
        };
    };
});
var invariantAdditive = new Invariant(function (f) {
    return function (v) {
        return function (v1) {
            return f(v1);
        };
    };
});
var imapF = function (dictFunctor) {
    return function (f) {
        return function (v) {
            return Data_Functor.map(dictFunctor)(f);
        };
    };
};
var invariantArray = new Invariant(imapF(Data_Functor.functorArray));
var invariantFn = new Invariant(imapF(Data_Functor.functorFn));
var imap = function (dict) {
    return dict.imap;
};
module.exports = {
    imap: imap,
    Invariant: Invariant,
    imapF: imapF,
    invariantFn: invariantFn,
    invariantArray: invariantArray,
    invariantAdditive: invariantAdditive,
    invariantConj: invariantConj,
    invariantDisj: invariantDisj,
    invariantDual: invariantDual,
    invariantEndo: invariantEndo,
    invariantMultiplicative: invariantMultiplicative
};

},{"../Control.Semigroupoid/index.js":51,"../Data.Functor/index.js":102,"../Data.Monoid.Additive/index.js":113,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Endo/index.js":117,"../Data.Monoid.Multiplicative/index.js":118}],99:[function(require,module,exports){
"use strict";

exports.mapWithIndexArray = function (f) {
  return function (xs) {
    var l = xs.length;
    var result = Array(l);
    for (var i = 0; i < l; i++) {
      result[i] = f(i)(xs[i]);
    }
    return result;
  };
};

},{}],100:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Maybe_First = require("../Data.Maybe.First/index.js");
var Data_Maybe_Last = require("../Data.Maybe.Last/index.js");
var Data_Monoid_Additive = require("../Data.Monoid.Additive/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var FunctorWithIndex = function (Functor0, mapWithIndex) {
    this.Functor0 = Functor0;
    this.mapWithIndex = mapWithIndex;
};
var mapWithIndex = function (dict) {
    return dict.mapWithIndex;
};
var mapDefault = function (dictFunctorWithIndex) {
    return function (f) {
        return mapWithIndex(dictFunctorWithIndex)(Data_Function["const"](f));
    };
};
var functorWithIndexMultiplicative = new FunctorWithIndex(function () {
    return Data_Monoid_Multiplicative.functorMultiplicative;
}, function (f) {
    return Data_Functor.map(Data_Monoid_Multiplicative.functorMultiplicative)(f(Data_Unit.unit));
});
var functorWithIndexMaybe = new FunctorWithIndex(function () {
    return Data_Maybe.functorMaybe;
}, function (f) {
    return Data_Functor.map(Data_Maybe.functorMaybe)(f(Data_Unit.unit));
});
var functorWithIndexLast = new FunctorWithIndex(function () {
    return Data_Maybe_Last.functorLast;
}, function (f) {
    return Data_Functor.map(Data_Maybe_Last.functorLast)(f(Data_Unit.unit));
});
var functorWithIndexFirst = new FunctorWithIndex(function () {
    return Data_Maybe_First.functorFirst;
}, function (f) {
    return Data_Functor.map(Data_Maybe_First.functorFirst)(f(Data_Unit.unit));
});
var functorWithIndexDual = new FunctorWithIndex(function () {
    return Data_Monoid_Dual.functorDual;
}, function (f) {
    return Data_Functor.map(Data_Monoid_Dual.functorDual)(f(Data_Unit.unit));
});
var functorWithIndexDisj = new FunctorWithIndex(function () {
    return Data_Monoid_Disj.functorDisj;
}, function (f) {
    return Data_Functor.map(Data_Monoid_Disj.functorDisj)(f(Data_Unit.unit));
});
var functorWithIndexConj = new FunctorWithIndex(function () {
    return Data_Monoid_Conj.functorConj;
}, function (f) {
    return Data_Functor.map(Data_Monoid_Conj.functorConj)(f(Data_Unit.unit));
});
var functorWithIndexArray = new FunctorWithIndex(function () {
    return Data_Functor.functorArray;
}, $foreign.mapWithIndexArray);
var functorWithIndexAdditive = new FunctorWithIndex(function () {
    return Data_Monoid_Additive.functorAdditive;
}, function (f) {
    return Data_Functor.map(Data_Monoid_Additive.functorAdditive)(f(Data_Unit.unit));
});
module.exports = {
    FunctorWithIndex: FunctorWithIndex,
    mapWithIndex: mapWithIndex,
    mapDefault: mapDefault,
    functorWithIndexArray: functorWithIndexArray,
    functorWithIndexMaybe: functorWithIndexMaybe,
    functorWithIndexFirst: functorWithIndexFirst,
    functorWithIndexLast: functorWithIndexLast,
    functorWithIndexAdditive: functorWithIndexAdditive,
    functorWithIndexDual: functorWithIndexDual,
    functorWithIndexConj: functorWithIndexConj,
    functorWithIndexDisj: functorWithIndexDisj,
    functorWithIndexMultiplicative: functorWithIndexMultiplicative
};

},{"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Maybe.First/index.js":110,"../Data.Maybe.Last/index.js":111,"../Data.Maybe/index.js":112,"../Data.Monoid.Additive/index.js":113,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Unit/index.js":168,"../Prelude/index.js":195,"./foreign.js":99}],101:[function(require,module,exports){
"use strict";

exports.arrayMap = function (f) {
  return function (arr) {
    var l = arr.length;
    var result = new Array(l);
    for (var i = 0; i < l; i++) {
      result[i] = f(arr[i]);
    }
    return result;
  };
};

},{}],102:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Functor = function (map) {
    this.map = map;
};
var map = function (dict) {
    return dict.map;
};
var mapFlipped = function (dictFunctor) {
    return function (fa) {
        return function (f) {
            return map(dictFunctor)(f)(fa);
        };
    };
};
var $$void = function (dictFunctor) {
    return map(dictFunctor)(Data_Function["const"](Data_Unit.unit));
};
var voidLeft = function (dictFunctor) {
    return function (f) {
        return function (x) {
            return map(dictFunctor)(Data_Function["const"](x))(f);
        };
    };
};
var voidRight = function (dictFunctor) {
    return function (x) {
        return map(dictFunctor)(Data_Function["const"](x));
    };
};
var functorFn = new Functor(Control_Semigroupoid.compose(Control_Semigroupoid.semigroupoidFn));
var functorArray = new Functor($foreign.arrayMap);
var flap = function (dictFunctor) {
    return function (ff) {
        return function (x) {
            return map(dictFunctor)(function (f) {
                return f(x);
            })(ff);
        };
    };
};
module.exports = {
    Functor: Functor,
    map: map,
    mapFlipped: mapFlipped,
    "void": $$void,
    voidRight: voidRight,
    voidLeft: voidLeft,
    flap: flap,
    functorFn: functorFn,
    functorArray: functorArray
};

},{"../Control.Semigroupoid/index.js":51,"../Data.Function/index.js":95,"../Data.Unit/index.js":168,"./foreign.js":101}],103:[function(require,module,exports){
"use strict";

exports.boolConj = function (b1) {
  return function (b2) {
    return b1 && b2;
  };
};

exports.boolDisj = function (b1) {
  return function (b2) {
    return b1 || b2;
  };
};

exports.boolNot = function (b) {
  return !b;
};

},{}],104:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_Row = require("../Type.Data.Row/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var HeytingAlgebra = function (conj, disj, ff, implies, not, tt) {
    this.conj = conj;
    this.disj = disj;
    this.ff = ff;
    this.implies = implies;
    this.not = not;
    this.tt = tt;
};
var HeytingAlgebraRecord = function (conjRecord, disjRecord, ffRecord, impliesRecord, notRecord, ttRecord) {
    this.conjRecord = conjRecord;
    this.disjRecord = disjRecord;
    this.ffRecord = ffRecord;
    this.impliesRecord = impliesRecord;
    this.notRecord = notRecord;
    this.ttRecord = ttRecord;
};
var ttRecord = function (dict) {
    return dict.ttRecord;
};
var tt = function (dict) {
    return dict.tt;
};
var notRecord = function (dict) {
    return dict.notRecord;
};
var not = function (dict) {
    return dict.not;
};
var impliesRecord = function (dict) {
    return dict.impliesRecord;
};
var implies = function (dict) {
    return dict.implies;
};
var heytingAlgebraUnit = new HeytingAlgebra(function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
}, function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
}, Data_Unit.unit, function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
}, function (v) {
    return Data_Unit.unit;
}, Data_Unit.unit);
var heytingAlgebraRecordNil = new HeytingAlgebraRecord(function (v) {
    return function (v1) {
        return function (v2) {
            return {};
        };
    };
}, function (v) {
    return function (v1) {
        return function (v2) {
            return {};
        };
    };
}, function (v) {
    return function (v1) {
        return {};
    };
}, function (v) {
    return function (v1) {
        return function (v2) {
            return {};
        };
    };
}, function (v) {
    return function (v1) {
        return {};
    };
}, function (v) {
    return function (v1) {
        return {};
    };
});
var ffRecord = function (dict) {
    return dict.ffRecord;
};
var ff = function (dict) {
    return dict.ff;
};
var disjRecord = function (dict) {
    return dict.disjRecord;
};
var disj = function (dict) {
    return dict.disj;
};
var heytingAlgebraBoolean = new HeytingAlgebra($foreign.boolConj, $foreign.boolDisj, false, function (a) {
    return function (b) {
        return disj(heytingAlgebraBoolean)(not(heytingAlgebraBoolean)(a))(b);
    };
}, $foreign.boolNot, true);
var conjRecord = function (dict) {
    return dict.conjRecord;
};
var heytingAlgebraRecord = function (dictRowToList) {
    return function (dictHeytingAlgebraRecord) {
        return new HeytingAlgebra(conjRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value), disjRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value), ffRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(Type_Data_Row.RProxy.value), impliesRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value), notRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value), ttRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(Type_Data_Row.RProxy.value));
    };
};
var conj = function (dict) {
    return dict.conj;
};
var heytingAlgebraFunction = function (dictHeytingAlgebra) {
    return new HeytingAlgebra(function (f) {
        return function (g) {
            return function (a) {
                return conj(dictHeytingAlgebra)(f(a))(g(a));
            };
        };
    }, function (f) {
        return function (g) {
            return function (a) {
                return disj(dictHeytingAlgebra)(f(a))(g(a));
            };
        };
    }, function (v) {
        return ff(dictHeytingAlgebra);
    }, function (f) {
        return function (g) {
            return function (a) {
                return implies(dictHeytingAlgebra)(f(a))(g(a));
            };
        };
    }, function (f) {
        return function (a) {
            return not(dictHeytingAlgebra)(f(a));
        };
    }, function (v) {
        return tt(dictHeytingAlgebra);
    });
};
var heytingAlgebraRecordCons = function (dictIsSymbol) {
    return function (dictCons) {
        return function (dictHeytingAlgebraRecord) {
            return function (dictHeytingAlgebra) {
                return new HeytingAlgebraRecord(function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = conjRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var insert = Record_Unsafe.unsafeSet(key);
                            var get = Record_Unsafe.unsafeGet(key);
                            return insert(conj(dictHeytingAlgebra)(get(ra))(get(rb)))(tail);
                        };
                    };
                }, function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = disjRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var insert = Record_Unsafe.unsafeSet(key);
                            var get = Record_Unsafe.unsafeGet(key);
                            return insert(disj(dictHeytingAlgebra)(get(ra))(get(rb)))(tail);
                        };
                    };
                }, function (v) {
                    return function (row) {
                        var tail = ffRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(row);
                        var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                        var insert = Record_Unsafe.unsafeSet(key);
                        return insert(ff(dictHeytingAlgebra))(tail);
                    };
                }, function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = impliesRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var insert = Record_Unsafe.unsafeSet(key);
                            var get = Record_Unsafe.unsafeGet(key);
                            return insert(implies(dictHeytingAlgebra)(get(ra))(get(rb)))(tail);
                        };
                    };
                }, function (v) {
                    return function (row) {
                        var tail = notRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(row);
                        var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                        var insert = Record_Unsafe.unsafeSet(key);
                        var get = Record_Unsafe.unsafeGet(key);
                        return insert(not(dictHeytingAlgebra)(get(row)))(tail);
                    };
                }, function (v) {
                    return function (row) {
                        var tail = ttRecord(dictHeytingAlgebraRecord)(Type_Data_RowList.RLProxy.value)(row);
                        var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                        var insert = Record_Unsafe.unsafeSet(key);
                        return insert(tt(dictHeytingAlgebra))(tail);
                    };
                });
            };
        };
    };
};
module.exports = {
    HeytingAlgebra: HeytingAlgebra,
    tt: tt,
    ff: ff,
    implies: implies,
    conj: conj,
    disj: disj,
    not: not,
    HeytingAlgebraRecord: HeytingAlgebraRecord,
    ffRecord: ffRecord,
    ttRecord: ttRecord,
    impliesRecord: impliesRecord,
    conjRecord: conjRecord,
    disjRecord: disjRecord,
    notRecord: notRecord,
    heytingAlgebraBoolean: heytingAlgebraBoolean,
    heytingAlgebraUnit: heytingAlgebraUnit,
    heytingAlgebraFunction: heytingAlgebraFunction,
    heytingAlgebraRecord: heytingAlgebraRecord,
    heytingAlgebraRecordNil: heytingAlgebraRecordNil,
    heytingAlgebraRecordCons: heytingAlgebraRecordCons
};

},{"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168,"../Record.Unsafe/index.js":197,"../Type.Data.Row/index.js":199,"../Type.Data.RowList/index.js":198,"./foreign.js":103}],105:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Comonad = require("../Control.Comonad/index.js");
var Control_Extend = require("../Control.Extend/index.js");
var Control_Lazy = require("../Control.Lazy/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_BooleanAlgebra = require("../Data.BooleanAlgebra/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_CommutativeRing = require("../Data.CommutativeRing/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_Invariant = require("../Data.Functor.Invariant/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Prelude = require("../Prelude/index.js");
var Identity = function (x) {
    return x;
};
var showIdentity = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Identity " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semiringIdentity = function (dictSemiring) {
    return dictSemiring;
};
var semigroupIdenity = function (dictSemigroup) {
    return dictSemigroup;
};
var ringIdentity = function (dictRing) {
    return dictRing;
};
var ordIdentity = function (dictOrd) {
    return dictOrd;
};
var newtypeIdentity = new Data_Newtype.Newtype(function (n) {
    return n;
}, Identity);
var monoidIdentity = function (dictMonoid) {
    return dictMonoid;
};
var lazyIdentity = function (dictLazy) {
    return dictLazy;
};
var heytingAlgebraIdentity = function (dictHeytingAlgebra) {
    return dictHeytingAlgebra;
};
var functorIdentity = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var invariantIdentity = new Data_Functor_Invariant.Invariant(Data_Functor_Invariant.imapF(functorIdentity));
var foldableIdentity = new Data_Foldable.Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(z)(v);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(v)(z);
        };
    };
});
var traversableIdentity = new Data_Traversable.Traversable(function () {
    return foldableIdentity;
}, function () {
    return functorIdentity;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Identity)(v);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Identity)(f(v));
        };
    };
});
var extendIdentity = new Control_Extend.Extend(function () {
    return functorIdentity;
}, function (f) {
    return function (m) {
        return f(m);
    };
});
var euclideanRingIdentity = function (dictEuclideanRing) {
    return dictEuclideanRing;
};
var eqIdentity = function (dictEq) {
    return dictEq;
};
var eq1Identity = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqIdentity(dictEq));
});
var ord1Identity = new Data_Ord.Ord1(function () {
    return eq1Identity;
}, function (dictOrd) {
    return Data_Ord.compare(ordIdentity(dictOrd));
});
var comonadIdentity = new Control_Comonad.Comonad(function () {
    return extendIdentity;
}, function (v) {
    return v;
});
var commutativeRingIdentity = function (dictCommutativeRing) {
    return dictCommutativeRing;
};
var boundedIdentity = function (dictBounded) {
    return dictBounded;
};
var booleanAlgebraIdentity = function (dictBooleanAlgebra) {
    return dictBooleanAlgebra;
};
var applyIdentity = new Control_Apply.Apply(function () {
    return functorIdentity;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindIdentity = new Control_Bind.Bind(function () {
    return applyIdentity;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeIdentity = new Control_Applicative.Applicative(function () {
    return applyIdentity;
}, Identity);
var monadIdentity = new Control_Monad.Monad(function () {
    return applicativeIdentity;
}, function () {
    return bindIdentity;
});
var altIdentity = new Control_Alt.Alt(function () {
    return functorIdentity;
}, function (x) {
    return function (v) {
        return x;
    };
});
module.exports = {
    Identity: Identity,
    newtypeIdentity: newtypeIdentity,
    eqIdentity: eqIdentity,
    ordIdentity: ordIdentity,
    boundedIdentity: boundedIdentity,
    heytingAlgebraIdentity: heytingAlgebraIdentity,
    booleanAlgebraIdentity: booleanAlgebraIdentity,
    semigroupIdenity: semigroupIdenity,
    monoidIdentity: monoidIdentity,
    semiringIdentity: semiringIdentity,
    euclideanRingIdentity: euclideanRingIdentity,
    ringIdentity: ringIdentity,
    commutativeRingIdentity: commutativeRingIdentity,
    lazyIdentity: lazyIdentity,
    showIdentity: showIdentity,
    eq1Identity: eq1Identity,
    ord1Identity: ord1Identity,
    functorIdentity: functorIdentity,
    invariantIdentity: invariantIdentity,
    altIdentity: altIdentity,
    applyIdentity: applyIdentity,
    applicativeIdentity: applicativeIdentity,
    bindIdentity: bindIdentity,
    monadIdentity: monadIdentity,
    extendIdentity: extendIdentity,
    comonadIdentity: comonadIdentity,
    foldableIdentity: foldableIdentity,
    traversableIdentity: traversableIdentity
};

},{"../Control.Alt/index.js":15,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Comonad/index.js":25,"../Control.Extend/index.js":27,"../Control.Lazy/index.js":28,"../Control.Monad/index.js":47,"../Data.BooleanAlgebra/index.js":75,"../Data.Bounded/index.js":78,"../Data.CommutativeRing/index.js":79,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.Foldable/index.js":92,"../Data.Functor.Invariant/index.js":98,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Data.Traversable/index.js":159,"../Prelude/index.js":195}],106:[function(require,module,exports){
"use strict";

// module Data.Int.Bits

exports.and = function (n1) {
  return function (n2) {
    /* jshint bitwise: false */
    return n1 & n2;
  };
};

exports.or = function (n1) {
  return function (n2) {
    /* jshint bitwise: false */
    return n1 | n2;
  };
};

exports.xor = function (n1) {
  return function (n2) {
    /* jshint bitwise: false */
    return n1 ^ n2;
  };
};

exports.shl = function (n1) {
  return function (n2) {
    /* jshint bitwise: false */
    return n1 << n2;
  };
};

exports.shr = function (n1) {
  return function (n2) {
    /* jshint bitwise: false */
    return n1 >> n2;
  };
};

exports.zshr = function (n1) {
  return function (n2) {
    /* jshint bitwise: false */
    return n1 >>> n2;
  };
};

exports.complement = function (n) {
  /* jshint bitwise: false */
  return ~n;
};

},{}],107:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
module.exports = {
    and: $foreign.and,
    or: $foreign.or,
    xor: $foreign.xor,
    shl: $foreign.shl,
    shr: $foreign.shr,
    zshr: $foreign.zshr,
    complement: $foreign.complement
};

},{"./foreign.js":106}],108:[function(require,module,exports){
"use strict";

exports.fromNumberImpl = function (just) {
  return function (nothing) {
    return function (n) {
      /* jshint bitwise: false */
      return (n | 0) === n ? just(n) : nothing;
    };
  };
};

exports.toNumber = function (n) {
  return n;
};

exports.fromStringAsImpl = function (just) {
  return function (nothing) {
    return function (radix) {
      var digits;
      if (radix < 11) {
        digits = "[0-" + (radix - 1).toString() + "]";
      } else if (radix === 11) {
        digits = "[0-9a]";
      } else {
        digits = "[0-9a-" + String.fromCharCode(86 + radix) + "]";
      }
      var pattern = new RegExp("^[\\+\\-]?" + digits + "+$", "i");

      return function (s) {
        /* jshint bitwise: false */
        if (pattern.test(s)) {
          var i = parseInt(s, radix);
          return (i | 0) === i ? just(i) : nothing;
        } else {
          return nothing;
        }
      };
    };
  };
};

exports.toStringAs = function (radix) {
  return function (i) {
    return i.toString(radix);
  };
};


exports.quot = function (x) {
  return function (y) {
    /* jshint bitwise: false */
    return x / y | 0;
  };
};

exports.rem = function (x) {
  return function (y) {
    return x % y;
  };
};

exports.pow = function (x) {
  return function (y) {
    /* jshint bitwise: false */
    return Math.pow(x,y) | 0;
  };
};

},{}],109:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_CommutativeRing = require("../Data.CommutativeRing/index.js");
var Data_DivisionRing = require("../Data.DivisionRing/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Int_Bits = require("../Data.Int.Bits/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Global = require("../Global/index.js");
var $$Math = require("../Math/index.js");
var Prelude = require("../Prelude/index.js");
var Radix = function (x) {
    return x;
};
var Even = (function () {
    function Even() {

    };
    Even.value = new Even();
    return Even;
})();
var Odd = (function () {
    function Odd() {

    };
    Odd.value = new Odd();
    return Odd;
})();
var showParity = new Data_Show.Show(function (v) {
    if (v instanceof Even) {
        return "Even";
    };
    if (v instanceof Odd) {
        return "Odd";
    };
    throw new Error("Failed pattern match at Data.Int line 112, column 1 - line 112, column 35: " + [ v.constructor.name ]);
});
var radix = function (n) {
    if (n >= 2 && n <= 36) {
        return new Data_Maybe.Just(n);
    };
    if (Data_Boolean.otherwise) {
        return Data_Maybe.Nothing.value;
    };
    throw new Error("Failed pattern match at Data.Int line 193, column 1 - line 193, column 28: " + [ n.constructor.name ]);
};
var odd = function (x) {
    return (x & 1) !== 0;
};
var octal = 8;
var hexadecimal = 16;
var fromStringAs = $foreign.fromStringAsImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var fromString = fromStringAs(10);
var fromNumber = $foreign.fromNumberImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var unsafeClamp = function (x) {
    if (x === Global.infinity) {
        return 0;
    };
    if (x === -Global.infinity) {
        return 0;
    };
    if (x >= $foreign.toNumber(Data_Bounded.top(Data_Bounded.boundedInt))) {
        return Data_Bounded.top(Data_Bounded.boundedInt);
    };
    if (x <= $foreign.toNumber(Data_Bounded.bottom(Data_Bounded.boundedInt))) {
        return Data_Bounded.bottom(Data_Bounded.boundedInt);
    };
    if (Data_Boolean.otherwise) {
        return Data_Maybe.fromMaybe(0)(fromNumber(x));
    };
    throw new Error("Failed pattern match at Data.Int line 66, column 1 - line 66, column 29: " + [ x.constructor.name ]);
};
var round = function ($23) {
    return unsafeClamp($$Math.round($23));
};
var floor = function ($24) {
    return unsafeClamp($$Math.floor($24));
};
var even = function (x) {
    return (x & 1) === 0;
};
var parity = function (n) {
    var $14 = even(n);
    if ($14) {
        return Even.value;
    };
    return Odd.value;
};
var eqParity = new Data_Eq.Eq(function (x) {
    return function (y) {
        if (x instanceof Even && y instanceof Even) {
            return true;
        };
        if (x instanceof Odd && y instanceof Odd) {
            return true;
        };
        return false;
    };
});
var ordParity = new Data_Ord.Ord(function () {
    return eqParity;
}, function (x) {
    return function (y) {
        if (x instanceof Even && y instanceof Even) {
            return Data_Ordering.EQ.value;
        };
        if (x instanceof Even) {
            return Data_Ordering.LT.value;
        };
        if (y instanceof Even) {
            return Data_Ordering.GT.value;
        };
        if (x instanceof Odd && y instanceof Odd) {
            return Data_Ordering.EQ.value;
        };
        throw new Error("Failed pattern match at Data.Int line 110, column 8 - line 110, column 40: " + [ x.constructor.name, y.constructor.name ]);
    };
});
var semiringParity = new Data_Semiring.Semiring(function (x) {
    return function (y) {
        var $19 = Data_Eq.eq(eqParity)(x)(y);
        if ($19) {
            return Even.value;
        };
        return Odd.value;
    };
}, function (v) {
    return function (v1) {
        if (v instanceof Odd && v1 instanceof Odd) {
            return Odd.value;
        };
        return Even.value;
    };
}, Odd.value, Even.value);
var ringParity = new Data_Ring.Ring(function () {
    return semiringParity;
}, Data_Semiring.add(semiringParity));
var divisionRingParity = new Data_DivisionRing.DivisionRing(function () {
    return ringParity;
}, Control_Category.identity(Control_Category.categoryFn));
var decimal = 10;
var commutativeRingParity = new Data_CommutativeRing.CommutativeRing(function () {
    return ringParity;
});
var euclideanRingParity = new Data_EuclideanRing.EuclideanRing(function () {
    return commutativeRingParity;
}, function (v) {
    if (v instanceof Even) {
        return 0;
    };
    if (v instanceof Odd) {
        return 1;
    };
    throw new Error("Failed pattern match at Data.Int line 132, column 1 - line 132, column 53: " + [ v.constructor.name ]);
}, function (x) {
    return function (v) {
        return x;
    };
}, function (v) {
    return function (v1) {
        return Even.value;
    };
});
var ceil = function ($25) {
    return unsafeClamp($$Math.ceil($25));
};
var boundedParity = new Data_Bounded.Bounded(function () {
    return ordParity;
}, Even.value, Odd.value);
var binary = 2;
var base36 = 36;
module.exports = {
    fromNumber: fromNumber,
    ceil: ceil,
    floor: floor,
    round: round,
    fromString: fromString,
    radix: radix,
    binary: binary,
    octal: octal,
    decimal: decimal,
    hexadecimal: hexadecimal,
    base36: base36,
    fromStringAs: fromStringAs,
    Even: Even,
    Odd: Odd,
    parity: parity,
    even: even,
    odd: odd,
    eqParity: eqParity,
    ordParity: ordParity,
    showParity: showParity,
    boundedParity: boundedParity,
    semiringParity: semiringParity,
    ringParity: ringParity,
    commutativeRingParity: commutativeRingParity,
    euclideanRingParity: euclideanRingParity,
    divisionRingParity: divisionRingParity,
    toNumber: $foreign.toNumber,
    toStringAs: $foreign.toStringAs,
    quot: $foreign.quot,
    rem: $foreign.rem,
    pow: $foreign.pow
};

},{"../Control.Category/index.js":24,"../Control.Semigroupoid/index.js":51,"../Data.Boolean/index.js":76,"../Data.Bounded/index.js":78,"../Data.CommutativeRing/index.js":79,"../Data.DivisionRing/index.js":81,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.HeytingAlgebra/index.js":104,"../Data.Int.Bits/index.js":107,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Global/index.js":187,"../Math/index.js":190,"../Prelude/index.js":195,"./foreign.js":108}],110:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Extend = require("../Control.Extend/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_Invariant = require("../Data.Functor.Invariant/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var First = function (x) {
    return x;
};
var showFirst = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "First (" + (Data_Show.show(Data_Maybe.showMaybe(dictShow))(v) + ")");
    });
};
var semigroupFirst = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        if (v instanceof Data_Maybe.Just) {
            return v;
        };
        return v1;
    };
});
var ordFirst = function (dictOrd) {
    return Data_Maybe.ordMaybe(dictOrd);
};
var ord1First = Data_Maybe.ord1Maybe;
var newtypeFirst = new Data_Newtype.Newtype(function (n) {
    return n;
}, First);
var monoidFirst = new Data_Monoid.Monoid(function () {
    return semigroupFirst;
}, Data_Maybe.Nothing.value);
var monadFirst = Data_Maybe.monadMaybe;
var invariantFirst = Data_Maybe.invariantMaybe;
var functorFirst = Data_Maybe.functorMaybe;
var extendFirst = Data_Maybe.extendMaybe;
var eqFirst = function (dictEq) {
    return Data_Maybe.eqMaybe(dictEq);
};
var eq1First = Data_Maybe.eq1Maybe;
var boundedFirst = function (dictBounded) {
    return Data_Maybe.boundedMaybe(dictBounded);
};
var bindFirst = Data_Maybe.bindMaybe;
var applyFirst = Data_Maybe.applyMaybe;
var applicativeFirst = Data_Maybe.applicativeMaybe;
var altFirst = new Control_Alt.Alt(function () {
    return functorFirst;
}, Data_Semigroup.append(semigroupFirst));
var plusFirst = new Control_Plus.Plus(function () {
    return altFirst;
}, Data_Monoid.mempty(monoidFirst));
var alternativeFirst = new Control_Alternative.Alternative(function () {
    return applicativeFirst;
}, function () {
    return plusFirst;
});
var monadZeroFirst = new Control_MonadZero.MonadZero(function () {
    return alternativeFirst;
}, function () {
    return monadFirst;
});
module.exports = {
    First: First,
    newtypeFirst: newtypeFirst,
    eqFirst: eqFirst,
    eq1First: eq1First,
    ordFirst: ordFirst,
    ord1First: ord1First,
    boundedFirst: boundedFirst,
    functorFirst: functorFirst,
    invariantFirst: invariantFirst,
    applyFirst: applyFirst,
    applicativeFirst: applicativeFirst,
    bindFirst: bindFirst,
    monadFirst: monadFirst,
    extendFirst: extendFirst,
    showFirst: showFirst,
    semigroupFirst: semigroupFirst,
    monoidFirst: monoidFirst,
    altFirst: altFirst,
    plusFirst: plusFirst,
    alternativeFirst: alternativeFirst,
    monadZeroFirst: monadZeroFirst
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Extend/index.js":27,"../Control.Monad/index.js":47,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor.Invariant/index.js":98,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],111:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Extend = require("../Control.Extend/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_Invariant = require("../Data.Functor.Invariant/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Last = function (x) {
    return x;
};
var showLast = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Last " + (Data_Show.show(Data_Maybe.showMaybe(dictShow))(v) + ")");
    });
};
var semigroupLast = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        if (v1 instanceof Data_Maybe.Just) {
            return v1;
        };
        if (v1 instanceof Data_Maybe.Nothing) {
            return v;
        };
        throw new Error("Failed pattern match at Data.Maybe.Last line 52, column 1 - line 52, column 45: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var ordLast = function (dictOrd) {
    return Data_Maybe.ordMaybe(dictOrd);
};
var ord1Last = Data_Maybe.ord1Maybe;
var newtypeLast = new Data_Newtype.Newtype(function (n) {
    return n;
}, Last);
var monoidLast = new Data_Monoid.Monoid(function () {
    return semigroupLast;
}, Data_Maybe.Nothing.value);
var monadLast = Data_Maybe.monadMaybe;
var invariantLast = Data_Maybe.invariantMaybe;
var functorLast = Data_Maybe.functorMaybe;
var extendLast = Data_Maybe.extendMaybe;
var eqLast = function (dictEq) {
    return Data_Maybe.eqMaybe(dictEq);
};
var eq1Last = Data_Maybe.eq1Maybe;
var boundedLast = function (dictBounded) {
    return Data_Maybe.boundedMaybe(dictBounded);
};
var bindLast = Data_Maybe.bindMaybe;
var applyLast = Data_Maybe.applyMaybe;
var applicativeLast = Data_Maybe.applicativeMaybe;
var altLast = new Control_Alt.Alt(function () {
    return functorLast;
}, Data_Semigroup.append(semigroupLast));
var plusLast = new Control_Plus.Plus(function () {
    return altLast;
}, Data_Monoid.mempty(monoidLast));
var alternativeLast = new Control_Alternative.Alternative(function () {
    return applicativeLast;
}, function () {
    return plusLast;
});
var monadZeroLast = new Control_MonadZero.MonadZero(function () {
    return alternativeLast;
}, function () {
    return monadLast;
});
module.exports = {
    Last: Last,
    newtypeLast: newtypeLast,
    eqLast: eqLast,
    eq1Last: eq1Last,
    ordLast: ordLast,
    ord1Last: ord1Last,
    boundedLast: boundedLast,
    functorLast: functorLast,
    invariantLast: invariantLast,
    applyLast: applyLast,
    applicativeLast: applicativeLast,
    bindLast: bindLast,
    monadLast: monadLast,
    extendLast: extendLast,
    showLast: showLast,
    semigroupLast: semigroupLast,
    monoidLast: monoidLast,
    altLast: altLast,
    plusLast: plusLast,
    alternativeLast: alternativeLast,
    monadZeroLast: monadZeroLast
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Extend/index.js":27,"../Control.Monad/index.js":47,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor.Invariant/index.js":98,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],112:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Extend = require("../Control.Extend/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_MonadZero = require("../Control.MonadZero/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_Invariant = require("../Data.Functor.Invariant/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var Nothing = (function () {
    function Nothing() {

    };
    Nothing.value = new Nothing();
    return Nothing;
})();
var Just = (function () {
    function Just(value0) {
        this.value0 = value0;
    };
    Just.create = function (value0) {
        return new Just(value0);
    };
    return Just;
})();
var showMaybe = function (dictShow) {
    return new Data_Show.Show(function (v) {
        if (v instanceof Just) {
            return "(Just " + (Data_Show.show(dictShow)(v.value0) + ")");
        };
        if (v instanceof Nothing) {
            return "Nothing";
        };
        throw new Error("Failed pattern match at Data.Maybe line 206, column 1 - line 206, column 47: " + [ v.constructor.name ]);
    });
};
var semigroupMaybe = function (dictSemigroup) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            if (v instanceof Nothing) {
                return v1;
            };
            if (v1 instanceof Nothing) {
                return v;
            };
            if (v instanceof Just && v1 instanceof Just) {
                return new Just(Data_Semigroup.append(dictSemigroup)(v.value0)(v1.value0));
            };
            throw new Error("Failed pattern match at Data.Maybe line 175, column 1 - line 175, column 62: " + [ v.constructor.name, v1.constructor.name ]);
        };
    });
};
var optional = function (dictAlternative) {
    return function (a) {
        return Control_Alt.alt((dictAlternative.Plus1()).Alt0())(Data_Functor.map(((dictAlternative.Plus1()).Alt0()).Functor0())(Just.create)(a))(Control_Applicative.pure(dictAlternative.Applicative0())(Nothing.value));
    };
};
var monoidMaybe = function (dictSemigroup) {
    return new Data_Monoid.Monoid(function () {
        return semigroupMaybe(dictSemigroup);
    }, Nothing.value);
};
var maybe$prime = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof Nothing) {
                return v(Data_Unit.unit);
            };
            if (v2 instanceof Just) {
                return v1(v2.value0);
            };
            throw new Error("Failed pattern match at Data.Maybe line 231, column 1 - line 231, column 62: " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};
var maybe = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof Nothing) {
                return v;
            };
            if (v2 instanceof Just) {
                return v1(v2.value0);
            };
            throw new Error("Failed pattern match at Data.Maybe line 218, column 1 - line 218, column 51: " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};
var isNothing = maybe(true)(Data_Function["const"](false));
var isJust = maybe(false)(Data_Function["const"](true));
var functorMaybe = new Data_Functor.Functor(function (v) {
    return function (v1) {
        if (v1 instanceof Just) {
            return new Just(v(v1.value0));
        };
        return Nothing.value;
    };
});
var invariantMaybe = new Data_Functor_Invariant.Invariant(Data_Functor_Invariant.imapF(functorMaybe));
var fromMaybe$prime = function (a) {
    return maybe$prime(a)(Control_Category.identity(Control_Category.categoryFn));
};
var fromMaybe = function (a) {
    return maybe(a)(Control_Category.identity(Control_Category.categoryFn));
};
var fromJust = function (dictPartial) {
    return function (v) {
        var $__unused = function (dictPartial1) {
            return function ($dollar35) {
                return $dollar35;
            };
        };
        return $__unused(dictPartial)((function () {
            if (v instanceof Just) {
                return v.value0;
            };
            throw new Error("Failed pattern match at Data.Maybe line 269, column 1 - line 269, column 46: " + [ v.constructor.name ]);
        })());
    };
};
var extendMaybe = new Control_Extend.Extend(function () {
    return functorMaybe;
}, function (v) {
    return function (v1) {
        if (v1 instanceof Nothing) {
            return Nothing.value;
        };
        return new Just(v(v1));
    };
});
var eqMaybe = function (dictEq) {
    return new Data_Eq.Eq(function (x) {
        return function (y) {
            if (x instanceof Nothing && y instanceof Nothing) {
                return true;
            };
            if (x instanceof Just && y instanceof Just) {
                return Data_Eq.eq(dictEq)(x.value0)(y.value0);
            };
            return false;
        };
    });
};
var ordMaybe = function (dictOrd) {
    return new Data_Ord.Ord(function () {
        return eqMaybe(dictOrd.Eq0());
    }, function (x) {
        return function (y) {
            if (x instanceof Nothing && y instanceof Nothing) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Nothing) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Nothing) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Just && y instanceof Just) {
                return Data_Ord.compare(dictOrd)(x.value0)(y.value0);
            };
            throw new Error("Failed pattern match at Data.Maybe line 195, column 8 - line 195, column 51: " + [ x.constructor.name, y.constructor.name ]);
        };
    });
};
var eq1Maybe = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqMaybe(dictEq));
});
var ord1Maybe = new Data_Ord.Ord1(function () {
    return eq1Maybe;
}, function (dictOrd) {
    return Data_Ord.compare(ordMaybe(dictOrd));
});
var boundedMaybe = function (dictBounded) {
    return new Data_Bounded.Bounded(function () {
        return ordMaybe(dictBounded.Ord0());
    }, Nothing.value, new Just(Data_Bounded.top(dictBounded)));
};
var applyMaybe = new Control_Apply.Apply(function () {
    return functorMaybe;
}, function (v) {
    return function (v1) {
        if (v instanceof Just) {
            return Data_Functor.map(functorMaybe)(v.value0)(v1);
        };
        if (v instanceof Nothing) {
            return Nothing.value;
        };
        throw new Error("Failed pattern match at Data.Maybe line 67, column 1 - line 67, column 35: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var bindMaybe = new Control_Bind.Bind(function () {
    return applyMaybe;
}, function (v) {
    return function (v1) {
        if (v instanceof Just) {
            return v1(v.value0);
        };
        if (v instanceof Nothing) {
            return Nothing.value;
        };
        throw new Error("Failed pattern match at Data.Maybe line 126, column 1 - line 126, column 33: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var applicativeMaybe = new Control_Applicative.Applicative(function () {
    return applyMaybe;
}, Just.create);
var monadMaybe = new Control_Monad.Monad(function () {
    return applicativeMaybe;
}, function () {
    return bindMaybe;
});
var altMaybe = new Control_Alt.Alt(function () {
    return functorMaybe;
}, function (v) {
    return function (v1) {
        if (v instanceof Nothing) {
            return v1;
        };
        return v;
    };
});
var plusMaybe = new Control_Plus.Plus(function () {
    return altMaybe;
}, Nothing.value);
var alternativeMaybe = new Control_Alternative.Alternative(function () {
    return applicativeMaybe;
}, function () {
    return plusMaybe;
});
var monadZeroMaybe = new Control_MonadZero.MonadZero(function () {
    return alternativeMaybe;
}, function () {
    return monadMaybe;
});
module.exports = {
    Nothing: Nothing,
    Just: Just,
    maybe: maybe,
    "maybe'": maybe$prime,
    fromMaybe: fromMaybe,
    "fromMaybe'": fromMaybe$prime,
    isJust: isJust,
    isNothing: isNothing,
    fromJust: fromJust,
    optional: optional,
    functorMaybe: functorMaybe,
    applyMaybe: applyMaybe,
    applicativeMaybe: applicativeMaybe,
    altMaybe: altMaybe,
    plusMaybe: plusMaybe,
    alternativeMaybe: alternativeMaybe,
    bindMaybe: bindMaybe,
    monadMaybe: monadMaybe,
    monadZeroMaybe: monadZeroMaybe,
    extendMaybe: extendMaybe,
    invariantMaybe: invariantMaybe,
    semigroupMaybe: semigroupMaybe,
    monoidMaybe: monoidMaybe,
    eqMaybe: eqMaybe,
    eq1Maybe: eq1Maybe,
    ordMaybe: ordMaybe,
    ord1Maybe: ord1Maybe,
    boundedMaybe: boundedMaybe,
    showMaybe: showMaybe
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Category/index.js":24,"../Control.Extend/index.js":27,"../Control.Monad/index.js":47,"../Control.MonadZero/index.js":46,"../Control.Plus/index.js":50,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Function/index.js":95,"../Data.Functor.Invariant/index.js":98,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Data.Unit/index.js":168,"../Prelude/index.js":195}],113:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Additive = function (x) {
    return x;
};
var showAdditive = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Additive " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupAdditive = function (dictSemiring) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Data_Semiring.add(dictSemiring)(v)(v1);
        };
    });
};
var ordAdditive = function (dictOrd) {
    return dictOrd;
};
var monoidAdditive = function (dictSemiring) {
    return new Data_Monoid.Monoid(function () {
        return semigroupAdditive(dictSemiring);
    }, Data_Semiring.zero(dictSemiring));
};
var functorAdditive = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var eqAdditive = function (dictEq) {
    return dictEq;
};
var eq1Additive = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqAdditive(dictEq));
});
var ord1Additive = new Data_Ord.Ord1(function () {
    return eq1Additive;
}, function (dictOrd) {
    return Data_Ord.compare(ordAdditive(dictOrd));
});
var boundedAdditive = function (dictBounded) {
    return dictBounded;
};
var applyAdditive = new Control_Apply.Apply(function () {
    return functorAdditive;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindAdditive = new Control_Bind.Bind(function () {
    return applyAdditive;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeAdditive = new Control_Applicative.Applicative(function () {
    return applyAdditive;
}, Additive);
var monadAdditive = new Control_Monad.Monad(function () {
    return applicativeAdditive;
}, function () {
    return bindAdditive;
});
module.exports = {
    Additive: Additive,
    eqAdditive: eqAdditive,
    eq1Additive: eq1Additive,
    ordAdditive: ordAdditive,
    ord1Additive: ord1Additive,
    boundedAdditive: boundedAdditive,
    showAdditive: showAdditive,
    functorAdditive: functorAdditive,
    applyAdditive: applyAdditive,
    applicativeAdditive: applicativeAdditive,
    bindAdditive: bindAdditive,
    monadAdditive: monadAdditive,
    semigroupAdditive: semigroupAdditive,
    monoidAdditive: monoidAdditive
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Prelude/index.js":195}],114:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Conj = function (x) {
    return x;
};
var showConj = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Conj " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semiringConj = function (dictHeytingAlgebra) {
    return new Data_Semiring.Semiring(function (v) {
        return function (v1) {
            return Data_HeytingAlgebra.conj(dictHeytingAlgebra)(v)(v1);
        };
    }, function (v) {
        return function (v1) {
            return Data_HeytingAlgebra.disj(dictHeytingAlgebra)(v)(v1);
        };
    }, Data_HeytingAlgebra.ff(dictHeytingAlgebra), Data_HeytingAlgebra.tt(dictHeytingAlgebra));
};
var semigroupConj = function (dictHeytingAlgebra) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Data_HeytingAlgebra.conj(dictHeytingAlgebra)(v)(v1);
        };
    });
};
var ordConj = function (dictOrd) {
    return dictOrd;
};
var monoidConj = function (dictHeytingAlgebra) {
    return new Data_Monoid.Monoid(function () {
        return semigroupConj(dictHeytingAlgebra);
    }, Data_HeytingAlgebra.tt(dictHeytingAlgebra));
};
var functorConj = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var eqConj = function (dictEq) {
    return dictEq;
};
var eq1Conj = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqConj(dictEq));
});
var ord1Conj = new Data_Ord.Ord1(function () {
    return eq1Conj;
}, function (dictOrd) {
    return Data_Ord.compare(ordConj(dictOrd));
});
var boundedConj = function (dictBounded) {
    return dictBounded;
};
var applyConj = new Control_Apply.Apply(function () {
    return functorConj;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindConj = new Control_Bind.Bind(function () {
    return applyConj;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeConj = new Control_Applicative.Applicative(function () {
    return applyConj;
}, Conj);
var monadConj = new Control_Monad.Monad(function () {
    return applicativeConj;
}, function () {
    return bindConj;
});
module.exports = {
    Conj: Conj,
    eqConj: eqConj,
    eq1Conj: eq1Conj,
    ordConj: ordConj,
    ord1Conj: ord1Conj,
    boundedConj: boundedConj,
    showConj: showConj,
    functorConj: functorConj,
    applyConj: applyConj,
    applicativeConj: applicativeConj,
    bindConj: bindConj,
    monadConj: monadConj,
    semigroupConj: semigroupConj,
    monoidConj: monoidConj,
    semiringConj: semiringConj
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Prelude/index.js":195}],115:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Disj = function (x) {
    return x;
};
var showDisj = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Disj " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semiringDisj = function (dictHeytingAlgebra) {
    return new Data_Semiring.Semiring(function (v) {
        return function (v1) {
            return Data_HeytingAlgebra.disj(dictHeytingAlgebra)(v)(v1);
        };
    }, function (v) {
        return function (v1) {
            return Data_HeytingAlgebra.conj(dictHeytingAlgebra)(v)(v1);
        };
    }, Data_HeytingAlgebra.tt(dictHeytingAlgebra), Data_HeytingAlgebra.ff(dictHeytingAlgebra));
};
var semigroupDisj = function (dictHeytingAlgebra) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Data_HeytingAlgebra.disj(dictHeytingAlgebra)(v)(v1);
        };
    });
};
var ordDisj = function (dictOrd) {
    return dictOrd;
};
var monoidDisj = function (dictHeytingAlgebra) {
    return new Data_Monoid.Monoid(function () {
        return semigroupDisj(dictHeytingAlgebra);
    }, Data_HeytingAlgebra.ff(dictHeytingAlgebra));
};
var functorDisj = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var eqDisj = function (dictEq) {
    return dictEq;
};
var eq1Disj = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqDisj(dictEq));
});
var ord1Disj = new Data_Ord.Ord1(function () {
    return eq1Disj;
}, function (dictOrd) {
    return Data_Ord.compare(ordDisj(dictOrd));
});
var boundedDisj = function (dictBounded) {
    return dictBounded;
};
var applyDisj = new Control_Apply.Apply(function () {
    return functorDisj;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindDisj = new Control_Bind.Bind(function () {
    return applyDisj;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeDisj = new Control_Applicative.Applicative(function () {
    return applyDisj;
}, Disj);
var monadDisj = new Control_Monad.Monad(function () {
    return applicativeDisj;
}, function () {
    return bindDisj;
});
module.exports = {
    Disj: Disj,
    eqDisj: eqDisj,
    eq1Disj: eq1Disj,
    ordDisj: ordDisj,
    ord1Disj: ord1Disj,
    boundedDisj: boundedDisj,
    showDisj: showDisj,
    functorDisj: functorDisj,
    applyDisj: applyDisj,
    applicativeDisj: applicativeDisj,
    bindDisj: bindDisj,
    monadDisj: monadDisj,
    semigroupDisj: semigroupDisj,
    monoidDisj: monoidDisj,
    semiringDisj: semiringDisj
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Prelude/index.js":195}],116:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Dual = function (x) {
    return x;
};
var showDual = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Dual " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupDual = function (dictSemigroup) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Data_Semigroup.append(dictSemigroup)(v1)(v);
        };
    });
};
var ordDual = function (dictOrd) {
    return dictOrd;
};
var monoidDual = function (dictMonoid) {
    return new Data_Monoid.Monoid(function () {
        return semigroupDual(dictMonoid.Semigroup0());
    }, Data_Monoid.mempty(dictMonoid));
};
var functorDual = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var eqDual = function (dictEq) {
    return dictEq;
};
var eq1Dual = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqDual(dictEq));
});
var ord1Dual = new Data_Ord.Ord1(function () {
    return eq1Dual;
}, function (dictOrd) {
    return Data_Ord.compare(ordDual(dictOrd));
});
var boundedDual = function (dictBounded) {
    return dictBounded;
};
var applyDual = new Control_Apply.Apply(function () {
    return functorDual;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindDual = new Control_Bind.Bind(function () {
    return applyDual;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeDual = new Control_Applicative.Applicative(function () {
    return applyDual;
}, Dual);
var monadDual = new Control_Monad.Monad(function () {
    return applicativeDual;
}, function () {
    return bindDual;
});
module.exports = {
    Dual: Dual,
    eqDual: eqDual,
    eq1Dual: eq1Dual,
    ordDual: ordDual,
    ord1Dual: ord1Dual,
    boundedDual: boundedDual,
    showDual: showDual,
    functorDual: functorDual,
    applyDual: applyDual,
    applicativeDual: applicativeDual,
    bindDual: bindDual,
    monadDual: monadDual,
    semigroupDual: semigroupDual,
    monoidDual: monoidDual
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],117:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Endo = function (x) {
    return x;
};
var showEndo = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Endo " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupEndo = function (dictSemigroupoid) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Control_Semigroupoid.compose(dictSemigroupoid)(v)(v1);
        };
    });
};
var ordEndo = function (dictOrd) {
    return dictOrd;
};
var monoidEndo = function (dictCategory) {
    return new Data_Monoid.Monoid(function () {
        return semigroupEndo(dictCategory.Semigroupoid0());
    }, Control_Category.identity(dictCategory));
};
var eqEndo = function (dictEq) {
    return dictEq;
};
var boundedEndo = function (dictBounded) {
    return dictBounded;
};
module.exports = {
    Endo: Endo,
    eqEndo: eqEndo,
    ordEndo: ordEndo,
    boundedEndo: boundedEndo,
    showEndo: showEndo,
    semigroupEndo: semigroupEndo,
    monoidEndo: monoidEndo
};

},{"../Control.Category/index.js":24,"../Control.Semigroupoid/index.js":51,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],118:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Multiplicative = function (x) {
    return x;
};
var showMultiplicative = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Multiplicative " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupMultiplicative = function (dictSemiring) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Data_Semiring.mul(dictSemiring)(v)(v1);
        };
    });
};
var ordMultiplicative = function (dictOrd) {
    return dictOrd;
};
var monoidMultiplicative = function (dictSemiring) {
    return new Data_Monoid.Monoid(function () {
        return semigroupMultiplicative(dictSemiring);
    }, Data_Semiring.one(dictSemiring));
};
var functorMultiplicative = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var eqMultiplicative = function (dictEq) {
    return dictEq;
};
var eq1Multiplicative = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqMultiplicative(dictEq));
});
var ord1Multiplicative = new Data_Ord.Ord1(function () {
    return eq1Multiplicative;
}, function (dictOrd) {
    return Data_Ord.compare(ordMultiplicative(dictOrd));
});
var boundedMultiplicative = function (dictBounded) {
    return dictBounded;
};
var applyMultiplicative = new Control_Apply.Apply(function () {
    return functorMultiplicative;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindMultiplicative = new Control_Bind.Bind(function () {
    return applyMultiplicative;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeMultiplicative = new Control_Applicative.Applicative(function () {
    return applyMultiplicative;
}, Multiplicative);
var monadMultiplicative = new Control_Monad.Monad(function () {
    return applicativeMultiplicative;
}, function () {
    return bindMultiplicative;
});
module.exports = {
    Multiplicative: Multiplicative,
    eqMultiplicative: eqMultiplicative,
    eq1Multiplicative: eq1Multiplicative,
    ordMultiplicative: ordMultiplicative,
    ord1Multiplicative: ord1Multiplicative,
    boundedMultiplicative: boundedMultiplicative,
    showMultiplicative: showMultiplicative,
    functorMultiplicative: functorMultiplicative,
    applyMultiplicative: applyMultiplicative,
    applicativeMultiplicative: applicativeMultiplicative,
    bindMultiplicative: bindMultiplicative,
    monadMultiplicative: monadMultiplicative,
    semigroupMultiplicative: semigroupMultiplicative,
    monoidMultiplicative: monoidMultiplicative
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Prelude/index.js":195}],119:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var Monoid = function (Semigroup0, mempty) {
    this.Semigroup0 = Semigroup0;
    this.mempty = mempty;
};
var MonoidRecord = function (SemigroupRecord0, memptyRecord) {
    this.SemigroupRecord0 = SemigroupRecord0;
    this.memptyRecord = memptyRecord;
};
var monoidUnit = new Monoid(function () {
    return Data_Semigroup.semigroupUnit;
}, Data_Unit.unit);
var monoidString = new Monoid(function () {
    return Data_Semigroup.semigroupString;
}, "");
var monoidRecordNil = new MonoidRecord(function () {
    return Data_Semigroup.semigroupRecordNil;
}, function (v) {
    return {};
});
var monoidOrdering = new Monoid(function () {
    return Data_Ordering.semigroupOrdering;
}, Data_Ordering.EQ.value);
var monoidArray = new Monoid(function () {
    return Data_Semigroup.semigroupArray;
}, [  ]);
var memptyRecord = function (dict) {
    return dict.memptyRecord;
};
var monoidRecord = function (dictRowToList) {
    return function (dictMonoidRecord) {
        return new Monoid(function () {
            return Data_Semigroup.semigroupRecord(dictRowToList)(dictMonoidRecord.SemigroupRecord0());
        }, memptyRecord(dictMonoidRecord)(Type_Data_RowList.RLProxy.value));
    };
};
var mempty = function (dict) {
    return dict.mempty;
};
var monoidFn = function (dictMonoid) {
    return new Monoid(function () {
        return Data_Semigroup.semigroupFn(dictMonoid.Semigroup0());
    }, function (v) {
        return mempty(dictMonoid);
    });
};
var monoidRecordCons = function (dictIsSymbol) {
    return function (dictMonoid) {
        return function (dictCons) {
            return function (dictMonoidRecord) {
                return new MonoidRecord(function () {
                    return Data_Semigroup.semigroupRecordCons(dictIsSymbol)(dictCons)(dictMonoidRecord.SemigroupRecord0())(dictMonoid.Semigroup0());
                }, function (v) {
                    var tail = memptyRecord(dictMonoidRecord)(Type_Data_RowList.RLProxy.value);
                    var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                    var insert = Record_Unsafe.unsafeSet(key);
                    return insert(mempty(dictMonoid))(tail);
                });
            };
        };
    };
};
var power = function (dictMonoid) {
    return function (x) {
        var go = function (p) {
            if (p <= 0) {
                return mempty(dictMonoid);
            };
            if (p === 1) {
                return x;
            };
            if (Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt)(p)(2) === 0) {
                var x$prime = go(Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt)(p)(2));
                return Data_Semigroup.append(dictMonoid.Semigroup0())(x$prime)(x$prime);
            };
            if (Data_Boolean.otherwise) {
                var x$prime = go(Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt)(p)(2));
                return Data_Semigroup.append(dictMonoid.Semigroup0())(x$prime)(Data_Semigroup.append(dictMonoid.Semigroup0())(x$prime)(x));
            };
            throw new Error("Failed pattern match at Data.Monoid line 66, column 3 - line 66, column 17: " + [ p.constructor.name ]);
        };
        return go;
    };
};
var guard = function (dictMonoid) {
    return function (v) {
        return function (v1) {
            if (v) {
                return v1;
            };
            if (!v) {
                return mempty(dictMonoid);
            };
            throw new Error("Failed pattern match at Data.Monoid line 74, column 1 - line 74, column 49: " + [ v.constructor.name, v1.constructor.name ]);
        };
    };
};
module.exports = {
    Monoid: Monoid,
    mempty: mempty,
    power: power,
    guard: guard,
    MonoidRecord: MonoidRecord,
    memptyRecord: memptyRecord,
    monoidUnit: monoidUnit,
    monoidOrdering: monoidOrdering,
    monoidFn: monoidFn,
    monoidString: monoidString,
    monoidArray: monoidArray,
    monoidRecord: monoidRecord,
    monoidRecordNil: monoidRecordNil,
    monoidRecordCons: monoidRecordCons
};

},{"../Data.Boolean/index.js":76,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Semigroup/index.js":137,"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168,"../Record.Unsafe/index.js":197,"../Type.Data.RowList/index.js":198}],120:[function(require,module,exports){
arguments[4][64][0].apply(exports,arguments)
},{"dup":64}],121:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid_Additive = require("../Data.Monoid.Additive/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Endo = require("../Data.Monoid.Endo/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Semigroup_First = require("../Data.Semigroup.First/index.js");
var Data_Semigroup_Last = require("../Data.Semigroup.Last/index.js");
var Prelude = require("../Prelude/index.js");
var Newtype = function (unwrap, wrap) {
    this.unwrap = unwrap;
    this.wrap = wrap;
};
var wrap = function (dict) {
    return dict.wrap;
};
var unwrap = function (dict) {
    return dict.unwrap;
};
var underF2 = function (dictFunctor) {
    return function (dictFunctor1) {
        return function (dictNewtype) {
            return function (dictNewtype1) {
                return function (v) {
                    return function (f) {
                        return function ($66) {
                            return function ($67) {
                                return Data_Functor.map(dictFunctor1)(unwrap(dictNewtype1))(Data_Function.on(f)(Data_Functor.map(dictFunctor)(wrap(dictNewtype)))($66)($67));
                            };
                        };
                    };
                };
            };
        };
    };
};
var underF = function (dictFunctor) {
    return function (dictFunctor1) {
        return function (dictNewtype) {
            return function (dictNewtype1) {
                return function (v) {
                    return function (f) {
                        return function ($68) {
                            return Data_Functor.map(dictFunctor1)(unwrap(dictNewtype1))(f(Data_Functor.map(dictFunctor)(wrap(dictNewtype))($68)));
                        };
                    };
                };
            };
        };
    };
};
var under2 = function (dictNewtype) {
    return function (dictNewtype1) {
        return function (v) {
            return function (f) {
                return function ($69) {
                    return function ($70) {
                        return unwrap(dictNewtype1)(Data_Function.on(f)(wrap(dictNewtype))($69)($70));
                    };
                };
            };
        };
    };
};
var under = function (dictNewtype) {
    return function (dictNewtype1) {
        return function (v) {
            return function (f) {
                return function ($71) {
                    return unwrap(dictNewtype1)(f(wrap(dictNewtype)($71)));
                };
            };
        };
    };
};
var un = function (dictNewtype) {
    return function (v) {
        return unwrap(dictNewtype);
    };
};
var traverse = function (dictFunctor) {
    return function (dictNewtype) {
        return function (v) {
            return function (f) {
                return function ($72) {
                    return Data_Functor.map(dictFunctor)(wrap(dictNewtype))(f(unwrap(dictNewtype)($72)));
                };
            };
        };
    };
};
var overF2 = function (dictFunctor) {
    return function (dictFunctor1) {
        return function (dictNewtype) {
            return function (dictNewtype1) {
                return function (v) {
                    return function (f) {
                        return function ($73) {
                            return function ($74) {
                                return Data_Functor.map(dictFunctor1)(wrap(dictNewtype1))(Data_Function.on(f)(Data_Functor.map(dictFunctor)(unwrap(dictNewtype)))($73)($74));
                            };
                        };
                    };
                };
            };
        };
    };
};
var overF = function (dictFunctor) {
    return function (dictFunctor1) {
        return function (dictNewtype) {
            return function (dictNewtype1) {
                return function (v) {
                    return function (f) {
                        return function ($75) {
                            return Data_Functor.map(dictFunctor1)(wrap(dictNewtype1))(f(Data_Functor.map(dictFunctor)(unwrap(dictNewtype))($75)));
                        };
                    };
                };
            };
        };
    };
};
var over2 = function (dictNewtype) {
    return function (dictNewtype1) {
        return function (v) {
            return function (f) {
                return function ($76) {
                    return function ($77) {
                        return wrap(dictNewtype1)(Data_Function.on(f)(unwrap(dictNewtype))($76)($77));
                    };
                };
            };
        };
    };
};
var over = function (dictNewtype) {
    return function (dictNewtype1) {
        return function (v) {
            return function (f) {
                return function ($78) {
                    return wrap(dictNewtype1)(f(unwrap(dictNewtype)($78)));
                };
            };
        };
    };
};
var op = function (dictNewtype) {
    return un(dictNewtype);
};
var newtypeMultiplicative = new Newtype(function (v) {
    return v;
}, Data_Monoid_Multiplicative.Multiplicative);
var newtypeLast = new Newtype(function (v) {
    return v;
}, Data_Semigroup_Last.Last);
var newtypeFirst = new Newtype(function (v) {
    return v;
}, Data_Semigroup_First.First);
var newtypeEndo = new Newtype(function (v) {
    return v;
}, Data_Monoid_Endo.Endo);
var newtypeDual = new Newtype(function (v) {
    return v;
}, Data_Monoid_Dual.Dual);
var newtypeDisj = new Newtype(function (v) {
    return v;
}, Data_Monoid_Disj.Disj);
var newtypeConj = new Newtype(function (v) {
    return v;
}, Data_Monoid_Conj.Conj);
var newtypeAdditive = new Newtype(function (v) {
    return v;
}, Data_Monoid_Additive.Additive);
var collect = function (dictFunctor) {
    return function (dictNewtype) {
        return function (v) {
            return function (f) {
                return function ($79) {
                    return wrap(dictNewtype)(f(Data_Functor.map(dictFunctor)(unwrap(dictNewtype))($79)));
                };
            };
        };
    };
};
var alaF = function (dictFunctor) {
    return function (dictFunctor1) {
        return function (dictNewtype) {
            return function (dictNewtype1) {
                return function (v) {
                    return function (f) {
                        return function ($80) {
                            return Data_Functor.map(dictFunctor1)(unwrap(dictNewtype1))(f(Data_Functor.map(dictFunctor)(wrap(dictNewtype))($80)));
                        };
                    };
                };
            };
        };
    };
};
var ala = function (dictFunctor) {
    return function (dictNewtype) {
        return function (dictNewtype1) {
            return function (v) {
                return function (f) {
                    return Data_Functor.map(dictFunctor)(unwrap(dictNewtype))(f(wrap(dictNewtype1)));
                };
            };
        };
    };
};
module.exports = {
    unwrap: unwrap,
    wrap: wrap,
    Newtype: Newtype,
    un: un,
    op: op,
    ala: ala,
    alaF: alaF,
    over: over,
    overF: overF,
    under: under,
    underF: underF,
    over2: over2,
    overF2: overF2,
    under2: under2,
    underF2: underF2,
    traverse: traverse,
    collect: collect,
    newtypeAdditive: newtypeAdditive,
    newtypeMultiplicative: newtypeMultiplicative,
    newtypeConj: newtypeConj,
    newtypeDisj: newtypeDisj,
    newtypeDual: newtypeDual,
    newtypeEndo: newtypeEndo,
    newtypeFirst: newtypeFirst,
    newtypeLast: newtypeLast
};

},{"../Control.Semigroupoid/index.js":51,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Monoid.Additive/index.js":113,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Endo/index.js":117,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Semigroup.First/index.js":132,"../Data.Semigroup.Last/index.js":134,"../Prelude/index.js":195}],122:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_FoldableWithIndex = require("../Data.FoldableWithIndex/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_FunctorWithIndex = require("../Data.FunctorWithIndex/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semigroup_Foldable = require("../Data.Semigroup.Foldable/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Data_TraversableWithIndex = require("../Data.TraversableWithIndex/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unfoldable = require("../Data.Unfoldable/index.js");
var Data_Unfoldable1 = require("../Data.Unfoldable1/index.js");
var Prelude = require("../Prelude/index.js");
var NonEmpty = (function () {
    function NonEmpty(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    NonEmpty.create = function (value0) {
        return function (value1) {
            return new NonEmpty(value0, value1);
        };
    };
    return NonEmpty;
})();
var unfoldable1NonEmpty = function (dictUnfoldable) {
    return new Data_Unfoldable1.Unfoldable1(function (f) {
        return function (b) {
            return Data_Tuple.uncurry(NonEmpty.create)(Data_Functor.map(Data_Tuple.functorTuple)(Data_Unfoldable.unfoldr(dictUnfoldable)(Data_Functor.map(Data_Maybe.functorMaybe)(f)))(f(b)));
        };
    });
};
var tail = function (v) {
    return v.value1;
};
var singleton = function (dictPlus) {
    return function (a) {
        return new NonEmpty(a, Control_Plus.empty(dictPlus));
    };
};
var showNonEmpty = function (dictShow) {
    return function (dictShow1) {
        return new Data_Show.Show(function (v) {
            return "(NonEmpty " + (Data_Show.show(dictShow)(v.value0) + (" " + (Data_Show.show(dictShow1)(v.value1) + ")")));
        });
    };
};
var oneOf = function (dictAlternative) {
    return function (v) {
        return Control_Alt.alt((dictAlternative.Plus1()).Alt0())(Control_Applicative.pure(dictAlternative.Applicative0())(v.value0))(v.value1);
    };
};
var head = function (v) {
    return v.value0;
};
var functorNonEmpty = function (dictFunctor) {
    return new Data_Functor.Functor(function (f) {
        return function (m) {
            return new NonEmpty(f(m.value0), Data_Functor.map(dictFunctor)(f)(m.value1));
        };
    });
};
var functorWithIndex = function (dictFunctorWithIndex) {
    return new Data_FunctorWithIndex.FunctorWithIndex(function () {
        return functorNonEmpty(dictFunctorWithIndex.Functor0());
    }, function (f) {
        return function (v) {
            return new NonEmpty(f(Data_Maybe.Nothing.value)(v.value0), Data_FunctorWithIndex.mapWithIndex(dictFunctorWithIndex)(function ($146) {
                return f(Data_Maybe.Just.create($146));
            })(v.value1));
        };
    });
};
var fromNonEmpty = function (f) {
    return function (v) {
        return f(v.value0)(v.value1);
    };
};
var foldl1 = function (dictFoldable) {
    return function (f) {
        return function (v) {
            return Data_Foldable.foldl(dictFoldable)(f)(v.value0)(v.value1);
        };
    };
};
var foldableNonEmpty = function (dictFoldable) {
    return new Data_Foldable.Foldable(function (dictMonoid) {
        return function (f) {
            return function (v) {
                return Data_Semigroup.append(dictMonoid.Semigroup0())(f(v.value0))(Data_Foldable.foldMap(dictFoldable)(dictMonoid)(f)(v.value1));
            };
        };
    }, function (f) {
        return function (b) {
            return function (v) {
                return Data_Foldable.foldl(dictFoldable)(f)(f(b)(v.value0))(v.value1);
            };
        };
    }, function (f) {
        return function (b) {
            return function (v) {
                return f(v.value0)(Data_Foldable.foldr(dictFoldable)(f)(b)(v.value1));
            };
        };
    });
};
var foldableWithIndexNonEmpty = function (dictFoldableWithIndex) {
    return new Data_FoldableWithIndex.FoldableWithIndex(function () {
        return foldableNonEmpty(dictFoldableWithIndex.Foldable0());
    }, function (dictMonoid) {
        return function (f) {
            return function (v) {
                return Data_Semigroup.append(dictMonoid.Semigroup0())(f(Data_Maybe.Nothing.value)(v.value0))(Data_FoldableWithIndex.foldMapWithIndex(dictFoldableWithIndex)(dictMonoid)(function ($147) {
                    return f(Data_Maybe.Just.create($147));
                })(v.value1));
            };
        };
    }, function (f) {
        return function (b) {
            return function (v) {
                return Data_FoldableWithIndex.foldlWithIndex(dictFoldableWithIndex)(function ($148) {
                    return f(Data_Maybe.Just.create($148));
                })(f(Data_Maybe.Nothing.value)(b)(v.value0))(v.value1);
            };
        };
    }, function (f) {
        return function (b) {
            return function (v) {
                return f(Data_Maybe.Nothing.value)(v.value0)(Data_FoldableWithIndex.foldrWithIndex(dictFoldableWithIndex)(function ($149) {
                    return f(Data_Maybe.Just.create($149));
                })(b)(v.value1));
            };
        };
    });
};
var traversableNonEmpty = function (dictTraversable) {
    return new Data_Traversable.Traversable(function () {
        return foldableNonEmpty(dictTraversable.Foldable1());
    }, function () {
        return functorNonEmpty(dictTraversable.Functor0());
    }, function (dictApplicative) {
        return function (v) {
            return Control_Apply.apply(dictApplicative.Apply0())(Data_Functor.map((dictApplicative.Apply0()).Functor0())(NonEmpty.create)(v.value0))(Data_Traversable.sequence(dictTraversable)(dictApplicative)(v.value1));
        };
    }, function (dictApplicative) {
        return function (f) {
            return function (v) {
                return Control_Apply.apply(dictApplicative.Apply0())(Data_Functor.map((dictApplicative.Apply0()).Functor0())(NonEmpty.create)(f(v.value0)))(Data_Traversable.traverse(dictTraversable)(dictApplicative)(f)(v.value1));
            };
        };
    });
};
var traversableWithIndexNonEmpty = function (dictTraversableWithIndex) {
    return new Data_TraversableWithIndex.TraversableWithIndex(function () {
        return foldableWithIndexNonEmpty(dictTraversableWithIndex.FoldableWithIndex1());
    }, function () {
        return functorWithIndex(dictTraversableWithIndex.FunctorWithIndex0());
    }, function () {
        return traversableNonEmpty(dictTraversableWithIndex.Traversable2());
    }, function (dictApplicative) {
        return function (f) {
            return function (v) {
                return Control_Apply.apply(dictApplicative.Apply0())(Data_Functor.map((dictApplicative.Apply0()).Functor0())(NonEmpty.create)(f(Data_Maybe.Nothing.value)(v.value0)))(Data_TraversableWithIndex.traverseWithIndex(dictTraversableWithIndex)(dictApplicative)(function ($150) {
                    return f(Data_Maybe.Just.create($150));
                })(v.value1));
            };
        };
    });
};
var foldable1NonEmpty = function (dictFoldable) {
    return new Data_Semigroup_Foldable.Foldable1(function () {
        return foldableNonEmpty(dictFoldable);
    }, function (dictSemigroup) {
        return Data_Semigroup_Foldable.foldMap1(foldable1NonEmpty(dictFoldable))(dictSemigroup)(Control_Category.identity(Control_Category.categoryFn));
    }, function (dictSemigroup) {
        return function (f) {
            return function (v) {
                return Data_Foldable.foldl(dictFoldable)(function (s) {
                    return function (a1) {
                        return Data_Semigroup.append(dictSemigroup)(s)(f(a1));
                    };
                })(f(v.value0))(v.value1);
            };
        };
    });
};
var eqNonEmpty = function (dictEq1) {
    return function (dictEq) {
        return new Data_Eq.Eq(function (x) {
            return function (y) {
                return Data_Eq.eq(dictEq)(x.value0)(y.value0) && Data_Eq.eq1(dictEq1)(dictEq)(x.value1)(y.value1);
            };
        });
    };
};
var ordNonEmpty = function (dictOrd1) {
    return function (dictOrd) {
        return new Data_Ord.Ord(function () {
            return eqNonEmpty(dictOrd1.Eq10())(dictOrd.Eq0());
        }, function (x) {
            return function (y) {
                var v = Data_Ord.compare(dictOrd)(x.value0)(y.value0);
                if (v instanceof Data_Ordering.LT) {
                    return Data_Ordering.LT.value;
                };
                if (v instanceof Data_Ordering.GT) {
                    return Data_Ordering.GT.value;
                };
                return Data_Ord.compare1(dictOrd1)(dictOrd)(x.value1)(y.value1);
            };
        });
    };
};
var eq1NonEmpty = function (dictEq1) {
    return new Data_Eq.Eq1(function (dictEq) {
        return Data_Eq.eq(eqNonEmpty(dictEq1)(dictEq));
    });
};
var ord1NonEmpty = function (dictOrd1) {
    return new Data_Ord.Ord1(function () {
        return eq1NonEmpty(dictOrd1.Eq10());
    }, function (dictOrd) {
        return Data_Ord.compare(ordNonEmpty(dictOrd1)(dictOrd));
    });
};
module.exports = {
    NonEmpty: NonEmpty,
    singleton: singleton,
    foldl1: foldl1,
    fromNonEmpty: fromNonEmpty,
    oneOf: oneOf,
    head: head,
    tail: tail,
    showNonEmpty: showNonEmpty,
    eqNonEmpty: eqNonEmpty,
    eq1NonEmpty: eq1NonEmpty,
    ordNonEmpty: ordNonEmpty,
    ord1NonEmpty: ord1NonEmpty,
    functorNonEmpty: functorNonEmpty,
    functorWithIndex: functorWithIndex,
    foldableNonEmpty: foldableNonEmpty,
    foldableWithIndexNonEmpty: foldableWithIndexNonEmpty,
    traversableNonEmpty: traversableNonEmpty,
    traversableWithIndexNonEmpty: traversableWithIndexNonEmpty,
    foldable1NonEmpty: foldable1NonEmpty,
    unfoldable1NonEmpty: unfoldable1NonEmpty
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.FoldableWithIndex/index.js":90,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.FunctorWithIndex/index.js":100,"../Data.HeytingAlgebra/index.js":104,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Semigroup.Foldable/index.js":133,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Data.Traversable/index.js":159,"../Data.TraversableWithIndex/index.js":157,"../Data.Tuple/index.js":160,"../Data.Unfoldable/index.js":166,"../Data.Unfoldable1/index.js":164,"../Prelude/index.js":195}],123:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Max = function (x) {
    return x;
};
var showMax = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Max " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupMax = function (dictOrd) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Data_Ord.max(dictOrd)(v)(v1);
        };
    });
};
var newtypeMax = new Data_Newtype.Newtype(function (n) {
    return n;
}, Max);
var monoidMax = function (dictBounded) {
    return new Data_Monoid.Monoid(function () {
        return semigroupMax(dictBounded.Ord0());
    }, Data_Bounded.bottom(dictBounded));
};
var eqMax = function (dictEq) {
    return dictEq;
};
var ordMax = function (dictOrd) {
    return new Data_Ord.Ord(function () {
        return eqMax(dictOrd.Eq0());
    }, function (v) {
        return function (v1) {
            return Data_Ord.compare(dictOrd)(v)(v1);
        };
    });
};
module.exports = {
    Max: Max,
    newtypeMax: newtypeMax,
    eqMax: eqMax,
    ordMax: ordMax,
    semigroupMax: semigroupMax,
    monoidMax: monoidMax,
    showMax: showMax
};

},{"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],124:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Min = function (x) {
    return x;
};
var showMin = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Min " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupMin = function (dictOrd) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Data_Ord.min(dictOrd)(v)(v1);
        };
    });
};
var newtypeMin = new Data_Newtype.Newtype(function (n) {
    return n;
}, Min);
var monoidMin = function (dictBounded) {
    return new Data_Monoid.Monoid(function () {
        return semigroupMin(dictBounded.Ord0());
    }, Data_Bounded.top(dictBounded));
};
var eqMin = function (dictEq) {
    return dictEq;
};
var ordMin = function (dictOrd) {
    return new Data_Ord.Ord(function () {
        return eqMin(dictOrd.Eq0());
    }, function (v) {
        return function (v1) {
            return Data_Ord.compare(dictOrd)(v)(v1);
        };
    });
};
module.exports = {
    Min: Min,
    newtypeMin: newtypeMin,
    eqMin: eqMin,
    ordMin: ordMin,
    semigroupMin: semigroupMin,
    monoidMin: monoidMin,
    showMin: showMin
};

},{"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],125:[function(require,module,exports){
"use strict";

exports.unsafeCompareImpl = function (lt) {
  return function (eq) {
    return function (gt) {
      return function (x) {
        return function (y) {
          return x < y ? lt : x === y ? eq : gt;
        };
      };
    };
  };
};

},{}],126:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var unsafeCompare = $foreign.unsafeCompareImpl(Data_Ordering.LT.value)(Data_Ordering.EQ.value)(Data_Ordering.GT.value);
module.exports = {
    unsafeCompare: unsafeCompare
};

},{"../Data.Ordering/index.js":129,"./foreign.js":125}],127:[function(require,module,exports){
"use strict";

exports.ordArrayImpl = function (f) {
  return function (xs) {
    return function (ys) {
      var i = 0;
      var xlen = xs.length;
      var ylen = ys.length;
      while (i < xlen && i < ylen) {
        var x = xs[i];
        var y = ys[i];
        var o = f(x)(y);
        if (o !== 0) {
          return o;
        }
        i++;
      }
      if (xlen === ylen) {
        return 0;
      } else if (xlen > ylen) {
        return -1;
      } else {
        return 1;
      }
    };
  };
};

},{}],128:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Ord_Unsafe = require("../Data.Ord.Unsafe/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Data_Void = require("../Data.Void/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var Ord = function (Eq0, compare) {
    this.Eq0 = Eq0;
    this.compare = compare;
};
var Ord1 = function (Eq10, compare1) {
    this.Eq10 = Eq10;
    this.compare1 = compare1;
};
var OrdRecord = function (EqRecord0, compareRecord) {
    this.EqRecord0 = EqRecord0;
    this.compareRecord = compareRecord;
};
var ordVoid = new Ord(function () {
    return Data_Eq.eqVoid;
}, function (v) {
    return function (v1) {
        return Data_Ordering.EQ.value;
    };
});
var ordUnit = new Ord(function () {
    return Data_Eq.eqUnit;
}, function (v) {
    return function (v1) {
        return Data_Ordering.EQ.value;
    };
});
var ordString = new Ord(function () {
    return Data_Eq.eqString;
}, Data_Ord_Unsafe.unsafeCompare);
var ordRecordNil = new OrdRecord(function () {
    return Data_Eq.eqRowNil;
}, function (v) {
    return function (v1) {
        return function (v2) {
            return Data_Ordering.EQ.value;
        };
    };
});
var ordOrdering = new Ord(function () {
    return Data_Ordering.eqOrdering;
}, function (v) {
    return function (v1) {
        if (v instanceof Data_Ordering.LT && v1 instanceof Data_Ordering.LT) {
            return Data_Ordering.EQ.value;
        };
        if (v instanceof Data_Ordering.EQ && v1 instanceof Data_Ordering.EQ) {
            return Data_Ordering.EQ.value;
        };
        if (v instanceof Data_Ordering.GT && v1 instanceof Data_Ordering.GT) {
            return Data_Ordering.EQ.value;
        };
        if (v instanceof Data_Ordering.LT) {
            return Data_Ordering.LT.value;
        };
        if (v instanceof Data_Ordering.EQ && v1 instanceof Data_Ordering.LT) {
            return Data_Ordering.GT.value;
        };
        if (v instanceof Data_Ordering.EQ && v1 instanceof Data_Ordering.GT) {
            return Data_Ordering.LT.value;
        };
        if (v instanceof Data_Ordering.GT) {
            return Data_Ordering.GT.value;
        };
        throw new Error("Failed pattern match at Data.Ord line 73, column 1 - line 73, column 37: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var ordNumber = new Ord(function () {
    return Data_Eq.eqNumber;
}, Data_Ord_Unsafe.unsafeCompare);
var ordInt = new Ord(function () {
    return Data_Eq.eqInt;
}, Data_Ord_Unsafe.unsafeCompare);
var ordChar = new Ord(function () {
    return Data_Eq.eqChar;
}, Data_Ord_Unsafe.unsafeCompare);
var ordBoolean = new Ord(function () {
    return Data_Eq.eqBoolean;
}, Data_Ord_Unsafe.unsafeCompare);
var compareRecord = function (dict) {
    return dict.compareRecord;
};
var ordRecord = function (dictRowToList) {
    return function (dictOrdRecord) {
        return new Ord(function () {
            return Data_Eq.eqRec(dictRowToList)(dictOrdRecord.EqRecord0());
        }, compareRecord(dictOrdRecord)(Type_Data_RowList.RLProxy.value));
    };
};
var compare1 = function (dict) {
    return dict.compare1;
};
var compare = function (dict) {
    return dict.compare;
};
var comparing = function (dictOrd) {
    return function (f) {
        return function (x) {
            return function (y) {
                return compare(dictOrd)(f(x))(f(y));
            };
        };
    };
};
var greaterThan = function (dictOrd) {
    return function (a1) {
        return function (a2) {
            var v = compare(dictOrd)(a1)(a2);
            if (v instanceof Data_Ordering.GT) {
                return true;
            };
            return false;
        };
    };
};
var greaterThanOrEq = function (dictOrd) {
    return function (a1) {
        return function (a2) {
            var v = compare(dictOrd)(a1)(a2);
            if (v instanceof Data_Ordering.LT) {
                return false;
            };
            return true;
        };
    };
};
var signum = function (dictOrd) {
    return function (dictRing) {
        return function (x) {
            var $43 = greaterThanOrEq(dictOrd)(x)(Data_Semiring.zero(dictRing.Semiring0()));
            if ($43) {
                return Data_Semiring.one(dictRing.Semiring0());
            };
            return Data_Ring.negate(dictRing)(Data_Semiring.one(dictRing.Semiring0()));
        };
    };
};
var lessThan = function (dictOrd) {
    return function (a1) {
        return function (a2) {
            var v = compare(dictOrd)(a1)(a2);
            if (v instanceof Data_Ordering.LT) {
                return true;
            };
            return false;
        };
    };
};
var lessThanOrEq = function (dictOrd) {
    return function (a1) {
        return function (a2) {
            var v = compare(dictOrd)(a1)(a2);
            if (v instanceof Data_Ordering.GT) {
                return false;
            };
            return true;
        };
    };
};
var max = function (dictOrd) {
    return function (x) {
        return function (y) {
            var v = compare(dictOrd)(x)(y);
            if (v instanceof Data_Ordering.LT) {
                return y;
            };
            if (v instanceof Data_Ordering.EQ) {
                return x;
            };
            if (v instanceof Data_Ordering.GT) {
                return x;
            };
            throw new Error("Failed pattern match at Data.Ord line 128, column 3 - line 131, column 12: " + [ v.constructor.name ]);
        };
    };
};
var min = function (dictOrd) {
    return function (x) {
        return function (y) {
            var v = compare(dictOrd)(x)(y);
            if (v instanceof Data_Ordering.LT) {
                return x;
            };
            if (v instanceof Data_Ordering.EQ) {
                return x;
            };
            if (v instanceof Data_Ordering.GT) {
                return y;
            };
            throw new Error("Failed pattern match at Data.Ord line 119, column 3 - line 122, column 12: " + [ v.constructor.name ]);
        };
    };
};
var ordArray = function (dictOrd) {
    return new Ord(function () {
        return Data_Eq.eqArray(dictOrd.Eq0());
    }, (function () {
        var toDelta = function (x) {
            return function (y) {
                var v = compare(dictOrd)(x)(y);
                if (v instanceof Data_Ordering.EQ) {
                    return 0;
                };
                if (v instanceof Data_Ordering.LT) {
                    return 1;
                };
                if (v instanceof Data_Ordering.GT) {
                    return -1 | 0;
                };
                throw new Error("Failed pattern match at Data.Ord line 66, column 7 - line 71, column 1: " + [ v.constructor.name ]);
            };
        };
        return function (xs) {
            return function (ys) {
                return compare(ordInt)(0)($foreign.ordArrayImpl(toDelta)(xs)(ys));
            };
        };
    })());
};
var ord1Array = new Ord1(function () {
    return Data_Eq.eq1Array;
}, function (dictOrd) {
    return compare(ordArray(dictOrd));
});
var ordRecordCons = function (dictOrdRecord) {
    return function (dictCons) {
        return function (dictIsSymbol) {
            return function (dictOrd) {
                return new OrdRecord(function () {
                    return Data_Eq.eqRowCons(dictOrdRecord.EqRecord0())(dictCons)(dictIsSymbol)(dictOrd.Eq0());
                }, function (v) {
                    return function (ra) {
                        return function (rb) {
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var left = compare(dictOrd)(Record_Unsafe.unsafeGet(key)(ra))(Record_Unsafe.unsafeGet(key)(rb));
                            var $49 = Data_Eq.notEq(Data_Ordering.eqOrdering)(left)(Data_Ordering.EQ.value);
                            if ($49) {
                                return left;
                            };
                            return compareRecord(dictOrdRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                        };
                    };
                });
            };
        };
    };
};
var clamp = function (dictOrd) {
    return function (low) {
        return function (hi) {
            return function (x) {
                return min(dictOrd)(hi)(max(dictOrd)(low)(x));
            };
        };
    };
};
var between = function (dictOrd) {
    return function (low) {
        return function (hi) {
            return function (x) {
                if (lessThan(dictOrd)(x)(low)) {
                    return false;
                };
                if (greaterThan(dictOrd)(x)(hi)) {
                    return false;
                };
                return true;
            };
        };
    };
};
var abs = function (dictOrd) {
    return function (dictRing) {
        return function (x) {
            var $53 = greaterThanOrEq(dictOrd)(x)(Data_Semiring.zero(dictRing.Semiring0()));
            if ($53) {
                return x;
            };
            return Data_Ring.negate(dictRing)(x);
        };
    };
};
module.exports = {
    Ord: Ord,
    compare: compare,
    Ord1: Ord1,
    compare1: compare1,
    lessThan: lessThan,
    lessThanOrEq: lessThanOrEq,
    greaterThan: greaterThan,
    greaterThanOrEq: greaterThanOrEq,
    comparing: comparing,
    min: min,
    max: max,
    clamp: clamp,
    between: between,
    abs: abs,
    signum: signum,
    OrdRecord: OrdRecord,
    compareRecord: compareRecord,
    ordBoolean: ordBoolean,
    ordInt: ordInt,
    ordNumber: ordNumber,
    ordString: ordString,
    ordChar: ordChar,
    ordUnit: ordUnit,
    ordVoid: ordVoid,
    ordArray: ordArray,
    ordOrdering: ordOrdering,
    ord1Array: ord1Array,
    ordRecordNil: ordRecordNil,
    ordRecordCons: ordRecordCons,
    ordRecord: ordRecord
};

},{"../Data.Eq/index.js":86,"../Data.Ord.Unsafe/index.js":126,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139,"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168,"../Data.Void/index.js":169,"../Record.Unsafe/index.js":197,"../Type.Data.RowList/index.js":198,"./foreign.js":127}],129:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Eq = require("../Data.Eq/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var LT = (function () {
    function LT() {

    };
    LT.value = new LT();
    return LT;
})();
var GT = (function () {
    function GT() {

    };
    GT.value = new GT();
    return GT;
})();
var EQ = (function () {
    function EQ() {

    };
    EQ.value = new EQ();
    return EQ;
})();
var showOrdering = new Data_Show.Show(function (v) {
    if (v instanceof LT) {
        return "LT";
    };
    if (v instanceof GT) {
        return "GT";
    };
    if (v instanceof EQ) {
        return "EQ";
    };
    throw new Error("Failed pattern match at Data.Ordering line 26, column 1 - line 26, column 39: " + [ v.constructor.name ]);
});
var semigroupOrdering = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        if (v instanceof LT) {
            return LT.value;
        };
        if (v instanceof GT) {
            return GT.value;
        };
        if (v instanceof EQ) {
            return v1;
        };
        throw new Error("Failed pattern match at Data.Ordering line 21, column 1 - line 21, column 49: " + [ v.constructor.name, v1.constructor.name ]);
    };
});
var invert = function (v) {
    if (v instanceof GT) {
        return LT.value;
    };
    if (v instanceof EQ) {
        return EQ.value;
    };
    if (v instanceof LT) {
        return GT.value;
    };
    throw new Error("Failed pattern match at Data.Ordering line 33, column 1 - line 33, column 31: " + [ v.constructor.name ]);
};
var eqOrdering = new Data_Eq.Eq(function (v) {
    return function (v1) {
        if (v instanceof LT && v1 instanceof LT) {
            return true;
        };
        if (v instanceof GT && v1 instanceof GT) {
            return true;
        };
        if (v instanceof EQ && v1 instanceof EQ) {
            return true;
        };
        return false;
    };
});
module.exports = {
    LT: LT,
    GT: GT,
    EQ: EQ,
    invert: invert,
    eqOrdering: eqOrdering,
    semigroupOrdering: semigroupOrdering,
    showOrdering: showOrdering
};

},{"../Data.Eq/index.js":86,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141}],130:[function(require,module,exports){
"use strict";

exports.intSub = function (x) {
  return function (y) {
    /* jshint bitwise: false */
    return x - y | 0;
  };
};

exports.numSub = function (n1) {
  return function (n2) {
    return n1 - n2;
  };
};

},{}],131:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var Ring = function (Semiring0, sub) {
    this.Semiring0 = Semiring0;
    this.sub = sub;
};
var RingRecord = function (SemiringRecord0, subRecord) {
    this.SemiringRecord0 = SemiringRecord0;
    this.subRecord = subRecord;
};
var subRecord = function (dict) {
    return dict.subRecord;
};
var sub = function (dict) {
    return dict.sub;
};
var ringUnit = new Ring(function () {
    return Data_Semiring.semiringUnit;
}, function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
});
var ringRecordNil = new RingRecord(function () {
    return Data_Semiring.semiringRecordNil;
}, function (v) {
    return function (v1) {
        return function (v2) {
            return {};
        };
    };
});
var ringRecordCons = function (dictIsSymbol) {
    return function (dictCons) {
        return function (dictRingRecord) {
            return function (dictRing) {
                return new RingRecord(function () {
                    return Data_Semiring.semiringRecordCons(dictIsSymbol)(dictCons)(dictRingRecord.SemiringRecord0())(dictRing.Semiring0());
                }, function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = subRecord(dictRingRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var insert = Record_Unsafe.unsafeSet(key);
                            var get = Record_Unsafe.unsafeGet(key);
                            return insert(sub(dictRing)(get(ra))(get(rb)))(tail);
                        };
                    };
                });
            };
        };
    };
};
var ringRecord = function (dictRowToList) {
    return function (dictRingRecord) {
        return new Ring(function () {
            return Data_Semiring.semiringRecord(dictRowToList)(dictRingRecord.SemiringRecord0());
        }, subRecord(dictRingRecord)(Type_Data_RowList.RLProxy.value));
    };
};
var ringNumber = new Ring(function () {
    return Data_Semiring.semiringNumber;
}, $foreign.numSub);
var ringInt = new Ring(function () {
    return Data_Semiring.semiringInt;
}, $foreign.intSub);
var ringFn = function (dictRing) {
    return new Ring(function () {
        return Data_Semiring.semiringFn(dictRing.Semiring0());
    }, function (f) {
        return function (g) {
            return function (x) {
                return sub(dictRing)(f(x))(g(x));
            };
        };
    });
};
var negate = function (dictRing) {
    return function (a) {
        return sub(dictRing)(Data_Semiring.zero(dictRing.Semiring0()))(a);
    };
};
module.exports = {
    Ring: Ring,
    sub: sub,
    negate: negate,
    RingRecord: RingRecord,
    subRecord: subRecord,
    ringInt: ringInt,
    ringNumber: ringNumber,
    ringUnit: ringUnit,
    ringFn: ringFn,
    ringRecord: ringRecord,
    ringRecordNil: ringRecordNil,
    ringRecordCons: ringRecordCons
};

},{"../Data.Semiring/index.js":139,"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168,"../Record.Unsafe/index.js":197,"../Type.Data.RowList/index.js":198,"./foreign.js":130}],132:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var First = function (x) {
    return x;
};
var showFirst = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(First " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupFirst = new Data_Semigroup.Semigroup(function (x) {
    return function (v) {
        return x;
    };
});
var ordFirst = function (dictOrd) {
    return dictOrd;
};
var functorFirst = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var eqFirst = function (dictEq) {
    return dictEq;
};
var eq1First = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqFirst(dictEq));
});
var ord1First = new Data_Ord.Ord1(function () {
    return eq1First;
}, function (dictOrd) {
    return Data_Ord.compare(ordFirst(dictOrd));
});
var boundedFirst = function (dictBounded) {
    return dictBounded;
};
var applyFirst = new Control_Apply.Apply(function () {
    return functorFirst;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindFirst = new Control_Bind.Bind(function () {
    return applyFirst;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeFirst = new Control_Applicative.Applicative(function () {
    return applyFirst;
}, First);
var monadFirst = new Control_Monad.Monad(function () {
    return applicativeFirst;
}, function () {
    return bindFirst;
});
module.exports = {
    First: First,
    eqFirst: eqFirst,
    eq1First: eq1First,
    ordFirst: ordFirst,
    ord1First: ord1First,
    boundedFirst: boundedFirst,
    showFirst: showFirst,
    functorFirst: functorFirst,
    applyFirst: applyFirst,
    applicativeFirst: applicativeFirst,
    bindFirst: bindFirst,
    monadFirst: monadFirst,
    semigroupFirst: semigroupFirst
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],133:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord_Max = require("../Data.Ord.Max/index.js");
var Data_Ord_Min = require("../Data.Ord.Min/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var JoinWith = function (x) {
    return x;
};
var Act = function (x) {
    return x;
};
var Foldable1 = function (Foldable0, fold1, foldMap1) {
    this.Foldable0 = Foldable0;
    this.fold1 = fold1;
    this.foldMap1 = foldMap1;
};
var semigroupJoinWith = function (dictSemigroup) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return JoinWith(function (j) {
                return Data_Semigroup.append(dictSemigroup)(v(j))(Data_Semigroup.append(dictSemigroup)(j)(v1(j)));
            });
        };
    });
};
var semigroupAct = function (dictApply) {
    return new Data_Semigroup.Semigroup(function (v) {
        return function (v1) {
            return Control_Apply.applySecond(dictApply)(v)(v1);
        };
    });
};
var joinee = function (v) {
    return v;
};
var getAct = function (v) {
    return v;
};
var foldMap1 = function (dict) {
    return dict.foldMap1;
};
var intercalateMap = function (dictFoldable1) {
    return function (dictSemigroup) {
        return function (j) {
            return function (f) {
                return function (foldable) {
                    return joinee(foldMap1(dictFoldable1)(semigroupJoinWith(dictSemigroup))(function ($43) {
                        return JoinWith(Data_Function["const"](f($43)));
                    })(foldable))(j);
                };
            };
        };
    };
};
var intercalate = function (dictFoldable1) {
    return function (dictSemigroup) {
        return Data_Function.flip(intercalateMap(dictFoldable1)(dictSemigroup))(Control_Category.identity(Control_Category.categoryFn));
    };
};
var maximum = function (dictOrd) {
    return function (dictFoldable1) {
        return Data_Newtype.ala(Data_Functor.functorFn)(Data_Ord_Max.newtypeMax)(Data_Ord_Max.newtypeMax)(Data_Ord_Max.Max)(foldMap1(dictFoldable1)(Data_Ord_Max.semigroupMax(dictOrd)));
    };
};
var minimum = function (dictOrd) {
    return function (dictFoldable1) {
        return Data_Newtype.ala(Data_Functor.functorFn)(Data_Ord_Min.newtypeMin)(Data_Ord_Min.newtypeMin)(Data_Ord_Min.Min)(foldMap1(dictFoldable1)(Data_Ord_Min.semigroupMin(dictOrd)));
    };
};
var traverse1_ = function (dictFoldable1) {
    return function (dictApply) {
        return function (f) {
            return function (t) {
                return Data_Functor.voidRight(dictApply.Functor0())(Data_Unit.unit)(getAct(foldMap1(dictFoldable1)(semigroupAct(dictApply))(function ($44) {
                    return Act(f($44));
                })(t)));
            };
        };
    };
};
var for1_ = function (dictFoldable1) {
    return function (dictApply) {
        return Data_Function.flip(traverse1_(dictFoldable1)(dictApply));
    };
};
var sequence1_ = function (dictFoldable1) {
    return function (dictApply) {
        return traverse1_(dictFoldable1)(dictApply)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var fold1Default = function (dictFoldable1) {
    return function (dictSemigroup) {
        return foldMap1(dictFoldable1)(dictSemigroup)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var foldableDual = new Foldable1(function () {
    return Data_Foldable.foldableDual;
}, function (dictSemigroup) {
    return fold1Default(foldableDual)(dictSemigroup);
}, function (dictSemigroup) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
});
var foldableMultiplicative = new Foldable1(function () {
    return Data_Foldable.foldableMultiplicative;
}, function (dictSemigroup) {
    return fold1Default(foldableMultiplicative)(dictSemigroup);
}, function (dictSemigroup) {
    return function (f) {
        return function (v) {
            return f(v);
        };
    };
});
var fold1 = function (dict) {
    return dict.fold1;
};
var foldMap1Default = function (dictFoldable1) {
    return function (dictFunctor) {
        return function (dictSemigroup) {
            return function (f) {
                return function ($45) {
                    return fold1(dictFoldable1)(dictSemigroup)(Data_Functor.map(dictFunctor)(f)($45));
                };
            };
        };
    };
};
module.exports = {
    Foldable1: Foldable1,
    foldMap1: foldMap1,
    fold1: fold1,
    traverse1_: traverse1_,
    for1_: for1_,
    sequence1_: sequence1_,
    foldMap1Default: foldMap1Default,
    fold1Default: fold1Default,
    intercalate: intercalate,
    intercalateMap: intercalateMap,
    foldableDual: foldableDual,
    foldableMultiplicative: foldableMultiplicative
};

},{"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Control.Semigroupoid/index.js":51,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Newtype/index.js":121,"../Data.Ord.Max/index.js":123,"../Data.Ord.Min/index.js":124,"../Data.Semigroup/index.js":137,"../Data.Unit/index.js":168,"../Prelude/index.js":195}],134:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Last = function (x) {
    return x;
};
var showLast = function (dictShow) {
    return new Data_Show.Show(function (v) {
        return "(Last " + (Data_Show.show(dictShow)(v) + ")");
    });
};
var semigroupLast = new Data_Semigroup.Semigroup(function (v) {
    return function (x) {
        return x;
    };
});
var ordLast = function (dictOrd) {
    return dictOrd;
};
var functorLast = new Data_Functor.Functor(function (f) {
    return function (m) {
        return f(m);
    };
});
var eqLast = function (dictEq) {
    return dictEq;
};
var eq1Last = new Data_Eq.Eq1(function (dictEq) {
    return Data_Eq.eq(eqLast(dictEq));
});
var ord1Last = new Data_Ord.Ord1(function () {
    return eq1Last;
}, function (dictOrd) {
    return Data_Ord.compare(ordLast(dictOrd));
});
var boundedLast = function (dictBounded) {
    return dictBounded;
};
var applyLast = new Control_Apply.Apply(function () {
    return functorLast;
}, function (v) {
    return function (v1) {
        return v(v1);
    };
});
var bindLast = new Control_Bind.Bind(function () {
    return applyLast;
}, function (v) {
    return function (f) {
        return f(v);
    };
});
var applicativeLast = new Control_Applicative.Applicative(function () {
    return applyLast;
}, Last);
var monadLast = new Control_Monad.Monad(function () {
    return applicativeLast;
}, function () {
    return bindLast;
});
module.exports = {
    Last: Last,
    eqLast: eqLast,
    eq1Last: eq1Last,
    ordLast: ordLast,
    ord1Last: ord1Last,
    boundedLast: boundedLast,
    showLast: showLast,
    functorLast: functorLast,
    applyLast: applyLast,
    applicativeLast: applicativeLast,
    bindLast: bindLast,
    monadLast: monadLast,
    semigroupLast: semigroupLast
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Bounded/index.js":78,"../Data.Eq/index.js":86,"../Data.Functor/index.js":102,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],135:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Semigroup_Foldable = require("../Data.Semigroup.Foldable/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Prelude = require("../Prelude/index.js");
var Traversable1 = function (Foldable10, Traversable1, sequence1, traverse1) {
    this.Foldable10 = Foldable10;
    this.Traversable1 = Traversable1;
    this.sequence1 = sequence1;
    this.traverse1 = traverse1;
};
var traverse1 = function (dict) {
    return dict.traverse1;
};
var sequence1Default = function (dictTraversable1) {
    return function (dictApply) {
        return traverse1(dictTraversable1)(dictApply)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var traversableDual = new Traversable1(function () {
    return Data_Semigroup_Foldable.foldableDual;
}, function () {
    return Data_Traversable.traversableDual;
}, function (dictApply) {
    return sequence1Default(traversableDual)(dictApply);
}, function (dictApply) {
    return function (f) {
        return function (v) {
            return Data_Functor.map(dictApply.Functor0())(Data_Monoid_Dual.Dual)(f(v));
        };
    };
});
var traversableMultiplicative = new Traversable1(function () {
    return Data_Semigroup_Foldable.foldableMultiplicative;
}, function () {
    return Data_Traversable.traversableMultiplicative;
}, function (dictApply) {
    return sequence1Default(traversableMultiplicative)(dictApply);
}, function (dictApply) {
    return function (f) {
        return function (v) {
            return Data_Functor.map(dictApply.Functor0())(Data_Monoid_Multiplicative.Multiplicative)(f(v));
        };
    };
});
var sequence1 = function (dict) {
    return dict.sequence1;
};
var traverse1Default = function (dictTraversable1) {
    return function (dictApply) {
        return function (f) {
            return function (ta) {
                return sequence1(dictTraversable1)(dictApply)(Data_Functor.map((dictTraversable1.Traversable1()).Functor0())(f)(ta));
            };
        };
    };
};
module.exports = {
    sequence1: sequence1,
    traverse1: traverse1,
    Traversable1: Traversable1,
    traverse1Default: traverse1Default,
    sequence1Default: sequence1Default,
    traversableDual: traversableDual,
    traversableMultiplicative: traversableMultiplicative
};

},{"../Control.Category/index.js":24,"../Data.Functor/index.js":102,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Semigroup.Foldable/index.js":133,"../Data.Traversable/index.js":159,"../Prelude/index.js":195}],136:[function(require,module,exports){
"use strict";

exports.concatString = function (s1) {
  return function (s2) {
    return s1 + s2;
  };
};

exports.concatArray = function (xs) {
  return function (ys) {
    if (xs.length === 0) return ys;
    if (ys.length === 0) return xs;
    return xs.concat(ys);
  };
};

},{}],137:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Data_Void = require("../Data.Void/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var Semigroup = function (append) {
    this.append = append;
};
var SemigroupRecord = function (appendRecord) {
    this.appendRecord = appendRecord;
};
var semigroupVoid = new Semigroup(function (v) {
    return Data_Void.absurd;
});
var semigroupUnit = new Semigroup(function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
});
var semigroupString = new Semigroup($foreign.concatString);
var semigroupRecordNil = new SemigroupRecord(function (v) {
    return function (v1) {
        return function (v2) {
            return {};
        };
    };
});
var semigroupArray = new Semigroup($foreign.concatArray);
var appendRecord = function (dict) {
    return dict.appendRecord;
};
var semigroupRecord = function (dictRowToList) {
    return function (dictSemigroupRecord) {
        return new Semigroup(appendRecord(dictSemigroupRecord)(Type_Data_RowList.RLProxy.value));
    };
};
var append = function (dict) {
    return dict.append;
};
var semigroupFn = function (dictSemigroup) {
    return new Semigroup(function (f) {
        return function (g) {
            return function (x) {
                return append(dictSemigroup)(f(x))(g(x));
            };
        };
    });
};
var semigroupRecordCons = function (dictIsSymbol) {
    return function (dictCons) {
        return function (dictSemigroupRecord) {
            return function (dictSemigroup) {
                return new SemigroupRecord(function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = appendRecord(dictSemigroupRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var insert = Record_Unsafe.unsafeSet(key);
                            var get = Record_Unsafe.unsafeGet(key);
                            return insert(append(dictSemigroup)(get(ra))(get(rb)))(tail);
                        };
                    };
                });
            };
        };
    };
};
module.exports = {
    Semigroup: Semigroup,
    append: append,
    SemigroupRecord: SemigroupRecord,
    appendRecord: appendRecord,
    semigroupString: semigroupString,
    semigroupUnit: semigroupUnit,
    semigroupVoid: semigroupVoid,
    semigroupFn: semigroupFn,
    semigroupArray: semigroupArray,
    semigroupRecord: semigroupRecord,
    semigroupRecordNil: semigroupRecordNil,
    semigroupRecordCons: semigroupRecordCons
};

},{"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168,"../Data.Void/index.js":169,"../Record.Unsafe/index.js":197,"../Type.Data.RowList/index.js":198,"./foreign.js":136}],138:[function(require,module,exports){
"use strict";

exports.intAdd = function (x) {
  return function (y) {
    /* jshint bitwise: false */
    return x + y | 0;
  };
};

exports.intMul = function (x) {
  return function (y) {
    /* jshint bitwise: false */
    return x * y | 0;
  };
};

exports.numAdd = function (n1) {
  return function (n2) {
    return n1 + n2;
  };
};

exports.numMul = function (n1) {
  return function (n2) {
    return n1 * n2;
  };
};

},{}],139:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_Row = require("../Type.Data.Row/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var Semiring = function (add, mul, one, zero) {
    this.add = add;
    this.mul = mul;
    this.one = one;
    this.zero = zero;
};
var SemiringRecord = function (addRecord, mulRecord, oneRecord, zeroRecord) {
    this.addRecord = addRecord;
    this.mulRecord = mulRecord;
    this.oneRecord = oneRecord;
    this.zeroRecord = zeroRecord;
};
var zeroRecord = function (dict) {
    return dict.zeroRecord;
};
var zero = function (dict) {
    return dict.zero;
};
var semiringUnit = new Semiring(function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
}, function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
}, Data_Unit.unit, Data_Unit.unit);
var semiringRecordNil = new SemiringRecord(function (v) {
    return function (v1) {
        return function (v2) {
            return {};
        };
    };
}, function (v) {
    return function (v1) {
        return function (v2) {
            return {};
        };
    };
}, function (v) {
    return function (v1) {
        return {};
    };
}, function (v) {
    return function (v1) {
        return {};
    };
});
var semiringNumber = new Semiring($foreign.numAdd, $foreign.numMul, 1.0, 0.0);
var semiringInt = new Semiring($foreign.intAdd, $foreign.intMul, 1, 0);
var oneRecord = function (dict) {
    return dict.oneRecord;
};
var one = function (dict) {
    return dict.one;
};
var mulRecord = function (dict) {
    return dict.mulRecord;
};
var mul = function (dict) {
    return dict.mul;
};
var addRecord = function (dict) {
    return dict.addRecord;
};
var semiringRecord = function (dictRowToList) {
    return function (dictSemiringRecord) {
        return new Semiring(addRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value), mulRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value), oneRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value)(Type_Data_Row.RProxy.value), zeroRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value)(Type_Data_Row.RProxy.value));
    };
};
var add = function (dict) {
    return dict.add;
};
var semiringFn = function (dictSemiring) {
    return new Semiring(function (f) {
        return function (g) {
            return function (x) {
                return add(dictSemiring)(f(x))(g(x));
            };
        };
    }, function (f) {
        return function (g) {
            return function (x) {
                return mul(dictSemiring)(f(x))(g(x));
            };
        };
    }, function (v) {
        return one(dictSemiring);
    }, function (v) {
        return zero(dictSemiring);
    });
};
var semiringRecordCons = function (dictIsSymbol) {
    return function (dictCons) {
        return function (dictSemiringRecord) {
            return function (dictSemiring) {
                return new SemiringRecord(function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = addRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var insert = Record_Unsafe.unsafeSet(key);
                            var get = Record_Unsafe.unsafeGet(key);
                            return insert(add(dictSemiring)(get(ra))(get(rb)))(tail);
                        };
                    };
                }, function (v) {
                    return function (ra) {
                        return function (rb) {
                            var tail = mulRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value)(ra)(rb);
                            var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                            var insert = Record_Unsafe.unsafeSet(key);
                            var get = Record_Unsafe.unsafeGet(key);
                            return insert(mul(dictSemiring)(get(ra))(get(rb)))(tail);
                        };
                    };
                }, function (v) {
                    return function (v1) {
                        var tail = oneRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value)(Type_Data_Row.RProxy.value);
                        var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                        var insert = Record_Unsafe.unsafeSet(key);
                        return insert(one(dictSemiring))(tail);
                    };
                }, function (v) {
                    return function (v1) {
                        var tail = zeroRecord(dictSemiringRecord)(Type_Data_RowList.RLProxy.value)(Type_Data_Row.RProxy.value);
                        var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                        var insert = Record_Unsafe.unsafeSet(key);
                        return insert(zero(dictSemiring))(tail);
                    };
                });
            };
        };
    };
};
module.exports = {
    Semiring: Semiring,
    add: add,
    zero: zero,
    mul: mul,
    one: one,
    SemiringRecord: SemiringRecord,
    addRecord: addRecord,
    mulRecord: mulRecord,
    oneRecord: oneRecord,
    zeroRecord: zeroRecord,
    semiringInt: semiringInt,
    semiringNumber: semiringNumber,
    semiringFn: semiringFn,
    semiringUnit: semiringUnit,
    semiringRecord: semiringRecord,
    semiringRecordNil: semiringRecordNil,
    semiringRecordCons: semiringRecordCons
};

},{"../Data.Symbol/index.js":153,"../Data.Unit/index.js":168,"../Record.Unsafe/index.js":197,"../Type.Data.Row/index.js":199,"../Type.Data.RowList/index.js":198,"./foreign.js":138}],140:[function(require,module,exports){
"use strict";

exports.showIntImpl = function (n) {
  return n.toString();
};

exports.showNumberImpl = function (n) {
  var str = n.toString();
  return isNaN(str + ".0") ? str : str + ".0";
};

exports.showCharImpl = function (c) {
  var code = c.charCodeAt(0);
  if (code < 0x20 || code === 0x7F) {
    switch (c) {
      case "\x07": return "'\\a'";
      case "\b": return "'\\b'";
      case "\f": return "'\\f'";
      case "\n": return "'\\n'";
      case "\r": return "'\\r'";
      case "\t": return "'\\t'";
      case "\v": return "'\\v'";
    }
    return "'\\" + code.toString(10) + "'";
  }
  return c === "'" || c === "\\" ? "'\\" + c + "'" : "'" + c + "'";
};

exports.showStringImpl = function (s) {
  var l = s.length;
  return "\"" + s.replace(
    /[\0-\x1F\x7F"\\]/g, // eslint-disable-line no-control-regex
    function (c, i) {
      switch (c) {
        case "\"":
        case "\\":
          return "\\" + c;
        case "\x07": return "\\a";
        case "\b": return "\\b";
        case "\f": return "\\f";
        case "\n": return "\\n";
        case "\r": return "\\r";
        case "\t": return "\\t";
        case "\v": return "\\v";
      }
      var k = i + 1;
      var empty = k < l && s[k] >= "0" && s[k] <= "9" ? "\\&" : "";
      return "\\" + c.charCodeAt(0).toString(10) + empty;
    }
  ) + "\"";
};

exports.showArrayImpl = function (f) {
  return function (xs) {
    var ss = [];
    for (var i = 0, l = xs.length; i < l; i++) {
      ss[i] = f(xs[i]);
    }
    return "[" + ss.join(",") + "]";
  };
};

exports.cons = function (head) {
  return function (tail) {
    return [head].concat(tail);
  };
};

exports.join = function (separator) {
  return function (xs) {
    return xs.join(separator);
  };
};

},{}],141:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Symbol = require("../Data.Symbol/index.js");
var Record_Unsafe = require("../Record.Unsafe/index.js");
var Type_Data_RowList = require("../Type.Data.RowList/index.js");
var Show = function (show) {
    this.show = show;
};
var ShowRecordFields = function (showRecordFields) {
    this.showRecordFields = showRecordFields;
};
var showString = new Show($foreign.showStringImpl);
var showRecordFieldsNil = new ShowRecordFields(function (v) {
    return function (v1) {
        return [  ];
    };
});
var showRecordFields = function (dict) {
    return dict.showRecordFields;
};
var showRecord = function (dictRowToList) {
    return function (dictShowRecordFields) {
        return new Show(function (record) {
            var v = showRecordFields(dictShowRecordFields)(Type_Data_RowList.RLProxy.value)(record);
            if (v.length === 0) {
                return "{}";
            };
            return $foreign.join(" ")([ "{", $foreign.join(", ")(v), "}" ]);
        });
    };
};
var showNumber = new Show($foreign.showNumberImpl);
var showInt = new Show($foreign.showIntImpl);
var showChar = new Show($foreign.showCharImpl);
var showBoolean = new Show(function (v) {
    if (v) {
        return "true";
    };
    if (!v) {
        return "false";
    };
    throw new Error("Failed pattern match at Data.Show line 20, column 1 - line 20, column 37: " + [ v.constructor.name ]);
});
var show = function (dict) {
    return dict.show;
};
var showArray = function (dictShow) {
    return new Show($foreign.showArrayImpl(show(dictShow)));
};
var showRecordFieldsCons = function (dictIsSymbol) {
    return function (dictShowRecordFields) {
        return function (dictShow) {
            return new ShowRecordFields(function (v) {
                return function (record) {
                    var tail = showRecordFields(dictShowRecordFields)(Type_Data_RowList.RLProxy.value)(record);
                    var key = Data_Symbol.reflectSymbol(dictIsSymbol)(Data_Symbol.SProxy.value);
                    var focus = Record_Unsafe.unsafeGet(key)(record);
                    return $foreign.cons($foreign.join(": ")([ key, show(dictShow)(focus) ]))(tail);
                };
            });
        };
    };
};
module.exports = {
    Show: Show,
    show: show,
    ShowRecordFields: ShowRecordFields,
    showRecordFields: showRecordFields,
    showBoolean: showBoolean,
    showInt: showInt,
    showNumber: showNumber,
    showChar: showChar,
    showString: showString,
    showArray: showArray,
    showRecord: showRecord,
    showRecordFieldsNil: showRecordFieldsNil,
    showRecordFieldsCons: showRecordFieldsCons
};

},{"../Data.Symbol/index.js":153,"../Record.Unsafe/index.js":197,"../Type.Data.RowList/index.js":198,"./foreign.js":140}],142:[function(require,module,exports){
"use strict";
/* global Symbol */

var hasArrayFrom = typeof Array.from === "function";
var hasStringIterator =
  typeof Symbol !== "undefined" &&
  Symbol != null &&
  typeof Symbol.iterator !== "undefined" &&
  typeof String.prototype[Symbol.iterator] === "function";
var hasFromCodePoint = typeof String.prototype.fromCodePoint === "function";
var hasCodePointAt = typeof String.prototype.codePointAt === "function";

exports._unsafeCodePointAt0 = function (fallback) {
  return hasCodePointAt
    ? function (str) { return str.codePointAt(0); }
    : fallback;
};

exports._codePointAt = function (fallback) {
  return function (Just) {
    return function (Nothing) {
      return function (unsafeCodePointAt0) {
        return function (index) {
          return function (str) {
            var length = str.length;
            if (index < 0 || index >= length) return Nothing;
            if (hasStringIterator) {
              var iter = str[Symbol.iterator]();
              for (var i = index;; --i) {
                var o = iter.next();
                if (o.done) return Nothing;
                if (i === 0) return Just(unsafeCodePointAt0(o.value));
              }
            }
            return fallback(index)(str);
          };
        };
      };
    };
  };
};

exports._countPrefix = function (fallback) {
  return function (unsafeCodePointAt0) {
    if (hasStringIterator) {
      return function (pred) {
        return function (str) {
          var iter = str[Symbol.iterator]();
          for (var cpCount = 0; ; ++cpCount) {
            var o = iter.next();
            if (o.done) return cpCount;
            var cp = unsafeCodePointAt0(o.value);
            if (!pred(cp)) return cpCount;
          }
        };
      };
    }
    return fallback;
  };
};

exports._fromCodePointArray = function (singleton) {
  return hasFromCodePoint
    ? function (cps) {
      // Function.prototype.apply will fail for very large second parameters,
      // so we don't use it for arrays with 10,000 or more entries.
      if (cps.length < 10e3) {
        return String.fromCodePoint.apply(String, cps);
      }
      return cps.map(singleton).join("");
    }
    : function (cps) {
      return cps.map(singleton).join("");
    };
};

exports._singleton = function (fallback) {
  return hasFromCodePoint ? String.fromCodePoint : fallback;
};

exports._take = function (fallback) {
  return function (n) {
    if (hasStringIterator) {
      return function (str) {
        var accum = "";
        var iter = str[Symbol.iterator]();
        for (var i = 0; i < n; ++i) {
          var o = iter.next();
          if (o.done) return accum;
          accum += o.value;
        }
        return accum;
      };
    }
    return fallback(n);
  };
};

exports._toCodePointArray = function (fallback) {
  return function (unsafeCodePointAt0) {
    if (hasArrayFrom) {
      return function (str) {
        return Array.from(str, unsafeCodePointAt0);
      };
    }
    return fallback;
  };
};

},{}],143:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Array = require("../Data.Array/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_Enum = require("../Data.Enum/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Int = require("../Data.Int/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_String_CodeUnits = require("../Data.String.CodeUnits/index.js");
var Data_String_Common = require("../Data.String.Common/index.js");
var Data_String_Pattern = require("../Data.String.Pattern/index.js");
var Data_String_Unsafe = require("../Data.String.Unsafe/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unfoldable = require("../Data.Unfoldable/index.js");
var Prelude = require("../Prelude/index.js");
var CodePoint = function (x) {
    return x;
};
var unsurrogate = function (lead) {
    return function (trail) {
        return (((lead - 55296 | 0) * 1024 | 0) + (trail - 56320 | 0) | 0) + 65536 | 0;
    };
};
var showCodePoint = new Data_Show.Show(function (v) {
    return "(CodePoint 0x" + (Data_String_Common.toUpper(Data_Int.toStringAs(Data_Int.hexadecimal)(v)) + ")");
});
var isTrail = function (cu) {
    return 56320 <= cu && cu <= 57343;
};
var isLead = function (cu) {
    return 55296 <= cu && cu <= 56319;
};
var uncons = function (s) {
    var v = Data_String_CodeUnits.length(s);
    if (v === 0) {
        return Data_Maybe.Nothing.value;
    };
    if (v === 1) {
        return new Data_Maybe.Just({
            head: Data_Enum.fromEnum(Data_Enum.boundedEnumChar)(Data_String_Unsafe.charAt(0)(s)),
            tail: ""
        });
    };
    var cu1 = Data_Enum.fromEnum(Data_Enum.boundedEnumChar)(Data_String_Unsafe.charAt(1)(s));
    var cu0 = Data_Enum.fromEnum(Data_Enum.boundedEnumChar)(Data_String_Unsafe.charAt(0)(s));
    var $21 = isLead(cu0) && isTrail(cu1);
    if ($21) {
        return new Data_Maybe.Just({
            head: unsurrogate(cu0)(cu1),
            tail: Data_String_CodeUnits.drop(2)(s)
        });
    };
    return new Data_Maybe.Just({
        head: cu0,
        tail: Data_String_CodeUnits.drop(1)(s)
    });
};
var unconsButWithTuple = function (s) {
    return Data_Functor.map(Data_Maybe.functorMaybe)(function (v) {
        return new Data_Tuple.Tuple(v.head, v.tail);
    })(uncons(s));
};
var toCodePointArrayFallback = function (s) {
    return Data_Unfoldable.unfoldr(Data_Unfoldable.unfoldableArray)(unconsButWithTuple)(s);
};
var unsafeCodePointAt0Fallback = function (s) {
    var cu1 = Data_Enum.fromEnum(Data_Enum.boundedEnumChar)(Data_String_Unsafe.charAt(1)(s));
    var cu0 = Data_Enum.fromEnum(Data_Enum.boundedEnumChar)(Data_String_Unsafe.charAt(0)(s));
    var $25 = isLead(cu0) && isTrail(cu1);
    if ($25) {
        return unsurrogate(cu0)(cu1);
    };
    return cu0;
};
var unsafeCodePointAt0 = $foreign._unsafeCodePointAt0(unsafeCodePointAt0Fallback);
var toCodePointArray = $foreign._toCodePointArray(toCodePointArrayFallback)(unsafeCodePointAt0);
var length = function ($51) {
    return Data_Array.length(toCodePointArray($51));
};
var lastIndexOf = function (p) {
    return function (s) {
        return Data_Functor.map(Data_Maybe.functorMaybe)(function (i) {
            return length(Data_String_CodeUnits.take(i)(s));
        })(Data_String_CodeUnits.lastIndexOf(p)(s));
    };
};
var indexOf = function (p) {
    return function (s) {
        return Data_Functor.map(Data_Maybe.functorMaybe)(function (i) {
            return length(Data_String_CodeUnits.take(i)(s));
        })(Data_String_CodeUnits.indexOf(p)(s));
    };
};
var fromCharCode = function ($52) {
    return Data_String_CodeUnits.singleton(Data_Enum.toEnumWithDefaults(Data_Enum.boundedEnumChar)(Data_Bounded.bottom(Data_Bounded.boundedChar))(Data_Bounded.top(Data_Bounded.boundedChar))($52));
};
var singletonFallback = function (v) {
    if (v <= 65535) {
        return fromCharCode(v);
    };
    var lead = Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt)(v - 65536 | 0)(1024) + 55296 | 0;
    var trail = Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt)(v - 65536 | 0)(1024) + 56320 | 0;
    return fromCharCode(lead) + fromCharCode(trail);
};
var fromCodePointArray = $foreign._fromCodePointArray(singletonFallback);
var singleton = $foreign._singleton(singletonFallback);
var takeFallback = function (n) {
    return function (v) {
        if (n < 1) {
            return "";
        };
        var v1 = uncons(v);
        if (v1 instanceof Data_Maybe.Just) {
            return singleton(v1.value0.head) + takeFallback(n - 1 | 0)(v1.value0.tail);
        };
        return v;
    };
};
var take = $foreign._take(takeFallback);
var lastIndexOf$prime = function (p) {
    return function (i) {
        return function (s) {
            var i$prime = Data_String_CodeUnits.length(take(i)(s));
            return Data_Functor.map(Data_Maybe.functorMaybe)(function (k) {
                return length(Data_String_CodeUnits.take(k)(s));
            })(Data_String_CodeUnits["lastIndexOf'"](p)(i$prime)(s));
        };
    };
};
var splitAt = function (i) {
    return function (s) {
        var before = take(i)(s);
        return {
            before: before,
            after: Data_String_CodeUnits.drop(Data_String_CodeUnits.length(before))(s)
        };
    };
};
var eqCodePoint = new Data_Eq.Eq(function (x) {
    return function (y) {
        return x === y;
    };
});
var ordCodePoint = new Data_Ord.Ord(function () {
    return eqCodePoint;
}, function (x) {
    return function (y) {
        return Data_Ord.compare(Data_Ord.ordInt)(x)(y);
    };
});
var drop = function (n) {
    return function (s) {
        return Data_String_CodeUnits.drop(Data_String_CodeUnits.length(take(n)(s)))(s);
    };
};
var indexOf$prime = function (p) {
    return function (i) {
        return function (s) {
            var s$prime = drop(i)(s);
            return Data_Functor.map(Data_Maybe.functorMaybe)(function (k) {
                return i + length(Data_String_CodeUnits.take(k)(s$prime)) | 0;
            })(Data_String_CodeUnits.indexOf(p)(s$prime));
        };
    };
};
var countTail = function ($copy_p) {
    return function ($copy_s) {
        return function ($copy_accum) {
            var $tco_var_p = $copy_p;
            var $tco_var_s = $copy_s;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(p, s, accum) {
                var v = uncons(s);
                if (v instanceof Data_Maybe.Just) {
                    var $38 = p(v.value0.head);
                    if ($38) {
                        $tco_var_p = p;
                        $tco_var_s = v.value0.tail;
                        $copy_accum = accum + 1 | 0;
                        return;
                    };
                    $tco_done = true;
                    return accum;
                };
                $tco_done = true;
                return accum;
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_p, $tco_var_s, $copy_accum);
            };
            return $tco_result;
        };
    };
};
var countFallback = function (p) {
    return function (s) {
        return countTail(p)(s)(0);
    };
};
var countPrefix = $foreign._countPrefix(countFallback)(unsafeCodePointAt0);
var dropWhile = function (p) {
    return function (s) {
        return drop(countPrefix(p)(s))(s);
    };
};
var takeWhile = function (p) {
    return function (s) {
        return take(countPrefix(p)(s))(s);
    };
};
var codePointFromChar = function ($53) {
    return CodePoint(Data_Enum.fromEnum(Data_Enum.boundedEnumChar)($53));
};
var codePointAtFallback = function ($copy_n) {
    return function ($copy_s) {
        var $tco_var_n = $copy_n;
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(n, s) {
            var v = uncons(s);
            if (v instanceof Data_Maybe.Just) {
                var $43 = n === 0;
                if ($43) {
                    $tco_done = true;
                    return new Data_Maybe.Just(v.value0.head);
                };
                $tco_var_n = n - 1 | 0;
                $copy_s = v.value0.tail;
                return;
            };
            $tco_done = true;
            return Data_Maybe.Nothing.value;
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($tco_var_n, $copy_s);
        };
        return $tco_result;
    };
};
var codePointAt = function (v) {
    return function (v1) {
        if (v < 0) {
            return Data_Maybe.Nothing.value;
        };
        if (v === 0 && v1 === "") {
            return Data_Maybe.Nothing.value;
        };
        if (v === 0) {
            return new Data_Maybe.Just(unsafeCodePointAt0(v1));
        };
        return $foreign._codePointAt(codePointAtFallback)(Data_Maybe.Just.create)(Data_Maybe.Nothing.value)(unsafeCodePointAt0)(v)(v1);
    };
};
var boundedCodePoint = new Data_Bounded.Bounded(function () {
    return ordCodePoint;
}, 0, 1114111);
var boundedEnumCodePoint = new Data_Enum.BoundedEnum(function () {
    return boundedCodePoint;
}, function () {
    return enumCodePoint;
}, 1114111 + 1 | 0, function (v) {
    return v;
}, function (n) {
    if (n >= 0 && n <= 1114111) {
        return new Data_Maybe.Just(n);
    };
    if (Data_Boolean.otherwise) {
        return Data_Maybe.Nothing.value;
    };
    throw new Error("Failed pattern match at Data.String.CodePoints line 63, column 1 - line 63, column 55: " + [ n.constructor.name ]);
});
var enumCodePoint = new Data_Enum.Enum(function () {
    return ordCodePoint;
}, Data_Enum.defaultPred(Data_Enum.toEnum(boundedEnumCodePoint))(Data_Enum.fromEnum(boundedEnumCodePoint)), Data_Enum.defaultSucc(Data_Enum.toEnum(boundedEnumCodePoint))(Data_Enum.fromEnum(boundedEnumCodePoint)));
module.exports = {
    codePointFromChar: codePointFromChar,
    singleton: singleton,
    fromCodePointArray: fromCodePointArray,
    toCodePointArray: toCodePointArray,
    codePointAt: codePointAt,
    uncons: uncons,
    length: length,
    countPrefix: countPrefix,
    indexOf: indexOf,
    "indexOf'": indexOf$prime,
    lastIndexOf: lastIndexOf,
    "lastIndexOf'": lastIndexOf$prime,
    take: take,
    takeWhile: takeWhile,
    drop: drop,
    dropWhile: dropWhile,
    splitAt: splitAt,
    eqCodePoint: eqCodePoint,
    ordCodePoint: ordCodePoint,
    showCodePoint: showCodePoint,
    boundedCodePoint: boundedCodePoint,
    enumCodePoint: enumCodePoint,
    boundedEnumCodePoint: boundedEnumCodePoint
};

},{"../Control.Semigroupoid/index.js":51,"../Data.Array/index.js":66,"../Data.Boolean/index.js":76,"../Data.Bounded/index.js":78,"../Data.Enum/index.js":84,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Int/index.js":109,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Data.String.CodeUnits/index.js":145,"../Data.String.Common/index.js":147,"../Data.String.Pattern/index.js":148,"../Data.String.Unsafe/index.js":150,"../Data.Tuple/index.js":160,"../Data.Unfoldable/index.js":166,"../Prelude/index.js":195,"./foreign.js":142}],144:[function(require,module,exports){
"use strict";

exports.fromCharArray = function (a) {
  return a.join("");
};

exports.toCharArray = function (s) {
  return s.split("");
};

exports.singleton = function (c) {
  return c;
};

exports._charAt = function (just) {
  return function (nothing) {
    return function (i) {
      return function (s) {
        return i >= 0 && i < s.length ? just(s.charAt(i)) : nothing;
      };
    };
  };
};

exports._toChar = function (just) {
  return function (nothing) {
    return function (s) {
      return s.length === 1 ? just(s) : nothing;
    };
  };
};

exports.length = function (s) {
  return s.length;
};

exports.countPrefix = function (p) {
  return function (s) {
    var i = 0;
    while (i < s.length && p(s.charAt(i))) i++;
    return i;
  };
};

exports._indexOf = function (just) {
  return function (nothing) {
    return function (x) {
      return function (s) {
        var i = s.indexOf(x);
        return i === -1 ? nothing : just(i);
      };
    };
  };
};

exports["_indexOf'"] = function (just) {
  return function (nothing) {
    return function (x) {
      return function (startAt) {
        return function (s) {
          if (startAt < 0 || startAt > s.length) return nothing;
          var i = s.indexOf(x, startAt);
          return i === -1 ? nothing : just(i);
        };
      };
    };
  };
};

exports._lastIndexOf = function (just) {
  return function (nothing) {
    return function (x) {
      return function (s) {
        var i = s.lastIndexOf(x);
        return i === -1 ? nothing : just(i);
      };
    };
  };
};

exports["_lastIndexOf'"] = function (just) {
  return function (nothing) {
    return function (x) {
      return function (startAt) {
        return function (s) {
          if (startAt < 0 || startAt > s.length) return nothing;
          var i = s.lastIndexOf(x, startAt);
          return i === -1 ? nothing : just(i);
        };
      };
    };
  };
};

exports.take = function (n) {
  return function (s) {
    return s.substr(0, n);
  };
};

exports.drop = function (n) {
  return function (s) {
    return s.substring(n);
  };
};

exports._slice = function (b) {
  return function (e) {
    return function (s) {
      return s.slice(b,e);
    };
  };
};

exports.splitAt = function (i) {
  return function (s) {
    return { before: s.substring(0, i), after: s.substring(i) };
  };
};

},{}],145:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_String_Pattern = require("../Data.String.Pattern/index.js");
var Data_String_Unsafe = require("../Data.String.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var uncons = function (v) {
    if (v === "") {
        return Data_Maybe.Nothing.value;
    };
    return new Data_Maybe.Just({
        head: Data_String_Unsafe.charAt(0)(v),
        tail: $foreign.drop(1)(v)
    });
};
var toChar = $foreign._toChar(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var takeWhile = function (p) {
    return function (s) {
        return $foreign.take($foreign.countPrefix(p)(s))(s);
    };
};
var takeRight = function (i) {
    return function (s) {
        return $foreign.drop($foreign.length(s) - i | 0)(s);
    };
};
var slice = function (b) {
    return function (e) {
        return function (s) {
            var l = $foreign.length(s);
            var norm = function (x) {
                if (x < 0) {
                    return l + x | 0;
                };
                if (Data_Boolean.otherwise) {
                    return x;
                };
                throw new Error("Failed pattern match at Data.String.CodeUnits line 314, column 5 - line 315, column 27: " + [ x.constructor.name ]);
            };
            var e$prime = norm(e);
            var b$prime = norm(b);
            var $7 = b$prime < 0 || (b$prime >= l || (e$prime < 0 || (e$prime >= l || b$prime > e$prime)));
            if ($7) {
                return Data_Maybe.Nothing.value;
            };
            return new Data_Maybe.Just($foreign._slice(b)(e)(s));
        };
    };
};
var lastIndexOf$prime = $foreign["_lastIndexOf'"](Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var lastIndexOf = $foreign._lastIndexOf(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var stripSuffix = function (v) {
    return function (str) {
        var v1 = lastIndexOf(v)(str);
        if (v1 instanceof Data_Maybe.Just && v1.value0 === ($foreign.length(str) - $foreign.length(v) | 0)) {
            return Data_Maybe.Just.create($foreign.take(v1.value0)(str));
        };
        return Data_Maybe.Nothing.value;
    };
};
var indexOf$prime = $foreign["_indexOf'"](Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var indexOf = $foreign._indexOf(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var stripPrefix = function (v) {
    return function (str) {
        var v1 = indexOf(v)(str);
        if (v1 instanceof Data_Maybe.Just && v1.value0 === 0) {
            return Data_Maybe.Just.create($foreign.drop($foreign.length(v))(str));
        };
        return Data_Maybe.Nothing.value;
    };
};
var dropWhile = function (p) {
    return function (s) {
        return $foreign.drop($foreign.countPrefix(p)(s))(s);
    };
};
var dropRight = function (i) {
    return function (s) {
        return $foreign.take($foreign.length(s) - i | 0)(s);
    };
};
var contains = function (pat) {
    return function ($16) {
        return Data_Maybe.isJust(indexOf(pat)($16));
    };
};
var charAt = $foreign._charAt(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
module.exports = {
    stripPrefix: stripPrefix,
    stripSuffix: stripSuffix,
    contains: contains,
    charAt: charAt,
    toChar: toChar,
    uncons: uncons,
    indexOf: indexOf,
    "indexOf'": indexOf$prime,
    lastIndexOf: lastIndexOf,
    "lastIndexOf'": lastIndexOf$prime,
    takeRight: takeRight,
    takeWhile: takeWhile,
    dropRight: dropRight,
    dropWhile: dropWhile,
    slice: slice,
    singleton: $foreign.singleton,
    fromCharArray: $foreign.fromCharArray,
    toCharArray: $foreign.toCharArray,
    length: $foreign.length,
    countPrefix: $foreign.countPrefix,
    take: $foreign.take,
    drop: $foreign.drop,
    splitAt: $foreign.splitAt
};

},{"../Control.Semigroupoid/index.js":51,"../Data.Boolean/index.js":76,"../Data.Eq/index.js":86,"../Data.Function/index.js":95,"../Data.HeytingAlgebra/index.js":104,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139,"../Data.String.Pattern/index.js":148,"../Data.String.Unsafe/index.js":150,"../Prelude/index.js":195,"./foreign.js":144}],146:[function(require,module,exports){
"use strict";

exports._localeCompare = function (lt) {
  return function (eq) {
    return function (gt) {
      return function (s1) {
        return function (s2) {
          var result = s1.localeCompare(s2);
          return result < 0 ? lt : result > 0 ? gt : eq;
        };
      };
    };
  };
};

exports.replace = function (s1) {
  return function (s2) {
    return function (s3) {
      return s3.replace(s1, s2);
    };
  };
};

exports.replaceAll = function (s1) {
  return function (s2) {
    return function (s3) {
      return s3.replace(new RegExp(s1.replace(/[-\/\\^$*+?.()|[\]{}]/g, "\\$&"), "g"), s2); // eslint-disable-line no-useless-escape
    };
  };
};

exports.split = function (sep) {
  return function (s) {
    return s.split(sep);
  };
};

exports.toLower = function (s) {
  return s.toLowerCase();
};

exports.toUpper = function (s) {
  return s.toUpperCase();
};

exports.trim = function (s) {
  return s.trim();
};

exports.joinWith = function (s) {
  return function (xs) {
    return xs.join(s);
  };
};

},{}],147:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_String_Pattern = require("../Data.String.Pattern/index.js");
var Prelude = require("../Prelude/index.js");
var $$null = function (s) {
    return s === "";
};
var localeCompare = $foreign._localeCompare(Data_Ordering.LT.value)(Data_Ordering.EQ.value)(Data_Ordering.GT.value);
module.exports = {
    "null": $$null,
    localeCompare: localeCompare,
    replace: $foreign.replace,
    replaceAll: $foreign.replaceAll,
    split: $foreign.split,
    toLower: $foreign.toLower,
    toUpper: $foreign.toUpper,
    trim: $foreign.trim,
    joinWith: $foreign.joinWith
};

},{"../Data.Eq/index.js":86,"../Data.Ordering/index.js":129,"../Data.String.Pattern/index.js":148,"../Prelude/index.js":195,"./foreign.js":146}],148:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Eq = require("../Data.Eq/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Replacement = function (x) {
    return x;
};
var Pattern = function (x) {
    return x;
};
var showReplacement = new Data_Show.Show(function (v) {
    return "(Replacement " + (Data_Show.show(Data_Show.showString)(v) + ")");
});
var showPattern = new Data_Show.Show(function (v) {
    return "(Pattern " + (Data_Show.show(Data_Show.showString)(v) + ")");
});
var newtypeReplacement = new Data_Newtype.Newtype(function (n) {
    return n;
}, Replacement);
var newtypePattern = new Data_Newtype.Newtype(function (n) {
    return n;
}, Pattern);
var eqReplacement = new Data_Eq.Eq(function (x) {
    return function (y) {
        return x === y;
    };
});
var ordReplacement = new Data_Ord.Ord(function () {
    return eqReplacement;
}, function (x) {
    return function (y) {
        return Data_Ord.compare(Data_Ord.ordString)(x)(y);
    };
});
var eqPattern = new Data_Eq.Eq(function (x) {
    return function (y) {
        return x === y;
    };
});
var ordPattern = new Data_Ord.Ord(function () {
    return eqPattern;
}, function (x) {
    return function (y) {
        return Data_Ord.compare(Data_Ord.ordString)(x)(y);
    };
});
module.exports = {
    Pattern: Pattern,
    Replacement: Replacement,
    eqPattern: eqPattern,
    ordPattern: ordPattern,
    newtypePattern: newtypePattern,
    showPattern: showPattern,
    eqReplacement: eqReplacement,
    ordReplacement: ordReplacement,
    newtypeReplacement: newtypeReplacement,
    showReplacement: showReplacement
};

},{"../Data.Eq/index.js":86,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Semigroup/index.js":137,"../Data.Show/index.js":141,"../Prelude/index.js":195}],149:[function(require,module,exports){
"use strict";

exports.charAt = function (i) {
  return function (s) {
    if (i >= 0 && i < s.length) return s.charAt(i);
    throw new Error("Data.String.Unsafe.charAt: Invalid index.");
  };
};

exports.char = function (s) {
  if (s.length === 1) return s.charAt(0);
  throw new Error("Data.String.Unsafe.char: Expected string of length 1.");
};

},{}],150:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
module.exports = {
    "char": $foreign["char"],
    charAt: $foreign.charAt
};

},{"./foreign.js":149}],151:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_String_CodePoints = require("../Data.String.CodePoints/index.js");
var Data_String_Common = require("../Data.String.Common/index.js");
var Data_String_Pattern = require("../Data.String.Pattern/index.js");
module.exports = {};

},{"../Data.String.CodePoints/index.js":143,"../Data.String.Common/index.js":147,"../Data.String.Pattern/index.js":148}],152:[function(require,module,exports){
"use strict";

// module Data.Symbol

exports.unsafeCoerce = function (arg) {
  return arg;
};


},{}],153:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var SProxy = (function () {
    function SProxy() {

    };
    SProxy.value = new SProxy();
    return SProxy;
})();
var IsSymbol = function (reflectSymbol) {
    this.reflectSymbol = reflectSymbol;
};
var reifySymbol = function (s) {
    return function (f) {
        return $foreign.unsafeCoerce(function (dictIsSymbol) {
            return f(dictIsSymbol);
        })({
            reflectSymbol: function (v) {
                return s;
            }
        })(SProxy.value);
    };
};
var reflectSymbol = function (dict) {
    return dict.reflectSymbol;
};
module.exports = {
    IsSymbol: IsSymbol,
    reflectSymbol: reflectSymbol,
    reifySymbol: reifySymbol,
    SProxy: SProxy
};

},{"./foreign.js":152}],154:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Prelude = require("../Prelude/index.js");
var Seconds = function (x) {
    return x;
};
var Minutes = function (x) {
    return x;
};
var Milliseconds = function (x) {
    return x;
};
var Hours = function (x) {
    return x;
};
var Days = function (x) {
    return x;
};
var Duration = function (fromDuration, toDuration) {
    this.fromDuration = fromDuration;
    this.toDuration = toDuration;
};
var toDuration = function (dict) {
    return dict.toDuration;
};
var showSeconds = new Data_Show.Show(function (v) {
    return "(Seconds " + (Data_Show.show(Data_Show.showNumber)(v) + ")");
});
var showMinutes = new Data_Show.Show(function (v) {
    return "(Minutes " + (Data_Show.show(Data_Show.showNumber)(v) + ")");
});
var showMilliseconds = new Data_Show.Show(function (v) {
    return "(Milliseconds " + (Data_Show.show(Data_Show.showNumber)(v) + ")");
});
var showHours = new Data_Show.Show(function (v) {
    return "(Hours " + (Data_Show.show(Data_Show.showNumber)(v) + ")");
});
var showDays = new Data_Show.Show(function (v) {
    return "(Days " + (Data_Show.show(Data_Show.showNumber)(v) + ")");
});
var semigroupSeconds = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        return v + v1;
    };
});
var semigroupMinutes = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        return v + v1;
    };
});
var semigroupMilliseconds = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        return v + v1;
    };
});
var semigroupHours = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        return v + v1;
    };
});
var semigroupDays = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        return v + v1;
    };
});
var ordSeconds = Data_Ord.ordNumber;
var ordMinutes = Data_Ord.ordNumber;
var ordMilliseconds = Data_Ord.ordNumber;
var ordHours = Data_Ord.ordNumber;
var ordDays = Data_Ord.ordNumber;
var newtypeSeconds = new Data_Newtype.Newtype(function (n) {
    return n;
}, Seconds);
var newtypeMinutes = new Data_Newtype.Newtype(function (n) {
    return n;
}, Minutes);
var newtypeMilliseconds = new Data_Newtype.Newtype(function (n) {
    return n;
}, Milliseconds);
var newtypeHours = new Data_Newtype.Newtype(function (n) {
    return n;
}, Hours);
var newtypeDays = new Data_Newtype.Newtype(function (n) {
    return n;
}, Days);
var monoidSeconds = new Data_Monoid.Monoid(function () {
    return semigroupSeconds;
}, 0.0);
var monoidMinutes = new Data_Monoid.Monoid(function () {
    return semigroupMinutes;
}, 0.0);
var monoidMilliseconds = new Data_Monoid.Monoid(function () {
    return semigroupMilliseconds;
}, 0.0);
var monoidHours = new Data_Monoid.Monoid(function () {
    return semigroupHours;
}, 0.0);
var monoidDays = new Data_Monoid.Monoid(function () {
    return semigroupDays;
}, 0.0);
var fromDuration = function (dict) {
    return dict.fromDuration;
};
var negateDuration = function (dictDuration) {
    return function ($56) {
        return toDuration(dictDuration)(Data_Newtype.over(newtypeMilliseconds)(newtypeMilliseconds)(Milliseconds)(Data_Ring.negate(Data_Ring.ringNumber))(fromDuration(dictDuration)($56)));
    };
};
var eqSeconds = Data_Eq.eqNumber;
var eqMinutes = Data_Eq.eqNumber;
var eqMilliseconds = Data_Eq.eqNumber;
var eqHours = Data_Eq.eqNumber;
var eqDays = Data_Eq.eqNumber;
var durationSeconds = new Duration(Data_Newtype.over(newtypeSeconds)(newtypeMilliseconds)(Seconds)(function (v) {
    return v * 1000.0;
}), Data_Newtype.over(newtypeMilliseconds)(newtypeSeconds)(Milliseconds)(function (v) {
    return v / 1000.0;
}));
var durationMinutes = new Duration(Data_Newtype.over(newtypeMinutes)(newtypeMilliseconds)(Minutes)(function (v) {
    return v * 60000.0;
}), Data_Newtype.over(newtypeMilliseconds)(newtypeMinutes)(Milliseconds)(function (v) {
    return v / 60000.0;
}));
var durationMilliseconds = new Duration(Control_Category.identity(Control_Category.categoryFn), Control_Category.identity(Control_Category.categoryFn));
var durationHours = new Duration(Data_Newtype.over(newtypeHours)(newtypeMilliseconds)(Hours)(function (v) {
    return v * 3600000.0;
}), Data_Newtype.over(newtypeMilliseconds)(newtypeHours)(Milliseconds)(function (v) {
    return v / 3600000.0;
}));
var durationDays = new Duration(Data_Newtype.over(newtypeDays)(newtypeMilliseconds)(Days)(function (v) {
    return v * 8.64e7;
}), Data_Newtype.over(newtypeMilliseconds)(newtypeDays)(Milliseconds)(function (v) {
    return v / 8.64e7;
}));
var convertDuration = function (dictDuration) {
    return function (dictDuration1) {
        return function ($57) {
            return toDuration(dictDuration1)(fromDuration(dictDuration)($57));
        };
    };
};
module.exports = {
    fromDuration: fromDuration,
    toDuration: toDuration,
    Milliseconds: Milliseconds,
    Seconds: Seconds,
    Minutes: Minutes,
    Hours: Hours,
    Days: Days,
    Duration: Duration,
    convertDuration: convertDuration,
    negateDuration: negateDuration,
    newtypeMilliseconds: newtypeMilliseconds,
    eqMilliseconds: eqMilliseconds,
    ordMilliseconds: ordMilliseconds,
    semigroupMilliseconds: semigroupMilliseconds,
    monoidMilliseconds: monoidMilliseconds,
    showMilliseconds: showMilliseconds,
    newtypeSeconds: newtypeSeconds,
    eqSeconds: eqSeconds,
    ordSeconds: ordSeconds,
    semigroupSeconds: semigroupSeconds,
    monoidSeconds: monoidSeconds,
    showSeconds: showSeconds,
    newtypeMinutes: newtypeMinutes,
    eqMinutes: eqMinutes,
    ordMinutes: ordMinutes,
    semigroupMinutes: semigroupMinutes,
    monoidMinutes: monoidMinutes,
    showMinutes: showMinutes,
    newtypeHours: newtypeHours,
    eqHours: eqHours,
    ordHours: ordHours,
    semigroupHours: semigroupHours,
    monoidHours: monoidHours,
    showHours: showHours,
    newtypeDays: newtypeDays,
    eqDays: eqDays,
    ordDays: ordDays,
    semigroupDays: semigroupDays,
    monoidDays: monoidDays,
    showDays: showDays,
    durationMilliseconds: durationMilliseconds,
    durationSeconds: durationSeconds,
    durationMinutes: durationMinutes,
    durationHours: durationHours,
    durationDays: durationDays
};

},{"../Control.Category/index.js":24,"../Control.Semigroupoid/index.js":51,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Prelude/index.js":195}],155:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Traversable_Accum = require("../Data.Traversable.Accum/index.js");
var Prelude = require("../Prelude/index.js");
var StateR = function (x) {
    return x;
};
var StateL = function (x) {
    return x;
};
var stateR = function (v) {
    return v;
};
var stateL = function (v) {
    return v;
};
var functorStateR = new Data_Functor.Functor(function (f) {
    return function (k) {
        return function (s) {
            var v = stateR(k)(s);
            return {
                accum: v.accum,
                value: f(v.value)
            };
        };
    };
});
var functorStateL = new Data_Functor.Functor(function (f) {
    return function (k) {
        return function (s) {
            var v = stateL(k)(s);
            return {
                accum: v.accum,
                value: f(v.value)
            };
        };
    };
});
var applyStateR = new Control_Apply.Apply(function () {
    return functorStateR;
}, function (f) {
    return function (x) {
        return function (s) {
            var v = stateR(x)(s);
            var v1 = stateR(f)(v.accum);
            return {
                accum: v1.accum,
                value: v1.value(v.value)
            };
        };
    };
});
var applyStateL = new Control_Apply.Apply(function () {
    return functorStateL;
}, function (f) {
    return function (x) {
        return function (s) {
            var v = stateL(f)(s);
            var v1 = stateL(x)(v.accum);
            return {
                accum: v1.accum,
                value: v.value(v1.value)
            };
        };
    };
});
var applicativeStateR = new Control_Applicative.Applicative(function () {
    return applyStateR;
}, function (a) {
    return function (s) {
        return {
            accum: s,
            value: a
        };
    };
});
var applicativeStateL = new Control_Applicative.Applicative(function () {
    return applyStateL;
}, function (a) {
    return function (s) {
        return {
            accum: s,
            value: a
        };
    };
});
module.exports = {
    StateL: StateL,
    stateL: stateL,
    StateR: StateR,
    stateR: stateR,
    functorStateL: functorStateL,
    applyStateL: applyStateL,
    applicativeStateL: applicativeStateL,
    functorStateR: functorStateR,
    applyStateR: applyStateR,
    applicativeStateR: applicativeStateR
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Data.Functor/index.js":102,"../Data.Traversable.Accum/index.js":156,"../Prelude/index.js":195}],156:[function(require,module,exports){
arguments[4][64][0].apply(exports,arguments)
},{"dup":64}],157:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_FoldableWithIndex = require("../Data.FoldableWithIndex/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_FunctorWithIndex = require("../Data.FunctorWithIndex/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Maybe_First = require("../Data.Maybe.First/index.js");
var Data_Maybe_Last = require("../Data.Maybe.Last/index.js");
var Data_Monoid_Additive = require("../Data.Monoid.Additive/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Data_Traversable_Accum = require("../Data.Traversable.Accum/index.js");
var Data_Traversable_Accum_Internal = require("../Data.Traversable.Accum.Internal/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var TraversableWithIndex = function (FoldableWithIndex1, FunctorWithIndex0, Traversable2, traverseWithIndex) {
    this.FoldableWithIndex1 = FoldableWithIndex1;
    this.FunctorWithIndex0 = FunctorWithIndex0;
    this.Traversable2 = Traversable2;
    this.traverseWithIndex = traverseWithIndex;
};
var traverseWithIndexDefault = function (dictTraversableWithIndex) {
    return function (dictApplicative) {
        return function (f) {
            return function ($19) {
                return Data_Traversable.sequence(dictTraversableWithIndex.Traversable2())(dictApplicative)(Data_FunctorWithIndex.mapWithIndex(dictTraversableWithIndex.FunctorWithIndex0())(f)($19));
            };
        };
    };
};
var traverseWithIndex = function (dict) {
    return dict.traverseWithIndex;
};
var traverseDefault = function (dictTraversableWithIndex) {
    return function (dictApplicative) {
        return function (f) {
            return traverseWithIndex(dictTraversableWithIndex)(dictApplicative)(Data_Function["const"](f));
        };
    };
};
var traversableWithIndexMultiplicative = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexMultiplicative;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexMultiplicative;
}, function () {
    return Data_Traversable.traversableMultiplicative;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableMultiplicative)(dictApplicative)(f(Data_Unit.unit));
    };
});
var traversableWithIndexMaybe = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexMaybe;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexMaybe;
}, function () {
    return Data_Traversable.traversableMaybe;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableMaybe)(dictApplicative)(f(Data_Unit.unit));
    };
});
var traversableWithIndexLast = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexLast;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexLast;
}, function () {
    return Data_Traversable.traversableLast;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableLast)(dictApplicative)(f(Data_Unit.unit));
    };
});
var traversableWithIndexFirst = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexFirst;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexFirst;
}, function () {
    return Data_Traversable.traversableFirst;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableFirst)(dictApplicative)(f(Data_Unit.unit));
    };
});
var traversableWithIndexDual = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexDual;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexDual;
}, function () {
    return Data_Traversable.traversableDual;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableDual)(dictApplicative)(f(Data_Unit.unit));
    };
});
var traversableWithIndexDisj = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexDisj;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexDisj;
}, function () {
    return Data_Traversable.traversableDisj;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableDisj)(dictApplicative)(f(Data_Unit.unit));
    };
});
var traversableWithIndexConj = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexConj;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexConj;
}, function () {
    return Data_Traversable.traversableConj;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableConj)(dictApplicative)(f(Data_Unit.unit));
    };
});
var traversableWithIndexArray = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexArray;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexArray;
}, function () {
    return Data_Traversable.traversableArray;
}, function (dictApplicative) {
    return traverseWithIndexDefault(traversableWithIndexArray)(dictApplicative);
});
var traversableWithIndexAdditive = new TraversableWithIndex(function () {
    return Data_FoldableWithIndex.foldableWithIndexAdditive;
}, function () {
    return Data_FunctorWithIndex.functorWithIndexAdditive;
}, function () {
    return Data_Traversable.traversableAdditive;
}, function (dictApplicative) {
    return function (f) {
        return Data_Traversable.traverse(Data_Traversable.traversableAdditive)(dictApplicative)(f(Data_Unit.unit));
    };
});
var mapAccumRWithIndex = function (dictTraversableWithIndex) {
    return function (f) {
        return function (s0) {
            return function (xs) {
                return Data_Traversable_Accum_Internal.stateR(traverseWithIndex(dictTraversableWithIndex)(Data_Traversable_Accum_Internal.applicativeStateR)(function (i) {
                    return function (a) {
                        return function (s) {
                            return f(i)(s)(a);
                        };
                    };
                })(xs))(s0);
            };
        };
    };
};
var scanrWithIndex = function (dictTraversableWithIndex) {
    return function (f) {
        return function (b0) {
            return function (xs) {
                return (mapAccumRWithIndex(dictTraversableWithIndex)(function (i) {
                    return function (b) {
                        return function (a) {
                            var b$prime = f(i)(a)(b);
                            return {
                                accum: b$prime,
                                value: b$prime
                            };
                        };
                    };
                })(b0)(xs)).value;
            };
        };
    };
};
var mapAccumLWithIndex = function (dictTraversableWithIndex) {
    return function (f) {
        return function (s0) {
            return function (xs) {
                return Data_Traversable_Accum_Internal.stateL(traverseWithIndex(dictTraversableWithIndex)(Data_Traversable_Accum_Internal.applicativeStateL)(function (i) {
                    return function (a) {
                        return function (s) {
                            return f(i)(s)(a);
                        };
                    };
                })(xs))(s0);
            };
        };
    };
};
var scanlWithIndex = function (dictTraversableWithIndex) {
    return function (f) {
        return function (b0) {
            return function (xs) {
                return (mapAccumLWithIndex(dictTraversableWithIndex)(function (i) {
                    return function (b) {
                        return function (a) {
                            var b$prime = f(i)(b)(a);
                            return {
                                accum: b$prime,
                                value: b$prime
                            };
                        };
                    };
                })(b0)(xs)).value;
            };
        };
    };
};
var forWithIndex = function (dictApplicative) {
    return function (dictTraversableWithIndex) {
        return Data_Function.flip(traverseWithIndex(dictTraversableWithIndex)(dictApplicative));
    };
};
module.exports = {
    TraversableWithIndex: TraversableWithIndex,
    traverseWithIndex: traverseWithIndex,
    traverseWithIndexDefault: traverseWithIndexDefault,
    forWithIndex: forWithIndex,
    scanlWithIndex: scanlWithIndex,
    mapAccumLWithIndex: mapAccumLWithIndex,
    scanrWithIndex: scanrWithIndex,
    mapAccumRWithIndex: mapAccumRWithIndex,
    traverseDefault: traverseDefault,
    traversableWithIndexArray: traversableWithIndexArray,
    traversableWithIndexMaybe: traversableWithIndexMaybe,
    traversableWithIndexFirst: traversableWithIndexFirst,
    traversableWithIndexLast: traversableWithIndexLast,
    traversableWithIndexAdditive: traversableWithIndexAdditive,
    traversableWithIndexDual: traversableWithIndexDual,
    traversableWithIndexConj: traversableWithIndexConj,
    traversableWithIndexDisj: traversableWithIndexDisj,
    traversableWithIndexMultiplicative: traversableWithIndexMultiplicative
};

},{"../Control.Semigroupoid/index.js":51,"../Data.FoldableWithIndex/index.js":90,"../Data.Function/index.js":95,"../Data.FunctorWithIndex/index.js":100,"../Data.Maybe.First/index.js":110,"../Data.Maybe.Last/index.js":111,"../Data.Maybe/index.js":112,"../Data.Monoid.Additive/index.js":113,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Traversable.Accum.Internal/index.js":155,"../Data.Traversable.Accum/index.js":156,"../Data.Traversable/index.js":159,"../Data.Unit/index.js":168,"../Prelude/index.js":195}],158:[function(require,module,exports){
"use strict";

// jshint maxparams: 3

exports.traverseArrayImpl = function () {
  function array1(a) {
    return [a];
  }

  function array2(a) {
    return function (b) {
      return [a, b];
    };
  }

  function array3(a) {
    return function (b) {
      return function (c) {
        return [a, b, c];
      };
    };
  }

  function concat2(xs) {
    return function (ys) {
      return xs.concat(ys);
    };
  }

  return function (apply) {
    return function (map) {
      return function (pure) {
        return function (f) {
          return function (array) {
            function go(bot, top) {
              switch (top - bot) {
              case 0: return pure([]);
              case 1: return map(array1)(f(array[bot]));
              case 2: return apply(map(array2)(f(array[bot])))(f(array[bot + 1]));
              case 3: return apply(apply(map(array3)(f(array[bot])))(f(array[bot + 1])))(f(array[bot + 2]));
              default:
                // This slightly tricky pivot selection aims to produce two
                // even-length partitions where possible.
                var pivot = bot + Math.floor((top - bot) / 4) * 2;
                return apply(map(concat2)(go(bot, pivot)))(go(pivot, top));
              }
            }
            return go(0, array.length);
          };
        };
      };
    };
  };
}();

},{}],159:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Category = require("../Control.Category/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Maybe_First = require("../Data.Maybe.First/index.js");
var Data_Maybe_Last = require("../Data.Maybe.Last/index.js");
var Data_Monoid_Additive = require("../Data.Monoid.Additive/index.js");
var Data_Monoid_Conj = require("../Data.Monoid.Conj/index.js");
var Data_Monoid_Disj = require("../Data.Monoid.Disj/index.js");
var Data_Monoid_Dual = require("../Data.Monoid.Dual/index.js");
var Data_Monoid_Multiplicative = require("../Data.Monoid.Multiplicative/index.js");
var Data_Traversable_Accum = require("../Data.Traversable.Accum/index.js");
var Data_Traversable_Accum_Internal = require("../Data.Traversable.Accum.Internal/index.js");
var Prelude = require("../Prelude/index.js");
var Traversable = function (Foldable1, Functor0, sequence, traverse) {
    this.Foldable1 = Foldable1;
    this.Functor0 = Functor0;
    this.sequence = sequence;
    this.traverse = traverse;
};
var traverse = function (dict) {
    return dict.traverse;
};
var traversableMultiplicative = new Traversable(function () {
    return Data_Foldable.foldableMultiplicative;
}, function () {
    return Data_Monoid_Multiplicative.functorMultiplicative;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Multiplicative.Multiplicative)(v);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Multiplicative.Multiplicative)(f(v));
        };
    };
});
var traversableMaybe = new Traversable(function () {
    return Data_Foldable.foldableMaybe;
}, function () {
    return Data_Maybe.functorMaybe;
}, function (dictApplicative) {
    return function (v) {
        if (v instanceof Data_Maybe.Nothing) {
            return Control_Applicative.pure(dictApplicative)(Data_Maybe.Nothing.value);
        };
        if (v instanceof Data_Maybe.Just) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Maybe.Just.create)(v.value0);
        };
        throw new Error("Failed pattern match at Data.Traversable line 86, column 1 - line 86, column 47: " + [ v.constructor.name ]);
    };
}, function (dictApplicative) {
    return function (v) {
        return function (v1) {
            if (v1 instanceof Data_Maybe.Nothing) {
                return Control_Applicative.pure(dictApplicative)(Data_Maybe.Nothing.value);
            };
            if (v1 instanceof Data_Maybe.Just) {
                return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Maybe.Just.create)(v(v1.value0));
            };
            throw new Error("Failed pattern match at Data.Traversable line 86, column 1 - line 86, column 47: " + [ v.constructor.name, v1.constructor.name ]);
        };
    };
});
var traversableDual = new Traversable(function () {
    return Data_Foldable.foldableDual;
}, function () {
    return Data_Monoid_Dual.functorDual;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Dual.Dual)(v);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Dual.Dual)(f(v));
        };
    };
});
var traversableDisj = new Traversable(function () {
    return Data_Foldable.foldableDisj;
}, function () {
    return Data_Monoid_Disj.functorDisj;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Disj.Disj)(v);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Disj.Disj)(f(v));
        };
    };
});
var traversableConj = new Traversable(function () {
    return Data_Foldable.foldableConj;
}, function () {
    return Data_Monoid_Conj.functorConj;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Conj.Conj)(v);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Conj.Conj)(f(v));
        };
    };
});
var traversableAdditive = new Traversable(function () {
    return Data_Foldable.foldableAdditive;
}, function () {
    return Data_Monoid_Additive.functorAdditive;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Additive.Additive)(v);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Monoid_Additive.Additive)(f(v));
        };
    };
});
var sequenceDefault = function (dictTraversable) {
    return function (dictApplicative) {
        return traverse(dictTraversable)(dictApplicative)(Control_Category.identity(Control_Category.categoryFn));
    };
};
var traversableArray = new Traversable(function () {
    return Data_Foldable.foldableArray;
}, function () {
    return Data_Functor.functorArray;
}, function (dictApplicative) {
    return sequenceDefault(traversableArray)(dictApplicative);
}, function (dictApplicative) {
    return $foreign.traverseArrayImpl(Control_Apply.apply(dictApplicative.Apply0()))(Data_Functor.map((dictApplicative.Apply0()).Functor0()))(Control_Applicative.pure(dictApplicative));
});
var sequence = function (dict) {
    return dict.sequence;
};
var traversableFirst = new Traversable(function () {
    return Data_Foldable.foldableFirst;
}, function () {
    return Data_Maybe_First.functorFirst;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Maybe_First.First)(sequence(traversableMaybe)(dictApplicative)(v));
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Maybe_First.First)(traverse(traversableMaybe)(dictApplicative)(f)(v));
        };
    };
});
var traversableLast = new Traversable(function () {
    return Data_Foldable.foldableLast;
}, function () {
    return Data_Maybe_Last.functorLast;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Maybe_Last.Last)(sequence(traversableMaybe)(dictApplicative)(v));
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Data_Maybe_Last.Last)(traverse(traversableMaybe)(dictApplicative)(f)(v));
        };
    };
});
var traverseDefault = function (dictTraversable) {
    return function (dictApplicative) {
        return function (f) {
            return function (ta) {
                return sequence(dictTraversable)(dictApplicative)(Data_Functor.map(dictTraversable.Functor0())(f)(ta));
            };
        };
    };
};
var mapAccumR = function (dictTraversable) {
    return function (f) {
        return function (s0) {
            return function (xs) {
                return Data_Traversable_Accum_Internal.stateR(traverse(dictTraversable)(Data_Traversable_Accum_Internal.applicativeStateR)(function (a) {
                    return function (s) {
                        return f(s)(a);
                    };
                })(xs))(s0);
            };
        };
    };
};
var scanr = function (dictTraversable) {
    return function (f) {
        return function (b0) {
            return function (xs) {
                return (mapAccumR(dictTraversable)(function (b) {
                    return function (a) {
                        var b$prime = f(a)(b);
                        return {
                            accum: b$prime,
                            value: b$prime
                        };
                    };
                })(b0)(xs)).value;
            };
        };
    };
};
var mapAccumL = function (dictTraversable) {
    return function (f) {
        return function (s0) {
            return function (xs) {
                return Data_Traversable_Accum_Internal.stateL(traverse(dictTraversable)(Data_Traversable_Accum_Internal.applicativeStateL)(function (a) {
                    return function (s) {
                        return f(s)(a);
                    };
                })(xs))(s0);
            };
        };
    };
};
var scanl = function (dictTraversable) {
    return function (f) {
        return function (b0) {
            return function (xs) {
                return (mapAccumL(dictTraversable)(function (b) {
                    return function (a) {
                        var b$prime = f(b)(a);
                        return {
                            accum: b$prime,
                            value: b$prime
                        };
                    };
                })(b0)(xs)).value;
            };
        };
    };
};
var $$for = function (dictApplicative) {
    return function (dictTraversable) {
        return function (x) {
            return function (f) {
                return traverse(dictTraversable)(dictApplicative)(f)(x);
            };
        };
    };
};
module.exports = {
    Traversable: Traversable,
    traverse: traverse,
    sequence: sequence,
    traverseDefault: traverseDefault,
    sequenceDefault: sequenceDefault,
    "for": $$for,
    scanl: scanl,
    scanr: scanr,
    mapAccumL: mapAccumL,
    mapAccumR: mapAccumR,
    traversableArray: traversableArray,
    traversableMaybe: traversableMaybe,
    traversableFirst: traversableFirst,
    traversableLast: traversableLast,
    traversableAdditive: traversableAdditive,
    traversableDual: traversableDual,
    traversableConj: traversableConj,
    traversableDisj: traversableDisj,
    traversableMultiplicative: traversableMultiplicative
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Category/index.js":24,"../Data.Foldable/index.js":92,"../Data.Functor/index.js":102,"../Data.Maybe.First/index.js":110,"../Data.Maybe.Last/index.js":111,"../Data.Maybe/index.js":112,"../Data.Monoid.Additive/index.js":113,"../Data.Monoid.Conj/index.js":114,"../Data.Monoid.Disj/index.js":115,"../Data.Monoid.Dual/index.js":116,"../Data.Monoid.Multiplicative/index.js":118,"../Data.Traversable.Accum.Internal/index.js":155,"../Data.Traversable.Accum/index.js":156,"../Prelude/index.js":195,"./foreign.js":158}],160:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Biapplicative = require("../Control.Biapplicative/index.js");
var Control_Biapply = require("../Control.Biapply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Comonad = require("../Control.Comonad/index.js");
var Control_Extend = require("../Control.Extend/index.js");
var Control_Lazy = require("../Control.Lazy/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Bifoldable = require("../Data.Bifoldable/index.js");
var Data_Bifunctor = require("../Data.Bifunctor/index.js");
var Data_Bitraversable = require("../Data.Bitraversable/index.js");
var Data_BooleanAlgebra = require("../Data.BooleanAlgebra/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_CommutativeRing = require("../Data.CommutativeRing/index.js");
var Data_Distributive = require("../Data.Distributive/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Functor_Invariant = require("../Data.Functor.Invariant/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Maybe_First = require("../Data.Maybe.First/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Prelude = require("../Prelude/index.js");
var Type_Equality = require("../Type.Equality/index.js");
var Tuple = (function () {
    function Tuple(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Tuple.create = function (value0) {
        return function (value1) {
            return new Tuple(value0, value1);
        };
    };
    return Tuple;
})();
var uncurry = function (f) {
    return function (v) {
        return f(v.value0)(v.value1);
    };
};
var swap = function (v) {
    return new Tuple(v.value1, v.value0);
};
var snd = function (v) {
    return v.value1;
};
var showTuple = function (dictShow) {
    return function (dictShow1) {
        return new Data_Show.Show(function (v) {
            return "(Tuple " + (Data_Show.show(dictShow)(v.value0) + (" " + (Data_Show.show(dictShow1)(v.value1) + ")")));
        });
    };
};
var semiringTuple = function (dictSemiring) {
    return function (dictSemiring1) {
        return new Data_Semiring.Semiring(function (v) {
            return function (v1) {
                return new Tuple(Data_Semiring.add(dictSemiring)(v.value0)(v1.value0), Data_Semiring.add(dictSemiring1)(v.value1)(v1.value1));
            };
        }, function (v) {
            return function (v1) {
                return new Tuple(Data_Semiring.mul(dictSemiring)(v.value0)(v1.value0), Data_Semiring.mul(dictSemiring1)(v.value1)(v1.value1));
            };
        }, new Tuple(Data_Semiring.one(dictSemiring), Data_Semiring.one(dictSemiring1)), new Tuple(Data_Semiring.zero(dictSemiring), Data_Semiring.zero(dictSemiring1)));
    };
};
var semigroupoidTuple = new Control_Semigroupoid.Semigroupoid(function (v) {
    return function (v1) {
        return new Tuple(v1.value0, v.value1);
    };
});
var semigroupTuple = function (dictSemigroup) {
    return function (dictSemigroup1) {
        return new Data_Semigroup.Semigroup(function (v) {
            return function (v1) {
                return new Tuple(Data_Semigroup.append(dictSemigroup)(v.value0)(v1.value0), Data_Semigroup.append(dictSemigroup1)(v.value1)(v1.value1));
            };
        });
    };
};
var ringTuple = function (dictRing) {
    return function (dictRing1) {
        return new Data_Ring.Ring(function () {
            return semiringTuple(dictRing.Semiring0())(dictRing1.Semiring0());
        }, function (v) {
            return function (v1) {
                return new Tuple(Data_Ring.sub(dictRing)(v.value0)(v1.value0), Data_Ring.sub(dictRing1)(v.value1)(v1.value1));
            };
        });
    };
};
var monoidTuple = function (dictMonoid) {
    return function (dictMonoid1) {
        return new Data_Monoid.Monoid(function () {
            return semigroupTuple(dictMonoid.Semigroup0())(dictMonoid1.Semigroup0());
        }, new Tuple(Data_Monoid.mempty(dictMonoid), Data_Monoid.mempty(dictMonoid1)));
    };
};
var lookup = function (dictFoldable) {
    return function (dictEq) {
        return function (a) {
            return function ($266) {
                return Data_Newtype.unwrap(Data_Maybe_First.newtypeFirst)(Data_Foldable.foldMap(dictFoldable)(Data_Maybe_First.monoidFirst)(function (v) {
                    var $149 = Data_Eq.eq(dictEq)(a)(v.value0);
                    if ($149) {
                        return new Data_Maybe.Just(v.value1);
                    };
                    return Data_Maybe.Nothing.value;
                })($266));
            };
        };
    };
};
var heytingAlgebraTuple = function (dictHeytingAlgebra) {
    return function (dictHeytingAlgebra1) {
        return new Data_HeytingAlgebra.HeytingAlgebra(function (v) {
            return function (v1) {
                return new Tuple(Data_HeytingAlgebra.conj(dictHeytingAlgebra)(v.value0)(v1.value0), Data_HeytingAlgebra.conj(dictHeytingAlgebra1)(v.value1)(v1.value1));
            };
        }, function (v) {
            return function (v1) {
                return new Tuple(Data_HeytingAlgebra.disj(dictHeytingAlgebra)(v.value0)(v1.value0), Data_HeytingAlgebra.disj(dictHeytingAlgebra1)(v.value1)(v1.value1));
            };
        }, new Tuple(Data_HeytingAlgebra.ff(dictHeytingAlgebra), Data_HeytingAlgebra.ff(dictHeytingAlgebra1)), function (v) {
            return function (v1) {
                return new Tuple(Data_HeytingAlgebra.implies(dictHeytingAlgebra)(v.value0)(v1.value0), Data_HeytingAlgebra.implies(dictHeytingAlgebra1)(v.value1)(v1.value1));
            };
        }, function (v) {
            return new Tuple(Data_HeytingAlgebra.not(dictHeytingAlgebra)(v.value0), Data_HeytingAlgebra.not(dictHeytingAlgebra1)(v.value1));
        }, new Tuple(Data_HeytingAlgebra.tt(dictHeytingAlgebra), Data_HeytingAlgebra.tt(dictHeytingAlgebra1)));
    };
};
var functorTuple = new Data_Functor.Functor(function (f) {
    return function (m) {
        return new Tuple(m.value0, f(m.value1));
    };
});
var invariantTuple = new Data_Functor_Invariant.Invariant(Data_Functor_Invariant.imapF(functorTuple));
var fst = function (v) {
    return v.value0;
};
var lazyTuple = function (dictLazy) {
    return function (dictLazy1) {
        return new Control_Lazy.Lazy(function (f) {
            return new Tuple(Control_Lazy.defer(dictLazy)(function (v) {
                return fst(f(Data_Unit.unit));
            }), Control_Lazy.defer(dictLazy1)(function (v) {
                return snd(f(Data_Unit.unit));
            }));
        });
    };
};
var foldableTuple = new Data_Foldable.Foldable(function (dictMonoid) {
    return function (f) {
        return function (v) {
            return f(v.value1);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(z)(v.value1);
        };
    };
}, function (f) {
    return function (z) {
        return function (v) {
            return f(v.value1)(z);
        };
    };
});
var traversableTuple = new Data_Traversable.Traversable(function () {
    return foldableTuple;
}, function () {
    return functorTuple;
}, function (dictApplicative) {
    return function (v) {
        return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Tuple.create(v.value0))(v.value1);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (v) {
            return Data_Functor.map((dictApplicative.Apply0()).Functor0())(Tuple.create(v.value0))(f(v.value1));
        };
    };
});
var extendTuple = new Control_Extend.Extend(function () {
    return functorTuple;
}, function (f) {
    return function (v) {
        return new Tuple(v.value0, f(v));
    };
});
var eqTuple = function (dictEq) {
    return function (dictEq1) {
        return new Data_Eq.Eq(function (x) {
            return function (y) {
                return Data_Eq.eq(dictEq)(x.value0)(y.value0) && Data_Eq.eq(dictEq1)(x.value1)(y.value1);
            };
        });
    };
};
var ordTuple = function (dictOrd) {
    return function (dictOrd1) {
        return new Data_Ord.Ord(function () {
            return eqTuple(dictOrd.Eq0())(dictOrd1.Eq0());
        }, function (x) {
            return function (y) {
                var v = Data_Ord.compare(dictOrd)(x.value0)(y.value0);
                if (v instanceof Data_Ordering.LT) {
                    return Data_Ordering.LT.value;
                };
                if (v instanceof Data_Ordering.GT) {
                    return Data_Ordering.GT.value;
                };
                return Data_Ord.compare(dictOrd1)(x.value1)(y.value1);
            };
        });
    };
};
var eq1Tuple = function (dictEq) {
    return new Data_Eq.Eq1(function (dictEq1) {
        return Data_Eq.eq(eqTuple(dictEq)(dictEq1));
    });
};
var ord1Tuple = function (dictOrd) {
    return new Data_Ord.Ord1(function () {
        return eq1Tuple(dictOrd.Eq0());
    }, function (dictOrd1) {
        return Data_Ord.compare(ordTuple(dictOrd)(dictOrd1));
    });
};
var distributiveTuple = function (dictTypeEquals) {
    return new Data_Distributive.Distributive(function () {
        return functorTuple;
    }, function (dictFunctor) {
        return Data_Distributive.collectDefault(distributiveTuple(dictTypeEquals))(dictFunctor);
    }, function (dictFunctor) {
        return function ($267) {
            return Tuple.create(Type_Equality.from(dictTypeEquals)(Data_Unit.unit))(Data_Functor.map(dictFunctor)(snd)($267));
        };
    });
};
var curry = function (f) {
    return function (a) {
        return function (b) {
            return f(new Tuple(a, b));
        };
    };
};
var comonadTuple = new Control_Comonad.Comonad(function () {
    return extendTuple;
}, snd);
var commutativeRingTuple = function (dictCommutativeRing) {
    return function (dictCommutativeRing1) {
        return new Data_CommutativeRing.CommutativeRing(function () {
            return ringTuple(dictCommutativeRing.Ring0())(dictCommutativeRing1.Ring0());
        });
    };
};
var boundedTuple = function (dictBounded) {
    return function (dictBounded1) {
        return new Data_Bounded.Bounded(function () {
            return ordTuple(dictBounded.Ord0())(dictBounded1.Ord0());
        }, new Tuple(Data_Bounded.bottom(dictBounded), Data_Bounded.bottom(dictBounded1)), new Tuple(Data_Bounded.top(dictBounded), Data_Bounded.top(dictBounded1)));
    };
};
var booleanAlgebraTuple = function (dictBooleanAlgebra) {
    return function (dictBooleanAlgebra1) {
        return new Data_BooleanAlgebra.BooleanAlgebra(function () {
            return heytingAlgebraTuple(dictBooleanAlgebra.HeytingAlgebra0())(dictBooleanAlgebra1.HeytingAlgebra0());
        });
    };
};
var bifunctorTuple = new Data_Bifunctor.Bifunctor(function (f) {
    return function (g) {
        return function (v) {
            return new Tuple(f(v.value0), g(v.value1));
        };
    };
});
var bifoldableTuple = new Data_Bifoldable.Bifoldable(function (dictMonoid) {
    return function (f) {
        return function (g) {
            return function (v) {
                return Data_Semigroup.append(dictMonoid.Semigroup0())(f(v.value0))(g(v.value1));
            };
        };
    };
}, function (f) {
    return function (g) {
        return function (z) {
            return function (v) {
                return g(f(z)(v.value0))(v.value1);
            };
        };
    };
}, function (f) {
    return function (g) {
        return function (z) {
            return function (v) {
                return f(v.value0)(g(v.value1)(z));
            };
        };
    };
});
var bitraversableTuple = new Data_Bitraversable.Bitraversable(function () {
    return bifoldableTuple;
}, function () {
    return bifunctorTuple;
}, function (dictApplicative) {
    return function (v) {
        return Control_Apply.apply(dictApplicative.Apply0())(Data_Functor.map((dictApplicative.Apply0()).Functor0())(Tuple.create)(v.value0))(v.value1);
    };
}, function (dictApplicative) {
    return function (f) {
        return function (g) {
            return function (v) {
                return Control_Apply.apply(dictApplicative.Apply0())(Data_Functor.map((dictApplicative.Apply0()).Functor0())(Tuple.create)(f(v.value0)))(g(v.value1));
            };
        };
    };
});
var biapplyTuple = new Control_Biapply.Biapply(function () {
    return bifunctorTuple;
}, function (v) {
    return function (v1) {
        return new Tuple(v.value0(v1.value0), v.value1(v1.value1));
    };
});
var biapplicativeTuple = new Control_Biapplicative.Biapplicative(function () {
    return biapplyTuple;
}, Tuple.create);
var applyTuple = function (dictSemigroup) {
    return new Control_Apply.Apply(function () {
        return functorTuple;
    }, function (v) {
        return function (v1) {
            return new Tuple(Data_Semigroup.append(dictSemigroup)(v.value0)(v1.value0), v.value1(v1.value1));
        };
    });
};
var bindTuple = function (dictSemigroup) {
    return new Control_Bind.Bind(function () {
        return applyTuple(dictSemigroup);
    }, function (v) {
        return function (f) {
            var v1 = f(v.value1);
            return new Tuple(Data_Semigroup.append(dictSemigroup)(v.value0)(v1.value0), v1.value1);
        };
    });
};
var applicativeTuple = function (dictMonoid) {
    return new Control_Applicative.Applicative(function () {
        return applyTuple(dictMonoid.Semigroup0());
    }, Tuple.create(Data_Monoid.mempty(dictMonoid)));
};
var monadTuple = function (dictMonoid) {
    return new Control_Monad.Monad(function () {
        return applicativeTuple(dictMonoid);
    }, function () {
        return bindTuple(dictMonoid.Semigroup0());
    });
};
module.exports = {
    Tuple: Tuple,
    fst: fst,
    snd: snd,
    curry: curry,
    uncurry: uncurry,
    swap: swap,
    lookup: lookup,
    showTuple: showTuple,
    eqTuple: eqTuple,
    eq1Tuple: eq1Tuple,
    ordTuple: ordTuple,
    ord1Tuple: ord1Tuple,
    boundedTuple: boundedTuple,
    semigroupoidTuple: semigroupoidTuple,
    semigroupTuple: semigroupTuple,
    monoidTuple: monoidTuple,
    semiringTuple: semiringTuple,
    ringTuple: ringTuple,
    commutativeRingTuple: commutativeRingTuple,
    heytingAlgebraTuple: heytingAlgebraTuple,
    booleanAlgebraTuple: booleanAlgebraTuple,
    functorTuple: functorTuple,
    invariantTuple: invariantTuple,
    bifunctorTuple: bifunctorTuple,
    applyTuple: applyTuple,
    biapplyTuple: biapplyTuple,
    applicativeTuple: applicativeTuple,
    biapplicativeTuple: biapplicativeTuple,
    bindTuple: bindTuple,
    monadTuple: monadTuple,
    extendTuple: extendTuple,
    comonadTuple: comonadTuple,
    lazyTuple: lazyTuple,
    foldableTuple: foldableTuple,
    bifoldableTuple: bifoldableTuple,
    traversableTuple: traversableTuple,
    bitraversableTuple: bitraversableTuple,
    distributiveTuple: distributiveTuple
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Biapplicative/index.js":20,"../Control.Biapply/index.js":21,"../Control.Bind/index.js":23,"../Control.Comonad/index.js":25,"../Control.Extend/index.js":27,"../Control.Lazy/index.js":28,"../Control.Monad/index.js":47,"../Control.Semigroupoid/index.js":51,"../Data.Bifoldable/index.js":67,"../Data.Bifunctor/index.js":73,"../Data.Bitraversable/index.js":74,"../Data.BooleanAlgebra/index.js":75,"../Data.Bounded/index.js":78,"../Data.CommutativeRing/index.js":79,"../Data.Distributive/index.js":80,"../Data.Eq/index.js":86,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Functor.Invariant/index.js":98,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Maybe.First/index.js":110,"../Data.Maybe/index.js":112,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Data.Traversable/index.js":159,"../Data.Unit/index.js":168,"../Prelude/index.js":195,"../Type.Equality/index.js":200}],161:[function(require,module,exports){
"use strict";

exports.from = function (val) {
    return val >>> 0;
};

exports.exact = function (just) {
    return function (nothing) {
        return function (conv) {
            return function (val) {
                var cval = conv(val);
                if (cval == val) {
                    return just(cval);
                }
                return nothing;
            };
        };
    };
};

exports.toInt = function (uval) {
    return uval | 0;
};

exports.toNumber = function (uval) {
    return uval;
};

exports.uintAdd = function (x) {
    return function (y) {
        return (x + y) >>> 0;
    };
};

exports.uintMul = function (x) {
    return function (y) {
        return (x * y) >>> 0;
    };
};

exports.uintSub = function (x) {
    return function (y) {
        return (x - y) >>> 0;
    };
};

exports.uintDiv = function (x) {
    return function (y) {
        return (x / y) >>> 0;
    };
};

exports.uintMod = function (x) {
    return function (y) {
        return (x % y) >>> 0;
    };
};

exports.uintDegree = function (x) {
    return Math.abs(x | 0);
};

exports.uintEq = function (x) {
    return function (y) {
        return x == y;
    };
};

exports.uintCmp = function (lt) {
    return function (eq) {
        return function (gt) {
            return function (x) {
                return function (y) {
                    if (x < y) return lt;
                    if (x === y) return eq;
                    return gt;
                };
            };
        };
    };
};

exports.fromStringImpl = function (s) {
    var n = Number(s);
    if (n === parseInt(s)) {
        return n;
    }
    return NaN;
};

exports.toString = function (x) {
    return x.toString();
};

exports.pow = function (u) {
    return function (p) {
        return Math.pow(u, p) >>> 0;
    };
};

exports.and = function (n1) {
    return function (n2) {
        return (n1 & n2) >>> 0;
    };
};

exports.or = function (n1) {
    return function (n2) {
        return (n1 | n2) >>> 0;
    };
};

exports.xor = function (n1) {
    return function (n2) {
        return (n1 ^ n2) >>> 0;
    };
};

exports.shl = function (n1) {
    return function (n2) {
        return (n1 << n2) >>> 0;
    };
};

exports.shr = function (n1) {
    return function (n2) {
        return (n1 >> n2) >>> 0;
    };
};

exports.zshr = function (n1) {
    return function (n2) {
        return (n1 >>> n2) >>> 0;
    };
};

exports.complement = function (n) {
    return (~n >>> 0);
};

},{}],162:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_CommutativeRing = require("../Data.CommutativeRing/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var $$Math = require("../Math/index.js");
var uintShowInstance = new Data_Show.Show(function (u) {
    return $foreign.toString(u) + "u";
});
var uintEqInstance = new Data_Eq.Eq($foreign.uintEq);
var uintOrd = new Data_Ord.Ord(function () {
    return uintEqInstance;
}, $foreign.uintCmp(Data_Ordering.LT.value)(Data_Ordering.EQ.value)(Data_Ordering.GT.value));
var toInt$prime = $foreign.exact(Data_Maybe.Just.create)(Data_Maybe.Nothing.value)($foreign.toInt);
var fromNumber = $foreign.from;
var fromNumber$prime = $foreign.exact(Data_Maybe.Just.create)(Data_Maybe.Nothing.value)(fromNumber);
var fromString = function ($0) {
    return fromNumber$prime($foreign.fromStringImpl($0));
};
var fromInt = $foreign.from;
var fromInt$prime = $foreign.exact(Data_Maybe.Just.create)(Data_Maybe.Nothing.value)(fromInt);
var uintBounded = new Data_Bounded.Bounded(function () {
    return uintOrd;
}, fromInt(0), fromInt(-1 | 0));
var uintSemiring = new Data_Semiring.Semiring($foreign.uintAdd, $foreign.uintMul, fromInt(1), fromInt(0));
var uintRing = new Data_Ring.Ring(function () {
    return uintSemiring;
}, $foreign.uintSub);
var uintCommutativeRing = new Data_CommutativeRing.CommutativeRing(function () {
    return uintRing;
});
var uintEuclideanRing = new Data_EuclideanRing.EuclideanRing(function () {
    return uintCommutativeRing;
}, $foreign.uintDegree, $foreign.uintDiv, $foreign.uintMod);
var odd = function (u) {
    return Data_Eq.eq(uintEqInstance)(Data_EuclideanRing.mod(uintEuclideanRing)(u)(fromInt(2)))(fromInt(1));
};
var even = function (u) {
    return Data_Eq.eq(uintEqInstance)(Data_EuclideanRing.mod(uintEuclideanRing)(u)(fromInt(2)))(fromInt(0));
};
var clamp$prime = Data_Ord.clamp(Data_Ord.ordNumber)($foreign.toNumber(Data_Bounded.bottom(uintBounded)))($foreign.toNumber(Data_Bounded.top(uintBounded)));
var floor = function ($1) {
    return fromNumber($$Math.floor(clamp$prime($1)));
};
var round = function ($2) {
    return fromNumber($$Math.round(clamp$prime($2)));
};
var ceil = function ($3) {
    return fromNumber($$Math.ceil(clamp$prime($3)));
};
module.exports = {
    fromInt: fromInt,
    "fromInt'": fromInt$prime,
    "toInt'": toInt$prime,
    fromNumber: fromNumber,
    "fromNumber'": fromNumber$prime,
    floor: floor,
    ceil: ceil,
    round: round,
    fromString: fromString,
    uintSemiring: uintSemiring,
    uintRing: uintRing,
    uintCommutativeRing: uintCommutativeRing,
    uintEuclideanRing: uintEuclideanRing,
    uintEqInstance: uintEqInstance,
    uintOrd: uintOrd,
    uintShowInstance: uintShowInstance,
    uintBounded: uintBounded,
    toInt: $foreign.toInt,
    toNumber: $foreign.toNumber,
    pow: $foreign.pow,
    and: $foreign.and,
    or: $foreign.or,
    xor: $foreign.xor,
    shl: $foreign.shl,
    shr: $foreign.shr,
    zshr: $foreign.zshr,
    complement: $foreign.complement,
    toString: $foreign.toString
};

},{"../Control.Semigroupoid/index.js":51,"../Data.Bounded/index.js":78,"../Data.CommutativeRing/index.js":79,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.Function/index.js":95,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Math/index.js":190,"./foreign.js":161}],163:[function(require,module,exports){
"use strict";

exports.unfoldr1ArrayImpl = function (isNothing) {
  return function (fromJust) {
    return function (fst) {
      return function (snd) {
        return function (f) {
          return function (b) {
            var result = [];
            var value = b;
            while (true) { // eslint-disable-line no-constant-condition
              var tuple = f(value);
              result.push(fst(tuple));
              var maybe = snd(tuple);
              if (isNothing(maybe)) return result;
              value = fromJust(maybe);
            }
          };
        };
      };
    };
  };
};

},{}],164:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup_Traversable = require("../Data.Semigroup.Traversable/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var Unfoldable1 = function (unfoldr1) {
    this.unfoldr1 = unfoldr1;
};
var unfoldr1 = function (dict) {
    return dict.unfoldr1;
};
var unfoldable1Array = new Unfoldable1($foreign.unfoldr1ArrayImpl(Data_Maybe.isNothing)(Data_Maybe.fromJust())(Data_Tuple.fst)(Data_Tuple.snd));
var replicate1 = function (dictUnfoldable1) {
    return function (n) {
        return function (v) {
            var step = function (i) {
                if (i <= 0) {
                    return new Data_Tuple.Tuple(v, Data_Maybe.Nothing.value);
                };
                if (Data_Boolean.otherwise) {
                    return new Data_Tuple.Tuple(v, new Data_Maybe.Just(i - 1 | 0));
                };
                throw new Error("Failed pattern match at Data.Unfoldable1 line 47, column 5 - line 47, column 39: " + [ i.constructor.name ]);
            };
            return unfoldr1(dictUnfoldable1)(step)(n - 1 | 0);
        };
    };
};
var replicate1A = function (dictApply) {
    return function (dictUnfoldable1) {
        return function (dictTraversable1) {
            return function (n) {
                return function (m) {
                    return Data_Semigroup_Traversable.sequence1(dictTraversable1)(dictApply)(replicate1(dictUnfoldable1)(n)(m));
                };
            };
        };
    };
};
var singleton = function (dictUnfoldable1) {
    return replicate1(dictUnfoldable1)(1);
};
var range = function (dictUnfoldable1) {
    return function (start) {
        return function (end) {
            var go = function (delta) {
                return function (i) {
                    var i$prime = i + delta | 0;
                    return new Data_Tuple.Tuple(i, (function () {
                        var $8 = i === end;
                        if ($8) {
                            return Data_Maybe.Nothing.value;
                        };
                        return new Data_Maybe.Just(i$prime);
                    })());
                };
            };
            var delta = (function () {
                var $9 = end >= start;
                if ($9) {
                    return 1;
                };
                return -1 | 0;
            })();
            return unfoldr1(dictUnfoldable1)(go(delta))(start);
        };
    };
};
module.exports = {
    Unfoldable1: Unfoldable1,
    unfoldr1: unfoldr1,
    replicate1: replicate1,
    replicate1A: replicate1A,
    singleton: singleton,
    range: range,
    unfoldable1Array: unfoldable1Array
};

},{"../Data.Boolean/index.js":76,"../Data.Eq/index.js":86,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Semigroup.Traversable/index.js":135,"../Data.Semiring/index.js":139,"../Data.Tuple/index.js":160,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195,"./foreign.js":163}],165:[function(require,module,exports){
"use strict";

exports.unfoldrArrayImpl = function (isNothing) {
  return function (fromJust) {
    return function (fst) {
      return function (snd) {
        return function (f) {
          return function (b) {
            var result = [];
            var value = b;
            while (true) { // eslint-disable-line no-constant-condition
              var maybe = f(value);
              if (isNothing(maybe)) return result;
              var tuple = fromJust(maybe);
              result.push(fst(tuple));
              value = snd(tuple);
            }
          };
        };
      };
    };
  };
};

},{}],166:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Traversable = require("../Data.Traversable/index.js");
var Data_Tuple = require("../Data.Tuple/index.js");
var Data_Unfoldable1 = require("../Data.Unfoldable1/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var Unfoldable = function (Unfoldable10, unfoldr) {
    this.Unfoldable10 = Unfoldable10;
    this.unfoldr = unfoldr;
};
var unfoldr = function (dict) {
    return dict.unfoldr;
};
var unfoldableArray = new Unfoldable(function () {
    return Data_Unfoldable1.unfoldable1Array;
}, $foreign.unfoldrArrayImpl(Data_Maybe.isNothing)(Data_Maybe.fromJust())(Data_Tuple.fst)(Data_Tuple.snd));
var replicate = function (dictUnfoldable) {
    return function (n) {
        return function (v) {
            var step = function (i) {
                var $7 = i <= 0;
                if ($7) {
                    return Data_Maybe.Nothing.value;
                };
                return new Data_Maybe.Just(new Data_Tuple.Tuple(v, i - 1 | 0));
            };
            return unfoldr(dictUnfoldable)(step)(n);
        };
    };
};
var replicateA = function (dictApplicative) {
    return function (dictUnfoldable) {
        return function (dictTraversable) {
            return function (n) {
                return function (m) {
                    return Data_Traversable.sequence(dictTraversable)(dictApplicative)(replicate(dictUnfoldable)(n)(m));
                };
            };
        };
    };
};
var none = function (dictUnfoldable) {
    return unfoldr(dictUnfoldable)(Data_Function["const"](Data_Maybe.Nothing.value))(Data_Unit.unit);
};
var fromMaybe = function (dictUnfoldable) {
    return unfoldr(dictUnfoldable)(function (b) {
        return Data_Functor.map(Data_Maybe.functorMaybe)(Data_Function.flip(Data_Tuple.Tuple.create)(Data_Maybe.Nothing.value))(b);
    });
};
module.exports = {
    Unfoldable: Unfoldable,
    unfoldr: unfoldr,
    replicate: replicate,
    replicateA: replicateA,
    none: none,
    fromMaybe: fromMaybe,
    unfoldableArray: unfoldableArray
};

},{"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Traversable/index.js":159,"../Data.Tuple/index.js":160,"../Data.Unfoldable1/index.js":164,"../Data.Unit/index.js":168,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195,"./foreign.js":165}],167:[function(require,module,exports){
"use strict";

exports.unit = {};

},{}],168:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Show = require("../Data.Show/index.js");
var showUnit = new Data_Show.Show(function (v) {
    return "unit";
});
module.exports = {
    showUnit: showUnit,
    unit: $foreign.unit
};

},{"../Data.Show/index.js":141,"./foreign.js":167}],169:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Data_Show = require("../Data.Show/index.js");
var Void = function (x) {
    return x;
};
var absurd = function (a) {
    var spin = function ($copy_v) {
        var $tco_result;
        function $tco_loop(v) {
            $copy_v = v;
            return;
        };
        while (!false) {
            $tco_result = $tco_loop($copy_v);
        };
        return $tco_result;
    };
    return spin(a);
};
var showVoid = new Data_Show.Show(absurd);
module.exports = {
    absurd: absurd,
    showVoid: showVoid
};

},{"../Data.Show/index.js":141}],170:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Function = require("../Data.Function/index.js");
var Effect = require("../Effect/index.js");
var Effect_Aff = require("../Effect.Aff/index.js");
var Effect_Exception = require("../Effect.Exception/index.js");
var Effect_Uncurried = require("../Effect.Uncurried/index.js");
var Prelude = require("../Prelude/index.js");
var EffectFnCanceler = function (x) {
    return x;
};
var EffectFnAff = function (x) {
    return x;
};
var fromEffectFnAff = function (v) {
    return Effect_Aff.makeAff(function (k) {
        return function __do() {
            var v1 = v(function ($4) {
                return k(Data_Either.Left.create($4))();
            }, function ($5) {
                return k(Data_Either.Right.create($5))();
            });
            return function (e) {
                return Effect_Aff.makeAff(function (k2) {
                    return function __do() {
                        v1(e, function ($6) {
                            return k2(Data_Either.Left.create($6))();
                        }, function ($7) {
                            return k2(Data_Either.Right.create($7))();
                        });
                        return Effect_Aff.nonCanceler;
                    };
                });
            };
        };
    });
};
module.exports = {
    EffectFnAff: EffectFnAff,
    EffectFnCanceler: EffectFnCanceler,
    fromEffectFnAff: fromEffectFnAff
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Control.Semigroupoid/index.js":51,"../Data.Either/index.js":82,"../Data.Function/index.js":95,"../Effect.Aff/index.js":172,"../Effect.Exception/index.js":177,"../Effect.Uncurried/index.js":181,"../Effect/index.js":185,"../Prelude/index.js":195}],171:[function(require,module,exports){
(function (setImmediate,clearImmediate){
/* globals setImmediate, clearImmediate, setTimeout, clearTimeout */
/* jshint -W083, -W098, -W003 */
"use strict";

var Aff = function () {
  // A unique value for empty.
  var EMPTY = {};

  /*

  An awkward approximation. We elide evidence we would otherwise need in PS for
  efficiency sake.

  data Aff eff a
    = Pure a
    | Throw Error
    | Catch (Aff eff a) (Error -> Aff eff a)
    | Sync (Eff eff a)
    | Async ((Either Error a -> Eff eff Unit) -> Eff eff (Canceler eff))
    | forall b. Bind (Aff eff b) (b -> Aff eff a)
    | forall b. Bracket (Aff eff b) (BracketConditions eff b) (b -> Aff eff a)
    | forall b. Fork Boolean (Aff eff b) ?(Fiber eff b -> a)
    | Sequential (ParAff aff a)

  */
  var PURE    = "Pure";
  var THROW   = "Throw";
  var CATCH   = "Catch";
  var SYNC    = "Sync";
  var ASYNC   = "Async";
  var BIND    = "Bind";
  var BRACKET = "Bracket";
  var FORK    = "Fork";
  var SEQ     = "Sequential";

  /*

  data ParAff eff a
    = forall b. Map (b -> a) (ParAff eff b)
    | forall b. Apply (ParAff eff (b -> a)) (ParAff eff b)
    | Alt (ParAff eff a) (ParAff eff a)
    | ?Par (Aff eff a)

  */
  var MAP   = "Map";
  var APPLY = "Apply";
  var ALT   = "Alt";

  // Various constructors used in interpretation
  var CONS      = "Cons";      // Cons-list, for stacks
  var RESUME    = "Resume";    // Continue indiscriminately
  var RELEASE   = "Release";   // Continue with bracket finalizers
  var FINALIZER = "Finalizer"; // A non-interruptible effect
  var FINALIZED = "Finalized"; // Marker for finalization
  var FORKED    = "Forked";    // Reference to a forked fiber, with resumption stack
  var FIBER     = "Fiber";     // Actual fiber reference
  var THUNK     = "Thunk";     // Primed effect, ready to invoke

  function Aff(tag, _1, _2, _3) {
    this.tag = tag;
    this._1  = _1;
    this._2  = _2;
    this._3  = _3;
  }

  function AffCtr(tag) {
    var fn = function (_1, _2, _3) {
      return new Aff(tag, _1, _2, _3);
    };
    fn.tag = tag;
    return fn;
  }

  function nonCanceler(error) {
    return new Aff(PURE, void 0);
  }

  function runEff(eff) {
    try {
      eff();
    } catch (error) {
      setTimeout(function () {
        throw error;
      }, 0);
    }
  }

  function runSync(left, right, eff) {
    try {
      return right(eff());
    } catch (error) {
      return left(error);
    }
  }

  function runAsync(left, eff, k) {
    try {
      return eff(k)();
    } catch (error) {
      k(left(error))();
      return nonCanceler;
    }
  }

  var Scheduler = function () {
    var limit    = 1024;
    var size     = 0;
    var ix       = 0;
    var queue    = new Array(limit);
    var draining = false;

    function drain() {
      var thunk;
      draining = true;
      while (size !== 0) {
        size--;
        thunk     = queue[ix];
        queue[ix] = void 0;
        ix        = (ix + 1) % limit;
        thunk();
      }
      draining = false;
    }

    return {
      isDraining: function () {
        return draining;
      },
      enqueue: function (cb) {
        var i, tmp;
        if (size === limit) {
          tmp = draining;
          drain();
          draining = tmp;
        }

        queue[(ix + size) % limit] = cb;
        size++;

        if (!draining) {
          drain();
        }
      }
    };
  }();

  function Supervisor(util) {
    var fibers  = {};
    var fiberId = 0;
    var count   = 0;

    return {
      register: function (fiber) {
        var fid = fiberId++;
        fiber.onComplete({
          rethrow: true,
          handler: function (result) {
            return function () {
              count--;
              delete fibers[fid];
            };
          }
        });
        fibers[fid] = fiber;
        count++;
      },
      isEmpty: function () {
        return count === 0;
      },
      killAll: function (killError, cb) {
        return function () {
          var killCount = 0;
          var kills     = {};

          function kill(fid) {
            kills[fid] = fibers[fid].kill(killError, function (result) {
              return function () {
                delete kills[fid];
                killCount--;
                if (util.isLeft(result) && util.fromLeft(result)) {
                  setTimeout(function () {
                    throw util.fromLeft(result);
                  }, 0);
                }
                if (killCount === 0) {
                  cb();
                }
              };
            })();
          }

          for (var k in fibers) {
            if (fibers.hasOwnProperty(k)) {
              killCount++;
              kill(k);
            }
          }

          fibers  = {};
          fiberId = 0;
          count   = 0;

          return function (error) {
            return new Aff(SYNC, function () {
              for (var k in kills) {
                if (kills.hasOwnProperty(k)) {
                  kills[k]();
                }
              }
            });
          };
        };
      }
    };
  }

  // Fiber state machine
  var SUSPENDED   = 0; // Suspended, pending a join.
  var CONTINUE    = 1; // Interpret the next instruction.
  var STEP_BIND   = 2; // Apply the next bind.
  var STEP_RESULT = 3; // Handle potential failure from a result.
  var PENDING     = 4; // An async effect is running.
  var RETURN      = 5; // The current stack has returned.
  var COMPLETED   = 6; // The entire fiber has completed.

  function Fiber(util, supervisor, aff) {
    // Monotonically increasing tick, increased on each asynchronous turn.
    var runTick = 0;

    // The current branch of the state machine.
    var status = SUSPENDED;

    // The current point of interest for the state machine branch.
    var step      = aff;  // Successful step
    var fail      = null; // Failure step
    var interrupt = null; // Asynchronous interrupt

    // Stack of continuations for the current fiber.
    var bhead = null;
    var btail = null;

    // Stack of attempts and finalizers for error recovery. Every `Cons` is also
    // tagged with current `interrupt` state. We use this to track which items
    // should be ignored or evaluated as a result of a kill.
    var attempts = null;

    // A special state is needed for Bracket, because it cannot be killed. When
    // we enter a bracket acquisition or finalizer, we increment the counter,
    // and then decrement once complete.
    var bracketCount = 0;

    // Each join gets a new id so they can be revoked.
    var joinId  = 0;
    var joins   = null;
    var rethrow = true;

    // Each invocation of `run` requires a tick. When an asynchronous effect is
    // resolved, we must check that the local tick coincides with the fiber
    // tick before resuming. This prevents multiple async continuations from
    // accidentally resuming the same fiber. A common example may be invoking
    // the provided callback in `makeAff` more than once, but it may also be an
    // async effect resuming after the fiber was already cancelled.
    function run(localRunTick) {
      var tmp, result, attempt, canceler;
      while (true) {
        tmp       = null;
        result    = null;
        attempt   = null;
        canceler  = null;

        switch (status) {
        case STEP_BIND:
          status = CONTINUE;
          step   = bhead(step);
          if (btail === null) {
            bhead = null;
          } else {
            bhead = btail._1;
            btail = btail._2;
          }
          break;

        case STEP_RESULT:
          if (util.isLeft(step)) {
            status = RETURN;
            fail   = step;
            step   = null;
          } else if (bhead === null) {
            status = RETURN;
          } else {
            status = STEP_BIND;
            step   = util.fromRight(step);
          }
          break;

        case CONTINUE:
          switch (step.tag) {
          case BIND:
            if (bhead) {
              btail = new Aff(CONS, bhead, btail);
            }
            bhead  = step._2;
            status = CONTINUE;
            step   = step._1;
            break;

          case PURE:
            if (bhead === null) {
              status = RETURN;
              step   = util.right(step._1);
            } else {
              status = STEP_BIND;
              step   = step._1;
            }
            break;

          case SYNC:
            status = STEP_RESULT;
            step   = runSync(util.left, util.right, step._1);
            break;

          case ASYNC:
            status = PENDING;
            step   = runAsync(util.left, step._1, function (result) {
              return function () {
                if (runTick !== localRunTick) {
                  return;
                }
                runTick++;
                Scheduler.enqueue(function () {
                  status = STEP_RESULT;
                  step   = result;
                  run(runTick);
                });
              };
            });
            return;

          case THROW:
            status = RETURN;
            fail   = util.left(step._1);
            step   = null;
            break;

          // Enqueue the Catch so that we can call the error handler later on
          // in case of an exception.
          case CATCH:
            if (bhead === null) {
              attempts = new Aff(CONS, step, attempts, interrupt);
            } else {
              attempts = new Aff(CONS, step, new Aff(CONS, new Aff(RESUME, bhead, btail), attempts, interrupt), interrupt);
            }
            bhead    = null;
            btail    = null;
            status   = CONTINUE;
            step     = step._1;
            break;

          // Enqueue the Bracket so that we can call the appropriate handlers
          // after resource acquisition.
          case BRACKET:
            bracketCount++;
            if (bhead === null) {
              attempts = new Aff(CONS, step, attempts, interrupt);
            } else {
              attempts = new Aff(CONS, step, new Aff(CONS, new Aff(RESUME, bhead, btail), attempts, interrupt), interrupt);
            }
            bhead  = null;
            btail  = null;
            status = CONTINUE;
            step   = step._1;
            break;

          case FORK:
            status = STEP_RESULT;
            tmp    = Fiber(util, supervisor, step._2);
            if (supervisor) {
              supervisor.register(tmp);
            }
            if (step._1) {
              tmp.run();
            }
            step = util.right(tmp);
            break;

          case SEQ:
            status = CONTINUE;
            step   = sequential(util, supervisor, step._1);
            break;
          }
          break;

        case RETURN:
          bhead = null;
          btail = null;
          // If the current stack has returned, and we have no other stacks to
          // resume or finalizers to run, the fiber has halted and we can
          // invoke all join callbacks. Otherwise we need to resume.
          if (attempts === null) {
            status = COMPLETED;
            step   = interrupt || fail || step;
          } else {
            // The interrupt status for the enqueued item.
            tmp      = attempts._3;
            attempt  = attempts._1;
            attempts = attempts._2;

            switch (attempt.tag) {
            // We cannot recover from an interrupt. Otherwise we should
            // continue stepping, or run the exception handler if an exception
            // was raised.
            case CATCH:
              // We should compare the interrupt status as well because we
              // only want it to apply if there has been an interrupt since
              // enqueuing the catch.
              if (interrupt && interrupt !== tmp) {
                status = RETURN;
              } else if (fail) {
                status = CONTINUE;
                step   = attempt._2(util.fromLeft(fail));
                fail   = null;
              }
              break;

            // We cannot resume from an interrupt or exception.
            case RESUME:
              // As with Catch, we only want to ignore in the case of an
              // interrupt since enqueing the item.
              if (interrupt && interrupt !== tmp || fail) {
                status = RETURN;
              } else {
                bhead  = attempt._1;
                btail  = attempt._2;
                status = STEP_BIND;
                step   = util.fromRight(step);
              }
              break;

            // If we have a bracket, we should enqueue the handlers,
            // and continue with the success branch only if the fiber has
            // not been interrupted. If the bracket acquisition failed, we
            // should not run either.
            case BRACKET:
              bracketCount--;
              if (fail === null) {
                result   = util.fromRight(step);
                // We need to enqueue the Release with the same interrupt
                // status as the Bracket that is initiating it.
                attempts = new Aff(CONS, new Aff(RELEASE, attempt._2, result), attempts, tmp);
                // We should only coninue as long as the interrupt status has not changed or
                // we are currently within a non-interruptable finalizer.
                if (interrupt === tmp || bracketCount > 0) {
                  status = CONTINUE;
                  step   = attempt._3(result);
                }
              }
              break;

            // Enqueue the appropriate handler. We increase the bracket count
            // because it should not be cancelled.
            case RELEASE:
              bracketCount++;
              attempts = new Aff(CONS, new Aff(FINALIZED, step), attempts, interrupt);
              status   = CONTINUE;
              // It has only been killed if the interrupt status has changed
              // since we enqueued the item.
              if (interrupt && interrupt !== tmp) {
                step = attempt._1.killed(util.fromLeft(interrupt))(attempt._2);
              } else if (fail) {
                step = attempt._1.failed(util.fromLeft(fail))(attempt._2);
              } else {
                step = attempt._1.completed(util.fromRight(step))(attempt._2);
              }
              break;

            case FINALIZER:
              bracketCount++;
              attempts = new Aff(CONS, new Aff(FINALIZED, step), attempts, interrupt);
              status   = CONTINUE;
              step     = attempt._1;
              break;

            case FINALIZED:
              bracketCount--;
              status = RETURN;
              step   = attempt._1;
              break;
            }
          }
          break;

        case COMPLETED:
          for (var k in joins) {
            if (joins.hasOwnProperty(k)) {
              rethrow = rethrow && joins[k].rethrow;
              runEff(joins[k].handler(step));
            }
          }
          joins = null;
          // If we have an interrupt and a fail, then the thread threw while
          // running finalizers. This should always rethrow in a fresh stack.
          if (interrupt && fail) {
            setTimeout(function () {
              throw util.fromLeft(fail);
            }, 0);
          // If we have an unhandled exception, and no other fiber has joined
          // then we need to throw the exception in a fresh stack.
          } else if (util.isLeft(step) && rethrow) {
            setTimeout(function () {
              // Guard on reathrow because a completely synchronous fiber can
              // still have an observer which was added after-the-fact.
              if (rethrow) {
                throw util.fromLeft(step);
              }
            }, 0);
          }
          return;
        case SUSPENDED:
          status = CONTINUE;
          break;
        case PENDING: return;
        }
      }
    }

    function onComplete(join) {
      return function () {
        if (status === COMPLETED) {
          rethrow = rethrow && join.rethrow;
          join.handler(step)();
          return function () {};
        }

        var jid    = joinId++;
        joins      = joins || {};
        joins[jid] = join;

        return function() {
          if (joins !== null) {
            delete joins[jid];
          }
        };
      };
    }

    function kill(error, cb) {
      return function () {
        if (status === COMPLETED) {
          cb(util.right(void 0))();
          return function () {};
        }

        var canceler = onComplete({
          rethrow: false,
          handler: function (/* unused */) {
            return cb(util.right(void 0));
          }
        })();

        switch (status) {
        case SUSPENDED:
          interrupt = util.left(error);
          status    = COMPLETED;
          step      = interrupt;
          run(runTick);
          break;
        case PENDING:
          if (interrupt === null) {
            interrupt = util.left(error);
          }
          if (bracketCount === 0) {
            if (status === PENDING) {
              attempts = new Aff(CONS, new Aff(FINALIZER, step(error)), attempts, interrupt);
            }
            status   = RETURN;
            step     = null;
            fail     = null;
            run(++runTick);
          }
          break;
        default:
          if (interrupt === null) {
            interrupt = util.left(error);
          }
          if (bracketCount === 0) {
            status = RETURN;
            step   = null;
            fail   = null;
          }
        }

        return canceler;
      };
    }

    function join(cb) {
      return function () {
        var canceler = onComplete({
          rethrow: false,
          handler: cb
        })();
        if (status === SUSPENDED) {
          run(runTick);
        }
        return canceler;
      };
    }

    return {
      kill: kill,
      join: join,
      onComplete: onComplete,
      isSuspended: function () {
        return status === SUSPENDED;
      },
      run: function () {
        if (status === SUSPENDED) {
          if (!Scheduler.isDraining()) {
            Scheduler.enqueue(function () {
              run(runTick);
            });
          } else {
            run(runTick);
          }
        }
      }
    };
  }

  function runPar(util, supervisor, par, cb) {
    // Table of all forked fibers.
    var fiberId   = 0;
    var fibers    = {};

    // Table of currently running cancelers, as a product of `Alt` behavior.
    var killId    = 0;
    var kills     = {};

    // Error used for early cancelation on Alt branches.
    var early     = new Error("[ParAff] Early exit");

    // Error used to kill the entire tree.
    var interrupt = null;

    // The root pointer of the tree.
    var root      = EMPTY;

    // Walks a tree, invoking all the cancelers. Returns the table of pending
    // cancellation fibers.
    function kill(error, par, cb) {
      var step  = par;
      var head  = null;
      var tail  = null;
      var count = 0;
      var kills = {};
      var tmp, kid;

      loop: while (true) {
        tmp = null;

        switch (step.tag) {
        case FORKED:
          if (step._3 === EMPTY) {
            tmp = fibers[step._1];
            kills[count++] = tmp.kill(error, function (result) {
              return function () {
                count--;
                if (count === 0) {
                  cb(result)();
                }
              };
            });
          }
          // Terminal case.
          if (head === null) {
            break loop;
          }
          // Go down the right side of the tree.
          step = head._2;
          if (tail === null) {
            head = null;
          } else {
            head = tail._1;
            tail = tail._2;
          }
          break;
        case MAP:
          step = step._2;
          break;
        case APPLY:
        case ALT:
          if (head) {
            tail = new Aff(CONS, head, tail);
          }
          head = step;
          step = step._1;
          break;
        }
      }

      if (count === 0) {
        cb(util.right(void 0))();
      } else {
        // Run the cancelation effects. We alias `count` because it's mutable.
        kid = 0;
        tmp = count;
        for (; kid < tmp; kid++) {
          kills[kid] = kills[kid]();
        }
      }

      return kills;
    }

    // When a fiber resolves, we need to bubble back up the tree with the
    // result, computing the applicative nodes.
    function join(result, head, tail) {
      var fail, step, lhs, rhs, tmp, kid;

      if (util.isLeft(result)) {
        fail = result;
        step = null;
      } else {
        step = result;
        fail = null;
      }

      loop: while (true) {
        lhs = null;
        rhs = null;
        tmp = null;
        kid = null;

        // We should never continue if the entire tree has been interrupted.
        if (interrupt !== null) {
          return;
        }

        // We've made it all the way to the root of the tree, which means
        // the tree has fully evaluated.
        if (head === null) {
          cb(fail || step)();
          return;
        }

        // The tree has already been computed, so we shouldn't try to do it
        // again. This should never happen.
        // TODO: Remove this?
        if (head._3 !== EMPTY) {
          return;
        }

        switch (head.tag) {
        case MAP:
          if (fail === null) {
            head._3 = util.right(head._1(util.fromRight(step)));
            step    = head._3;
          } else {
            head._3 = fail;
          }
          break;
        case APPLY:
          lhs = head._1._3;
          rhs = head._2._3;
          // If we have a failure we should kill the other side because we
          // can't possible yield a result anymore.
          if (fail) {
            head._3 = fail;
            tmp     = true;
            kid     = killId++;

            kills[kid] = kill(early, fail === lhs ? head._2 : head._1, function (/* unused */) {
              return function () {
                delete kills[kid];
                if (tmp) {
                  tmp = false;
                } else if (tail === null) {
                  join(fail, null, null);
                } else {
                  join(fail, tail._1, tail._2);
                }
              };
            });

            if (tmp) {
              tmp = false;
              return;
            }
          } else if (lhs === EMPTY || rhs === EMPTY) {
            // We can only proceed if both sides have resolved.
            return;
          } else {
            step    = util.right(util.fromRight(lhs)(util.fromRight(rhs)));
            head._3 = step;
          }
          break;
        case ALT:
          lhs = head._1._3;
          rhs = head._2._3;
          // We can only proceed if both have resolved or we have a success
          if (lhs === EMPTY && util.isLeft(rhs) || rhs === EMPTY && util.isLeft(lhs)) {
            return;
          }
          // If both sides resolve with an error, we should continue with the
          // first error
          if (lhs !== EMPTY && util.isLeft(lhs) && rhs !== EMPTY && util.isLeft(rhs)) {
            fail    = step === lhs ? rhs : lhs;
            step    = null;
            head._3 = fail;
          } else {
            head._3 = step;
            tmp     = true;
            kid     = killId++;
            // Once a side has resolved, we need to cancel the side that is still
            // pending before we can continue.
            kills[kid] = kill(early, step === lhs ? head._2 : head._1, function (/* unused */) {
              return function () {
                delete kills[kid];
                if (tmp) {
                  tmp = false;
                } else if (tail === null) {
                  join(step, null, null);
                } else {
                  join(step, tail._1, tail._2);
                }
              };
            });

            if (tmp) {
              tmp = false;
              return;
            }
          }
          break;
        }

        if (tail === null) {
          head = null;
        } else {
          head = tail._1;
          tail = tail._2;
        }
      }
    }

    function resolve(fiber) {
      return function (result) {
        return function () {
          delete fibers[fiber._1];
          fiber._3 = result;
          join(result, fiber._2._1, fiber._2._2);
        };
      };
    }

    // Walks the applicative tree, substituting non-applicative nodes with
    // `FORKED` nodes. In this tree, all applicative nodes use the `_3` slot
    // as a mutable slot for memoization. In an unresolved state, the `_3`
    // slot is `EMPTY`. In the cases of `ALT` and `APPLY`, we always walk
    // the left side first, because both operations are left-associative. As
    // we `RETURN` from those branches, we then walk the right side.
    function run() {
      var status = CONTINUE;
      var step   = par;
      var head   = null;
      var tail   = null;
      var tmp, fid;

      loop: while (true) {
        tmp = null;
        fid = null;

        switch (status) {
        case CONTINUE:
          switch (step.tag) {
          case MAP:
            if (head) {
              tail = new Aff(CONS, head, tail);
            }
            head = new Aff(MAP, step._1, EMPTY, EMPTY);
            step = step._2;
            break;
          case APPLY:
            if (head) {
              tail = new Aff(CONS, head, tail);
            }
            head = new Aff(APPLY, EMPTY, step._2, EMPTY);
            step = step._1;
            break;
          case ALT:
            if (head) {
              tail = new Aff(CONS, head, tail);
            }
            head = new Aff(ALT, EMPTY, step._2, EMPTY);
            step = step._1;
            break;
          default:
            // When we hit a leaf value, we suspend the stack in the `FORKED`.
            // When the fiber resolves, it can bubble back up the tree.
            fid    = fiberId++;
            status = RETURN;
            tmp    = step;
            step   = new Aff(FORKED, fid, new Aff(CONS, head, tail), EMPTY);
            tmp    = Fiber(util, supervisor, tmp);
            tmp.onComplete({
              rethrow: false,
              handler: resolve(step)
            })();
            fibers[fid] = tmp;
            if (supervisor) {
              supervisor.register(tmp);
            }
          }
          break;
        case RETURN:
          // Terminal case, we are back at the root.
          if (head === null) {
            break loop;
          }
          // If we are done with the right side, we need to continue down the
          // left. Otherwise we should continue up the stack.
          if (head._1 === EMPTY) {
            head._1 = step;
            status  = CONTINUE;
            step    = head._2;
            head._2 = EMPTY;
          } else {
            head._2 = step;
            step    = head;
            if (tail === null) {
              head  = null;
            } else {
              head  = tail._1;
              tail  = tail._2;
            }
          }
        }
      }

      // Keep a reference to the tree root so it can be cancelled.
      root = step;

      for (fid = 0; fid < fiberId; fid++) {
        fibers[fid].run();
      }
    }

    // Cancels the entire tree. If there are already subtrees being canceled,
    // we need to first cancel those joins. We will then add fresh joins for
    // all pending branches including those that were in the process of being
    // canceled.
    function cancel(error, cb) {
      interrupt = util.left(error);
      var innerKills;
      for (var kid in kills) {
        if (kills.hasOwnProperty(kid)) {
          innerKills = kills[kid];
          for (kid in innerKills) {
            if (innerKills.hasOwnProperty(kid)) {
              innerKills[kid]();
            }
          }
        }
      }

      kills = null;
      var newKills = kill(error, root, cb);

      return function (killError) {
        return new Aff(ASYNC, function (killCb) {
          return function () {
            for (var kid in newKills) {
              if (newKills.hasOwnProperty(kid)) {
                newKills[kid]();
              }
            }
            return nonCanceler;
          };
        });
      };
    }

    run();

    return function (killError) {
      return new Aff(ASYNC, function (killCb) {
        return function () {
          return cancel(killError, killCb);
        };
      });
    };
  }

  function sequential(util, supervisor, par) {
    return new Aff(ASYNC, function (cb) {
      return function () {
        return runPar(util, supervisor, par, cb);
      };
    });
  }

  Aff.EMPTY       = EMPTY;
  Aff.Pure        = AffCtr(PURE);
  Aff.Throw       = AffCtr(THROW);
  Aff.Catch       = AffCtr(CATCH);
  Aff.Sync        = AffCtr(SYNC);
  Aff.Async       = AffCtr(ASYNC);
  Aff.Bind        = AffCtr(BIND);
  Aff.Bracket     = AffCtr(BRACKET);
  Aff.Fork        = AffCtr(FORK);
  Aff.Seq         = AffCtr(SEQ);
  Aff.ParMap      = AffCtr(MAP);
  Aff.ParApply    = AffCtr(APPLY);
  Aff.ParAlt      = AffCtr(ALT);
  Aff.Fiber       = Fiber;
  Aff.Supervisor  = Supervisor;
  Aff.Scheduler   = Scheduler;
  Aff.nonCanceler = nonCanceler;

  return Aff;
}();

exports._pure = Aff.Pure;

exports._throwError = Aff.Throw;

exports._catchError = function (aff) {
  return function (k) {
    return Aff.Catch(aff, k);
  };
};

exports._map = function (f) {
  return function (aff) {
    if (aff.tag === Aff.Pure.tag) {
      return Aff.Pure(f(aff._1));
    } else {
      return Aff.Bind(aff, function (value) {
        return Aff.Pure(f(value));
      });
    }
  };
};

exports._bind = function (aff) {
  return function (k) {
    return Aff.Bind(aff, k);
  };
};

exports._fork = function (immediate) {
  return function (aff) {
    return Aff.Fork(immediate, aff);
  };
};

exports._liftEffect = Aff.Sync;

exports._parAffMap = function (f) {
  return function (aff) {
    return Aff.ParMap(f, aff);
  };
};

exports._parAffApply = function (aff1) {
  return function (aff2) {
    return Aff.ParApply(aff1, aff2);
  };
};

exports._parAffAlt = function (aff1) {
  return function (aff2) {
    return Aff.ParAlt(aff1, aff2);
  };
};

exports.makeAff = Aff.Async;

exports.generalBracket = function (acquire) {
  return function (options) {
    return function (k) {
      return Aff.Bracket(acquire, options, k);
    };
  };
};

exports._makeFiber = function (util, aff) {
  return function () {
    return Aff.Fiber(util, null, aff);
  };
};

exports._makeSupervisedFiber = function (util, aff) {
  return function () {
    var supervisor = Aff.Supervisor(util);
    return {
      fiber: Aff.Fiber(util, supervisor, aff),
      supervisor: supervisor
    };
  };
};

exports._killAll = function (error, supervisor, cb) {
  return supervisor.killAll(error, cb);
};

exports._delay = function () {
  function setDelay(n, k) {
    if (n === 0 && typeof setImmediate !== "undefined") {
      return setImmediate(k);
    } else {
      return setTimeout(k, n);
    }
  }

  function clearDelay(n, t) {
    if (n === 0 && typeof clearImmediate !== "undefined") {
      return clearImmediate(t);
    } else {
      return clearTimeout(t);
    }
  }

  return function (right, ms) {
    return Aff.Async(function (cb) {
      return function () {
        var timer = setDelay(ms, cb(right()));
        return function () {
          return Aff.Sync(function () {
            return right(clearDelay(ms, timer));
          });
        };
      };
    });
  };
}();

exports._sequential = Aff.Seq;

}).call(this,require("timers").setImmediate,require("timers").clearImmediate)
},{"timers":2}],172:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Alt = require("../Control.Alt/index.js");
var Control_Alternative = require("../Control.Alternative/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Lazy = require("../Control.Lazy/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Monad_Error_Class = require("../Control.Monad.Error.Class/index.js");
var Control_Monad_Rec_Class = require("../Control.Monad.Rec.Class/index.js");
var Control_Parallel = require("../Control.Parallel/index.js");
var Control_Parallel_Class = require("../Control.Parallel.Class/index.js");
var Control_Plus = require("../Control.Plus/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Function_Uncurried = require("../Data.Function.Uncurried/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Newtype = require("../Data.Newtype/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Time_Duration = require("../Data.Time.Duration/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Effect = require("../Effect/index.js");
var Effect_Class = require("../Effect.Class/index.js");
var Effect_Exception = require("../Effect.Exception/index.js");
var Effect_Unsafe = require("../Effect.Unsafe/index.js");
var Partial_Unsafe = require("../Partial.Unsafe/index.js");
var Prelude = require("../Prelude/index.js");
var Unsafe_Coerce = require("../Unsafe.Coerce/index.js");
var Fiber = function (x) {
    return x;
};
var FFIUtil = function (x) {
    return x;
};
var Canceler = function (x) {
    return x;
};
var suspendAff = $foreign._fork(false);
var newtypeCanceler = new Data_Newtype.Newtype(function (n) {
    return n;
}, Canceler);
var functorParAff = new Data_Functor.Functor($foreign._parAffMap);
var functorAff = new Data_Functor.Functor($foreign._map);
var forkAff = $foreign._fork(true);
var ffiUtil = (function () {
    var unsafeFromRight = function (v) {
        if (v instanceof Data_Either.Right) {
            return v.value0;
        };
        if (v instanceof Data_Either.Left) {
            return Partial_Unsafe.unsafeCrashWith("unsafeFromRight: Left");
        };
        throw new Error("Failed pattern match at Effect.Aff line 395, column 21 - line 397, column 31: " + [ v.constructor.name ]);
    };
    var unsafeFromLeft = function (v) {
        if (v instanceof Data_Either.Left) {
            return v.value0;
        };
        if (v instanceof Data_Either.Right) {
            return Partial_Unsafe.unsafeCrashWith("unsafeFromLeft: Right");
        };
        throw new Error("Failed pattern match at Effect.Aff line 390, column 20 - line 394, column 3: " + [ v.constructor.name ]);
    };
    var isLeft = function (v) {
        if (v instanceof Data_Either.Left) {
            return true;
        };
        if (v instanceof Data_Either.Right) {
            return false;
        };
        throw new Error("Failed pattern match at Effect.Aff line 385, column 12 - line 387, column 20: " + [ v.constructor.name ]);
    };
    return {
        isLeft: isLeft,
        fromLeft: unsafeFromLeft,
        fromRight: unsafeFromRight,
        left: Data_Either.Left.create,
        right: Data_Either.Right.create
    };
})();
var makeFiber = function (aff) {
    return $foreign._makeFiber(ffiUtil, aff);
};
var launchAff = function (aff) {
    return function __do() {
        var v = makeFiber(aff)();
        v.run();
        return v;
    };
};
var launchAff_ = function ($49) {
    return Data_Functor["void"](Effect.functorEffect)(launchAff($49));
};
var launchSuspendedAff = makeFiber;
var delay = function (v) {
    return $foreign._delay(Data_Either.Right.create, v);
};
var bracket = function (acquire) {
    return function (completed) {
        return $foreign.generalBracket(acquire)({
            killed: Data_Function["const"](completed),
            failed: Data_Function["const"](completed),
            completed: Data_Function["const"](completed)
        });
    };
};
var applyParAff = new Control_Apply.Apply(function () {
    return functorParAff;
}, $foreign._parAffApply);
var semigroupParAff = function (dictSemigroup) {
    return new Data_Semigroup.Semigroup(Control_Apply.lift2(applyParAff)(Data_Semigroup.append(dictSemigroup)));
};
var monadAff = new Control_Monad.Monad(function () {
    return applicativeAff;
}, function () {
    return bindAff;
});
var bindAff = new Control_Bind.Bind(function () {
    return applyAff;
}, $foreign._bind);
var applyAff = new Control_Apply.Apply(function () {
    return functorAff;
}, Control_Monad.ap(monadAff));
var applicativeAff = new Control_Applicative.Applicative(function () {
    return applyAff;
}, $foreign._pure);
var cancelWith = function (aff) {
    return function (v) {
        return $foreign.generalBracket(Control_Applicative.pure(applicativeAff)(Data_Unit.unit))({
            killed: function (e) {
                return function (v1) {
                    return v(e);
                };
            },
            failed: Data_Function["const"](Control_Applicative.pure(applicativeAff)),
            completed: Data_Function["const"](Control_Applicative.pure(applicativeAff))
        })(Data_Function["const"](aff));
    };
};
var $$finally = function (fin) {
    return function (a) {
        return bracket(Control_Applicative.pure(applicativeAff)(Data_Unit.unit))(Data_Function["const"](fin))(Data_Function["const"](a));
    };
};
var invincible = function (a) {
    return bracket(a)(Data_Function["const"](Control_Applicative.pure(applicativeAff)(Data_Unit.unit)))(Control_Applicative.pure(applicativeAff));
};
var lazyAff = new Control_Lazy.Lazy(function (f) {
    return Control_Bind.bind(bindAff)(Control_Applicative.pure(applicativeAff)(Data_Unit.unit))(f);
});
var semigroupAff = function (dictSemigroup) {
    return new Data_Semigroup.Semigroup(Control_Apply.lift2(applyAff)(Data_Semigroup.append(dictSemigroup)));
};
var monadEffectAff = new Effect_Class.MonadEffect(function () {
    return monadAff;
}, $foreign._liftEffect);
var effectCanceler = function ($50) {
    return Canceler(Data_Function["const"](Effect_Class.liftEffect(monadEffectAff)($50)));
};
var joinFiber = function (v) {
    return $foreign.makeAff(function (k) {
        return Data_Functor.map(Effect.functorEffect)(effectCanceler)(v.join(k));
    });
};
var functorFiber = new Data_Functor.Functor(function (f) {
    return function (t) {
        return Effect_Unsafe.unsafePerformEffect(makeFiber(Data_Functor.map(functorAff)(f)(joinFiber(t))));
    };
});
var applyFiber = new Control_Apply.Apply(function () {
    return functorFiber;
}, function (t1) {
    return function (t2) {
        return Effect_Unsafe.unsafePerformEffect(makeFiber(Control_Apply.apply(applyAff)(joinFiber(t1))(joinFiber(t2))));
    };
});
var applicativeFiber = new Control_Applicative.Applicative(function () {
    return applyFiber;
}, function (a) {
    return Effect_Unsafe.unsafePerformEffect(makeFiber(Control_Applicative.pure(applicativeAff)(a)));
});
var killFiber = function (e) {
    return function (v) {
        return Control_Bind.bind(bindAff)(Effect_Class.liftEffect(monadEffectAff)(v.isSuspended))(function (v1) {
            if (v1) {
                return Effect_Class.liftEffect(monadEffectAff)(Data_Functor["void"](Effect.functorEffect)(v.kill(e, Data_Function["const"](Control_Applicative.pure(Effect.applicativeEffect)(Data_Unit.unit)))));
            };
            return $foreign.makeAff(function (k) {
                return Data_Functor.map(Effect.functorEffect)(effectCanceler)(v.kill(e, k));
            });
        });
    };
};
var monadThrowAff = new Control_Monad_Error_Class.MonadThrow(function () {
    return monadAff;
}, $foreign._throwError);
var monadErrorAff = new Control_Monad_Error_Class.MonadError(function () {
    return monadThrowAff;
}, $foreign._catchError);
var attempt = Control_Monad_Error_Class["try"](monadErrorAff);
var runAff = function (k) {
    return function (aff) {
        return launchAff(Control_Bind.bindFlipped(bindAff)(function ($51) {
            return Effect_Class.liftEffect(monadEffectAff)(k($51));
        })(Control_Monad_Error_Class["try"](monadErrorAff)(aff)));
    };
};
var runAff_ = function (k) {
    return function (aff) {
        return Data_Functor["void"](Effect.functorEffect)(runAff(k)(aff));
    };
};
var runSuspendedAff = function (k) {
    return function (aff) {
        return launchSuspendedAff(Control_Bind.bindFlipped(bindAff)(function ($52) {
            return Effect_Class.liftEffect(monadEffectAff)(k($52));
        })(Control_Monad_Error_Class["try"](monadErrorAff)(aff)));
    };
};
var parallelAff = new Control_Parallel_Class.Parallel(function () {
    return applicativeParAff;
}, function () {
    return monadAff;
}, Unsafe_Coerce.unsafeCoerce, $foreign._sequential);
var applicativeParAff = new Control_Applicative.Applicative(function () {
    return applyParAff;
}, function ($53) {
    return Control_Parallel_Class.parallel(parallelAff)(Control_Applicative.pure(applicativeAff)($53));
});
var monoidParAff = function (dictMonoid) {
    return new Data_Monoid.Monoid(function () {
        return semigroupParAff(dictMonoid.Semigroup0());
    }, Control_Applicative.pure(applicativeParAff)(Data_Monoid.mempty(dictMonoid)));
};
var semigroupCanceler = new Data_Semigroup.Semigroup(function (v) {
    return function (v1) {
        return function (err) {
            return Control_Parallel.parSequence_(parallelAff)(Data_Foldable.foldableArray)([ v(err), v1(err) ]);
        };
    };
});
var supervise = function (aff) {
    var killError = Effect_Exception.error("[Aff] Child fiber outlived parent");
    var killAll = function (err) {
        return function (sup) {
            return $foreign.makeAff(function (k) {
                return $foreign._killAll(err, sup.supervisor, k(Control_Applicative.pure(Data_Either.applicativeEither)(Data_Unit.unit)));
            });
        };
    };
    var acquire = function __do() {
        var v = $foreign._makeSupervisedFiber(ffiUtil, aff)();
        v.fiber.run();
        return v;
    };
    return $foreign.generalBracket(Effect_Class.liftEffect(monadEffectAff)(acquire))({
        killed: function (err) {
            return function (sup) {
                return Control_Parallel.parSequence_(parallelAff)(Data_Foldable.foldableArray)([ killFiber(err)(sup.fiber), killAll(err)(sup) ]);
            };
        },
        failed: Data_Function["const"](killAll(killError)),
        completed: Data_Function["const"](killAll(killError))
    })(function ($54) {
        return joinFiber((function (v) {
            return v.fiber;
        })($54));
    });
};
var monadRecAff = new Control_Monad_Rec_Class.MonadRec(function () {
    return monadAff;
}, function (k) {
    var go = function (a) {
        return Control_Bind.bind(bindAff)(k(a))(function (v) {
            if (v instanceof Control_Monad_Rec_Class.Done) {
                return Control_Applicative.pure(applicativeAff)(v.value0);
            };
            if (v instanceof Control_Monad_Rec_Class.Loop) {
                return go(v.value0);
            };
            throw new Error("Failed pattern match at Effect.Aff line 99, column 7 - line 101, column 22: " + [ v.constructor.name ]);
        });
    };
    return go;
});
var monoidAff = function (dictMonoid) {
    return new Data_Monoid.Monoid(function () {
        return semigroupAff(dictMonoid.Semigroup0());
    }, Control_Applicative.pure(applicativeAff)(Data_Monoid.mempty(dictMonoid)));
};
var nonCanceler = Data_Function["const"](Control_Applicative.pure(applicativeAff)(Data_Unit.unit));
var monoidCanceler = new Data_Monoid.Monoid(function () {
    return semigroupCanceler;
}, nonCanceler);
var never = $foreign.makeAff(function (v) {
    return Control_Applicative.pure(Effect.applicativeEffect)(Data_Monoid.mempty(monoidCanceler));
});
var apathize = function ($55) {
    return Data_Functor.map(functorAff)(Data_Function["const"](Data_Unit.unit))(attempt($55));
};
var altParAff = new Control_Alt.Alt(function () {
    return functorParAff;
}, $foreign._parAffAlt);
var altAff = new Control_Alt.Alt(function () {
    return functorAff;
}, function (a1) {
    return function (a2) {
        return Control_Monad_Error_Class.catchError(monadErrorAff)(a1)(Data_Function["const"](a2));
    };
});
var plusAff = new Control_Plus.Plus(function () {
    return altAff;
}, Control_Monad_Error_Class.throwError(monadThrowAff)(Effect_Exception.error("Always fails")));
var plusParAff = new Control_Plus.Plus(function () {
    return altParAff;
}, Control_Parallel_Class.parallel(parallelAff)(Control_Plus.empty(plusAff)));
var alternativeParAff = new Control_Alternative.Alternative(function () {
    return applicativeParAff;
}, function () {
    return plusParAff;
});
module.exports = {
    Canceler: Canceler,
    launchAff: launchAff,
    launchAff_: launchAff_,
    launchSuspendedAff: launchSuspendedAff,
    runAff: runAff,
    runAff_: runAff_,
    runSuspendedAff: runSuspendedAff,
    forkAff: forkAff,
    suspendAff: suspendAff,
    supervise: supervise,
    attempt: attempt,
    apathize: apathize,
    delay: delay,
    never: never,
    "finally": $$finally,
    invincible: invincible,
    killFiber: killFiber,
    joinFiber: joinFiber,
    cancelWith: cancelWith,
    bracket: bracket,
    nonCanceler: nonCanceler,
    effectCanceler: effectCanceler,
    functorAff: functorAff,
    applyAff: applyAff,
    applicativeAff: applicativeAff,
    bindAff: bindAff,
    monadAff: monadAff,
    semigroupAff: semigroupAff,
    monoidAff: monoidAff,
    altAff: altAff,
    plusAff: plusAff,
    monadRecAff: monadRecAff,
    monadThrowAff: monadThrowAff,
    monadErrorAff: monadErrorAff,
    monadEffectAff: monadEffectAff,
    lazyAff: lazyAff,
    functorParAff: functorParAff,
    applyParAff: applyParAff,
    applicativeParAff: applicativeParAff,
    semigroupParAff: semigroupParAff,
    monoidParAff: monoidParAff,
    altParAff: altParAff,
    plusParAff: plusParAff,
    alternativeParAff: alternativeParAff,
    parallelAff: parallelAff,
    functorFiber: functorFiber,
    applyFiber: applyFiber,
    applicativeFiber: applicativeFiber,
    newtypeCanceler: newtypeCanceler,
    semigroupCanceler: semigroupCanceler,
    monoidCanceler: monoidCanceler,
    makeAff: $foreign.makeAff,
    generalBracket: $foreign.generalBracket
};

},{"../Control.Alt/index.js":15,"../Control.Alternative/index.js":16,"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Lazy/index.js":28,"../Control.Monad.Error.Class/index.js":31,"../Control.Monad.Rec.Class/index.js":36,"../Control.Monad/index.js":47,"../Control.Parallel.Class/index.js":48,"../Control.Parallel/index.js":49,"../Control.Plus/index.js":50,"../Control.Semigroupoid/index.js":51,"../Data.Either/index.js":82,"../Data.Foldable/index.js":92,"../Data.Function.Uncurried/index.js":94,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Newtype/index.js":121,"../Data.Semigroup/index.js":137,"../Data.Time.Duration/index.js":154,"../Data.Unit/index.js":168,"../Effect.Class/index.js":173,"../Effect.Exception/index.js":177,"../Effect.Unsafe/index.js":183,"../Effect/index.js":185,"../Partial.Unsafe/index.js":192,"../Prelude/index.js":195,"../Unsafe.Coerce/index.js":202,"./foreign.js":171}],173:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Category = require("../Control.Category/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Effect = require("../Effect/index.js");
var MonadEffect = function (Monad0, liftEffect) {
    this.Monad0 = Monad0;
    this.liftEffect = liftEffect;
};
var monadEffectEffect = new MonadEffect(function () {
    return Effect.monadEffect;
}, Control_Category.identity(Control_Category.categoryFn));
var liftEffect = function (dict) {
    return dict.liftEffect;
};
module.exports = {
    liftEffect: liftEffect,
    MonadEffect: MonadEffect,
    monadEffectEffect: monadEffectEffect
};

},{"../Control.Category/index.js":24,"../Control.Monad/index.js":47,"../Effect/index.js":185}],174:[function(require,module,exports){
"use strict";

exports.log = function (s) {
  return function () {
    console.log(s);
    return {};
  };
};

exports.warn = function (s) {
  return function () {
    console.warn(s);
    return {};
  };
};

exports.error = function (s) {
  return function () {
    console.error(s);
    return {};
  };
};

exports.info = function (s) {
  return function () {
    console.info(s);
    return {};
  };
};

},{}],175:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Effect = require("../Effect/index.js");
var warnShow = function (dictShow) {
    return function (a) {
        return $foreign.warn(Data_Show.show(dictShow)(a));
    };
};
var logShow = function (dictShow) {
    return function (a) {
        return $foreign.log(Data_Show.show(dictShow)(a));
    };
};
var infoShow = function (dictShow) {
    return function (a) {
        return $foreign.info(Data_Show.show(dictShow)(a));
    };
};
var errorShow = function (dictShow) {
    return function (a) {
        return $foreign.error(Data_Show.show(dictShow)(a));
    };
};
module.exports = {
    logShow: logShow,
    warnShow: warnShow,
    errorShow: errorShow,
    infoShow: infoShow,
    log: $foreign.log,
    warn: $foreign.warn,
    error: $foreign.error,
    info: $foreign.info
};

},{"../Data.Show/index.js":141,"../Data.Unit/index.js":168,"../Effect/index.js":185,"./foreign.js":174}],176:[function(require,module,exports){
"use strict";

exports.showErrorImpl = function (err) {
  return err.stack || err.toString();
};

exports.error = function (msg) {
  return new Error(msg);
};

exports.message = function (e) {
  return e.message;
};

exports.name = function (e) {
  return e.name || "Error";
};

exports.stackImpl = function (just) {
  return function (nothing) {
    return function (e) {
      return e.stack ? just(e.stack) : nothing;
    };
  };
};

exports.throwException = function (e) {
  return function () {
    throw e;
  };
};

exports.catchException = function (c) {
  return function (t) {
    return function () {
      try {
        return t();
      } catch (e) {
        if (e instanceof Error || Object.prototype.toString.call(e) === "[object Error]") {
          return c(e)();
        } else {
          return c(new Error(e.toString()))();
        }
      }
    };
  };
};

},{}],177:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Either = require("../Data.Either/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Show = require("../Data.Show/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var $$try = function (action) {
    return $foreign.catchException(function ($0) {
        return Control_Applicative.pure(Effect.applicativeEffect)(Data_Either.Left.create($0));
    })(Data_Functor.map(Effect.functorEffect)(Data_Either.Right.create)(action));
};
var $$throw = function ($1) {
    return $foreign.throwException($foreign.error($1));
};
var stack = $foreign.stackImpl(Data_Maybe.Just.create)(Data_Maybe.Nothing.value);
var showError = new Data_Show.Show($foreign.showErrorImpl);
module.exports = {
    stack: stack,
    "throw": $$throw,
    "try": $$try,
    showError: showError,
    error: $foreign.error,
    message: $foreign.message,
    name: $foreign.name,
    throwException: $foreign.throwException,
    catchException: $foreign.catchException
};

},{"../Control.Applicative/index.js":17,"../Control.Semigroupoid/index.js":51,"../Data.Either/index.js":82,"../Data.Functor/index.js":102,"../Data.Maybe/index.js":112,"../Data.Show/index.js":141,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":176}],178:[function(require,module,exports){
"use strict";

exports.new = function (val) {
  return function () {
    return { value: val };
  };
};

exports.read = function (ref) {
  return function () {
    return ref.value;
  };
};

exports["modify'"] = function (f) {
  return function (ref) {
    return function () {
      var t = f(ref.value);
      ref.value = t.state;
      return t.value;
    };
  };
};

exports.write = function (val) {
  return function (ref) {
    return function () {
      ref.value = val;
      return {};
    };
  };
};

},{}],179:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Effect = require("../Effect/index.js");
var Prelude = require("../Prelude/index.js");
var modify = function (f) {
    return $foreign["modify'"](function (s) {
        var s$prime = f(s);
        return {
            state: s$prime,
            value: s$prime
        };
    });
};
var modify_ = function (f) {
    return function (s) {
        return Data_Functor["void"](Effect.functorEffect)(modify(f)(s));
    };
};
module.exports = {
    modify: modify,
    modify_: modify_,
    "new": $foreign["new"],
    read: $foreign.read,
    "modify'": $foreign["modify'"],
    write: $foreign.write
};

},{"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Effect/index.js":185,"../Prelude/index.js":195,"./foreign.js":178}],180:[function(require,module,exports){
"use strict";

exports.mkEffectFn1 = function mkEffectFn1(fn) {
  return function(x) {
    return fn(x)();
  };
};

exports.mkEffectFn2 = function mkEffectFn2(fn) {
  return function(a, b) {
    return fn(a)(b)();
  };
};

exports.mkEffectFn3 = function mkEffectFn3(fn) {
  return function(a, b, c) {
    return fn(a)(b)(c)();
  };
};

exports.mkEffectFn4 = function mkEffectFn4(fn) {
  return function(a, b, c, d) {
    return fn(a)(b)(c)(d)();
  };
};

exports.mkEffectFn5 = function mkEffectFn5(fn) {
  return function(a, b, c, d, e) {
    return fn(a)(b)(c)(d)(e)();
  };
};

exports.mkEffectFn6 = function mkEffectFn6(fn) {
  return function(a, b, c, d, e, f) {
    return fn(a)(b)(c)(d)(e)(f)();
  };
};

exports.mkEffectFn7 = function mkEffectFn7(fn) {
  return function(a, b, c, d, e, f, g) {
    return fn(a)(b)(c)(d)(e)(f)(g)();
  };
};

exports.mkEffectFn8 = function mkEffectFn8(fn) {
  return function(a, b, c, d, e, f, g, h) {
    return fn(a)(b)(c)(d)(e)(f)(g)(h)();
  };
};

exports.mkEffectFn9 = function mkEffectFn9(fn) {
  return function(a, b, c, d, e, f, g, h, i) {
    return fn(a)(b)(c)(d)(e)(f)(g)(h)(i)();
  };
};

exports.mkEffectFn10 = function mkEffectFn10(fn) {
  return function(a, b, c, d, e, f, g, h, i, j) {
    return fn(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)();
  };
};

exports.runEffectFn1 = function runEffectFn1(fn) {
  return function(a) {
    return function() {
      return fn(a);
    };
  };
};

exports.runEffectFn2 = function runEffectFn2(fn) {
  return function(a) {
    return function(b) {
      return function() {
        return fn(a, b);
      };
    };
  };
};

exports.runEffectFn3 = function runEffectFn3(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function() {
          return fn(a, b, c);
        };
      };
    };
  };
};

exports.runEffectFn4 = function runEffectFn4(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function(d) {
          return function() {
            return fn(a, b, c, d);
          };
        };
      };
    };
  };
};

exports.runEffectFn5 = function runEffectFn5(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function(d) {
          return function(e) {
            return function() {
              return fn(a, b, c, d, e);
            };
          };
        };
      };
    };
  };
};

exports.runEffectFn6 = function runEffectFn6(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function(d) {
          return function(e) {
            return function(f) {
              return function() {
                return fn(a, b, c, d, e, f);
              };
            };
          };
        };
      };
    };
  };
};

exports.runEffectFn7 = function runEffectFn7(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function(d) {
          return function(e) {
            return function(f) {
              return function(g) {
                return function() {
                  return fn(a, b, c, d, e, f, g);
                };
              };
            };
          };
        };
      };
    };
  };
};

exports.runEffectFn8 = function runEffectFn8(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function(d) {
          return function(e) {
            return function(f) {
              return function(g) {
                return function(h) {
                  return function() {
                    return fn(a, b, c, d, e, f, g, h);
                  };
                };
              };
            };
          };
        };
      };
    };
  };
};

exports.runEffectFn9 = function runEffectFn9(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function(d) {
          return function(e) {
            return function(f) {
              return function(g) {
                return function(h) {
                  return function(i) {
                    return function() {
                      return fn(a, b, c, d, e, f, g, h, i);
                    };
                  };
                };
              };
            };
          };
        };
      };
    };
  };
};

exports.runEffectFn10 = function runEffectFn10(fn) {
  return function(a) {
    return function(b) {
      return function(c) {
        return function(d) {
          return function(e) {
            return function(f) {
              return function(g) {
                return function(h) {
                  return function(i) {
                    return function(j) {
                      return function() {
                        return fn(a, b, c, d, e, f, g, h, i, j);
                      };
                    };
                  };
                };
              };
            };
          };
        };
      };
    };
  };
};

},{}],181:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Effect = require("../Effect/index.js");
module.exports = {
    mkEffectFn1: $foreign.mkEffectFn1,
    mkEffectFn2: $foreign.mkEffectFn2,
    mkEffectFn3: $foreign.mkEffectFn3,
    mkEffectFn4: $foreign.mkEffectFn4,
    mkEffectFn5: $foreign.mkEffectFn5,
    mkEffectFn6: $foreign.mkEffectFn6,
    mkEffectFn7: $foreign.mkEffectFn7,
    mkEffectFn8: $foreign.mkEffectFn8,
    mkEffectFn9: $foreign.mkEffectFn9,
    mkEffectFn10: $foreign.mkEffectFn10,
    runEffectFn1: $foreign.runEffectFn1,
    runEffectFn2: $foreign.runEffectFn2,
    runEffectFn3: $foreign.runEffectFn3,
    runEffectFn4: $foreign.runEffectFn4,
    runEffectFn5: $foreign.runEffectFn5,
    runEffectFn6: $foreign.runEffectFn6,
    runEffectFn7: $foreign.runEffectFn7,
    runEffectFn8: $foreign.runEffectFn8,
    runEffectFn9: $foreign.runEffectFn9,
    runEffectFn10: $foreign.runEffectFn10
};

},{"../Effect/index.js":185,"./foreign.js":180}],182:[function(require,module,exports){
"use strict";

exports.unsafePerformEffect = function (f) {
  return f();
};

},{}],183:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Effect = require("../Effect/index.js");
module.exports = {
    unsafePerformEffect: $foreign.unsafePerformEffect
};

},{"../Effect/index.js":185,"./foreign.js":182}],184:[function(require,module,exports){
"use strict";

exports.pureE = function (a) {
  return function () {
    return a;
  };
};

exports.bindE = function (a) {
  return function (f) {
    return function () {
      return f(a())();
    };
  };
};

exports.untilE = function (f) {
  return function () {
    while (!f());
    return {};
  };
};

exports.whileE = function (f) {
  return function (a) {
    return function () {
      while (f()) {
        a();
      }
      return {};
    };
  };
};

exports.forE = function (lo) {
  return function (hi) {
    return function (f) {
      return function () {
        for (var i = lo; i < hi; i++) {
          f(i)();
        }
      };
    };
  };
};

exports.foreachE = function (as) {
  return function (f) {
    return function () {
      for (var i = 0, l = as.length; i < l; i++) {
        f(as[i])();
      }
    };
  };
};

},{}],185:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Prelude = require("../Prelude/index.js");
var monadEffect = new Control_Monad.Monad(function () {
    return applicativeEffect;
}, function () {
    return bindEffect;
});
var bindEffect = new Control_Bind.Bind(function () {
    return applyEffect;
}, $foreign.bindE);
var applyEffect = new Control_Apply.Apply(function () {
    return functorEffect;
}, Control_Monad.ap(monadEffect));
var applicativeEffect = new Control_Applicative.Applicative(function () {
    return applyEffect;
}, $foreign.pureE);
var functorEffect = new Data_Functor.Functor(Control_Applicative.liftA1(applicativeEffect));
var semigroupEffect = function (dictSemigroup) {
    return new Data_Semigroup.Semigroup(Control_Apply.lift2(applyEffect)(Data_Semigroup.append(dictSemigroup)));
};
var monoidEffect = function (dictMonoid) {
    return new Data_Monoid.Monoid(function () {
        return semigroupEffect(dictMonoid.Semigroup0());
    }, $foreign.pureE(Data_Monoid.mempty(dictMonoid)));
};
module.exports = {
    functorEffect: functorEffect,
    applyEffect: applyEffect,
    applicativeEffect: applicativeEffect,
    bindEffect: bindEffect,
    monadEffect: monadEffect,
    semigroupEffect: semigroupEffect,
    monoidEffect: monoidEffect,
    untilE: $foreign.untilE,
    whileE: $foreign.whileE,
    forE: $foreign.forE,
    foreachE: $foreign.foreachE
};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Monad/index.js":47,"../Data.Functor/index.js":102,"../Data.Monoid/index.js":119,"../Data.Semigroup/index.js":137,"../Prelude/index.js":195,"./foreign.js":184}],186:[function(require,module,exports){
/* globals exports */
"use strict";

exports.nan = NaN;

exports.isNaN = isNaN;

exports.infinity = Infinity;

exports.isFinite = isFinite;

exports.readInt = function (radix) {
  return function (n) {
    return parseInt(n, radix);
  };
};

exports.readFloat = parseFloat;

},{}],187:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
module.exports = {
    nan: $foreign.nan,
    "isNaN": $foreign["isNaN"],
    infinity: $foreign.infinity,
    "isFinite": $foreign["isFinite"],
    readInt: $foreign.readInt,
    readFloat: $foreign.readFloat
};

},{"./foreign.js":186}],188:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Audio_WebAudio_AudioParam = require("../Audio.WebAudio.AudioParam/index.js");
var Audio_WebAudio_BaseAudioContext = require("../Audio.WebAudio.BaseAudioContext/index.js");
var Audio_WebAudio_GainNode = require("../Audio.WebAudio.GainNode/index.js");
var Audio_WebAudio_Oscillator = require("../Audio.WebAudio.Oscillator/index.js");
var Audio_WebAudio_Types = require("../Audio.WebAudio.Types/index.js");
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Data_Array = require("../Data.Array/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Effect = require("../Effect/index.js");
var Effect_Console = require("../Effect.Console/index.js");
var Prelude = require("../Prelude/index.js");
var UserMod = require("../UserMod/index.js");
var main = function __do() {
    var v = Audio_WebAudio_BaseAudioContext.newAudioContext();
    var v1 = Audio_WebAudio_BaseAudioContext.createOscillator(v)();
    Audio_WebAudio_Oscillator.setOscillatorType(Audio_WebAudio_Oscillator.Sine.value)(v1)();
    Effect_Console.log("now calling startOscillator")();
    Audio_WebAudio_Oscillator.startOscillator(0.0)(v1)();
    Control_Bind.bindFlipped(Effect.bindEffect)(Audio_WebAudio_AudioParam.setValue(840.0))(Audio_WebAudio_Oscillator.frequency(v1))();
    Control_Bind.bindFlipped(Effect.bindEffect)(Audio_WebAudio_Types.connect(Audio_WebAudio_Types.connectableDestinationNode)(Audio_WebAudio_Types.audioNodeOscillatorNode)(v1))(Audio_WebAudio_BaseAudioContext.destination(v))();
    Audio_WebAudio_Oscillator.stopOscillator(1.0)(v1)();
    return Data_Unit.unit;
};
module.exports = {
    main: main
};

},{"../Audio.WebAudio.AudioParam/index.js":4,"../Audio.WebAudio.BaseAudioContext/index.js":6,"../Audio.WebAudio.GainNode/index.js":8,"../Audio.WebAudio.Oscillator/index.js":10,"../Audio.WebAudio.Types/index.js":12,"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Data.Array/index.js":66,"../Data.Unit/index.js":168,"../Effect.Console/index.js":175,"../Effect/index.js":185,"../Prelude/index.js":195,"../UserMod/index.js":203}],189:[function(require,module,exports){
"use strict";

// module Math

exports.abs = Math.abs;

exports.acos = Math.acos;

exports.asin = Math.asin;

exports.atan = Math.atan;

exports.atan2 = function (y) {
  return function (x) {
    return Math.atan2(y, x);
  };
};

exports.ceil = Math.ceil;

exports.cos = Math.cos;

exports.exp = Math.exp;

exports.floor = Math.floor;

exports.trunc = Math.trunc || function (n) {
  return n < 0 ? Math.ceil(n) : Math.floor(n);
};

exports.log = Math.log;

exports.max = function (n1) {
  return function (n2) {
    return Math.max(n1, n2);
  };
};

exports.min = function (n1) {
  return function (n2) {
    return Math.min(n1, n2);
  };
};

exports.pow = function (n) {
  return function (p) {
    return Math.pow(n, p);
  };
};

exports.remainder = function (n) {
  return function (m) {
    return n % m;
  };
};

exports.round = Math.round;

exports.sin = Math.sin;

exports.sqrt = Math.sqrt;

exports.tan = Math.tan;

exports.e = Math.E;

exports.ln2 = Math.LN2;

exports.ln10 = Math.LN10;

exports.log2e = Math.LOG2E;

exports.log10e = Math.LOG10E;

exports.pi = Math.PI;

exports.tau = 2 * Math.PI;

exports.sqrt1_2 = Math.SQRT1_2;

exports.sqrt2 = Math.SQRT2;

},{}],190:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
module.exports = {
    abs: $foreign.abs,
    acos: $foreign.acos,
    asin: $foreign.asin,
    atan: $foreign.atan,
    atan2: $foreign.atan2,
    ceil: $foreign.ceil,
    cos: $foreign.cos,
    exp: $foreign.exp,
    floor: $foreign.floor,
    log: $foreign.log,
    max: $foreign.max,
    min: $foreign.min,
    pow: $foreign.pow,
    round: $foreign.round,
    sin: $foreign.sin,
    sqrt: $foreign.sqrt,
    tan: $foreign.tan,
    trunc: $foreign.trunc,
    remainder: $foreign.remainder,
    e: $foreign.e,
    ln2: $foreign.ln2,
    ln10: $foreign.ln10,
    log2e: $foreign.log2e,
    log10e: $foreign.log10e,
    pi: $foreign.pi,
    tau: $foreign.tau,
    sqrt1_2: $foreign.sqrt1_2,
    sqrt2: $foreign.sqrt2
};

},{"./foreign.js":189}],191:[function(require,module,exports){
"use strict";

// module Partial.Unsafe

exports.unsafePartial = function (f) {
  return f();
};

},{}],192:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var Partial = require("../Partial/index.js");
var unsafePartialBecause = function (v) {
    return function (x) {
        return $foreign.unsafePartial(function (dictPartial) {
            return x(dictPartial);
        });
    };
};
var unsafeCrashWith = function (msg) {
    return $foreign.unsafePartial(function (dictPartial) {
        return Partial.crashWith(dictPartial)(msg);
    });
};
module.exports = {
    unsafePartialBecause: unsafePartialBecause,
    unsafeCrashWith: unsafeCrashWith,
    unsafePartial: $foreign.unsafePartial
};

},{"../Partial/index.js":194,"./foreign.js":191}],193:[function(require,module,exports){
"use strict";

// module Partial

exports.crashWith = function () {
  return function (msg) {
    throw new Error(msg);
  };
};

},{}],194:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
var crash = function (dictPartial) {
    return $foreign.crashWith(dictPartial)("Partial.crash: partial function");
};
module.exports = {
    crash: crash,
    crashWith: $foreign.crashWith
};

},{"./foreign.js":193}],195:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Apply = require("../Control.Apply/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Category = require("../Control.Category/index.js");
var Control_Monad = require("../Control.Monad/index.js");
var Control_Semigroupoid = require("../Control.Semigroupoid/index.js");
var Data_Boolean = require("../Data.Boolean/index.js");
var Data_BooleanAlgebra = require("../Data.BooleanAlgebra/index.js");
var Data_Bounded = require("../Data.Bounded/index.js");
var Data_CommutativeRing = require("../Data.CommutativeRing/index.js");
var Data_DivisionRing = require("../Data.DivisionRing/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Field = require("../Data.Field/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Functor = require("../Data.Functor/index.js");
var Data_HeytingAlgebra = require("../Data.HeytingAlgebra/index.js");
var Data_Monoid = require("../Data.Monoid/index.js");
var Data_NaturalTransformation = require("../Data.NaturalTransformation/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ordering = require("../Data.Ordering/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semigroup = require("../Data.Semigroup/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_Show = require("../Data.Show/index.js");
var Data_Unit = require("../Data.Unit/index.js");
var Data_Void = require("../Data.Void/index.js");
module.exports = {};

},{"../Control.Applicative/index.js":17,"../Control.Apply/index.js":19,"../Control.Bind/index.js":23,"../Control.Category/index.js":24,"../Control.Monad/index.js":47,"../Control.Semigroupoid/index.js":51,"../Data.Boolean/index.js":76,"../Data.BooleanAlgebra/index.js":75,"../Data.Bounded/index.js":78,"../Data.CommutativeRing/index.js":79,"../Data.DivisionRing/index.js":81,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.Field/index.js":89,"../Data.Function/index.js":95,"../Data.Functor/index.js":102,"../Data.HeytingAlgebra/index.js":104,"../Data.Monoid/index.js":119,"../Data.NaturalTransformation/index.js":120,"../Data.Ord/index.js":128,"../Data.Ordering/index.js":129,"../Data.Ring/index.js":131,"../Data.Semigroup/index.js":137,"../Data.Semiring/index.js":139,"../Data.Show/index.js":141,"../Data.Unit/index.js":168,"../Data.Void/index.js":169}],196:[function(require,module,exports){
"use strict";

exports.unsafeHas = function (label) {
  return function (rec) {
    return {}.hasOwnProperty.call(rec, label);
  };
};

exports.unsafeGet = function (label) {
  return function (rec) {
    return rec[label];
  };
};

exports.unsafeSet = function (label) {
  return function (value) {
    return function (rec) {
      var copy = {};
      for (var key in rec) {
        if ({}.hasOwnProperty.call(rec, key)) {
          copy[key] = rec[key];
        }
      }
      copy[label] = value;
      return copy;
    };
  };
};

exports.unsafeDelete = function (label) {
  return function (rec) {
    var copy = {};
    for (var key in rec) {
      if (key !== label && {}.hasOwnProperty.call(rec, key)) {
        copy[key] = rec[key];
      }
    }
    return copy;
  };
};

},{}],197:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
module.exports = {
    unsafeHas: $foreign.unsafeHas,
    unsafeGet: $foreign.unsafeGet,
    unsafeSet: $foreign.unsafeSet,
    unsafeDelete: $foreign.unsafeDelete
};

},{"./foreign.js":196}],198:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var RLProxy = (function () {
    function RLProxy() {

    };
    RLProxy.value = new RLProxy();
    return RLProxy;
})();
module.exports = {
    RLProxy: RLProxy
};

},{}],199:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var RProxy = (function () {
    function RProxy() {

    };
    RProxy.value = new RProxy();
    return RProxy;
})();
module.exports = {
    RProxy: RProxy
};

},{}],200:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var TypeEquals = function (from, to) {
    this.from = from;
    this.to = to;
};
var to = function (dict) {
    return dict.to;
};
var refl = new TypeEquals(function (a) {
    return a;
}, function (a) {
    return a;
});
var from = function (dict) {
    return dict.from;
};
module.exports = {
    TypeEquals: TypeEquals,
    to: to,
    from: from,
    refl: refl
};

},{}],201:[function(require,module,exports){
"use strict";

// module Unsafe.Coerce

exports.unsafeCoerce = function (x) {
  return x;
};

},{}],202:[function(require,module,exports){
// Generated by purs version 0.12.0
"use strict";
var $foreign = require("./foreign.js");
module.exports = {
    unsafeCoerce: $foreign.unsafeCoerce
};

},{"./foreign.js":201}],203:[function(require,module,exports){
"use strict";
var Control_Applicative = require("../Control.Applicative/index.js");
var Control_Bind = require("../Control.Bind/index.js");
var Control_Comonad = require("../Control.Comonad/index.js");
var Data_Array = require("../Data.Array/index.js");
var Data_Array_NonEmpty = require("../Data.Array.NonEmpty/index.js");
var Data_Enum = require("../Data.Enum/index.js");
var Data_Eq = require("../Data.Eq/index.js");
var Data_EuclideanRing = require("../Data.EuclideanRing/index.js");
var Data_Foldable = require("../Data.Foldable/index.js");
var Data_Function = require("../Data.Function/index.js");
var Data_Maybe = require("../Data.Maybe/index.js");
var Data_Ord = require("../Data.Ord/index.js");
var Data_Ring = require("../Data.Ring/index.js");
var Data_Semiring = require("../Data.Semiring/index.js");
var Data_String = require("../Data.String/index.js");
var Data_String_CodePoints = require("../Data.String.CodePoints/index.js");
var Effect_Console = require("../Effect.Console/index.js");
var Prelude = require("../Prelude/index.js");

// import Data.Ord (Ord)
var vtVal = 7;

// primes :: Int -> Array Int
// -- primes n = (filter \x -> (x `mod` 2) == 0)  (1..n)
// primes n =
// do
// (filter \x -> x `mod` 2  == 1)  (1..n)
// i <- (filter \x -> x `mod` 2  == 1)  (1..n)
// is n a factor of m
// isFactorOf 10 5
var isFactorOf = function (m) {
    return function (n) {
        return Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt)(m)(n) === 0;
    };
};
var isFactorable2 = function ($copy_n) {
    return function ($copy_v) {
        var $tco_var_n = $copy_n;
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(n, v) {
            if (v === 1) {
                $tco_done = true;
                return false;
            };
            var $9 = isFactorOf(n)(v);
            if ($9) {
                $tco_done = true;
                return true;
            };
            $tco_var_n = n;
            $copy_v = v - 1 | 0;
            return;
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($tco_var_n, $copy_v);
        };
        return $tco_result;
    };
};
var isFactorable = function (n) {
    var $10 = isFactorOf(n)(Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt)(n)(2));
    if ($10) {
        return true;
    };
    return isFactorable2(n)(Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt)(n)(2) - 1 | 0);
};
var factors$prime$prime = Control_Bind.bind(Control_Bind.bindArray)(Data_Array.range(1)(6))(function (v) {
    return Control_Bind.bind(Control_Bind.bindArray)(Data_Array.range(1)(6))(function (v1) {
        return Control_Applicative.pure(Control_Applicative.applicativeArray)([ v, v1 ]);
    });
});
var factors$prime = Control_Bind.bind(Control_Bind.bindArray)(Data_Array.range(1)(6))(function (v) {
    return Control_Bind.bind(Control_Bind.bindArray)(Data_Array.range(v)(6))(function (v1) {
        return Control_Applicative.pure(Control_Applicative.applicativeArray)([ v, v1, v ]);
    });
});
var factors = function (n) {
    return Data_Array.filter(function (xs) {
        return Data_Foldable.product(Data_Foldable.foldableArray)(Data_Semiring.semiringInt)(xs) === n;
    })(Control_Bind.bind(Control_Bind.bindArray)(Data_Array.range(1)(n))(function (v) {
        return Control_Bind.bind(Control_Bind.bindArray)(Data_Array.range(v)(n))(function (v1) {
            return Control_Applicative.pure(Control_Applicative.applicativeArray)([ v, v1 ]);
        });
    }));
};
var extractTail = function (r) {
    return Data_Maybe.maybe("")(function (x) {
        return x.tail;
    })(r);
};

// instance ordRomanNum :: Ord RomaNum where
//   compare = unsafeCompare
// do it recursively, then try to do it using list functions
// recursively  _
// list functions _
// M, m= 0x4d  , 0x6d
// D, d= 0x44  , 0x64
// C, c= 0x43  , 0x63
// L, c= 0x4C  , 0x6c
// X, x= 0x58  , 0x78
// V, v= 0x56  , 0x76
// I, i= 0x49  , 0x69
// convert roman number string to a arabic digits
// e.g. MCMI -> 1901
// romanToArabic :: String -> Int
// romanToArabic s =  r2a h t 0 0
//   where
//     u = S.uncons s
//     h = extractHead u
//     t = extractTail u
//
//
// r2a :: Array Char -> Int
// the workhorse of romanToArabic.  Has an accumulator for recursion.
// it takes the head and tail of a string, accumlator, final result
// r2a :: String -> String -> Int -> Int
// r2a h t a | h == "M" = 1000
//           | otherwise = 7
// h = head, t= tail, a=accumular, b=buffer (temp accumlator)
// r2a :: String -> String -> Int -> Int -> Int
// -- r2a h t a | h == "M" = r2a $ extractHead (uncons t) $ extractTail (uncons t) $ 1000
// -- r2a h t a | h == "M" = r2a h' t' 1000
//               -- where
//               --   u = S.uncons t
//               --   h' = extractHead u
//               --   t' = extractTail u
// r2a h t a b| h == "M" = r2a h' t'  1000  0
//           where
//             u = S.uncons t
//             h' = extractHead u
//             t' = extractTail u
//           | h == "D" = r2a (extractHead u) (extractTail $ S.uncons t) (a + 500)  (0)
//           where
//             u = S.uncons t
//           | h == "C" = r2a (extractHead u) (extractTail $ S.uncons t) (a + 100)  (0)
//           where
//             u = S.uncons t
//           | otherwise = a + 7
// a1 = "C"
// a2 = "C"
// r2a :: String -> String -> Int -> Int -> Int
// r2a h t a b
//           | h == "M" = r2a h' t'  1000  0
//           where
//             u = S.uncons t
//             h' = extractHead u
//             t' = extractTail u
//           | h == "D" = r2a h' t' (a + 500) 0
//           where
//             u = S.uncons t
//             h' = extractHead u
//             t' = extractTail u
//           | h == "C" = r2a h' t' a  100
//           where
//             u = S.uncons t
//             h' = extractHead u
//             t' = extractTail u
//           | otherwise = a + 7
// c= fromMaybe (codePointFromChar 'a') (codePointAt 0 "abc")
// returns
// > :type c
// CodePoint
// to convert to a string:
// CP.singleton c
// return "c"
// arabicToRoman ::
// how to reference a record in a maybe
// maybe 0 (\x -> x.b + 1) a
// where a= (Just { a: 7, b: 8 })
// maybe (codePointFromChar ' ') (\x -> x.head) r
// maybe "" (\x -> x.tail) r
// r=S.uncons "abcd"
// Note: cannot get the compiler to accept my type on this
// Note: the following three are to get at the Maybe created by 'uncons <str>'
var extractHead$prime = function (r) {
    return Data_Maybe.maybe(Data_String_CodePoints.codePointFromChar(" "))(function (x) {
        return x.head;
    })(r);
};
var extractHead = function (r) {
    return Data_String_CodePoints.singleton(Data_Maybe.maybe(Data_String_CodePoints.codePointFromChar(" "))(function (x) {
        return x.head;
    })(r));
};
var extractCharAsStr$prime = function (s) {
    return function (n) {
        return Data_String_CodePoints.singleton(Data_Maybe.fromMaybe(Data_String_CodePoints.codePointFromChar(" "))(Data_String_CodePoints.codePointAt(n)(s)));
    };
};

// extractCharAsStr :: n -> String
// example: extractCharAsStr 0 "abc"
// returns: "a"
var extractCharAsStr = function (n) {
    return function (s) {
        return Data_String_CodePoints.singleton(Data_Maybe.fromMaybe(Data_String_CodePoints.codePointFromChar(" "))(Data_String_CodePoints.codePointAt(n)(s)));
    };
};

// gcd n m = if n > m
//             then gcd (n - m) m
//             else gcd n (m - n)
// data TrafficLight :: Red | Yellow | Green
// class RomaNumClass :: String
// data RomanSeq = [M D C L V I]
// class (Bounded a, Enum a) <= BoundedEnum a where
// instance enumRomanDigit :: BoundedEnum RomanDigit where
//   succ I = V
//   pred V = I
// data RomanNum = "M" | "D" | "C" | "L" | "V" | "I" deriving (Ord)
// data RomanDigit a = M  | D | C | L | V | I deriving Ord)
// data RomanDigit a = M | D | C | L | V | I
// data RomanDigit a = M | D
// data RomanDigit  = M | D | C | L | V | I deriving (Eq)
//
// newRomanDigit :: Int -> RomanDigit
// newRomanDigit 1000 = M
// newRomanDigit 500 = D
// newRomanDigit _ = I
// instance showRomanDigit ::
//   -- where show (Foo {bar}) = "Foo bar=" ++ show bar
//   where show M = "M"
// instance showRomanDigit :: where show (M) = M
// instance showRomanDigit :: Show RomanDigit where
//   -- show x = "Foo bar=" <> show x
//   show M = "M"
//   show D = "D"
//   show C = "C"
//   show L = "L"
//   show V = "V"
//   show I = "I"
// instance showRomanDigit :: Compare RomanDigit where
//   (>) M D = true
// class Eq a <= Ord a where
//   compare :: a -> a -> RomanDigit
// class Ord a <= Ord a where
//   compare :: a -> a -> RomanDigit
// instance eqRomanDigit :: Eq RomanDigit where
// eq (RomanDigit a) (RomanDigit b) = a == b
// a b = a == b
// eq M M = true
// eq _ _ = true
// M == M = True
// D == D = True
// eq (ByEmail a) (ByEmail b) = a == b
// eq (ByPhone a) (ByPhone b) = a == b
// eq _ _ = false
// instance Eq RomanDigit where
//   M == M = True
//   D == D = True
// derive instance ordRomanDigit :: Ord RomanDigit
// derive instance ordRomanDigit :: Ord a => Ord (RomanDigit a)
// instance Ord RomanDigit where
//   M (>) D = true
// compareRomDig :: RomanDigit -> RomanDigit -> Boolean
// compareRomDig a b = a > b
var compRomDig = function (a) {
    return function (b) {
        return a > b;
    };
};
module.exports = {
    vtVal: vtVal,
    factors: factors,
    "factors'": factors$prime,
    "factors''": factors$prime$prime,
    isFactorOf: isFactorOf,
    isFactorable: isFactorable,
    isFactorable2: isFactorable2,
    compRomDig: compRomDig,
    "extractHead'": extractHead$prime,
    extractHead: extractHead,
    extractTail: extractTail,
    extractCharAsStr: extractCharAsStr,
    "extractCharAsStr'": extractCharAsStr$prime
};

},{"../Control.Applicative/index.js":17,"../Control.Bind/index.js":23,"../Control.Comonad/index.js":25,"../Data.Array.NonEmpty/index.js":54,"../Data.Array/index.js":66,"../Data.Enum/index.js":84,"../Data.Eq/index.js":86,"../Data.EuclideanRing/index.js":88,"../Data.Foldable/index.js":92,"../Data.Function/index.js":95,"../Data.Maybe/index.js":112,"../Data.Ord/index.js":128,"../Data.Ring/index.js":131,"../Data.Semiring/index.js":139,"../Data.String.CodePoints/index.js":143,"../Data.String/index.js":151,"../Effect.Console/index.js":175,"../Prelude/index.js":195}],204:[function(require,module,exports){
require('Main').main();

},{"Main":188}]},{},[204]);
