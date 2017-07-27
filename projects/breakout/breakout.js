"use strict";
function breakoutMain() {
  window.onload = jsMain;
}

function jsMain() {
  Haste.breakoutHsMain();
}

// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=0,_1=function(_){return _0;},_2=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_3=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_4=function(_5,_6,_){var _7=B(A1(_5,_)),_8=B(A1(_6,_));return _7;},_9=function(_a,_b,_){var _c=B(A1(_a,_)),_d=B(A1(_b,_));return new T(function(){return B(A1(_c,_d));});},_e=function(_f,_g,_){var _h=B(A1(_g,_));return _f;},_i=function(_j,_k,_){var _l=B(A1(_k,_));return new T(function(){return B(A1(_j,_l));});},_m=new T2(0,_i,_e),_n=function(_o,_){return _o;},_p=function(_q,_r,_){var _s=B(A1(_q,_));return new F(function(){return A1(_r,_);});},_t=new T5(0,_m,_n,_9,_p,_4),_u=new T(function(){return B(unCStr("base"));}),_v=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_w=new T(function(){return B(unCStr("IOException"));}),_x=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_u,_v,_w),_y=__Z,_z=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_x,_y,_y),_A=function(_B){return E(_z);},_C=function(_D){return E(E(_D).a);},_E=function(_F,_G,_H){var _I=B(A1(_F,_)),_J=B(A1(_G,_)),_K=hs_eqWord64(_I.a,_J.a);if(!_K){return __Z;}else{var _L=hs_eqWord64(_I.b,_J.b);return (!_L)?__Z:new T1(1,_H);}},_M=function(_N){var _O=E(_N);return new F(function(){return _E(B(_C(_O.a)),_A,_O.b);});},_P=new T(function(){return B(unCStr(": "));}),_Q=new T(function(){return B(unCStr(")"));}),_R=new T(function(){return B(unCStr(" ("));}),_S=function(_T,_U){var _V=E(_T);return (_V._==0)?E(_U):new T2(1,_V.a,new T(function(){return B(_S(_V.b,_U));}));},_W=new T(function(){return B(unCStr("interrupted"));}),_X=new T(function(){return B(unCStr("system error"));}),_Y=new T(function(){return B(unCStr("unsatisified constraints"));}),_Z=new T(function(){return B(unCStr("user error"));}),_10=new T(function(){return B(unCStr("permission denied"));}),_11=new T(function(){return B(unCStr("illegal operation"));}),_12=new T(function(){return B(unCStr("end of file"));}),_13=new T(function(){return B(unCStr("resource exhausted"));}),_14=new T(function(){return B(unCStr("resource busy"));}),_15=new T(function(){return B(unCStr("does not exist"));}),_16=new T(function(){return B(unCStr("already exists"));}),_17=new T(function(){return B(unCStr("resource vanished"));}),_18=new T(function(){return B(unCStr("timeout"));}),_19=new T(function(){return B(unCStr("unsupported operation"));}),_1a=new T(function(){return B(unCStr("hardware fault"));}),_1b=new T(function(){return B(unCStr("inappropriate type"));}),_1c=new T(function(){return B(unCStr("invalid argument"));}),_1d=new T(function(){return B(unCStr("failed"));}),_1e=new T(function(){return B(unCStr("protocol error"));}),_1f=function(_1g,_1h){switch(E(_1g)){case 0:return new F(function(){return _S(_16,_1h);});break;case 1:return new F(function(){return _S(_15,_1h);});break;case 2:return new F(function(){return _S(_14,_1h);});break;case 3:return new F(function(){return _S(_13,_1h);});break;case 4:return new F(function(){return _S(_12,_1h);});break;case 5:return new F(function(){return _S(_11,_1h);});break;case 6:return new F(function(){return _S(_10,_1h);});break;case 7:return new F(function(){return _S(_Z,_1h);});break;case 8:return new F(function(){return _S(_Y,_1h);});break;case 9:return new F(function(){return _S(_X,_1h);});break;case 10:return new F(function(){return _S(_1e,_1h);});break;case 11:return new F(function(){return _S(_1d,_1h);});break;case 12:return new F(function(){return _S(_1c,_1h);});break;case 13:return new F(function(){return _S(_1b,_1h);});break;case 14:return new F(function(){return _S(_1a,_1h);});break;case 15:return new F(function(){return _S(_19,_1h);});break;case 16:return new F(function(){return _S(_18,_1h);});break;case 17:return new F(function(){return _S(_17,_1h);});break;default:return new F(function(){return _S(_W,_1h);});}},_1i=new T(function(){return B(unCStr("}"));}),_1j=new T(function(){return B(unCStr("{handle: "));}),_1k=function(_1l,_1m,_1n,_1o,_1p,_1q){var _1r=new T(function(){var _1s=new T(function(){var _1t=new T(function(){var _1u=E(_1o);if(!_1u._){return E(_1q);}else{var _1v=new T(function(){return B(_S(_1u,new T(function(){return B(_S(_Q,_1q));},1)));},1);return B(_S(_R,_1v));}},1);return B(_1f(_1m,_1t));}),_1w=E(_1n);if(!_1w._){return E(_1s);}else{return B(_S(_1w,new T(function(){return B(_S(_P,_1s));},1)));}}),_1x=E(_1p);if(!_1x._){var _1y=E(_1l);if(!_1y._){return E(_1r);}else{var _1z=E(_1y.a);if(!_1z._){var _1A=new T(function(){var _1B=new T(function(){return B(_S(_1i,new T(function(){return B(_S(_P,_1r));},1)));},1);return B(_S(_1z.a,_1B));},1);return new F(function(){return _S(_1j,_1A);});}else{var _1C=new T(function(){var _1D=new T(function(){return B(_S(_1i,new T(function(){return B(_S(_P,_1r));},1)));},1);return B(_S(_1z.a,_1D));},1);return new F(function(){return _S(_1j,_1C);});}}}else{return new F(function(){return _S(_1x.a,new T(function(){return B(_S(_P,_1r));},1));});}},_1E=function(_1F){var _1G=E(_1F);return new F(function(){return _1k(_1G.a,_1G.b,_1G.c,_1G.d,_1G.f,_y);});},_1H=function(_1I){return new T2(0,_1J,_1I);},_1K=function(_1L,_1M,_1N){var _1O=E(_1M);return new F(function(){return _1k(_1O.a,_1O.b,_1O.c,_1O.d,_1O.f,_1N);});},_1P=function(_1Q,_1R){var _1S=E(_1Q);return new F(function(){return _1k(_1S.a,_1S.b,_1S.c,_1S.d,_1S.f,_1R);});},_1T=44,_1U=93,_1V=91,_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);if(!_20._){return new F(function(){return unAppCStr("[]",_1Z);});}else{var _21=new T(function(){var _22=new T(function(){var _23=function(_24){var _25=E(_24);if(!_25._){return E(new T2(1,_1U,_1Z));}else{var _26=new T(function(){return B(A2(_1X,_25.a,new T(function(){return B(_23(_25.b));})));});return new T2(1,_1T,_26);}};return B(_23(_20.b));});return B(A2(_1X,_20.a,_22));});return new T2(1,_1V,_21);}},_27=function(_28,_29){return new F(function(){return _1W(_1P,_28,_29);});},_2a=new T3(0,_1K,_1E,_27),_1J=new T(function(){return new T5(0,_A,_2a,_1H,_M,_1E);}),_2b=new T(function(){return E(_1J);}),_2c=function(_2d){return E(E(_2d).c);},_2e=__Z,_2f=7,_2g=function(_2h){return new T6(0,_2e,_2f,_y,_2h,_2e,_2e);},_2i=function(_2j,_){var _2k=new T(function(){return B(A2(_2c,_2b,new T(function(){return B(A1(_2g,_2j));})));});return new F(function(){return die(_2k);});},_2l=function(_2m,_){return new F(function(){return _2i(_2m,_);});},_2n=function(_2o){return new F(function(){return A1(_2l,_2o);});},_2p=function(_2q,_2r,_){var _2s=B(A1(_2q,_));return new F(function(){return A2(_2r,_2s,_);});},_2t=new T5(0,_t,_2p,_p,_n,_2n),_2u=function(_2v){return E(_2v);},_2w=new T2(0,_2t,_2u),_2x=new T(function(){return B(unCStr("!!: negative index"));}),_2y=new T(function(){return B(unCStr("Prelude."));}),_2z=new T(function(){return B(_S(_2y,_2x));}),_2A=new T(function(){return B(err(_2z));}),_2B=new T(function(){return B(unCStr("!!: index too large"));}),_2C=new T(function(){return B(_S(_2y,_2B));}),_2D=new T(function(){return B(err(_2C));}),_2E=function(_2F,_2G){while(1){var _2H=E(_2F);if(!_2H._){return E(_2D);}else{var _2I=E(_2G);if(!_2I){return E(_2H.a);}else{_2F=_2H.b;_2G=_2I-1|0;continue;}}}},_2J=function(_2K,_2L){if(_2L>=0){return new F(function(){return _2E(_2K,_2L);});}else{return E(_2A);}},_2M=new T(function(){return eval("document");}),_2N=function(_2O,_){var _2P=E(_2O);if(!_2P._){return _y;}else{var _2Q=B(_2N(_2P.b,_));return new T2(1,_2P.a,_2Q);}},_2R=function(_2S,_){var _2T=__arr2lst(0,_2S);return new F(function(){return _2N(_2T,_);});},_2U=new T(function(){return eval("(function(e,q){if(!e || typeof e.querySelectorAll !== \'function\') {return [];} else {return e.querySelectorAll(q);}})");}),_2V=function(_2W){return E(E(_2W).b);},_2X=function(_2Y,_2Z,_30){var _31=function(_){var _32=__app2(E(_2U),E(_2Z),toJSStr(E(_30)));return new F(function(){return _2R(_32,_);});};return new F(function(){return A2(_2V,_2Y,_31);});},_33="metaKey",_34="shiftKey",_35="altKey",_36="ctrlKey",_37="keyCode",_38=function(_39,_){var _3a=__get(_39,E(_37)),_3b=__get(_39,E(_36)),_3c=__get(_39,E(_35)),_3d=__get(_39,E(_34)),_3e=__get(_39,E(_33));return new T(function(){var _3f=Number(_3a),_3g=jsTrunc(_3f);return new T5(0,_3g,E(_3b),E(_3c),E(_3d),E(_3e));});},_3h=function(_3i,_3j,_){return new F(function(){return _38(E(_3j),_);});},_3k="keydown",_3l="keyup",_3m="keypress",_3n=function(_3o){switch(E(_3o)){case 0:return E(_3m);case 1:return E(_3l);default:return E(_3k);}},_3p=new T2(0,_3n,_3h),_3q=function(_3r,_){var _3s=__app1(E(_3),_3r);if(!_3s){return _2e;}else{var _3t=__app1(E(_2),_3r);return new T1(1,new T2(0,_3t,_3r));}},_3u=function(_3v,_){return new F(function(){return _3q(E(_3v),_);});},_3w=function(_3x){return E(_3x).b;},_3y=new T2(0,_3w,_3u),_3z=new T2(0,_2w,_n),_3A=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_3B=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_3C=function(_3D,_3E,_){var _3F=__app1(E(_3A),_3E),_3G=B(A2(_3D,_3E,_)),_3H=__app1(E(_3B),_3E);return new F(function(){return _1(_);});},_3I=new T3(0,255,255,255),_3J=480,_3K=460,_3L=new T(function(){return eval("(function(e){e.width = e.width;})");}),_3M=",",_3N="rgba(",_3O=new T(function(){return toJSStr(_y);}),_3P="rgb(",_3Q=")",_3R=new T2(1,_3Q,_y),_3S=function(_3T){var _3U=E(_3T);if(!_3U._){var _3V=jsCat(new T2(1,_3P,new T2(1,new T(function(){return String(_3U.a);}),new T2(1,_3M,new T2(1,new T(function(){return String(_3U.b);}),new T2(1,_3M,new T2(1,new T(function(){return String(_3U.c);}),_3R)))))),E(_3O));return E(_3V);}else{var _3W=jsCat(new T2(1,_3N,new T2(1,new T(function(){return String(_3U.a);}),new T2(1,_3M,new T2(1,new T(function(){return String(_3U.b);}),new T2(1,_3M,new T2(1,new T(function(){return String(_3U.c);}),new T2(1,_3M,new T2(1,new T(function(){return String(_3U.d);}),_3R)))))))),E(_3O));return E(_3W);}},_3X="strokeStyle",_3Y="fillStyle",_3Z=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_40=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_41=function(_42,_43){var _44=new T(function(){return B(_3S(_42));});return function(_45,_){var _46=E(_45),_47=E(_3Y),_48=E(_3Z),_49=__app2(_48,_46,_47),_4a=E(_3X),_4b=__app2(_48,_46,_4a),_4c=E(_44),_4d=E(_40),_4e=__app3(_4d,_46,_47,_4c),_4f=__app3(_4d,_46,_4a,_4c),_4g=B(A2(_43,_46,_)),_4h=String(_49),_4i=__app3(_4d,_46,_47,_4h),_4j=String(_4b),_4k=__app3(_4d,_46,_4a,_4j);return new F(function(){return _1(_);});};},_4l=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_4m=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_4n=function(_4o,_4p,_){var _4q=E(_4o);if(!_4q._){return _0;}else{var _4r=E(_4q.a),_4s=E(_4p),_4t=__app3(E(_4l),_4s,E(_4r.a),E(_4r.b)),_4u=E(_4q.b);if(!_4u._){return _0;}else{var _4v=E(_4u.a),_4w=E(_4m),_4x=__app3(_4w,_4s,E(_4v.a),E(_4v.b)),_4y=function(_4z,_){while(1){var _4A=E(_4z);if(!_4A._){return _0;}else{var _4B=E(_4A.a),_4C=__app3(_4w,_4s,E(_4B.a),E(_4B.b));_4z=_4A.b;continue;}}};return new F(function(){return _4y(_4u.b,_);});}}},_4D=function(_4E,_4F,_4G,_){var _4H=__app1(E(_3L),_4F),_4I=E(E(_4G).c),_4J=_4I+150,_4K=function(_4L,_){return new F(function(){return _4n(new T2(1,new T2(0,_4I,_3K),new T2(1,new T2(0,_4J,_3K),new T2(1,new T2(0,_4J,_3J),new T2(1,new T2(0,_4I,_3J),new T2(1,new T2(0,_4I,_3K),_y))))),_4L,_);});};return new F(function(){return A(_41,[_3I,function(_4M,_){return new F(function(){return _3C(_4K,E(_4M),_);});},_4E,_]);});},_4N=new T1(0,10),_4O=function(_4P){return E(E(_4P).a);},_4Q=function(_4R){return E(E(_4R).a);},_4S=function(_4T){return E(E(_4T).b);},_4U=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_4V=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_4W=function(_){return new F(function(){return __jsNull();});},_4X=function(_4Y){var _4Z=B(A1(_4Y,_));return E(_4Z);},_50=new T(function(){return B(_4X(_4W));}),_51=new T(function(){return E(_50);}),_52=function(_53){return E(E(_53).b);},_54=function(_55,_56,_57){var _58=B(_4O(_55)),_59=new T(function(){return B(_2V(_58));}),_5a=function(_5b){var _5c=function(_){var _5d=E(_56);if(!_5d._){var _5e=B(A1(_5b,_0)),_5f=__createJSFunc(0,function(_){var _5g=B(A1(_5e,_));return _51;}),_5h=__app2(E(_4V),_5d.a,_5f);return new T(function(){var _5i=Number(_5h),_5j=jsTrunc(_5i);return new T2(0,_5j,E(_5d));});}else{var _5k=B(A1(_5b,_0)),_5l=__createJSFunc(0,function(_){var _5m=B(A1(_5k,_));return _51;}),_5n=__app2(E(_4U),_5d.a,_5l);return new T(function(){var _5o=Number(_5n),_5p=jsTrunc(_5o);return new T2(0,_5p,E(_5d));});}};return new F(function(){return A1(_59,_5c);});},_5q=new T(function(){return B(A2(_52,_55,function(_5r){return E(_57);}));});return new F(function(){return A3(_4S,B(_4Q(_58)),_5q,_5a);});},_5s=function(_5t,_5u,_5v,_){var _5w=rMV(_5v),_5x=B(_4D(_5t,_5u,_5w,_)),_5y=new T(function(){return E(E(_5w).b);}),_5z=new T(function(){return E(E(_5w).a);}),_5A=new T(function(){var _5B=E(_5w);return new T4(0,new T2(0,new T(function(){return E(E(_5z).a)+E(E(_5y).a);}),new T(function(){return E(E(_5z).b)+E(E(_5y).b);})),_5B.b,_5B.c,_5B.d);}),_5C=mMV(_5v,function(_5D){return E(new T2(0,_5A,_0));}),_5E=E(_5C),_5F=B(A(_54,[_3z,_4N,function(_){return new F(function(){return _5s(_5t,_5u,_5v,_);});},_]));return _0;},_5G=function(_5H,_5I){var _5J=jsShowI(_5H);return new F(function(){return _S(fromJSStr(_5J),_5I);});},_5K=41,_5L=40,_5M=function(_5N,_5O,_5P){if(_5O>=0){return new F(function(){return _5G(_5O,_5P);});}else{if(_5N<=6){return new F(function(){return _5G(_5O,_5P);});}else{return new T2(1,_5L,new T(function(){var _5Q=jsShowI(_5O);return B(_S(fromJSStr(_5Q),new T2(1,_5K,_5P)));}));}}},_5R=2,_5S=function(_5T){return new F(function(){return fromJSStr(E(_5T));});},_5U=function(_5V){return E(E(_5V).a);},_5W=new T(function(){return eval("(function(e,p){return e.hasAttribute(p) ? e.getAttribute(p) : \'\';})");}),_5X=function(_5Y,_5Z,_60,_61){var _62=new T(function(){var _63=function(_){var _64=__app2(E(_5W),B(A2(_5U,_5Y,_60)),E(_61));return new T(function(){return String(_64);});};return E(_63);});return new F(function(){return A2(_2V,_5Z,_62);});},_65=function(_66){return E(E(_66).d);},_67=function(_68,_69,_6a,_6b){var _6c=B(_4Q(_69)),_6d=new T(function(){return B(_65(_6c));}),_6e=function(_6f){return new F(function(){return A1(_6d,new T(function(){return B(_5S(_6f));}));});},_6g=new T(function(){return B(_5X(_68,_69,_6a,new T(function(){return toJSStr(E(_6b));},1)));});return new F(function(){return A3(_4S,_6c,_6g,_6e);});},_6h=new T(function(){return B(unCStr("\n"));}),_6i=function(_6j,_6k,_){var _6l=jsWriteHandle(E(_6j),toJSStr(E(_6k)));return _0;},_6m=function(_6n,_6o,_){var _6p=E(_6n),_6q=jsWriteHandle(_6p,toJSStr(E(_6o)));return new F(function(){return _6i(_6p,_6h,_);});},_6r=75,_6s=0,_6t=20,_6u=new T2(0,_6t,_6t),_6v=8,_6w=10,_6x=new T2(0,_6v,_6w),_6y=new T4(0,_6u,_6x,_6r,_6s),_6z=new T(function(){return B(unCStr("Pattern match failure in do expression at breakout.hs:50:5-15"));}),_6A=new T6(0,_2e,_2f,_y,_6z,_2e,_2e),_6B=new T(function(){return B(_1H(_6A));}),_6C=new T(function(){return B(unCStr("height"));}),_6D=34,_6E=new T2(1,_6D,_y),_6F=new T(function(){return B(unCStr("width"));}),_6G=function(_6H){while(1){var _6I=E(_6H);if(!_6I._){_6H=new T1(1,I_fromInt(_6I.a));continue;}else{return new F(function(){return I_toString(_6I.a);});}}},_6J=function(_6K,_6L){return new F(function(){return _S(fromJSStr(B(_6G(_6K))),_6L);});},_6M=function(_6N,_6O){var _6P=E(_6N);if(!_6P._){var _6Q=_6P.a,_6R=E(_6O);return (_6R._==0)?_6Q<_6R.a:I_compareInt(_6R.a,_6Q)>0;}else{var _6S=_6P.a,_6T=E(_6O);return (_6T._==0)?I_compareInt(_6S,_6T.a)<0:I_compare(_6S,_6T.a)<0;}},_6U=new T1(0,0),_6V=function(_6W,_6X,_6Y){if(_6W<=6){return new F(function(){return _6J(_6X,_6Y);});}else{if(!B(_6M(_6X,_6U))){return new F(function(){return _6J(_6X,_6Y);});}else{return new T2(1,_5L,new T(function(){return B(_S(fromJSStr(B(_6G(_6X))),new T2(1,_5K,_6Y)));}));}}},_6Z=new T1(0,8),_70=new T(function(){return B(_6V(0,_6Z,_y));}),_71=new T(function(){return B(unAppCStr("abc=",_70));}),_72=new T(function(){return B(unCStr("ACK"));}),_73=new T(function(){return B(unCStr("BEL"));}),_74=new T(function(){return B(unCStr("BS"));}),_75=new T(function(){return B(unCStr("SP"));}),_76=new T2(1,_75,_y),_77=new T(function(){return B(unCStr("US"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("RS"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("GS"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("FS"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("ESC"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("SUB"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("EM"));}),_7k=new T2(1,_7j,_7i),_7l=new T(function(){return B(unCStr("CAN"));}),_7m=new T2(1,_7l,_7k),_7n=new T(function(){return B(unCStr("ETB"));}),_7o=new T2(1,_7n,_7m),_7p=new T(function(){return B(unCStr("SYN"));}),_7q=new T2(1,_7p,_7o),_7r=new T(function(){return B(unCStr("NAK"));}),_7s=new T2(1,_7r,_7q),_7t=new T(function(){return B(unCStr("DC4"));}),_7u=new T2(1,_7t,_7s),_7v=new T(function(){return B(unCStr("DC3"));}),_7w=new T2(1,_7v,_7u),_7x=new T(function(){return B(unCStr("DC2"));}),_7y=new T2(1,_7x,_7w),_7z=new T(function(){return B(unCStr("DC1"));}),_7A=new T2(1,_7z,_7y),_7B=new T(function(){return B(unCStr("DLE"));}),_7C=new T2(1,_7B,_7A),_7D=new T(function(){return B(unCStr("SI"));}),_7E=new T2(1,_7D,_7C),_7F=new T(function(){return B(unCStr("SO"));}),_7G=new T2(1,_7F,_7E),_7H=new T(function(){return B(unCStr("CR"));}),_7I=new T2(1,_7H,_7G),_7J=new T(function(){return B(unCStr("FF"));}),_7K=new T2(1,_7J,_7I),_7L=new T(function(){return B(unCStr("VT"));}),_7M=new T2(1,_7L,_7K),_7N=new T(function(){return B(unCStr("LF"));}),_7O=new T2(1,_7N,_7M),_7P=new T(function(){return B(unCStr("HT"));}),_7Q=new T2(1,_7P,_7O),_7R=new T2(1,_74,_7Q),_7S=new T2(1,_73,_7R),_7T=new T2(1,_72,_7S),_7U=new T(function(){return B(unCStr("ENQ"));}),_7V=new T2(1,_7U,_7T),_7W=new T(function(){return B(unCStr("EOT"));}),_7X=new T2(1,_7W,_7V),_7Y=new T(function(){return B(unCStr("ETX"));}),_7Z=new T2(1,_7Y,_7X),_80=new T(function(){return B(unCStr("STX"));}),_81=new T2(1,_80,_7Z),_82=new T(function(){return B(unCStr("SOH"));}),_83=new T2(1,_82,_81),_84=new T(function(){return B(unCStr("NUL"));}),_85=new T2(1,_84,_83),_86=92,_87=new T(function(){return B(unCStr("\\DEL"));}),_88=new T(function(){return B(unCStr("\\a"));}),_89=new T(function(){return B(unCStr("\\\\"));}),_8a=new T(function(){return B(unCStr("\\SO"));}),_8b=new T(function(){return B(unCStr("\\r"));}),_8c=new T(function(){return B(unCStr("\\f"));}),_8d=new T(function(){return B(unCStr("\\v"));}),_8e=new T(function(){return B(unCStr("\\n"));}),_8f=new T(function(){return B(unCStr("\\t"));}),_8g=new T(function(){return B(unCStr("\\b"));}),_8h=function(_8i,_8j){if(_8i<=127){var _8k=E(_8i);switch(_8k){case 92:return new F(function(){return _S(_89,_8j);});break;case 127:return new F(function(){return _S(_87,_8j);});break;default:if(_8k<32){var _8l=E(_8k);switch(_8l){case 7:return new F(function(){return _S(_88,_8j);});break;case 8:return new F(function(){return _S(_8g,_8j);});break;case 9:return new F(function(){return _S(_8f,_8j);});break;case 10:return new F(function(){return _S(_8e,_8j);});break;case 11:return new F(function(){return _S(_8d,_8j);});break;case 12:return new F(function(){return _S(_8c,_8j);});break;case 13:return new F(function(){return _S(_8b,_8j);});break;case 14:return new F(function(){return _S(_8a,new T(function(){var _8m=E(_8j);if(!_8m._){return __Z;}else{if(E(_8m.a)==72){return B(unAppCStr("\\&",_8m));}else{return E(_8m);}}},1));});break;default:return new F(function(){return _S(new T2(1,_86,new T(function(){return B(_2J(_85,_8l));})),_8j);});}}else{return new T2(1,_8k,_8j);}}}else{var _8n=new T(function(){var _8o=jsShowI(_8i);return B(_S(fromJSStr(_8o),new T(function(){var _8p=E(_8j);if(!_8p._){return __Z;}else{var _8q=E(_8p.a);if(_8q<48){return E(_8p);}else{if(_8q>57){return E(_8p);}else{return B(unAppCStr("\\&",_8p));}}}},1)));});return new T2(1,_86,_8n);}},_8r=new T(function(){return B(unCStr("\\\""));}),_8s=function(_8t,_8u){var _8v=E(_8t);if(!_8v._){return E(_8u);}else{var _8w=_8v.b,_8x=E(_8v.a);if(_8x==34){return new F(function(){return _S(_8r,new T(function(){return B(_8s(_8w,_8u));},1));});}else{return new F(function(){return _8h(_8x,new T(function(){return B(_8s(_8w,_8u));}));});}}},_8y=new T(function(){return B(_8s(_71,_6E));}),_8z=new T2(1,_6D,_8y),_8A=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T(function(){return B(_5M(0,7,_y));}),_8D=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_8E=new T(function(){return B(err(_8D));}),_8F=new T(function(){return B(unCStr("base"));}),_8G=new T(function(){return B(unCStr("Control.Exception.Base"));}),_8H=new T(function(){return B(unCStr("PatternMatchFail"));}),_8I=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_8F,_8G,_8H),_8J=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_8I,_y,_y),_8K=function(_8L){return E(_8J);},_8M=function(_8N){var _8O=E(_8N);return new F(function(){return _E(B(_C(_8O.a)),_8K,_8O.b);});},_8P=function(_8Q){return E(E(_8Q).a);},_8R=function(_8S){return new T2(0,_8T,_8S);},_8U=function(_8V,_8W){return new F(function(){return _S(E(_8V).a,_8W);});},_8X=function(_8Y,_8Z){return new F(function(){return _1W(_8U,_8Y,_8Z);});},_90=function(_91,_92,_93){return new F(function(){return _S(E(_92).a,_93);});},_94=new T3(0,_90,_8P,_8X),_8T=new T(function(){return new T5(0,_8K,_94,_8R,_8M,_8P);}),_95=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_96=function(_97,_98){return new F(function(){return die(new T(function(){return B(A2(_2c,_98,_97));}));});},_99=function(_9a,_9b){return new F(function(){return _96(_9a,_9b);});},_9c=function(_9d,_9e){var _9f=E(_9e);if(!_9f._){return new T2(0,_y,_y);}else{var _9g=_9f.a;if(!B(A1(_9d,_9g))){return new T2(0,_y,_9f);}else{var _9h=new T(function(){var _9i=B(_9c(_9d,_9f.b));return new T2(0,_9i.a,_9i.b);});return new T2(0,new T2(1,_9g,new T(function(){return E(E(_9h).a);})),new T(function(){return E(E(_9h).b);}));}}},_9j=32,_9k=new T(function(){return B(unCStr("\n"));}),_9l=function(_9m){return (E(_9m)==124)?false:true;},_9n=function(_9o,_9p){var _9q=B(_9c(_9l,B(unCStr(_9o)))),_9r=_9q.a,_9s=function(_9t,_9u){var _9v=new T(function(){var _9w=new T(function(){return B(_S(_9p,new T(function(){return B(_S(_9u,_9k));},1)));});return B(unAppCStr(": ",_9w));},1);return new F(function(){return _S(_9t,_9v);});},_9x=E(_9q.b);if(!_9x._){return new F(function(){return _9s(_9r,_y);});}else{if(E(_9x.a)==124){return new F(function(){return _9s(_9r,new T2(1,_9j,_9x.b));});}else{return new F(function(){return _9s(_9r,_y);});}}},_9y=function(_9z){return new F(function(){return _99(new T1(0,new T(function(){return B(_9n(_9z,_95));})),_8T);});},_9A=new T(function(){return B(_9y("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_9B=function(_9C,_9D){while(1){var _9E=B((function(_9F,_9G){var _9H=E(_9F);switch(_9H._){case 0:var _9I=E(_9G);if(!_9I._){return __Z;}else{_9C=B(A1(_9H.a,_9I.a));_9D=_9I.b;return __continue;}break;case 1:var _9J=B(A1(_9H.a,_9G)),_9K=_9G;_9C=_9J;_9D=_9K;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_9H.a,_9G),new T(function(){return B(_9B(_9H.b,_9G));}));default:return E(_9H.a);}})(_9C,_9D));if(_9E!=__continue){return _9E;}}},_9L=function(_9M,_9N){var _9O=function(_9P){var _9Q=E(_9N);if(_9Q._==3){return new T2(3,_9Q.a,new T(function(){return B(_9L(_9M,_9Q.b));}));}else{var _9R=E(_9M);if(_9R._==2){return E(_9Q);}else{var _9S=E(_9Q);if(_9S._==2){return E(_9R);}else{var _9T=function(_9U){var _9V=E(_9S);if(_9V._==4){var _9W=function(_9X){return new T1(4,new T(function(){return B(_S(B(_9B(_9R,_9X)),_9V.a));}));};return new T1(1,_9W);}else{var _9Y=E(_9R);if(_9Y._==1){var _9Z=_9Y.a,_a0=E(_9V);if(!_a0._){return new T1(1,function(_a1){return new F(function(){return _9L(B(A1(_9Z,_a1)),_a0);});});}else{var _a2=function(_a3){return new F(function(){return _9L(B(A1(_9Z,_a3)),new T(function(){return B(A1(_a0.a,_a3));}));});};return new T1(1,_a2);}}else{var _a4=E(_9V);if(!_a4._){return E(_9A);}else{var _a5=function(_a6){return new F(function(){return _9L(_9Y,new T(function(){return B(A1(_a4.a,_a6));}));});};return new T1(1,_a5);}}}},_a7=E(_9R);switch(_a7._){case 1:var _a8=E(_9S);if(_a8._==4){var _a9=function(_aa){return new T1(4,new T(function(){return B(_S(B(_9B(B(A1(_a7.a,_aa)),_aa)),_a8.a));}));};return new T1(1,_a9);}else{return new F(function(){return _9T(_);});}break;case 4:var _ab=_a7.a,_ac=E(_9S);switch(_ac._){case 0:var _ad=function(_ae){var _af=new T(function(){return B(_S(_ab,new T(function(){return B(_9B(_ac,_ae));},1)));});return new T1(4,_af);};return new T1(1,_ad);case 1:var _ag=function(_ah){var _ai=new T(function(){return B(_S(_ab,new T(function(){return B(_9B(B(A1(_ac.a,_ah)),_ah));},1)));});return new T1(4,_ai);};return new T1(1,_ag);default:return new T1(4,new T(function(){return B(_S(_ab,_ac.a));}));}break;default:return new F(function(){return _9T(_);});}}}}},_aj=E(_9M);switch(_aj._){case 0:var _ak=E(_9N);if(!_ak._){var _al=function(_am){return new F(function(){return _9L(B(A1(_aj.a,_am)),new T(function(){return B(A1(_ak.a,_am));}));});};return new T1(0,_al);}else{return new F(function(){return _9O(_);});}break;case 3:return new T2(3,_aj.a,new T(function(){return B(_9L(_aj.b,_9N));}));default:return new F(function(){return _9O(_);});}},_an=new T(function(){return B(unCStr("("));}),_ao=new T(function(){return B(unCStr(")"));}),_ap=function(_aq,_ar){while(1){var _as=E(_aq);if(!_as._){return (E(_ar)._==0)?true:false;}else{var _at=E(_ar);if(!_at._){return false;}else{if(E(_as.a)!=E(_at.a)){return false;}else{_aq=_as.b;_ar=_at.b;continue;}}}}},_au=function(_av,_aw){return E(_av)!=E(_aw);},_ax=function(_ay,_az){return E(_ay)==E(_az);},_aA=new T2(0,_ax,_au),_aB=function(_aC,_aD){while(1){var _aE=E(_aC);if(!_aE._){return (E(_aD)._==0)?true:false;}else{var _aF=E(_aD);if(!_aF._){return false;}else{if(E(_aE.a)!=E(_aF.a)){return false;}else{_aC=_aE.b;_aD=_aF.b;continue;}}}}},_aG=function(_aH,_aI){return (!B(_aB(_aH,_aI)))?true:false;},_aJ=new T2(0,_aB,_aG),_aK=function(_aL,_aM){var _aN=E(_aL);switch(_aN._){case 0:return new T1(0,function(_aO){return new F(function(){return _aK(B(A1(_aN.a,_aO)),_aM);});});case 1:return new T1(1,function(_aP){return new F(function(){return _aK(B(A1(_aN.a,_aP)),_aM);});});case 2:return new T0(2);case 3:return new F(function(){return _9L(B(A1(_aM,_aN.a)),new T(function(){return B(_aK(_aN.b,_aM));}));});break;default:var _aQ=function(_aR){var _aS=E(_aR);if(!_aS._){return __Z;}else{var _aT=E(_aS.a);return new F(function(){return _S(B(_9B(B(A1(_aM,_aT.a)),_aT.b)),new T(function(){return B(_aQ(_aS.b));},1));});}},_aU=B(_aQ(_aN.a));return (_aU._==0)?new T0(2):new T1(4,_aU);}},_aV=new T0(2),_aW=function(_aX){return new T2(3,_aX,_aV);},_aY=function(_aZ,_b0){var _b1=E(_aZ);if(!_b1){return new F(function(){return A1(_b0,_0);});}else{var _b2=new T(function(){return B(_aY(_b1-1|0,_b0));});return new T1(0,function(_b3){return E(_b2);});}},_b4=function(_b5,_b6,_b7){var _b8=new T(function(){return B(A1(_b5,_aW));}),_b9=function(_ba,_bb,_bc,_bd){while(1){var _be=B((function(_bf,_bg,_bh,_bi){var _bj=E(_bf);switch(_bj._){case 0:var _bk=E(_bg);if(!_bk._){return new F(function(){return A1(_b6,_bi);});}else{var _bl=_bh+1|0,_bm=_bi;_ba=B(A1(_bj.a,_bk.a));_bb=_bk.b;_bc=_bl;_bd=_bm;return __continue;}break;case 1:var _bn=B(A1(_bj.a,_bg)),_bo=_bg,_bl=_bh,_bm=_bi;_ba=_bn;_bb=_bo;_bc=_bl;_bd=_bm;return __continue;case 2:return new F(function(){return A1(_b6,_bi);});break;case 3:var _bp=new T(function(){return B(_aK(_bj,_bi));});return new F(function(){return _aY(_bh,function(_bq){return E(_bp);});});break;default:return new F(function(){return _aK(_bj,_bi);});}})(_ba,_bb,_bc,_bd));if(_be!=__continue){return _be;}}};return function(_br){return new F(function(){return _b9(_b8,_br,0,_b7);});};},_bs=function(_bt){return new F(function(){return A1(_bt,_y);});},_bu=function(_bv,_bw){var _bx=function(_by){var _bz=E(_by);if(!_bz._){return E(_bs);}else{var _bA=_bz.a;if(!B(A1(_bv,_bA))){return E(_bs);}else{var _bB=new T(function(){return B(_bx(_bz.b));}),_bC=function(_bD){var _bE=new T(function(){return B(A1(_bB,function(_bF){return new F(function(){return A1(_bD,new T2(1,_bA,_bF));});}));});return new T1(0,function(_bG){return E(_bE);});};return E(_bC);}}};return function(_bH){return new F(function(){return A2(_bx,_bH,_bw);});};},_bI=new T0(6),_bJ=new T(function(){return B(unCStr("valDig: Bad base"));}),_bK=new T(function(){return B(err(_bJ));}),_bL=function(_bM,_bN){var _bO=function(_bP,_bQ){var _bR=E(_bP);if(!_bR._){var _bS=new T(function(){return B(A1(_bQ,_y));});return function(_bT){return new F(function(){return A1(_bT,_bS);});};}else{var _bU=E(_bR.a),_bV=function(_bW){var _bX=new T(function(){return B(_bO(_bR.b,function(_bY){return new F(function(){return A1(_bQ,new T2(1,_bW,_bY));});}));}),_bZ=function(_c0){var _c1=new T(function(){return B(A1(_bX,_c0));});return new T1(0,function(_c2){return E(_c1);});};return E(_bZ);};switch(E(_bM)){case 8:if(48>_bU){var _c3=new T(function(){return B(A1(_bQ,_y));});return function(_c4){return new F(function(){return A1(_c4,_c3);});};}else{if(_bU>55){var _c5=new T(function(){return B(A1(_bQ,_y));});return function(_c6){return new F(function(){return A1(_c6,_c5);});};}else{return new F(function(){return _bV(_bU-48|0);});}}break;case 10:if(48>_bU){var _c7=new T(function(){return B(A1(_bQ,_y));});return function(_c8){return new F(function(){return A1(_c8,_c7);});};}else{if(_bU>57){var _c9=new T(function(){return B(A1(_bQ,_y));});return function(_ca){return new F(function(){return A1(_ca,_c9);});};}else{return new F(function(){return _bV(_bU-48|0);});}}break;case 16:if(48>_bU){if(97>_bU){if(65>_bU){var _cb=new T(function(){return B(A1(_bQ,_y));});return function(_cc){return new F(function(){return A1(_cc,_cb);});};}else{if(_bU>70){var _cd=new T(function(){return B(A1(_bQ,_y));});return function(_ce){return new F(function(){return A1(_ce,_cd);});};}else{return new F(function(){return _bV((_bU-65|0)+10|0);});}}}else{if(_bU>102){if(65>_bU){var _cf=new T(function(){return B(A1(_bQ,_y));});return function(_cg){return new F(function(){return A1(_cg,_cf);});};}else{if(_bU>70){var _ch=new T(function(){return B(A1(_bQ,_y));});return function(_ci){return new F(function(){return A1(_ci,_ch);});};}else{return new F(function(){return _bV((_bU-65|0)+10|0);});}}}else{return new F(function(){return _bV((_bU-97|0)+10|0);});}}}else{if(_bU>57){if(97>_bU){if(65>_bU){var _cj=new T(function(){return B(A1(_bQ,_y));});return function(_ck){return new F(function(){return A1(_ck,_cj);});};}else{if(_bU>70){var _cl=new T(function(){return B(A1(_bQ,_y));});return function(_cm){return new F(function(){return A1(_cm,_cl);});};}else{return new F(function(){return _bV((_bU-65|0)+10|0);});}}}else{if(_bU>102){if(65>_bU){var _cn=new T(function(){return B(A1(_bQ,_y));});return function(_co){return new F(function(){return A1(_co,_cn);});};}else{if(_bU>70){var _cp=new T(function(){return B(A1(_bQ,_y));});return function(_cq){return new F(function(){return A1(_cq,_cp);});};}else{return new F(function(){return _bV((_bU-65|0)+10|0);});}}}else{return new F(function(){return _bV((_bU-97|0)+10|0);});}}}else{return new F(function(){return _bV(_bU-48|0);});}}break;default:return E(_bK);}}},_cr=function(_cs){var _ct=E(_cs);if(!_ct._){return new T0(2);}else{return new F(function(){return A1(_bN,_ct);});}};return function(_cu){return new F(function(){return A3(_bO,_cu,_2u,_cr);});};},_cv=16,_cw=8,_cx=function(_cy){var _cz=function(_cA){return new F(function(){return A1(_cy,new T1(5,new T2(0,_cw,_cA)));});},_cB=function(_cC){return new F(function(){return A1(_cy,new T1(5,new T2(0,_cv,_cC)));});},_cD=function(_cE){switch(E(_cE)){case 79:return new T1(1,B(_bL(_cw,_cz)));case 88:return new T1(1,B(_bL(_cv,_cB)));case 111:return new T1(1,B(_bL(_cw,_cz)));case 120:return new T1(1,B(_bL(_cv,_cB)));default:return new T0(2);}};return function(_cF){return (E(_cF)==48)?E(new T1(0,_cD)):new T0(2);};},_cG=function(_cH){return new T1(0,B(_cx(_cH)));},_cI=function(_cJ){return new F(function(){return A1(_cJ,_2e);});},_cK=function(_cL){return new F(function(){return A1(_cL,_2e);});},_cM=10,_cN=new T1(0,1),_cO=new T1(0,2147483647),_cP=function(_cQ,_cR){while(1){var _cS=E(_cQ);if(!_cS._){var _cT=_cS.a,_cU=E(_cR);if(!_cU._){var _cV=_cU.a,_cW=addC(_cT,_cV);if(!E(_cW.b)){return new T1(0,_cW.a);}else{_cQ=new T1(1,I_fromInt(_cT));_cR=new T1(1,I_fromInt(_cV));continue;}}else{_cQ=new T1(1,I_fromInt(_cT));_cR=_cU;continue;}}else{var _cX=E(_cR);if(!_cX._){_cQ=_cS;_cR=new T1(1,I_fromInt(_cX.a));continue;}else{return new T1(1,I_add(_cS.a,_cX.a));}}}},_cY=new T(function(){return B(_cP(_cO,_cN));}),_cZ=function(_d0){var _d1=E(_d0);if(!_d1._){var _d2=E(_d1.a);return (_d2==(-2147483648))?E(_cY):new T1(0, -_d2);}else{return new T1(1,I_negate(_d1.a));}},_d3=new T1(0,10),_d4=function(_d5,_d6){while(1){var _d7=E(_d5);if(!_d7._){return E(_d6);}else{var _d8=_d6+1|0;_d5=_d7.b;_d6=_d8;continue;}}},_d9=function(_da,_db){var _dc=E(_db);return (_dc._==0)?__Z:new T2(1,new T(function(){return B(A1(_da,_dc.a));}),new T(function(){return B(_d9(_da,_dc.b));}));},_dd=function(_de){return new T1(0,_de);},_df=function(_dg){return new F(function(){return _dd(E(_dg));});},_dh=new T(function(){return B(unCStr("this should not happen"));}),_di=new T(function(){return B(err(_dh));}),_dj=function(_dk,_dl){while(1){var _dm=E(_dk);if(!_dm._){var _dn=_dm.a,_do=E(_dl);if(!_do._){var _dp=_do.a;if(!(imul(_dn,_dp)|0)){return new T1(0,imul(_dn,_dp)|0);}else{_dk=new T1(1,I_fromInt(_dn));_dl=new T1(1,I_fromInt(_dp));continue;}}else{_dk=new T1(1,I_fromInt(_dn));_dl=_do;continue;}}else{var _dq=E(_dl);if(!_dq._){_dk=_dm;_dl=new T1(1,I_fromInt(_dq.a));continue;}else{return new T1(1,I_mul(_dm.a,_dq.a));}}}},_dr=function(_ds,_dt){var _du=E(_dt);if(!_du._){return __Z;}else{var _dv=E(_du.b);return (_dv._==0)?E(_di):new T2(1,B(_cP(B(_dj(_du.a,_ds)),_dv.a)),new T(function(){return B(_dr(_ds,_dv.b));}));}},_dw=new T1(0,0),_dx=function(_dy,_dz,_dA){while(1){var _dB=B((function(_dC,_dD,_dE){var _dF=E(_dE);if(!_dF._){return E(_dw);}else{if(!E(_dF.b)._){return E(_dF.a);}else{var _dG=E(_dD);if(_dG<=40){var _dH=function(_dI,_dJ){while(1){var _dK=E(_dJ);if(!_dK._){return E(_dI);}else{var _dL=B(_cP(B(_dj(_dI,_dC)),_dK.a));_dI=_dL;_dJ=_dK.b;continue;}}};return new F(function(){return _dH(_dw,_dF);});}else{var _dM=B(_dj(_dC,_dC));if(!(_dG%2)){var _dN=B(_dr(_dC,_dF));_dy=_dM;_dz=quot(_dG+1|0,2);_dA=_dN;return __continue;}else{var _dN=B(_dr(_dC,new T2(1,_dw,_dF)));_dy=_dM;_dz=quot(_dG+1|0,2);_dA=_dN;return __continue;}}}}})(_dy,_dz,_dA));if(_dB!=__continue){return _dB;}}},_dO=function(_dP,_dQ){return new F(function(){return _dx(_dP,new T(function(){return B(_d4(_dQ,0));},1),B(_d9(_df,_dQ)));});},_dR=function(_dS){var _dT=new T(function(){var _dU=new T(function(){var _dV=function(_dW){return new F(function(){return A1(_dS,new T1(1,new T(function(){return B(_dO(_d3,_dW));})));});};return new T1(1,B(_bL(_cM,_dV)));}),_dX=function(_dY){if(E(_dY)==43){var _dZ=function(_e0){return new F(function(){return A1(_dS,new T1(1,new T(function(){return B(_dO(_d3,_e0));})));});};return new T1(1,B(_bL(_cM,_dZ)));}else{return new T0(2);}},_e1=function(_e2){if(E(_e2)==45){var _e3=function(_e4){return new F(function(){return A1(_dS,new T1(1,new T(function(){return B(_cZ(B(_dO(_d3,_e4))));})));});};return new T1(1,B(_bL(_cM,_e3)));}else{return new T0(2);}};return B(_9L(B(_9L(new T1(0,_e1),new T1(0,_dX))),_dU));});return new F(function(){return _9L(new T1(0,function(_e5){return (E(_e5)==101)?E(_dT):new T0(2);}),new T1(0,function(_e6){return (E(_e6)==69)?E(_dT):new T0(2);}));});},_e7=function(_e8){var _e9=function(_ea){return new F(function(){return A1(_e8,new T1(1,_ea));});};return function(_eb){return (E(_eb)==46)?new T1(1,B(_bL(_cM,_e9))):new T0(2);};},_ec=function(_ed){return new T1(0,B(_e7(_ed)));},_ee=function(_ef){var _eg=function(_eh){var _ei=function(_ej){return new T1(1,B(_b4(_dR,_cI,function(_ek){return new F(function(){return A1(_ef,new T1(5,new T3(1,_eh,_ej,_ek)));});})));};return new T1(1,B(_b4(_ec,_cK,_ei)));};return new F(function(){return _bL(_cM,_eg);});},_el=function(_em){return new T1(1,B(_ee(_em)));},_en=function(_eo){return E(E(_eo).a);},_ep=function(_eq,_er,_es){while(1){var _et=E(_es);if(!_et._){return false;}else{if(!B(A3(_en,_eq,_er,_et.a))){_es=_et.b;continue;}else{return true;}}}},_eu=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_ev=function(_ew){return new F(function(){return _ep(_aA,_ew,_eu);});},_ex=false,_ey=true,_ez=function(_eA){var _eB=new T(function(){return B(A1(_eA,_cw));}),_eC=new T(function(){return B(A1(_eA,_cv));});return function(_eD){switch(E(_eD)){case 79:return E(_eB);case 88:return E(_eC);case 111:return E(_eB);case 120:return E(_eC);default:return new T0(2);}};},_eE=function(_eF){return new T1(0,B(_ez(_eF)));},_eG=function(_eH){return new F(function(){return A1(_eH,_cM);});},_eI=function(_eJ){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_5M(9,_eJ,_y));}))));});},_eK=function(_eL){var _eM=E(_eL);if(!_eM._){return E(_eM.a);}else{return new F(function(){return I_toInt(_eM.a);});}},_eN=function(_eO,_eP){var _eQ=E(_eO);if(!_eQ._){var _eR=_eQ.a,_eS=E(_eP);return (_eS._==0)?_eR<=_eS.a:I_compareInt(_eS.a,_eR)>=0;}else{var _eT=_eQ.a,_eU=E(_eP);return (_eU._==0)?I_compareInt(_eT,_eU.a)<=0:I_compare(_eT,_eU.a)<=0;}},_eV=function(_eW){return new T0(2);},_eX=function(_eY){var _eZ=E(_eY);if(!_eZ._){return E(_eV);}else{var _f0=_eZ.a,_f1=E(_eZ.b);if(!_f1._){return E(_f0);}else{var _f2=new T(function(){return B(_eX(_f1));}),_f3=function(_f4){return new F(function(){return _9L(B(A1(_f0,_f4)),new T(function(){return B(A1(_f2,_f4));}));});};return E(_f3);}}},_f5=function(_f6,_f7){var _f8=function(_f9,_fa,_fb){var _fc=E(_f9);if(!_fc._){return new F(function(){return A1(_fb,_f6);});}else{var _fd=E(_fa);if(!_fd._){return new T0(2);}else{if(E(_fc.a)!=E(_fd.a)){return new T0(2);}else{var _fe=new T(function(){return B(_f8(_fc.b,_fd.b,_fb));});return new T1(0,function(_ff){return E(_fe);});}}}};return function(_fg){return new F(function(){return _f8(_f6,_fg,_f7);});};},_fh=new T(function(){return B(unCStr("SO"));}),_fi=14,_fj=function(_fk){var _fl=new T(function(){return B(A1(_fk,_fi));});return new T1(1,B(_f5(_fh,function(_fm){return E(_fl);})));},_fn=new T(function(){return B(unCStr("SOH"));}),_fo=1,_fp=function(_fq){var _fr=new T(function(){return B(A1(_fq,_fo));});return new T1(1,B(_f5(_fn,function(_fs){return E(_fr);})));},_ft=function(_fu){return new T1(1,B(_b4(_fp,_fj,_fu)));},_fv=new T(function(){return B(unCStr("NUL"));}),_fw=0,_fx=function(_fy){var _fz=new T(function(){return B(A1(_fy,_fw));});return new T1(1,B(_f5(_fv,function(_fA){return E(_fz);})));},_fB=new T(function(){return B(unCStr("STX"));}),_fC=2,_fD=function(_fE){var _fF=new T(function(){return B(A1(_fE,_fC));});return new T1(1,B(_f5(_fB,function(_fG){return E(_fF);})));},_fH=new T(function(){return B(unCStr("ETX"));}),_fI=3,_fJ=function(_fK){var _fL=new T(function(){return B(A1(_fK,_fI));});return new T1(1,B(_f5(_fH,function(_fM){return E(_fL);})));},_fN=new T(function(){return B(unCStr("EOT"));}),_fO=4,_fP=function(_fQ){var _fR=new T(function(){return B(A1(_fQ,_fO));});return new T1(1,B(_f5(_fN,function(_fS){return E(_fR);})));},_fT=new T(function(){return B(unCStr("ENQ"));}),_fU=5,_fV=function(_fW){var _fX=new T(function(){return B(A1(_fW,_fU));});return new T1(1,B(_f5(_fT,function(_fY){return E(_fX);})));},_fZ=new T(function(){return B(unCStr("ACK"));}),_g0=6,_g1=function(_g2){var _g3=new T(function(){return B(A1(_g2,_g0));});return new T1(1,B(_f5(_fZ,function(_g4){return E(_g3);})));},_g5=new T(function(){return B(unCStr("BEL"));}),_g6=7,_g7=function(_g8){var _g9=new T(function(){return B(A1(_g8,_g6));});return new T1(1,B(_f5(_g5,function(_ga){return E(_g9);})));},_gb=new T(function(){return B(unCStr("BS"));}),_gc=8,_gd=function(_ge){var _gf=new T(function(){return B(A1(_ge,_gc));});return new T1(1,B(_f5(_gb,function(_gg){return E(_gf);})));},_gh=new T(function(){return B(unCStr("HT"));}),_gi=9,_gj=function(_gk){var _gl=new T(function(){return B(A1(_gk,_gi));});return new T1(1,B(_f5(_gh,function(_gm){return E(_gl);})));},_gn=new T(function(){return B(unCStr("LF"));}),_go=10,_gp=function(_gq){var _gr=new T(function(){return B(A1(_gq,_go));});return new T1(1,B(_f5(_gn,function(_gs){return E(_gr);})));},_gt=new T(function(){return B(unCStr("VT"));}),_gu=11,_gv=function(_gw){var _gx=new T(function(){return B(A1(_gw,_gu));});return new T1(1,B(_f5(_gt,function(_gy){return E(_gx);})));},_gz=new T(function(){return B(unCStr("FF"));}),_gA=12,_gB=function(_gC){var _gD=new T(function(){return B(A1(_gC,_gA));});return new T1(1,B(_f5(_gz,function(_gE){return E(_gD);})));},_gF=new T(function(){return B(unCStr("CR"));}),_gG=13,_gH=function(_gI){var _gJ=new T(function(){return B(A1(_gI,_gG));});return new T1(1,B(_f5(_gF,function(_gK){return E(_gJ);})));},_gL=new T(function(){return B(unCStr("SI"));}),_gM=15,_gN=function(_gO){var _gP=new T(function(){return B(A1(_gO,_gM));});return new T1(1,B(_f5(_gL,function(_gQ){return E(_gP);})));},_gR=new T(function(){return B(unCStr("DLE"));}),_gS=16,_gT=function(_gU){var _gV=new T(function(){return B(A1(_gU,_gS));});return new T1(1,B(_f5(_gR,function(_gW){return E(_gV);})));},_gX=new T(function(){return B(unCStr("DC1"));}),_gY=17,_gZ=function(_h0){var _h1=new T(function(){return B(A1(_h0,_gY));});return new T1(1,B(_f5(_gX,function(_h2){return E(_h1);})));},_h3=new T(function(){return B(unCStr("DC2"));}),_h4=18,_h5=function(_h6){var _h7=new T(function(){return B(A1(_h6,_h4));});return new T1(1,B(_f5(_h3,function(_h8){return E(_h7);})));},_h9=new T(function(){return B(unCStr("DC3"));}),_ha=19,_hb=function(_hc){var _hd=new T(function(){return B(A1(_hc,_ha));});return new T1(1,B(_f5(_h9,function(_he){return E(_hd);})));},_hf=new T(function(){return B(unCStr("DC4"));}),_hg=20,_hh=function(_hi){var _hj=new T(function(){return B(A1(_hi,_hg));});return new T1(1,B(_f5(_hf,function(_hk){return E(_hj);})));},_hl=new T(function(){return B(unCStr("NAK"));}),_hm=21,_hn=function(_ho){var _hp=new T(function(){return B(A1(_ho,_hm));});return new T1(1,B(_f5(_hl,function(_hq){return E(_hp);})));},_hr=new T(function(){return B(unCStr("SYN"));}),_hs=22,_ht=function(_hu){var _hv=new T(function(){return B(A1(_hu,_hs));});return new T1(1,B(_f5(_hr,function(_hw){return E(_hv);})));},_hx=new T(function(){return B(unCStr("ETB"));}),_hy=23,_hz=function(_hA){var _hB=new T(function(){return B(A1(_hA,_hy));});return new T1(1,B(_f5(_hx,function(_hC){return E(_hB);})));},_hD=new T(function(){return B(unCStr("CAN"));}),_hE=24,_hF=function(_hG){var _hH=new T(function(){return B(A1(_hG,_hE));});return new T1(1,B(_f5(_hD,function(_hI){return E(_hH);})));},_hJ=new T(function(){return B(unCStr("EM"));}),_hK=25,_hL=function(_hM){var _hN=new T(function(){return B(A1(_hM,_hK));});return new T1(1,B(_f5(_hJ,function(_hO){return E(_hN);})));},_hP=new T(function(){return B(unCStr("SUB"));}),_hQ=26,_hR=function(_hS){var _hT=new T(function(){return B(A1(_hS,_hQ));});return new T1(1,B(_f5(_hP,function(_hU){return E(_hT);})));},_hV=new T(function(){return B(unCStr("ESC"));}),_hW=27,_hX=function(_hY){var _hZ=new T(function(){return B(A1(_hY,_hW));});return new T1(1,B(_f5(_hV,function(_i0){return E(_hZ);})));},_i1=new T(function(){return B(unCStr("FS"));}),_i2=28,_i3=function(_i4){var _i5=new T(function(){return B(A1(_i4,_i2));});return new T1(1,B(_f5(_i1,function(_i6){return E(_i5);})));},_i7=new T(function(){return B(unCStr("GS"));}),_i8=29,_i9=function(_ia){var _ib=new T(function(){return B(A1(_ia,_i8));});return new T1(1,B(_f5(_i7,function(_ic){return E(_ib);})));},_id=new T(function(){return B(unCStr("RS"));}),_ie=30,_if=function(_ig){var _ih=new T(function(){return B(A1(_ig,_ie));});return new T1(1,B(_f5(_id,function(_ii){return E(_ih);})));},_ij=new T(function(){return B(unCStr("US"));}),_ik=31,_il=function(_im){var _in=new T(function(){return B(A1(_im,_ik));});return new T1(1,B(_f5(_ij,function(_io){return E(_in);})));},_ip=new T(function(){return B(unCStr("SP"));}),_iq=32,_ir=function(_is){var _it=new T(function(){return B(A1(_is,_iq));});return new T1(1,B(_f5(_ip,function(_iu){return E(_it);})));},_iv=new T(function(){return B(unCStr("DEL"));}),_iw=127,_ix=function(_iy){var _iz=new T(function(){return B(A1(_iy,_iw));});return new T1(1,B(_f5(_iv,function(_iA){return E(_iz);})));},_iB=new T2(1,_ix,_y),_iC=new T2(1,_ir,_iB),_iD=new T2(1,_il,_iC),_iE=new T2(1,_if,_iD),_iF=new T2(1,_i9,_iE),_iG=new T2(1,_i3,_iF),_iH=new T2(1,_hX,_iG),_iI=new T2(1,_hR,_iH),_iJ=new T2(1,_hL,_iI),_iK=new T2(1,_hF,_iJ),_iL=new T2(1,_hz,_iK),_iM=new T2(1,_ht,_iL),_iN=new T2(1,_hn,_iM),_iO=new T2(1,_hh,_iN),_iP=new T2(1,_hb,_iO),_iQ=new T2(1,_h5,_iP),_iR=new T2(1,_gZ,_iQ),_iS=new T2(1,_gT,_iR),_iT=new T2(1,_gN,_iS),_iU=new T2(1,_gH,_iT),_iV=new T2(1,_gB,_iU),_iW=new T2(1,_gv,_iV),_iX=new T2(1,_gp,_iW),_iY=new T2(1,_gj,_iX),_iZ=new T2(1,_gd,_iY),_j0=new T2(1,_g7,_iZ),_j1=new T2(1,_g1,_j0),_j2=new T2(1,_fV,_j1),_j3=new T2(1,_fP,_j2),_j4=new T2(1,_fJ,_j3),_j5=new T2(1,_fD,_j4),_j6=new T2(1,_fx,_j5),_j7=new T2(1,_ft,_j6),_j8=new T(function(){return B(_eX(_j7));}),_j9=34,_ja=new T1(0,1114111),_jb=92,_jc=39,_jd=function(_je){var _jf=new T(function(){return B(A1(_je,_g6));}),_jg=new T(function(){return B(A1(_je,_gc));}),_jh=new T(function(){return B(A1(_je,_gi));}),_ji=new T(function(){return B(A1(_je,_go));}),_jj=new T(function(){return B(A1(_je,_gu));}),_jk=new T(function(){return B(A1(_je,_gA));}),_jl=new T(function(){return B(A1(_je,_gG));}),_jm=new T(function(){return B(A1(_je,_jb));}),_jn=new T(function(){return B(A1(_je,_jc));}),_jo=new T(function(){return B(A1(_je,_j9));}),_jp=new T(function(){var _jq=function(_jr){var _js=new T(function(){return B(_dd(E(_jr)));}),_jt=function(_ju){var _jv=B(_dO(_js,_ju));if(!B(_eN(_jv,_ja))){return new T0(2);}else{return new F(function(){return A1(_je,new T(function(){var _jw=B(_eK(_jv));if(_jw>>>0>1114111){return B(_eI(_jw));}else{return _jw;}}));});}};return new T1(1,B(_bL(_jr,_jt)));},_jx=new T(function(){var _jy=new T(function(){return B(A1(_je,_ik));}),_jz=new T(function(){return B(A1(_je,_ie));}),_jA=new T(function(){return B(A1(_je,_i8));}),_jB=new T(function(){return B(A1(_je,_i2));}),_jC=new T(function(){return B(A1(_je,_hW));}),_jD=new T(function(){return B(A1(_je,_hQ));}),_jE=new T(function(){return B(A1(_je,_hK));}),_jF=new T(function(){return B(A1(_je,_hE));}),_jG=new T(function(){return B(A1(_je,_hy));}),_jH=new T(function(){return B(A1(_je,_hs));}),_jI=new T(function(){return B(A1(_je,_hm));}),_jJ=new T(function(){return B(A1(_je,_hg));}),_jK=new T(function(){return B(A1(_je,_ha));}),_jL=new T(function(){return B(A1(_je,_h4));}),_jM=new T(function(){return B(A1(_je,_gY));}),_jN=new T(function(){return B(A1(_je,_gS));}),_jO=new T(function(){return B(A1(_je,_gM));}),_jP=new T(function(){return B(A1(_je,_fi));}),_jQ=new T(function(){return B(A1(_je,_g0));}),_jR=new T(function(){return B(A1(_je,_fU));}),_jS=new T(function(){return B(A1(_je,_fO));}),_jT=new T(function(){return B(A1(_je,_fI));}),_jU=new T(function(){return B(A1(_je,_fC));}),_jV=new T(function(){return B(A1(_je,_fo));}),_jW=new T(function(){return B(A1(_je,_fw));}),_jX=function(_jY){switch(E(_jY)){case 64:return E(_jW);case 65:return E(_jV);case 66:return E(_jU);case 67:return E(_jT);case 68:return E(_jS);case 69:return E(_jR);case 70:return E(_jQ);case 71:return E(_jf);case 72:return E(_jg);case 73:return E(_jh);case 74:return E(_ji);case 75:return E(_jj);case 76:return E(_jk);case 77:return E(_jl);case 78:return E(_jP);case 79:return E(_jO);case 80:return E(_jN);case 81:return E(_jM);case 82:return E(_jL);case 83:return E(_jK);case 84:return E(_jJ);case 85:return E(_jI);case 86:return E(_jH);case 87:return E(_jG);case 88:return E(_jF);case 89:return E(_jE);case 90:return E(_jD);case 91:return E(_jC);case 92:return E(_jB);case 93:return E(_jA);case 94:return E(_jz);case 95:return E(_jy);default:return new T0(2);}};return B(_9L(new T1(0,function(_jZ){return (E(_jZ)==94)?E(new T1(0,_jX)):new T0(2);}),new T(function(){return B(A1(_j8,_je));})));});return B(_9L(new T1(1,B(_b4(_eE,_eG,_jq))),_jx));});return new F(function(){return _9L(new T1(0,function(_k0){switch(E(_k0)){case 34:return E(_jo);case 39:return E(_jn);case 92:return E(_jm);case 97:return E(_jf);case 98:return E(_jg);case 102:return E(_jk);case 110:return E(_ji);case 114:return E(_jl);case 116:return E(_jh);case 118:return E(_jj);default:return new T0(2);}}),_jp);});},_k1=function(_k2){return new F(function(){return A1(_k2,_0);});},_k3=function(_k4){var _k5=E(_k4);if(!_k5._){return E(_k1);}else{var _k6=E(_k5.a),_k7=_k6>>>0,_k8=new T(function(){return B(_k3(_k5.b));});if(_k7>887){var _k9=u_iswspace(_k6);if(!E(_k9)){return E(_k1);}else{var _ka=function(_kb){var _kc=new T(function(){return B(A1(_k8,_kb));});return new T1(0,function(_kd){return E(_kc);});};return E(_ka);}}else{var _ke=E(_k7);if(_ke==32){var _kf=function(_kg){var _kh=new T(function(){return B(A1(_k8,_kg));});return new T1(0,function(_ki){return E(_kh);});};return E(_kf);}else{if(_ke-9>>>0>4){if(E(_ke)==160){var _kj=function(_kk){var _kl=new T(function(){return B(A1(_k8,_kk));});return new T1(0,function(_km){return E(_kl);});};return E(_kj);}else{return E(_k1);}}else{var _kn=function(_ko){var _kp=new T(function(){return B(A1(_k8,_ko));});return new T1(0,function(_kq){return E(_kp);});};return E(_kn);}}}}},_kr=function(_ks){var _kt=new T(function(){return B(_kr(_ks));}),_ku=function(_kv){return (E(_kv)==92)?E(_kt):new T0(2);},_kw=function(_kx){return E(new T1(0,_ku));},_ky=new T1(1,function(_kz){return new F(function(){return A2(_k3,_kz,_kw);});}),_kA=new T(function(){return B(_jd(function(_kB){return new F(function(){return A1(_ks,new T2(0,_kB,_ey));});}));}),_kC=function(_kD){var _kE=E(_kD);if(_kE==38){return E(_kt);}else{var _kF=_kE>>>0;if(_kF>887){var _kG=u_iswspace(_kE);return (E(_kG)==0)?new T0(2):E(_ky);}else{var _kH=E(_kF);return (_kH==32)?E(_ky):(_kH-9>>>0>4)?(E(_kH)==160)?E(_ky):new T0(2):E(_ky);}}};return new F(function(){return _9L(new T1(0,function(_kI){return (E(_kI)==92)?E(new T1(0,_kC)):new T0(2);}),new T1(0,function(_kJ){var _kK=E(_kJ);if(E(_kK)==92){return E(_kA);}else{return new F(function(){return A1(_ks,new T2(0,_kK,_ex));});}}));});},_kL=function(_kM,_kN){var _kO=new T(function(){return B(A1(_kN,new T1(1,new T(function(){return B(A1(_kM,_y));}))));}),_kP=function(_kQ){var _kR=E(_kQ),_kS=E(_kR.a);if(E(_kS)==34){if(!E(_kR.b)){return E(_kO);}else{return new F(function(){return _kL(function(_kT){return new F(function(){return A1(_kM,new T2(1,_kS,_kT));});},_kN);});}}else{return new F(function(){return _kL(function(_kU){return new F(function(){return A1(_kM,new T2(1,_kS,_kU));});},_kN);});}};return new F(function(){return _kr(_kP);});},_kV=new T(function(){return B(unCStr("_\'"));}),_kW=function(_kX){var _kY=u_iswalnum(_kX);if(!E(_kY)){return new F(function(){return _ep(_aA,_kX,_kV);});}else{return true;}},_kZ=function(_l0){return new F(function(){return _kW(E(_l0));});},_l1=new T(function(){return B(unCStr(",;()[]{}`"));}),_l2=new T(function(){return B(unCStr("=>"));}),_l3=new T2(1,_l2,_y),_l4=new T(function(){return B(unCStr("~"));}),_l5=new T2(1,_l4,_l3),_l6=new T(function(){return B(unCStr("@"));}),_l7=new T2(1,_l6,_l5),_l8=new T(function(){return B(unCStr("->"));}),_l9=new T2(1,_l8,_l7),_la=new T(function(){return B(unCStr("<-"));}),_lb=new T2(1,_la,_l9),_lc=new T(function(){return B(unCStr("|"));}),_ld=new T2(1,_lc,_lb),_le=new T(function(){return B(unCStr("\\"));}),_lf=new T2(1,_le,_ld),_lg=new T(function(){return B(unCStr("="));}),_lh=new T2(1,_lg,_lf),_li=new T(function(){return B(unCStr("::"));}),_lj=new T2(1,_li,_lh),_lk=new T(function(){return B(unCStr(".."));}),_ll=new T2(1,_lk,_lj),_lm=function(_ln){var _lo=new T(function(){return B(A1(_ln,_bI));}),_lp=new T(function(){var _lq=new T(function(){var _lr=function(_ls){var _lt=new T(function(){return B(A1(_ln,new T1(0,_ls)));});return new T1(0,function(_lu){return (E(_lu)==39)?E(_lt):new T0(2);});};return B(_jd(_lr));}),_lv=function(_lw){var _lx=E(_lw);switch(E(_lx)){case 39:return new T0(2);case 92:return E(_lq);default:var _ly=new T(function(){return B(A1(_ln,new T1(0,_lx)));});return new T1(0,function(_lz){return (E(_lz)==39)?E(_ly):new T0(2);});}},_lA=new T(function(){var _lB=new T(function(){return B(_kL(_2u,_ln));}),_lC=new T(function(){var _lD=new T(function(){var _lE=new T(function(){var _lF=function(_lG){var _lH=E(_lG),_lI=u_iswalpha(_lH);return (E(_lI)==0)?(E(_lH)==95)?new T1(1,B(_bu(_kZ,function(_lJ){return new F(function(){return A1(_ln,new T1(3,new T2(1,_lH,_lJ)));});}))):new T0(2):new T1(1,B(_bu(_kZ,function(_lK){return new F(function(){return A1(_ln,new T1(3,new T2(1,_lH,_lK)));});})));};return B(_9L(new T1(0,_lF),new T(function(){return new T1(1,B(_b4(_cG,_el,_ln)));})));}),_lL=function(_lM){return (!B(_ep(_aA,_lM,_eu)))?new T0(2):new T1(1,B(_bu(_ev,function(_lN){var _lO=new T2(1,_lM,_lN);if(!B(_ep(_aJ,_lO,_ll))){return new F(function(){return A1(_ln,new T1(4,_lO));});}else{return new F(function(){return A1(_ln,new T1(2,_lO));});}})));};return B(_9L(new T1(0,_lL),_lE));});return B(_9L(new T1(0,function(_lP){if(!B(_ep(_aA,_lP,_l1))){return new T0(2);}else{return new F(function(){return A1(_ln,new T1(2,new T2(1,_lP,_y)));});}}),_lD));});return B(_9L(new T1(0,function(_lQ){return (E(_lQ)==34)?E(_lB):new T0(2);}),_lC));});return B(_9L(new T1(0,function(_lR){return (E(_lR)==39)?E(new T1(0,_lv)):new T0(2);}),_lA));});return new F(function(){return _9L(new T1(1,function(_lS){return (E(_lS)._==0)?E(_lo):new T0(2);}),_lp);});},_lT=0,_lU=function(_lV,_lW){var _lX=new T(function(){var _lY=new T(function(){var _lZ=function(_m0){var _m1=new T(function(){var _m2=new T(function(){return B(A1(_lW,_m0));});return B(_lm(function(_m3){var _m4=E(_m3);return (_m4._==2)?(!B(_ap(_m4.a,_ao)))?new T0(2):E(_m2):new T0(2);}));}),_m5=function(_m6){return E(_m1);};return new T1(1,function(_m7){return new F(function(){return A2(_k3,_m7,_m5);});});};return B(A2(_lV,_lT,_lZ));});return B(_lm(function(_m8){var _m9=E(_m8);return (_m9._==2)?(!B(_ap(_m9.a,_an)))?new T0(2):E(_lY):new T0(2);}));}),_ma=function(_mb){return E(_lX);};return function(_mc){return new F(function(){return A2(_k3,_mc,_ma);});};},_md=function(_me,_mf){var _mg=function(_mh){var _mi=new T(function(){return B(A1(_me,_mh));}),_mj=function(_mk){return new F(function(){return _9L(B(A1(_mi,_mk)),new T(function(){return new T1(1,B(_lU(_mg,_mk)));}));});};return E(_mj);},_ml=new T(function(){return B(A1(_me,_mf));}),_mm=function(_mn){return new F(function(){return _9L(B(A1(_ml,_mn)),new T(function(){return new T1(1,B(_lU(_mg,_mn)));}));});};return E(_mm);},_mo=function(_mp,_mq){var _mr=function(_ms,_mt){var _mu=function(_mv){return new F(function(){return A1(_mt,new T(function(){return  -E(_mv);}));});},_mw=new T(function(){return B(_lm(function(_mx){return new F(function(){return A3(_mp,_mx,_ms,_mu);});}));}),_my=function(_mz){return E(_mw);},_mA=function(_mB){return new F(function(){return A2(_k3,_mB,_my);});},_mC=new T(function(){return B(_lm(function(_mD){var _mE=E(_mD);if(_mE._==4){var _mF=E(_mE.a);if(!_mF._){return new F(function(){return A3(_mp,_mE,_ms,_mt);});}else{if(E(_mF.a)==45){if(!E(_mF.b)._){return E(new T1(1,_mA));}else{return new F(function(){return A3(_mp,_mE,_ms,_mt);});}}else{return new F(function(){return A3(_mp,_mE,_ms,_mt);});}}}else{return new F(function(){return A3(_mp,_mE,_ms,_mt);});}}));}),_mG=function(_mH){return E(_mC);};return new T1(1,function(_mI){return new F(function(){return A2(_k3,_mI,_mG);});});};return new F(function(){return _md(_mr,_mq);});},_mJ=function(_mK){var _mL=E(_mK);if(!_mL._){var _mM=_mL.b,_mN=new T(function(){return B(_dx(new T(function(){return B(_dd(E(_mL.a)));}),new T(function(){return B(_d4(_mM,0));},1),B(_d9(_df,_mM))));});return new T1(1,_mN);}else{return (E(_mL.b)._==0)?(E(_mL.c)._==0)?new T1(1,new T(function(){return B(_dO(_d3,_mL.a));})):__Z:__Z;}},_mO=function(_mP,_mQ){return new T0(2);},_mR=function(_mS){var _mT=E(_mS);if(_mT._==5){var _mU=B(_mJ(_mT.a));if(!_mU._){return E(_mO);}else{var _mV=new T(function(){return B(_eK(_mU.a));});return function(_mW,_mX){return new F(function(){return A1(_mX,_mV);});};}}else{return E(_mO);}},_mY=function(_mZ){var _n0=function(_n1){return E(new T2(3,_mZ,_aV));};return new T1(1,function(_n2){return new F(function(){return A2(_k3,_n2,_n0);});});},_n3=new T(function(){return B(A3(_mo,_mR,_lT,_mY));}),_n4=new T(function(){return B(unCStr("invalid key pressed"));}),_n5=function(_n6){var _n7=new T(function(){var _n8=E(_n6);return new T4(0,_n8.a,_n8.b,new T(function(){return E(_n8.c)+5;}),_n8.d);});return new T2(0,_n7,_0);},_n9=function(_na){var _nb=new T(function(){var _nc=E(_na);return new T4(0,_nc.a,_nc.b,new T(function(){return E(_nc.c)-5;}),_nc.d);});return new T2(0,_nb,_0);},_nd=function(_ne){return E(E(_ne).b);},_nf=function(_ng){return E(E(_ng).a);},_nh=function(_){return new F(function(){return nMV(_2e);});},_ni=new T(function(){return B(_4X(_nh));}),_nj=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_nk=function(_nl,_nm,_nn,_no,_np,_nq){var _nr=B(_4O(_nl)),_ns=B(_4Q(_nr)),_nt=new T(function(){return B(_2V(_nr));}),_nu=new T(function(){return B(_65(_ns));}),_nv=new T(function(){return B(A2(_5U,_nm,_no));}),_nw=new T(function(){return B(A2(_nf,_nn,_np));}),_nx=function(_ny){return new F(function(){return A1(_nu,new T3(0,_nw,_nv,_ny));});},_nz=function(_nA){var _nB=new T(function(){var _nC=new T(function(){var _nD=__createJSFunc(2,function(_nE,_){var _nF=B(A2(E(_nA),_nE,_));return _51;}),_nG=_nD;return function(_){return new F(function(){return __app3(E(_nj),E(_nv),E(_nw),_nG);});};});return B(A1(_nt,_nC));});return new F(function(){return A3(_4S,_ns,_nB,_nx);});},_nH=new T(function(){var _nI=new T(function(){return B(_2V(_nr));}),_nJ=function(_nK){var _nL=new T(function(){return B(A1(_nI,function(_){var _=wMV(E(_ni),new T1(1,_nK));return new F(function(){return A(_nd,[_nn,_np,_nK,_]);});}));});return new F(function(){return A3(_4S,_ns,_nL,_nq);});};return B(A2(_52,_nl,_nJ));});return new F(function(){return A3(_4S,_ns,_nH,_nz);});},_nM=function(_nN){while(1){var _nO=B((function(_nP){var _nQ=E(_nP);if(!_nQ._){return __Z;}else{var _nR=_nQ.b,_nS=E(_nQ.a);if(!E(_nS.b)._){return new T2(1,_nS.a,new T(function(){return B(_nM(_nR));}));}else{_nN=_nR;return __continue;}}})(_nN));if(_nO!=__continue){return _nO;}}},_nT=function(_){return new F(function(){return jsMkStdout();});},_nU=new T(function(){return B(_4X(_nT));}),_nV=new T(function(){return eval("(function(x){console.log(x);})");}),_nW=function(_nX,_nY){var _nZ=function(_){var _o0=__app1(E(_nV),toJSStr(_nY));return new F(function(){return _1(_);});};return new F(function(){return A2(_2V,_nX,_nZ);});},_o1=function(_,_o2){var _o3=E(_o2);if(!_o3._){return new F(function(){return die(_6B);});}else{var _o4=_o3.a,_o5=B(_6m(_nU,_8C,_)),_o6=B(A(_67,[_3y,_2w,_o4,_6F,_])),_o7=B(_6m(_nU,_8z,_)),_o8=B(A(_67,[_3y,_2w,_o4,_6F,_])),_o9=B(_6m(_nU,new T2(1,_6D,new T(function(){return B(_8s(B(unAppCStr("width=",_o8)),_6E));})),_)),_oa=new T(function(){var _ob=B(_nM(B(_9B(_n3,_o8))));if(!_ob._){return E(_8B);}else{if(!E(_ob.b)._){return E(_ob.a);}else{return E(_8E);}}}),_oc=new T(function(){return B(_8s(B(unAppCStr("canvasWidth=",new T(function(){return B(_5M(0,E(_oa),_y));}))),_6E));}),_od=B(_6m(_nU,new T2(1,_6D,_oc),_)),_oe=new T(function(){return B(_8s(B(unAppCStr("doItInt canvasWidth=",new T(function(){return B(_5M(0,E(_oa),_y));}))),_6E));}),_of=B(_6m(_nU,new T2(1,_6D,_oe),_)),_og=B(A(_67,[_3y,_2w,_o4,_6C,_])),_oh=E(_o4),_oi=_oh.a,_oj=_oh.b,_ok=B(_4D(_oi,_oj,_6y,_)),_ol=nMV(_6y),_om=_ol,_on=function(_oo,_){var _op=E(_oo),_oq=_op.a,_or=_op.b,_os=_op.c,_ot=_op.d,_ou=_op.e,_ov=function(_ow){var _ox=function(_oy){if(E(_oq)==83){if(!E(_or)){if(!E(_os)){if(!E(_ot)){if(!E(_ou)){return new F(function(){return mMV(_om,_n5);});}else{return new F(function(){return A3(_nW,_2w,_n4,_);});}}else{return new F(function(){return A3(_nW,_2w,_n4,_);});}}else{return new F(function(){return A3(_nW,_2w,_n4,_);});}}else{return new F(function(){return A3(_nW,_2w,_n4,_);});}}else{return new F(function(){return A3(_nW,_2w,_n4,_);});}};if(E(_oq)==68){if(!E(_or)){if(!E(_os)){if(!E(_ot)){if(!E(_ou)){return new F(function(){return mMV(_om,_n5);});}else{return new F(function(){return _ox(_);});}}else{return new F(function(){return _ox(_);});}}else{return new F(function(){return _ox(_);});}}else{return new F(function(){return _ox(_);});}}else{return new F(function(){return _ox(_);});}};if(E(_oq)==65){if(!E(_or)){if(!E(_os)){if(!E(_ot)){if(!E(_ou)){return new F(function(){return mMV(_om,_n9);});}else{return new F(function(){return _ov(_);});}}else{return new F(function(){return _ov(_);});}}else{return new F(function(){return _ov(_);});}}else{return new F(function(){return _ov(_);});}}else{return new F(function(){return _ov(_);});}},_oz=B(A(_nk,[_3z,_3y,_3p,_oh,_5R,_on,_])),_oA=B(_5s(_oi,_oj,_om,_));return _51;}},_oB=new T(function(){return B(unCStr("#canvas"));}),_oC=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_oD=function(_){var _oE=__createJSFunc(0,function(_){var _oF=B(A(_2X,[_2w,_2M,_oB,_])),_oG=B(_2J(_oF,0)),_oH=__app1(E(_3),_oG);if(!_oH){return new F(function(){return _o1(_,_2e);});}else{var _oI=__app1(E(_2),_oG);return new F(function(){return _o1(_,new T1(1,new T2(0,_oI,_oG)));});}}),_oJ=__app2(E(_oC),"breakoutHsMain",_oE);return new F(function(){return _1(_);});},_oK=function(_){return new F(function(){return _oD(_);});};
var hasteMain = function() {B(A(_oK, [0]));};hasteMain(); breakoutMain()