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

var _0=0,_1=function(_){return _0;},_2=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_3=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_4=function(_5,_6,_){var _7=B(A1(_5,_)),_8=B(A1(_6,_));return _7;},_9=function(_a,_b,_){var _c=B(A1(_a,_)),_d=B(A1(_b,_));return new T(function(){return B(A1(_c,_d));});},_e=function(_f,_g,_){var _h=B(A1(_g,_));return _f;},_i=function(_j,_k,_){var _l=B(A1(_k,_));return new T(function(){return B(A1(_j,_l));});},_m=new T2(0,_i,_e),_n=function(_o,_){return _o;},_p=function(_q,_r,_){var _s=B(A1(_q,_));return new F(function(){return A1(_r,_);});},_t=new T5(0,_m,_n,_9,_p,_4),_u=new T(function(){return B(unCStr("base"));}),_v=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_w=new T(function(){return B(unCStr("IOException"));}),_x=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_u,_v,_w),_y=__Z,_z=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_x,_y,_y),_A=function(_B){return E(_z);},_C=function(_D){return E(E(_D).a);},_E=function(_F,_G,_H){var _I=B(A1(_F,_)),_J=B(A1(_G,_)),_K=hs_eqWord64(_I.a,_J.a);if(!_K){return __Z;}else{var _L=hs_eqWord64(_I.b,_J.b);return (!_L)?__Z:new T1(1,_H);}},_M=function(_N){var _O=E(_N);return new F(function(){return _E(B(_C(_O.a)),_A,_O.b);});},_P=new T(function(){return B(unCStr(": "));}),_Q=new T(function(){return B(unCStr(")"));}),_R=new T(function(){return B(unCStr(" ("));}),_S=function(_T,_U){var _V=E(_T);return (_V._==0)?E(_U):new T2(1,_V.a,new T(function(){return B(_S(_V.b,_U));}));},_W=new T(function(){return B(unCStr("interrupted"));}),_X=new T(function(){return B(unCStr("system error"));}),_Y=new T(function(){return B(unCStr("unsatisified constraints"));}),_Z=new T(function(){return B(unCStr("user error"));}),_10=new T(function(){return B(unCStr("permission denied"));}),_11=new T(function(){return B(unCStr("illegal operation"));}),_12=new T(function(){return B(unCStr("end of file"));}),_13=new T(function(){return B(unCStr("resource exhausted"));}),_14=new T(function(){return B(unCStr("resource busy"));}),_15=new T(function(){return B(unCStr("does not exist"));}),_16=new T(function(){return B(unCStr("already exists"));}),_17=new T(function(){return B(unCStr("resource vanished"));}),_18=new T(function(){return B(unCStr("timeout"));}),_19=new T(function(){return B(unCStr("unsupported operation"));}),_1a=new T(function(){return B(unCStr("hardware fault"));}),_1b=new T(function(){return B(unCStr("inappropriate type"));}),_1c=new T(function(){return B(unCStr("invalid argument"));}),_1d=new T(function(){return B(unCStr("failed"));}),_1e=new T(function(){return B(unCStr("protocol error"));}),_1f=function(_1g,_1h){switch(E(_1g)){case 0:return new F(function(){return _S(_16,_1h);});break;case 1:return new F(function(){return _S(_15,_1h);});break;case 2:return new F(function(){return _S(_14,_1h);});break;case 3:return new F(function(){return _S(_13,_1h);});break;case 4:return new F(function(){return _S(_12,_1h);});break;case 5:return new F(function(){return _S(_11,_1h);});break;case 6:return new F(function(){return _S(_10,_1h);});break;case 7:return new F(function(){return _S(_Z,_1h);});break;case 8:return new F(function(){return _S(_Y,_1h);});break;case 9:return new F(function(){return _S(_X,_1h);});break;case 10:return new F(function(){return _S(_1e,_1h);});break;case 11:return new F(function(){return _S(_1d,_1h);});break;case 12:return new F(function(){return _S(_1c,_1h);});break;case 13:return new F(function(){return _S(_1b,_1h);});break;case 14:return new F(function(){return _S(_1a,_1h);});break;case 15:return new F(function(){return _S(_19,_1h);});break;case 16:return new F(function(){return _S(_18,_1h);});break;case 17:return new F(function(){return _S(_17,_1h);});break;default:return new F(function(){return _S(_W,_1h);});}},_1i=new T(function(){return B(unCStr("}"));}),_1j=new T(function(){return B(unCStr("{handle: "));}),_1k=function(_1l,_1m,_1n,_1o,_1p,_1q){var _1r=new T(function(){var _1s=new T(function(){var _1t=new T(function(){var _1u=E(_1o);if(!_1u._){return E(_1q);}else{var _1v=new T(function(){return B(_S(_1u,new T(function(){return B(_S(_Q,_1q));},1)));},1);return B(_S(_R,_1v));}},1);return B(_1f(_1m,_1t));}),_1w=E(_1n);if(!_1w._){return E(_1s);}else{return B(_S(_1w,new T(function(){return B(_S(_P,_1s));},1)));}}),_1x=E(_1p);if(!_1x._){var _1y=E(_1l);if(!_1y._){return E(_1r);}else{var _1z=E(_1y.a);if(!_1z._){var _1A=new T(function(){var _1B=new T(function(){return B(_S(_1i,new T(function(){return B(_S(_P,_1r));},1)));},1);return B(_S(_1z.a,_1B));},1);return new F(function(){return _S(_1j,_1A);});}else{var _1C=new T(function(){var _1D=new T(function(){return B(_S(_1i,new T(function(){return B(_S(_P,_1r));},1)));},1);return B(_S(_1z.a,_1D));},1);return new F(function(){return _S(_1j,_1C);});}}}else{return new F(function(){return _S(_1x.a,new T(function(){return B(_S(_P,_1r));},1));});}},_1E=function(_1F){var _1G=E(_1F);return new F(function(){return _1k(_1G.a,_1G.b,_1G.c,_1G.d,_1G.f,_y);});},_1H=function(_1I){return new T2(0,_1J,_1I);},_1K=function(_1L,_1M,_1N){var _1O=E(_1M);return new F(function(){return _1k(_1O.a,_1O.b,_1O.c,_1O.d,_1O.f,_1N);});},_1P=function(_1Q,_1R){var _1S=E(_1Q);return new F(function(){return _1k(_1S.a,_1S.b,_1S.c,_1S.d,_1S.f,_1R);});},_1T=44,_1U=93,_1V=91,_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);if(!_20._){return new F(function(){return unAppCStr("[]",_1Z);});}else{var _21=new T(function(){var _22=new T(function(){var _23=function(_24){var _25=E(_24);if(!_25._){return E(new T2(1,_1U,_1Z));}else{var _26=new T(function(){return B(A2(_1X,_25.a,new T(function(){return B(_23(_25.b));})));});return new T2(1,_1T,_26);}};return B(_23(_20.b));});return B(A2(_1X,_20.a,_22));});return new T2(1,_1V,_21);}},_27=function(_28,_29){return new F(function(){return _1W(_1P,_28,_29);});},_2a=new T3(0,_1K,_1E,_27),_1J=new T(function(){return new T5(0,_A,_2a,_1H,_M,_1E);}),_2b=new T(function(){return E(_1J);}),_2c=function(_2d){return E(E(_2d).c);},_2e=__Z,_2f=7,_2g=function(_2h){return new T6(0,_2e,_2f,_y,_2h,_2e,_2e);},_2i=function(_2j,_){var _2k=new T(function(){return B(A2(_2c,_2b,new T(function(){return B(A1(_2g,_2j));})));});return new F(function(){return die(_2k);});},_2l=function(_2m,_){return new F(function(){return _2i(_2m,_);});},_2n=function(_2o){return new F(function(){return A1(_2l,_2o);});},_2p=function(_2q,_2r,_){var _2s=B(A1(_2q,_));return new F(function(){return A2(_2r,_2s,_);});},_2t=new T5(0,_t,_2p,_p,_n,_2n),_2u=function(_2v){return E(_2v);},_2w=new T2(0,_2t,_2u),_2x=new T(function(){return B(unCStr("!!: negative index"));}),_2y=new T(function(){return B(unCStr("Prelude."));}),_2z=new T(function(){return B(_S(_2y,_2x));}),_2A=new T(function(){return B(err(_2z));}),_2B=new T(function(){return B(unCStr("!!: index too large"));}),_2C=new T(function(){return B(_S(_2y,_2B));}),_2D=new T(function(){return B(err(_2C));}),_2E=function(_2F,_2G){while(1){var _2H=E(_2F);if(!_2H._){return E(_2D);}else{var _2I=E(_2G);if(!_2I){return E(_2H.a);}else{_2F=_2H.b;_2G=_2I-1|0;continue;}}}},_2J=function(_2K,_2L){if(_2L>=0){return new F(function(){return _2E(_2K,_2L);});}else{return E(_2A);}},_2M=new T(function(){return eval("document");}),_2N=function(_2O,_){var _2P=E(_2O);if(!_2P._){return _y;}else{var _2Q=B(_2N(_2P.b,_));return new T2(1,_2P.a,_2Q);}},_2R=function(_2S,_){var _2T=__arr2lst(0,_2S);return new F(function(){return _2N(_2T,_);});},_2U=new T(function(){return eval("(function(e,q){if(!e || typeof e.querySelectorAll !== \'function\') {return [];} else {return e.querySelectorAll(q);}})");}),_2V=function(_2W){return E(E(_2W).b);},_2X=function(_2Y,_2Z,_30){var _31=function(_){var _32=__app2(E(_2U),E(_2Z),toJSStr(E(_30)));return new F(function(){return _2R(_32,_);});};return new F(function(){return A2(_2V,_2Y,_31);});},_33="metaKey",_34="shiftKey",_35="altKey",_36="ctrlKey",_37="keyCode",_38=function(_39,_){var _3a=__get(_39,E(_37)),_3b=__get(_39,E(_36)),_3c=__get(_39,E(_35)),_3d=__get(_39,E(_34)),_3e=__get(_39,E(_33));return new T(function(){var _3f=Number(_3a),_3g=jsTrunc(_3f);return new T5(0,_3g,E(_3b),E(_3c),E(_3d),E(_3e));});},_3h=function(_3i,_3j,_){return new F(function(){return _38(E(_3j),_);});},_3k="keydown",_3l="keyup",_3m="keypress",_3n=function(_3o){switch(E(_3o)){case 0:return E(_3m);case 1:return E(_3l);default:return E(_3k);}},_3p=new T2(0,_3n,_3h),_3q=function(_3r,_){var _3s=__app1(E(_3),_3r);if(!_3s){return _2e;}else{var _3t=__app1(E(_2),_3r);return new T1(1,new T2(0,_3t,_3r));}},_3u=function(_3v,_){return new F(function(){return _3q(E(_3v),_);});},_3w=function(_3x){return E(_3x).b;},_3y=new T2(0,_3w,_3u),_3z=new T2(0,_2w,_n),_3A=new T(function(){return B(unCStr("Nothing"));}),_3B=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_3C=0,_3D=6.283185307179586,_3E=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_3F=function(_3G,_3H,_3I,_3J,_){var _3K=__app3(E(_3E),_3J,_3G+_3I,_3H),_3L=__apply(E(_3B),new T2(1,_3D,new T2(1,_3C,new T2(1,_3I,new T2(1,_3H,new T2(1,_3G,new T2(1,_3J,_y)))))));return new F(function(){return _1(_);});},_3M=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_3N=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_3O=function(_3P,_3Q,_){var _3R=__app1(E(_3M),_3Q),_3S=B(A2(_3P,_3Q,_)),_3T=__app1(E(_3N),_3Q);return new F(function(){return _1(_);});},_3U=new T3(0,255,255,255),_3V=480,_3W=460,_3X=new T(function(){return eval("(function(e){e.width = e.width;})");}),_3Y=",",_3Z="rgba(",_40=new T(function(){return toJSStr(_y);}),_41="rgb(",_42=")",_43=new T2(1,_42,_y),_44=function(_45){var _46=E(_45);if(!_46._){var _47=jsCat(new T2(1,_41,new T2(1,new T(function(){return String(_46.a);}),new T2(1,_3Y,new T2(1,new T(function(){return String(_46.b);}),new T2(1,_3Y,new T2(1,new T(function(){return String(_46.c);}),_43)))))),E(_40));return E(_47);}else{var _48=jsCat(new T2(1,_3Z,new T2(1,new T(function(){return String(_46.a);}),new T2(1,_3Y,new T2(1,new T(function(){return String(_46.b);}),new T2(1,_3Y,new T2(1,new T(function(){return String(_46.c);}),new T2(1,_3Y,new T2(1,new T(function(){return String(_46.d);}),_43)))))))),E(_40));return E(_48);}},_49="strokeStyle",_4a="fillStyle",_4b=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_4c=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_4d=function(_4e,_4f){var _4g=new T(function(){return B(_44(_4e));});return function(_4h,_){var _4i=E(_4h),_4j=E(_4a),_4k=E(_4b),_4l=__app2(_4k,_4i,_4j),_4m=E(_49),_4n=__app2(_4k,_4i,_4m),_4o=E(_4g),_4p=E(_4c),_4q=__app3(_4p,_4i,_4j,_4o),_4r=__app3(_4p,_4i,_4m,_4o),_4s=B(A2(_4f,_4i,_)),_4t=String(_4l),_4u=__app3(_4p,_4i,_4j,_4t),_4v=String(_4n),_4w=__app3(_4p,_4i,_4m,_4v);return new F(function(){return _1(_);});};},_4x=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_4y=function(_4z,_4A,_){var _4B=E(_4z);if(!_4B._){return _0;}else{var _4C=E(_4B.a),_4D=E(_4A),_4E=__app3(E(_3E),_4D,E(_4C.a),E(_4C.b)),_4F=E(_4B.b);if(!_4F._){return _0;}else{var _4G=E(_4F.a),_4H=E(_4x),_4I=__app3(_4H,_4D,E(_4G.a),E(_4G.b)),_4J=function(_4K,_){while(1){var _4L=E(_4K);if(!_4L._){return _0;}else{var _4M=E(_4L.a),_4N=__app3(_4H,_4D,E(_4M.a),E(_4M.b));_4K=_4L.b;continue;}}};return new F(function(){return _4J(_4F.b,_);});}}},_4O=new T3(0,243,114,89),_4P=function(_4Q,_4R,_4S,_){var _4T=__app1(E(_3X),_4R),_4U=function(_4V,_){var _4W=E(E(_4S).a);return new F(function(){return _3F(E(_4W.a),E(_4W.b),5,E(_4V),_);});},_4X=B(A(_4d,[_4O,function(_4Y,_){return new F(function(){return _3O(_4U,E(_4Y),_);});},_4Q,_])),_4Z=E(E(_4S).c),_50=_4Z+150,_51=function(_52,_){return new F(function(){return _4y(new T2(1,new T2(0,_4Z,_3W),new T2(1,new T2(0,_50,_3W),new T2(1,new T2(0,_50,_3V),new T2(1,new T2(0,_4Z,_3V),new T2(1,new T2(0,_4Z,_3W),_y))))),_52,_);});};return new F(function(){return A(_4d,[_3U,function(_53,_){return new F(function(){return _3O(_51,E(_53),_);});},_4Q,_]);});},_54=new T(function(){return B(unCStr("\n"));}),_55=function(_56,_57,_){var _58=jsWriteHandle(E(_56),toJSStr(E(_57)));return _0;},_59=function(_5a,_5b,_){var _5c=E(_5a),_5d=jsWriteHandle(_5c,toJSStr(E(_5b)));return new F(function(){return _55(_5c,_54,_);});},_5e=new T1(0,10),_5f=false,_5g=new T(function(){var _5h=jsShow(640);return fromJSStr(_5h);}),_5i=new T(function(){return B(unAppCStr("trace collisionWall cw=",_5g));}),_5j=function(_){return new F(function(){return jsMkStderr();});},_5k=function(_5l){var _5m=B(A1(_5l,_));return E(_5m);},_5n=new T(function(){return B(_5k(_5j));}),_5o=function(_5p,_5q){return new F(function(){return _5k(function(_){var _5r=B(_59(_5n,_5p,0));return _5q;});});},_5s=new T(function(){return B(_5o(_5i,_5f));}),_5t=34,_5u=new T2(1,_5t,_y),_5v=new T(function(){return B(unCStr("Just "));}),_5w=41,_5x=new T2(1,_5w,_y),_5y=function(_5z,_5A,_5B){return new F(function(){return A1(_5z,new T2(1,_1T,new T(function(){return B(A1(_5A,_5B));})));});},_5C=new T(function(){return B(unCStr(": empty list"));}),_5D=function(_5E){return new F(function(){return err(B(_S(_2y,new T(function(){return B(_S(_5E,_5C));},1))));});},_5F=new T(function(){return B(unCStr("foldr1"));}),_5G=new T(function(){return B(_5D(_5F));}),_5H=function(_5I,_5J){var _5K=E(_5J);if(!_5K._){return E(_5G);}else{var _5L=_5K.a,_5M=E(_5K.b);if(!_5M._){return E(_5L);}else{return new F(function(){return A2(_5I,_5L,new T(function(){return B(_5H(_5I,_5M));}));});}}},_5N=new T(function(){var _5O=jsShow(0);return fromJSStr(_5O);}),_5P=function(_5Q){return new F(function(){return _S(_5N,_5Q);});},_5R=new T2(1,_5P,_y),_5S=new T2(1,_5P,_5R),_5T=new T(function(){return B(_5H(_5y,_5S));}),_5U=new T(function(){return B(A1(_5T,_5x));}),_5V=40,_5W=new T2(1,_5V,_5U),_5X=new T(function(){return B(_S(_5v,_5W));}),_5Y=function(_5Z){return E(E(_5Z).a);},_60=function(_61){return E(E(_61).a);},_62=function(_63){return E(E(_63).b);},_64=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_65=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_66=function(_){return new F(function(){return __jsNull();});},_67=new T(function(){return B(_5k(_66));}),_68=new T(function(){return E(_67);}),_69=function(_6a){return E(E(_6a).b);},_6b=function(_6c,_6d,_6e){var _6f=B(_5Y(_6c)),_6g=new T(function(){return B(_2V(_6f));}),_6h=function(_6i){var _6j=function(_){var _6k=E(_6d);if(!_6k._){var _6l=B(A1(_6i,_0)),_6m=__createJSFunc(0,function(_){var _6n=B(A1(_6l,_));return _68;}),_6o=__app2(E(_65),_6k.a,_6m);return new T(function(){var _6p=Number(_6o),_6q=jsTrunc(_6p);return new T2(0,_6q,E(_6k));});}else{var _6r=B(A1(_6i,_0)),_6s=__createJSFunc(0,function(_){var _6t=B(A1(_6r,_));return _68;}),_6u=__app2(E(_64),_6k.a,_6s);return new T(function(){var _6v=Number(_6u),_6w=jsTrunc(_6v);return new T2(0,_6w,E(_6k));});}};return new F(function(){return A1(_6g,_6j);});},_6x=new T(function(){return B(A2(_69,_6c,function(_6y){return E(_6e);}));});return new F(function(){return A3(_62,B(_60(_6f)),_6x,_6h);});},_6z=new T(function(){return B(unCStr("ACK"));}),_6A=new T(function(){return B(unCStr("BEL"));}),_6B=new T(function(){return B(unCStr("BS"));}),_6C=new T(function(){return B(unCStr("SP"));}),_6D=new T2(1,_6C,_y),_6E=new T(function(){return B(unCStr("US"));}),_6F=new T2(1,_6E,_6D),_6G=new T(function(){return B(unCStr("RS"));}),_6H=new T2(1,_6G,_6F),_6I=new T(function(){return B(unCStr("GS"));}),_6J=new T2(1,_6I,_6H),_6K=new T(function(){return B(unCStr("FS"));}),_6L=new T2(1,_6K,_6J),_6M=new T(function(){return B(unCStr("ESC"));}),_6N=new T2(1,_6M,_6L),_6O=new T(function(){return B(unCStr("SUB"));}),_6P=new T2(1,_6O,_6N),_6Q=new T(function(){return B(unCStr("EM"));}),_6R=new T2(1,_6Q,_6P),_6S=new T(function(){return B(unCStr("CAN"));}),_6T=new T2(1,_6S,_6R),_6U=new T(function(){return B(unCStr("ETB"));}),_6V=new T2(1,_6U,_6T),_6W=new T(function(){return B(unCStr("SYN"));}),_6X=new T2(1,_6W,_6V),_6Y=new T(function(){return B(unCStr("NAK"));}),_6Z=new T2(1,_6Y,_6X),_70=new T(function(){return B(unCStr("DC4"));}),_71=new T2(1,_70,_6Z),_72=new T(function(){return B(unCStr("DC3"));}),_73=new T2(1,_72,_71),_74=new T(function(){return B(unCStr("DC2"));}),_75=new T2(1,_74,_73),_76=new T(function(){return B(unCStr("DC1"));}),_77=new T2(1,_76,_75),_78=new T(function(){return B(unCStr("DLE"));}),_79=new T2(1,_78,_77),_7a=new T(function(){return B(unCStr("SI"));}),_7b=new T2(1,_7a,_79),_7c=new T(function(){return B(unCStr("SO"));}),_7d=new T2(1,_7c,_7b),_7e=new T(function(){return B(unCStr("CR"));}),_7f=new T2(1,_7e,_7d),_7g=new T(function(){return B(unCStr("FF"));}),_7h=new T2(1,_7g,_7f),_7i=new T(function(){return B(unCStr("VT"));}),_7j=new T2(1,_7i,_7h),_7k=new T(function(){return B(unCStr("LF"));}),_7l=new T2(1,_7k,_7j),_7m=new T(function(){return B(unCStr("HT"));}),_7n=new T2(1,_7m,_7l),_7o=new T2(1,_6B,_7n),_7p=new T2(1,_6A,_7o),_7q=new T2(1,_6z,_7p),_7r=new T(function(){return B(unCStr("ENQ"));}),_7s=new T2(1,_7r,_7q),_7t=new T(function(){return B(unCStr("EOT"));}),_7u=new T2(1,_7t,_7s),_7v=new T(function(){return B(unCStr("ETX"));}),_7w=new T2(1,_7v,_7u),_7x=new T(function(){return B(unCStr("STX"));}),_7y=new T2(1,_7x,_7w),_7z=new T(function(){return B(unCStr("SOH"));}),_7A=new T2(1,_7z,_7y),_7B=new T(function(){return B(unCStr("NUL"));}),_7C=new T2(1,_7B,_7A),_7D=92,_7E=new T(function(){return B(unCStr("\\DEL"));}),_7F=new T(function(){return B(unCStr("\\a"));}),_7G=new T(function(){return B(unCStr("\\\\"));}),_7H=new T(function(){return B(unCStr("\\SO"));}),_7I=new T(function(){return B(unCStr("\\r"));}),_7J=new T(function(){return B(unCStr("\\f"));}),_7K=new T(function(){return B(unCStr("\\v"));}),_7L=new T(function(){return B(unCStr("\\n"));}),_7M=new T(function(){return B(unCStr("\\t"));}),_7N=new T(function(){return B(unCStr("\\b"));}),_7O=function(_7P,_7Q){if(_7P<=127){var _7R=E(_7P);switch(_7R){case 92:return new F(function(){return _S(_7G,_7Q);});break;case 127:return new F(function(){return _S(_7E,_7Q);});break;default:if(_7R<32){var _7S=E(_7R);switch(_7S){case 7:return new F(function(){return _S(_7F,_7Q);});break;case 8:return new F(function(){return _S(_7N,_7Q);});break;case 9:return new F(function(){return _S(_7M,_7Q);});break;case 10:return new F(function(){return _S(_7L,_7Q);});break;case 11:return new F(function(){return _S(_7K,_7Q);});break;case 12:return new F(function(){return _S(_7J,_7Q);});break;case 13:return new F(function(){return _S(_7I,_7Q);});break;case 14:return new F(function(){return _S(_7H,new T(function(){var _7T=E(_7Q);if(!_7T._){return __Z;}else{if(E(_7T.a)==72){return B(unAppCStr("\\&",_7T));}else{return E(_7T);}}},1));});break;default:return new F(function(){return _S(new T2(1,_7D,new T(function(){return B(_2J(_7C,_7S));})),_7Q);});}}else{return new T2(1,_7R,_7Q);}}}else{var _7U=new T(function(){var _7V=jsShowI(_7P);return B(_S(fromJSStr(_7V),new T(function(){var _7W=E(_7Q);if(!_7W._){return __Z;}else{var _7X=E(_7W.a);if(_7X<48){return E(_7W);}else{if(_7X>57){return E(_7W);}else{return B(unAppCStr("\\&",_7W));}}}},1)));});return new T2(1,_7D,_7U);}},_7Y=new T(function(){return B(unCStr("\\\""));}),_7Z=function(_80,_81){var _82=E(_80);if(!_82._){return E(_81);}else{var _83=_82.b,_84=E(_82.a);if(_84==34){return new F(function(){return _S(_7Y,new T(function(){return B(_7Z(_83,_81));},1));});}else{return new F(function(){return _7O(_84,new T(function(){return B(_7Z(_83,_81));}));});}}},_85=function(_){return new F(function(){return jsMkStdout();});},_86=new T(function(){return B(_5k(_85));}),_87=new T(function(){return B(unCStr("Prelude.undefined"));}),_88=new T(function(){return B(err(_87));}),_89=function(_8a,_8b,_8c,_){var _8d=rMV(_8c),_8e=B(_4P(_8a,_8b,_8d,_)),_8f=new T(function(){return E(E(_8d).b);}),_8g=new T(function(){return E(E(_8d).a);}),_8h=new T(function(){var _8i=E(_8d);return new T4(0,new T2(0,new T(function(){return E(E(_8g).a)+E(E(_8f).a);}),new T(function(){return E(E(_8g).b)+E(E(_8f).b);})),_8i.b,_8i.c,_8i.d);}),_8j=mMV(_8c,function(_8k){return E(new T2(0,_8h,_0));}),_8l=E(_8j),_8m=new T(function(){return B(_7Z(B(unAppCStr("abc=",new T(function(){if(!E(_5s)){var _8n=E(E(_8d).a);if(E(_8n.a)<=640){if(E(_8n.b)<=480){return E(_3A);}else{return E(_5X);}}else{return E(_5X);}}else{return E(_88);}}))),_5u));}),_8o=B(_59(_86,new T2(1,_5t,_8m),_)),_8p=B(A(_6b,[_3z,_5e,function(_){return new F(function(){return _89(_8a,_8b,_8c,_);});},_]));return _0;},_8q=function(_8r,_8s){var _8t=jsShowI(_8r);return new F(function(){return _S(fromJSStr(_8t),_8s);});},_8u=function(_8v,_8w,_8x){if(_8w>=0){return new F(function(){return _8q(_8w,_8x);});}else{if(_8v<=6){return new F(function(){return _8q(_8w,_8x);});}else{return new T2(1,_5V,new T(function(){var _8y=jsShowI(_8w);return B(_S(fromJSStr(_8y),new T2(1,_5w,_8x)));}));}}},_8z=2,_8A=function(_8B){return new F(function(){return fromJSStr(E(_8B));});},_8C=function(_8D){return E(E(_8D).a);},_8E=new T(function(){return eval("(function(e,p){return e.hasAttribute(p) ? e.getAttribute(p) : \'\';})");}),_8F=function(_8G,_8H,_8I,_8J){var _8K=new T(function(){var _8L=function(_){var _8M=__app2(E(_8E),B(A2(_8C,_8G,_8I)),E(_8J));return new T(function(){return String(_8M);});};return E(_8L);});return new F(function(){return A2(_2V,_8H,_8K);});},_8N=function(_8O){return E(E(_8O).d);},_8P=function(_8Q,_8R,_8S,_8T){var _8U=B(_60(_8R)),_8V=new T(function(){return B(_8N(_8U));}),_8W=function(_8X){return new F(function(){return A1(_8V,new T(function(){return B(_8A(_8X));}));});},_8Y=new T(function(){return B(_8F(_8Q,_8R,_8S,new T(function(){return toJSStr(E(_8T));},1)));});return new F(function(){return A3(_62,_8U,_8Y,_8W);});},_8Z=75,_90=0,_91=20,_92=new T2(0,_91,_91),_93=2,_94=3,_95=new T2(0,_93,_94),_96=new T4(0,_92,_95,_8Z,_90),_97=new T(function(){return B(unCStr("base"));}),_98=new T(function(){return B(unCStr("Control.Exception.Base"));}),_99=new T(function(){return B(unCStr("PatternMatchFail"));}),_9a=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_97,_98,_99),_9b=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_9a,_y,_y),_9c=function(_9d){return E(_9b);},_9e=function(_9f){var _9g=E(_9f);return new F(function(){return _E(B(_C(_9g.a)),_9c,_9g.b);});},_9h=function(_9i){return E(E(_9i).a);},_9j=function(_9k){return new T2(0,_9l,_9k);},_9m=function(_9n,_9o){return new F(function(){return _S(E(_9n).a,_9o);});},_9p=function(_9q,_9r){return new F(function(){return _1W(_9m,_9q,_9r);});},_9s=function(_9t,_9u,_9v){return new F(function(){return _S(E(_9u).a,_9v);});},_9w=new T3(0,_9s,_9h,_9p),_9l=new T(function(){return new T5(0,_9c,_9w,_9j,_9e,_9h);}),_9x=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_9y=function(_9z,_9A){return new F(function(){return die(new T(function(){return B(A2(_2c,_9A,_9z));}));});},_9B=function(_9C,_9D){return new F(function(){return _9y(_9C,_9D);});},_9E=function(_9F,_9G){var _9H=E(_9G);if(!_9H._){return new T2(0,_y,_y);}else{var _9I=_9H.a;if(!B(A1(_9F,_9I))){return new T2(0,_y,_9H);}else{var _9J=new T(function(){var _9K=B(_9E(_9F,_9H.b));return new T2(0,_9K.a,_9K.b);});return new T2(0,new T2(1,_9I,new T(function(){return E(E(_9J).a);})),new T(function(){return E(E(_9J).b);}));}}},_9L=32,_9M=new T(function(){return B(unCStr("\n"));}),_9N=function(_9O){return (E(_9O)==124)?false:true;},_9P=function(_9Q,_9R){var _9S=B(_9E(_9N,B(unCStr(_9Q)))),_9T=_9S.a,_9U=function(_9V,_9W){var _9X=new T(function(){var _9Y=new T(function(){return B(_S(_9R,new T(function(){return B(_S(_9W,_9M));},1)));});return B(unAppCStr(": ",_9Y));},1);return new F(function(){return _S(_9V,_9X);});},_9Z=E(_9S.b);if(!_9Z._){return new F(function(){return _9U(_9T,_y);});}else{if(E(_9Z.a)==124){return new F(function(){return _9U(_9T,new T2(1,_9L,_9Z.b));});}else{return new F(function(){return _9U(_9T,_y);});}}},_a0=function(_a1){return new F(function(){return _9B(new T1(0,new T(function(){return B(_9P(_a1,_9x));})),_9l);});},_a2=new T(function(){return B(_a0("Text\\ParserCombinators\\ReadP.hs:(128,3)-(151,52)|function <|>"));}),_a3=function(_a4,_a5){while(1){var _a6=B((function(_a7,_a8){var _a9=E(_a7);switch(_a9._){case 0:var _aa=E(_a8);if(!_aa._){return __Z;}else{_a4=B(A1(_a9.a,_aa.a));_a5=_aa.b;return __continue;}break;case 1:var _ab=B(A1(_a9.a,_a8)),_ac=_a8;_a4=_ab;_a5=_ac;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_a9.a,_a8),new T(function(){return B(_a3(_a9.b,_a8));}));default:return E(_a9.a);}})(_a4,_a5));if(_a6!=__continue){return _a6;}}},_ad=function(_ae,_af){var _ag=function(_ah){var _ai=E(_af);if(_ai._==3){return new T2(3,_ai.a,new T(function(){return B(_ad(_ae,_ai.b));}));}else{var _aj=E(_ae);if(_aj._==2){return E(_ai);}else{var _ak=E(_ai);if(_ak._==2){return E(_aj);}else{var _al=function(_am){var _an=E(_ak);if(_an._==4){var _ao=function(_ap){return new T1(4,new T(function(){return B(_S(B(_a3(_aj,_ap)),_an.a));}));};return new T1(1,_ao);}else{var _aq=E(_aj);if(_aq._==1){var _ar=_aq.a,_as=E(_an);if(!_as._){return new T1(1,function(_at){return new F(function(){return _ad(B(A1(_ar,_at)),_as);});});}else{var _au=function(_av){return new F(function(){return _ad(B(A1(_ar,_av)),new T(function(){return B(A1(_as.a,_av));}));});};return new T1(1,_au);}}else{var _aw=E(_an);if(!_aw._){return E(_a2);}else{var _ax=function(_ay){return new F(function(){return _ad(_aq,new T(function(){return B(A1(_aw.a,_ay));}));});};return new T1(1,_ax);}}}},_az=E(_aj);switch(_az._){case 1:var _aA=E(_ak);if(_aA._==4){var _aB=function(_aC){return new T1(4,new T(function(){return B(_S(B(_a3(B(A1(_az.a,_aC)),_aC)),_aA.a));}));};return new T1(1,_aB);}else{return new F(function(){return _al(_);});}break;case 4:var _aD=_az.a,_aE=E(_ak);switch(_aE._){case 0:var _aF=function(_aG){var _aH=new T(function(){return B(_S(_aD,new T(function(){return B(_a3(_aE,_aG));},1)));});return new T1(4,_aH);};return new T1(1,_aF);case 1:var _aI=function(_aJ){var _aK=new T(function(){return B(_S(_aD,new T(function(){return B(_a3(B(A1(_aE.a,_aJ)),_aJ));},1)));});return new T1(4,_aK);};return new T1(1,_aI);default:return new T1(4,new T(function(){return B(_S(_aD,_aE.a));}));}break;default:return new F(function(){return _al(_);});}}}}},_aL=E(_ae);switch(_aL._){case 0:var _aM=E(_af);if(!_aM._){var _aN=function(_aO){return new F(function(){return _ad(B(A1(_aL.a,_aO)),new T(function(){return B(A1(_aM.a,_aO));}));});};return new T1(0,_aN);}else{return new F(function(){return _ag(_);});}break;case 3:return new T2(3,_aL.a,new T(function(){return B(_ad(_aL.b,_af));}));default:return new F(function(){return _ag(_);});}},_aP=new T(function(){return B(unCStr("("));}),_aQ=new T(function(){return B(unCStr(")"));}),_aR=function(_aS,_aT){while(1){var _aU=E(_aS);if(!_aU._){return (E(_aT)._==0)?true:false;}else{var _aV=E(_aT);if(!_aV._){return false;}else{if(E(_aU.a)!=E(_aV.a)){return false;}else{_aS=_aU.b;_aT=_aV.b;continue;}}}}},_aW=function(_aX,_aY){return E(_aX)!=E(_aY);},_aZ=function(_b0,_b1){return E(_b0)==E(_b1);},_b2=new T2(0,_aZ,_aW),_b3=function(_b4,_b5){while(1){var _b6=E(_b4);if(!_b6._){return (E(_b5)._==0)?true:false;}else{var _b7=E(_b5);if(!_b7._){return false;}else{if(E(_b6.a)!=E(_b7.a)){return false;}else{_b4=_b6.b;_b5=_b7.b;continue;}}}}},_b8=function(_b9,_ba){return (!B(_b3(_b9,_ba)))?true:false;},_bb=new T2(0,_b3,_b8),_bc=function(_bd,_be){var _bf=E(_bd);switch(_bf._){case 0:return new T1(0,function(_bg){return new F(function(){return _bc(B(A1(_bf.a,_bg)),_be);});});case 1:return new T1(1,function(_bh){return new F(function(){return _bc(B(A1(_bf.a,_bh)),_be);});});case 2:return new T0(2);case 3:return new F(function(){return _ad(B(A1(_be,_bf.a)),new T(function(){return B(_bc(_bf.b,_be));}));});break;default:var _bi=function(_bj){var _bk=E(_bj);if(!_bk._){return __Z;}else{var _bl=E(_bk.a);return new F(function(){return _S(B(_a3(B(A1(_be,_bl.a)),_bl.b)),new T(function(){return B(_bi(_bk.b));},1));});}},_bm=B(_bi(_bf.a));return (_bm._==0)?new T0(2):new T1(4,_bm);}},_bn=new T0(2),_bo=function(_bp){return new T2(3,_bp,_bn);},_bq=function(_br,_bs){var _bt=E(_br);if(!_bt){return new F(function(){return A1(_bs,_0);});}else{var _bu=new T(function(){return B(_bq(_bt-1|0,_bs));});return new T1(0,function(_bv){return E(_bu);});}},_bw=function(_bx,_by,_bz){var _bA=new T(function(){return B(A1(_bx,_bo));}),_bB=function(_bC,_bD,_bE,_bF){while(1){var _bG=B((function(_bH,_bI,_bJ,_bK){var _bL=E(_bH);switch(_bL._){case 0:var _bM=E(_bI);if(!_bM._){return new F(function(){return A1(_by,_bK);});}else{var _bN=_bJ+1|0,_bO=_bK;_bC=B(A1(_bL.a,_bM.a));_bD=_bM.b;_bE=_bN;_bF=_bO;return __continue;}break;case 1:var _bP=B(A1(_bL.a,_bI)),_bQ=_bI,_bN=_bJ,_bO=_bK;_bC=_bP;_bD=_bQ;_bE=_bN;_bF=_bO;return __continue;case 2:return new F(function(){return A1(_by,_bK);});break;case 3:var _bR=new T(function(){return B(_bc(_bL,_bK));});return new F(function(){return _bq(_bJ,function(_bS){return E(_bR);});});break;default:return new F(function(){return _bc(_bL,_bK);});}})(_bC,_bD,_bE,_bF));if(_bG!=__continue){return _bG;}}};return function(_bT){return new F(function(){return _bB(_bA,_bT,0,_bz);});};},_bU=function(_bV){return new F(function(){return A1(_bV,_y);});},_bW=function(_bX,_bY){var _bZ=function(_c0){var _c1=E(_c0);if(!_c1._){return E(_bU);}else{var _c2=_c1.a;if(!B(A1(_bX,_c2))){return E(_bU);}else{var _c3=new T(function(){return B(_bZ(_c1.b));}),_c4=function(_c5){var _c6=new T(function(){return B(A1(_c3,function(_c7){return new F(function(){return A1(_c5,new T2(1,_c2,_c7));});}));});return new T1(0,function(_c8){return E(_c6);});};return E(_c4);}}};return function(_c9){return new F(function(){return A2(_bZ,_c9,_bY);});};},_ca=new T0(6),_cb=new T(function(){return B(unCStr("valDig: Bad base"));}),_cc=new T(function(){return B(err(_cb));}),_cd=function(_ce,_cf){var _cg=function(_ch,_ci){var _cj=E(_ch);if(!_cj._){var _ck=new T(function(){return B(A1(_ci,_y));});return function(_cl){return new F(function(){return A1(_cl,_ck);});};}else{var _cm=E(_cj.a),_cn=function(_co){var _cp=new T(function(){return B(_cg(_cj.b,function(_cq){return new F(function(){return A1(_ci,new T2(1,_co,_cq));});}));}),_cr=function(_cs){var _ct=new T(function(){return B(A1(_cp,_cs));});return new T1(0,function(_cu){return E(_ct);});};return E(_cr);};switch(E(_ce)){case 8:if(48>_cm){var _cv=new T(function(){return B(A1(_ci,_y));});return function(_cw){return new F(function(){return A1(_cw,_cv);});};}else{if(_cm>55){var _cx=new T(function(){return B(A1(_ci,_y));});return function(_cy){return new F(function(){return A1(_cy,_cx);});};}else{return new F(function(){return _cn(_cm-48|0);});}}break;case 10:if(48>_cm){var _cz=new T(function(){return B(A1(_ci,_y));});return function(_cA){return new F(function(){return A1(_cA,_cz);});};}else{if(_cm>57){var _cB=new T(function(){return B(A1(_ci,_y));});return function(_cC){return new F(function(){return A1(_cC,_cB);});};}else{return new F(function(){return _cn(_cm-48|0);});}}break;case 16:if(48>_cm){if(97>_cm){if(65>_cm){var _cD=new T(function(){return B(A1(_ci,_y));});return function(_cE){return new F(function(){return A1(_cE,_cD);});};}else{if(_cm>70){var _cF=new T(function(){return B(A1(_ci,_y));});return function(_cG){return new F(function(){return A1(_cG,_cF);});};}else{return new F(function(){return _cn((_cm-65|0)+10|0);});}}}else{if(_cm>102){if(65>_cm){var _cH=new T(function(){return B(A1(_ci,_y));});return function(_cI){return new F(function(){return A1(_cI,_cH);});};}else{if(_cm>70){var _cJ=new T(function(){return B(A1(_ci,_y));});return function(_cK){return new F(function(){return A1(_cK,_cJ);});};}else{return new F(function(){return _cn((_cm-65|0)+10|0);});}}}else{return new F(function(){return _cn((_cm-97|0)+10|0);});}}}else{if(_cm>57){if(97>_cm){if(65>_cm){var _cL=new T(function(){return B(A1(_ci,_y));});return function(_cM){return new F(function(){return A1(_cM,_cL);});};}else{if(_cm>70){var _cN=new T(function(){return B(A1(_ci,_y));});return function(_cO){return new F(function(){return A1(_cO,_cN);});};}else{return new F(function(){return _cn((_cm-65|0)+10|0);});}}}else{if(_cm>102){if(65>_cm){var _cP=new T(function(){return B(A1(_ci,_y));});return function(_cQ){return new F(function(){return A1(_cQ,_cP);});};}else{if(_cm>70){var _cR=new T(function(){return B(A1(_ci,_y));});return function(_cS){return new F(function(){return A1(_cS,_cR);});};}else{return new F(function(){return _cn((_cm-65|0)+10|0);});}}}else{return new F(function(){return _cn((_cm-97|0)+10|0);});}}}else{return new F(function(){return _cn(_cm-48|0);});}}break;default:return E(_cc);}}},_cT=function(_cU){var _cV=E(_cU);if(!_cV._){return new T0(2);}else{return new F(function(){return A1(_cf,_cV);});}};return function(_cW){return new F(function(){return A3(_cg,_cW,_2u,_cT);});};},_cX=16,_cY=8,_cZ=function(_d0){var _d1=function(_d2){return new F(function(){return A1(_d0,new T1(5,new T2(0,_cY,_d2)));});},_d3=function(_d4){return new F(function(){return A1(_d0,new T1(5,new T2(0,_cX,_d4)));});},_d5=function(_d6){switch(E(_d6)){case 79:return new T1(1,B(_cd(_cY,_d1)));case 88:return new T1(1,B(_cd(_cX,_d3)));case 111:return new T1(1,B(_cd(_cY,_d1)));case 120:return new T1(1,B(_cd(_cX,_d3)));default:return new T0(2);}};return function(_d7){return (E(_d7)==48)?E(new T1(0,_d5)):new T0(2);};},_d8=function(_d9){return new T1(0,B(_cZ(_d9)));},_da=function(_db){return new F(function(){return A1(_db,_2e);});},_dc=function(_dd){return new F(function(){return A1(_dd,_2e);});},_de=10,_df=new T1(0,1),_dg=new T1(0,2147483647),_dh=function(_di,_dj){while(1){var _dk=E(_di);if(!_dk._){var _dl=_dk.a,_dm=E(_dj);if(!_dm._){var _dn=_dm.a,_do=addC(_dl,_dn);if(!E(_do.b)){return new T1(0,_do.a);}else{_di=new T1(1,I_fromInt(_dl));_dj=new T1(1,I_fromInt(_dn));continue;}}else{_di=new T1(1,I_fromInt(_dl));_dj=_dm;continue;}}else{var _dp=E(_dj);if(!_dp._){_di=_dk;_dj=new T1(1,I_fromInt(_dp.a));continue;}else{return new T1(1,I_add(_dk.a,_dp.a));}}}},_dq=new T(function(){return B(_dh(_dg,_df));}),_dr=function(_ds){var _dt=E(_ds);if(!_dt._){var _du=E(_dt.a);return (_du==(-2147483648))?E(_dq):new T1(0, -_du);}else{return new T1(1,I_negate(_dt.a));}},_dv=new T1(0,10),_dw=function(_dx,_dy){while(1){var _dz=E(_dx);if(!_dz._){return E(_dy);}else{var _dA=_dy+1|0;_dx=_dz.b;_dy=_dA;continue;}}},_dB=function(_dC,_dD){var _dE=E(_dD);return (_dE._==0)?__Z:new T2(1,new T(function(){return B(A1(_dC,_dE.a));}),new T(function(){return B(_dB(_dC,_dE.b));}));},_dF=function(_dG){return new T1(0,_dG);},_dH=function(_dI){return new F(function(){return _dF(E(_dI));});},_dJ=new T(function(){return B(unCStr("this should not happen"));}),_dK=new T(function(){return B(err(_dJ));}),_dL=function(_dM,_dN){while(1){var _dO=E(_dM);if(!_dO._){var _dP=_dO.a,_dQ=E(_dN);if(!_dQ._){var _dR=_dQ.a;if(!(imul(_dP,_dR)|0)){return new T1(0,imul(_dP,_dR)|0);}else{_dM=new T1(1,I_fromInt(_dP));_dN=new T1(1,I_fromInt(_dR));continue;}}else{_dM=new T1(1,I_fromInt(_dP));_dN=_dQ;continue;}}else{var _dS=E(_dN);if(!_dS._){_dM=_dO;_dN=new T1(1,I_fromInt(_dS.a));continue;}else{return new T1(1,I_mul(_dO.a,_dS.a));}}}},_dT=function(_dU,_dV){var _dW=E(_dV);if(!_dW._){return __Z;}else{var _dX=E(_dW.b);return (_dX._==0)?E(_dK):new T2(1,B(_dh(B(_dL(_dW.a,_dU)),_dX.a)),new T(function(){return B(_dT(_dU,_dX.b));}));}},_dY=new T1(0,0),_dZ=function(_e0,_e1,_e2){while(1){var _e3=B((function(_e4,_e5,_e6){var _e7=E(_e6);if(!_e7._){return E(_dY);}else{if(!E(_e7.b)._){return E(_e7.a);}else{var _e8=E(_e5);if(_e8<=40){var _e9=function(_ea,_eb){while(1){var _ec=E(_eb);if(!_ec._){return E(_ea);}else{var _ed=B(_dh(B(_dL(_ea,_e4)),_ec.a));_ea=_ed;_eb=_ec.b;continue;}}};return new F(function(){return _e9(_dY,_e7);});}else{var _ee=B(_dL(_e4,_e4));if(!(_e8%2)){var _ef=B(_dT(_e4,_e7));_e0=_ee;_e1=quot(_e8+1|0,2);_e2=_ef;return __continue;}else{var _ef=B(_dT(_e4,new T2(1,_dY,_e7)));_e0=_ee;_e1=quot(_e8+1|0,2);_e2=_ef;return __continue;}}}}})(_e0,_e1,_e2));if(_e3!=__continue){return _e3;}}},_eg=function(_eh,_ei){return new F(function(){return _dZ(_eh,new T(function(){return B(_dw(_ei,0));},1),B(_dB(_dH,_ei)));});},_ej=function(_ek){var _el=new T(function(){var _em=new T(function(){var _en=function(_eo){return new F(function(){return A1(_ek,new T1(1,new T(function(){return B(_eg(_dv,_eo));})));});};return new T1(1,B(_cd(_de,_en)));}),_ep=function(_eq){if(E(_eq)==43){var _er=function(_es){return new F(function(){return A1(_ek,new T1(1,new T(function(){return B(_eg(_dv,_es));})));});};return new T1(1,B(_cd(_de,_er)));}else{return new T0(2);}},_et=function(_eu){if(E(_eu)==45){var _ev=function(_ew){return new F(function(){return A1(_ek,new T1(1,new T(function(){return B(_dr(B(_eg(_dv,_ew))));})));});};return new T1(1,B(_cd(_de,_ev)));}else{return new T0(2);}};return B(_ad(B(_ad(new T1(0,_et),new T1(0,_ep))),_em));});return new F(function(){return _ad(new T1(0,function(_ex){return (E(_ex)==101)?E(_el):new T0(2);}),new T1(0,function(_ey){return (E(_ey)==69)?E(_el):new T0(2);}));});},_ez=function(_eA){var _eB=function(_eC){return new F(function(){return A1(_eA,new T1(1,_eC));});};return function(_eD){return (E(_eD)==46)?new T1(1,B(_cd(_de,_eB))):new T0(2);};},_eE=function(_eF){return new T1(0,B(_ez(_eF)));},_eG=function(_eH){var _eI=function(_eJ){var _eK=function(_eL){return new T1(1,B(_bw(_ej,_da,function(_eM){return new F(function(){return A1(_eH,new T1(5,new T3(1,_eJ,_eL,_eM)));});})));};return new T1(1,B(_bw(_eE,_dc,_eK)));};return new F(function(){return _cd(_de,_eI);});},_eN=function(_eO){return new T1(1,B(_eG(_eO)));},_eP=function(_eQ){return E(E(_eQ).a);},_eR=function(_eS,_eT,_eU){while(1){var _eV=E(_eU);if(!_eV._){return false;}else{if(!B(A3(_eP,_eS,_eT,_eV.a))){_eU=_eV.b;continue;}else{return true;}}}},_eW=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_eX=function(_eY){return new F(function(){return _eR(_b2,_eY,_eW);});},_eZ=true,_f0=function(_f1){var _f2=new T(function(){return B(A1(_f1,_cY));}),_f3=new T(function(){return B(A1(_f1,_cX));});return function(_f4){switch(E(_f4)){case 79:return E(_f2);case 88:return E(_f3);case 111:return E(_f2);case 120:return E(_f3);default:return new T0(2);}};},_f5=function(_f6){return new T1(0,B(_f0(_f6)));},_f7=function(_f8){return new F(function(){return A1(_f8,_de);});},_f9=function(_fa){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_8u(9,_fa,_y));}))));});},_fb=function(_fc){var _fd=E(_fc);if(!_fd._){return E(_fd.a);}else{return new F(function(){return I_toInt(_fd.a);});}},_fe=function(_ff,_fg){var _fh=E(_ff);if(!_fh._){var _fi=_fh.a,_fj=E(_fg);return (_fj._==0)?_fi<=_fj.a:I_compareInt(_fj.a,_fi)>=0;}else{var _fk=_fh.a,_fl=E(_fg);return (_fl._==0)?I_compareInt(_fk,_fl.a)<=0:I_compare(_fk,_fl.a)<=0;}},_fm=function(_fn){return new T0(2);},_fo=function(_fp){var _fq=E(_fp);if(!_fq._){return E(_fm);}else{var _fr=_fq.a,_fs=E(_fq.b);if(!_fs._){return E(_fr);}else{var _ft=new T(function(){return B(_fo(_fs));}),_fu=function(_fv){return new F(function(){return _ad(B(A1(_fr,_fv)),new T(function(){return B(A1(_ft,_fv));}));});};return E(_fu);}}},_fw=function(_fx,_fy){var _fz=function(_fA,_fB,_fC){var _fD=E(_fA);if(!_fD._){return new F(function(){return A1(_fC,_fx);});}else{var _fE=E(_fB);if(!_fE._){return new T0(2);}else{if(E(_fD.a)!=E(_fE.a)){return new T0(2);}else{var _fF=new T(function(){return B(_fz(_fD.b,_fE.b,_fC));});return new T1(0,function(_fG){return E(_fF);});}}}};return function(_fH){return new F(function(){return _fz(_fx,_fH,_fy);});};},_fI=new T(function(){return B(unCStr("SO"));}),_fJ=14,_fK=function(_fL){var _fM=new T(function(){return B(A1(_fL,_fJ));});return new T1(1,B(_fw(_fI,function(_fN){return E(_fM);})));},_fO=new T(function(){return B(unCStr("SOH"));}),_fP=1,_fQ=function(_fR){var _fS=new T(function(){return B(A1(_fR,_fP));});return new T1(1,B(_fw(_fO,function(_fT){return E(_fS);})));},_fU=function(_fV){return new T1(1,B(_bw(_fQ,_fK,_fV)));},_fW=new T(function(){return B(unCStr("NUL"));}),_fX=0,_fY=function(_fZ){var _g0=new T(function(){return B(A1(_fZ,_fX));});return new T1(1,B(_fw(_fW,function(_g1){return E(_g0);})));},_g2=new T(function(){return B(unCStr("STX"));}),_g3=2,_g4=function(_g5){var _g6=new T(function(){return B(A1(_g5,_g3));});return new T1(1,B(_fw(_g2,function(_g7){return E(_g6);})));},_g8=new T(function(){return B(unCStr("ETX"));}),_g9=3,_ga=function(_gb){var _gc=new T(function(){return B(A1(_gb,_g9));});return new T1(1,B(_fw(_g8,function(_gd){return E(_gc);})));},_ge=new T(function(){return B(unCStr("EOT"));}),_gf=4,_gg=function(_gh){var _gi=new T(function(){return B(A1(_gh,_gf));});return new T1(1,B(_fw(_ge,function(_gj){return E(_gi);})));},_gk=new T(function(){return B(unCStr("ENQ"));}),_gl=5,_gm=function(_gn){var _go=new T(function(){return B(A1(_gn,_gl));});return new T1(1,B(_fw(_gk,function(_gp){return E(_go);})));},_gq=new T(function(){return B(unCStr("ACK"));}),_gr=6,_gs=function(_gt){var _gu=new T(function(){return B(A1(_gt,_gr));});return new T1(1,B(_fw(_gq,function(_gv){return E(_gu);})));},_gw=new T(function(){return B(unCStr("BEL"));}),_gx=7,_gy=function(_gz){var _gA=new T(function(){return B(A1(_gz,_gx));});return new T1(1,B(_fw(_gw,function(_gB){return E(_gA);})));},_gC=new T(function(){return B(unCStr("BS"));}),_gD=8,_gE=function(_gF){var _gG=new T(function(){return B(A1(_gF,_gD));});return new T1(1,B(_fw(_gC,function(_gH){return E(_gG);})));},_gI=new T(function(){return B(unCStr("HT"));}),_gJ=9,_gK=function(_gL){var _gM=new T(function(){return B(A1(_gL,_gJ));});return new T1(1,B(_fw(_gI,function(_gN){return E(_gM);})));},_gO=new T(function(){return B(unCStr("LF"));}),_gP=10,_gQ=function(_gR){var _gS=new T(function(){return B(A1(_gR,_gP));});return new T1(1,B(_fw(_gO,function(_gT){return E(_gS);})));},_gU=new T(function(){return B(unCStr("VT"));}),_gV=11,_gW=function(_gX){var _gY=new T(function(){return B(A1(_gX,_gV));});return new T1(1,B(_fw(_gU,function(_gZ){return E(_gY);})));},_h0=new T(function(){return B(unCStr("FF"));}),_h1=12,_h2=function(_h3){var _h4=new T(function(){return B(A1(_h3,_h1));});return new T1(1,B(_fw(_h0,function(_h5){return E(_h4);})));},_h6=new T(function(){return B(unCStr("CR"));}),_h7=13,_h8=function(_h9){var _ha=new T(function(){return B(A1(_h9,_h7));});return new T1(1,B(_fw(_h6,function(_hb){return E(_ha);})));},_hc=new T(function(){return B(unCStr("SI"));}),_hd=15,_he=function(_hf){var _hg=new T(function(){return B(A1(_hf,_hd));});return new T1(1,B(_fw(_hc,function(_hh){return E(_hg);})));},_hi=new T(function(){return B(unCStr("DLE"));}),_hj=16,_hk=function(_hl){var _hm=new T(function(){return B(A1(_hl,_hj));});return new T1(1,B(_fw(_hi,function(_hn){return E(_hm);})));},_ho=new T(function(){return B(unCStr("DC1"));}),_hp=17,_hq=function(_hr){var _hs=new T(function(){return B(A1(_hr,_hp));});return new T1(1,B(_fw(_ho,function(_ht){return E(_hs);})));},_hu=new T(function(){return B(unCStr("DC2"));}),_hv=18,_hw=function(_hx){var _hy=new T(function(){return B(A1(_hx,_hv));});return new T1(1,B(_fw(_hu,function(_hz){return E(_hy);})));},_hA=new T(function(){return B(unCStr("DC3"));}),_hB=19,_hC=function(_hD){var _hE=new T(function(){return B(A1(_hD,_hB));});return new T1(1,B(_fw(_hA,function(_hF){return E(_hE);})));},_hG=new T(function(){return B(unCStr("DC4"));}),_hH=20,_hI=function(_hJ){var _hK=new T(function(){return B(A1(_hJ,_hH));});return new T1(1,B(_fw(_hG,function(_hL){return E(_hK);})));},_hM=new T(function(){return B(unCStr("NAK"));}),_hN=21,_hO=function(_hP){var _hQ=new T(function(){return B(A1(_hP,_hN));});return new T1(1,B(_fw(_hM,function(_hR){return E(_hQ);})));},_hS=new T(function(){return B(unCStr("SYN"));}),_hT=22,_hU=function(_hV){var _hW=new T(function(){return B(A1(_hV,_hT));});return new T1(1,B(_fw(_hS,function(_hX){return E(_hW);})));},_hY=new T(function(){return B(unCStr("ETB"));}),_hZ=23,_i0=function(_i1){var _i2=new T(function(){return B(A1(_i1,_hZ));});return new T1(1,B(_fw(_hY,function(_i3){return E(_i2);})));},_i4=new T(function(){return B(unCStr("CAN"));}),_i5=24,_i6=function(_i7){var _i8=new T(function(){return B(A1(_i7,_i5));});return new T1(1,B(_fw(_i4,function(_i9){return E(_i8);})));},_ia=new T(function(){return B(unCStr("EM"));}),_ib=25,_ic=function(_id){var _ie=new T(function(){return B(A1(_id,_ib));});return new T1(1,B(_fw(_ia,function(_if){return E(_ie);})));},_ig=new T(function(){return B(unCStr("SUB"));}),_ih=26,_ii=function(_ij){var _ik=new T(function(){return B(A1(_ij,_ih));});return new T1(1,B(_fw(_ig,function(_il){return E(_ik);})));},_im=new T(function(){return B(unCStr("ESC"));}),_in=27,_io=function(_ip){var _iq=new T(function(){return B(A1(_ip,_in));});return new T1(1,B(_fw(_im,function(_ir){return E(_iq);})));},_is=new T(function(){return B(unCStr("FS"));}),_it=28,_iu=function(_iv){var _iw=new T(function(){return B(A1(_iv,_it));});return new T1(1,B(_fw(_is,function(_ix){return E(_iw);})));},_iy=new T(function(){return B(unCStr("GS"));}),_iz=29,_iA=function(_iB){var _iC=new T(function(){return B(A1(_iB,_iz));});return new T1(1,B(_fw(_iy,function(_iD){return E(_iC);})));},_iE=new T(function(){return B(unCStr("RS"));}),_iF=30,_iG=function(_iH){var _iI=new T(function(){return B(A1(_iH,_iF));});return new T1(1,B(_fw(_iE,function(_iJ){return E(_iI);})));},_iK=new T(function(){return B(unCStr("US"));}),_iL=31,_iM=function(_iN){var _iO=new T(function(){return B(A1(_iN,_iL));});return new T1(1,B(_fw(_iK,function(_iP){return E(_iO);})));},_iQ=new T(function(){return B(unCStr("SP"));}),_iR=32,_iS=function(_iT){var _iU=new T(function(){return B(A1(_iT,_iR));});return new T1(1,B(_fw(_iQ,function(_iV){return E(_iU);})));},_iW=new T(function(){return B(unCStr("DEL"));}),_iX=127,_iY=function(_iZ){var _j0=new T(function(){return B(A1(_iZ,_iX));});return new T1(1,B(_fw(_iW,function(_j1){return E(_j0);})));},_j2=new T2(1,_iY,_y),_j3=new T2(1,_iS,_j2),_j4=new T2(1,_iM,_j3),_j5=new T2(1,_iG,_j4),_j6=new T2(1,_iA,_j5),_j7=new T2(1,_iu,_j6),_j8=new T2(1,_io,_j7),_j9=new T2(1,_ii,_j8),_ja=new T2(1,_ic,_j9),_jb=new T2(1,_i6,_ja),_jc=new T2(1,_i0,_jb),_jd=new T2(1,_hU,_jc),_je=new T2(1,_hO,_jd),_jf=new T2(1,_hI,_je),_jg=new T2(1,_hC,_jf),_jh=new T2(1,_hw,_jg),_ji=new T2(1,_hq,_jh),_jj=new T2(1,_hk,_ji),_jk=new T2(1,_he,_jj),_jl=new T2(1,_h8,_jk),_jm=new T2(1,_h2,_jl),_jn=new T2(1,_gW,_jm),_jo=new T2(1,_gQ,_jn),_jp=new T2(1,_gK,_jo),_jq=new T2(1,_gE,_jp),_jr=new T2(1,_gy,_jq),_js=new T2(1,_gs,_jr),_jt=new T2(1,_gm,_js),_ju=new T2(1,_gg,_jt),_jv=new T2(1,_ga,_ju),_jw=new T2(1,_g4,_jv),_jx=new T2(1,_fY,_jw),_jy=new T2(1,_fU,_jx),_jz=new T(function(){return B(_fo(_jy));}),_jA=34,_jB=new T1(0,1114111),_jC=92,_jD=39,_jE=function(_jF){var _jG=new T(function(){return B(A1(_jF,_gx));}),_jH=new T(function(){return B(A1(_jF,_gD));}),_jI=new T(function(){return B(A1(_jF,_gJ));}),_jJ=new T(function(){return B(A1(_jF,_gP));}),_jK=new T(function(){return B(A1(_jF,_gV));}),_jL=new T(function(){return B(A1(_jF,_h1));}),_jM=new T(function(){return B(A1(_jF,_h7));}),_jN=new T(function(){return B(A1(_jF,_jC));}),_jO=new T(function(){return B(A1(_jF,_jD));}),_jP=new T(function(){return B(A1(_jF,_jA));}),_jQ=new T(function(){var _jR=function(_jS){var _jT=new T(function(){return B(_dF(E(_jS)));}),_jU=function(_jV){var _jW=B(_eg(_jT,_jV));if(!B(_fe(_jW,_jB))){return new T0(2);}else{return new F(function(){return A1(_jF,new T(function(){var _jX=B(_fb(_jW));if(_jX>>>0>1114111){return B(_f9(_jX));}else{return _jX;}}));});}};return new T1(1,B(_cd(_jS,_jU)));},_jY=new T(function(){var _jZ=new T(function(){return B(A1(_jF,_iL));}),_k0=new T(function(){return B(A1(_jF,_iF));}),_k1=new T(function(){return B(A1(_jF,_iz));}),_k2=new T(function(){return B(A1(_jF,_it));}),_k3=new T(function(){return B(A1(_jF,_in));}),_k4=new T(function(){return B(A1(_jF,_ih));}),_k5=new T(function(){return B(A1(_jF,_ib));}),_k6=new T(function(){return B(A1(_jF,_i5));}),_k7=new T(function(){return B(A1(_jF,_hZ));}),_k8=new T(function(){return B(A1(_jF,_hT));}),_k9=new T(function(){return B(A1(_jF,_hN));}),_ka=new T(function(){return B(A1(_jF,_hH));}),_kb=new T(function(){return B(A1(_jF,_hB));}),_kc=new T(function(){return B(A1(_jF,_hv));}),_kd=new T(function(){return B(A1(_jF,_hp));}),_ke=new T(function(){return B(A1(_jF,_hj));}),_kf=new T(function(){return B(A1(_jF,_hd));}),_kg=new T(function(){return B(A1(_jF,_fJ));}),_kh=new T(function(){return B(A1(_jF,_gr));}),_ki=new T(function(){return B(A1(_jF,_gl));}),_kj=new T(function(){return B(A1(_jF,_gf));}),_kk=new T(function(){return B(A1(_jF,_g9));}),_kl=new T(function(){return B(A1(_jF,_g3));}),_km=new T(function(){return B(A1(_jF,_fP));}),_kn=new T(function(){return B(A1(_jF,_fX));}),_ko=function(_kp){switch(E(_kp)){case 64:return E(_kn);case 65:return E(_km);case 66:return E(_kl);case 67:return E(_kk);case 68:return E(_kj);case 69:return E(_ki);case 70:return E(_kh);case 71:return E(_jG);case 72:return E(_jH);case 73:return E(_jI);case 74:return E(_jJ);case 75:return E(_jK);case 76:return E(_jL);case 77:return E(_jM);case 78:return E(_kg);case 79:return E(_kf);case 80:return E(_ke);case 81:return E(_kd);case 82:return E(_kc);case 83:return E(_kb);case 84:return E(_ka);case 85:return E(_k9);case 86:return E(_k8);case 87:return E(_k7);case 88:return E(_k6);case 89:return E(_k5);case 90:return E(_k4);case 91:return E(_k3);case 92:return E(_k2);case 93:return E(_k1);case 94:return E(_k0);case 95:return E(_jZ);default:return new T0(2);}};return B(_ad(new T1(0,function(_kq){return (E(_kq)==94)?E(new T1(0,_ko)):new T0(2);}),new T(function(){return B(A1(_jz,_jF));})));});return B(_ad(new T1(1,B(_bw(_f5,_f7,_jR))),_jY));});return new F(function(){return _ad(new T1(0,function(_kr){switch(E(_kr)){case 34:return E(_jP);case 39:return E(_jO);case 92:return E(_jN);case 97:return E(_jG);case 98:return E(_jH);case 102:return E(_jL);case 110:return E(_jJ);case 114:return E(_jM);case 116:return E(_jI);case 118:return E(_jK);default:return new T0(2);}}),_jQ);});},_ks=function(_kt){return new F(function(){return A1(_kt,_0);});},_ku=function(_kv){var _kw=E(_kv);if(!_kw._){return E(_ks);}else{var _kx=E(_kw.a),_ky=_kx>>>0,_kz=new T(function(){return B(_ku(_kw.b));});if(_ky>887){var _kA=u_iswspace(_kx);if(!E(_kA)){return E(_ks);}else{var _kB=function(_kC){var _kD=new T(function(){return B(A1(_kz,_kC));});return new T1(0,function(_kE){return E(_kD);});};return E(_kB);}}else{var _kF=E(_ky);if(_kF==32){var _kG=function(_kH){var _kI=new T(function(){return B(A1(_kz,_kH));});return new T1(0,function(_kJ){return E(_kI);});};return E(_kG);}else{if(_kF-9>>>0>4){if(E(_kF)==160){var _kK=function(_kL){var _kM=new T(function(){return B(A1(_kz,_kL));});return new T1(0,function(_kN){return E(_kM);});};return E(_kK);}else{return E(_ks);}}else{var _kO=function(_kP){var _kQ=new T(function(){return B(A1(_kz,_kP));});return new T1(0,function(_kR){return E(_kQ);});};return E(_kO);}}}}},_kS=function(_kT){var _kU=new T(function(){return B(_kS(_kT));}),_kV=function(_kW){return (E(_kW)==92)?E(_kU):new T0(2);},_kX=function(_kY){return E(new T1(0,_kV));},_kZ=new T1(1,function(_l0){return new F(function(){return A2(_ku,_l0,_kX);});}),_l1=new T(function(){return B(_jE(function(_l2){return new F(function(){return A1(_kT,new T2(0,_l2,_eZ));});}));}),_l3=function(_l4){var _l5=E(_l4);if(_l5==38){return E(_kU);}else{var _l6=_l5>>>0;if(_l6>887){var _l7=u_iswspace(_l5);return (E(_l7)==0)?new T0(2):E(_kZ);}else{var _l8=E(_l6);return (_l8==32)?E(_kZ):(_l8-9>>>0>4)?(E(_l8)==160)?E(_kZ):new T0(2):E(_kZ);}}};return new F(function(){return _ad(new T1(0,function(_l9){return (E(_l9)==92)?E(new T1(0,_l3)):new T0(2);}),new T1(0,function(_la){var _lb=E(_la);if(E(_lb)==92){return E(_l1);}else{return new F(function(){return A1(_kT,new T2(0,_lb,_5f));});}}));});},_lc=function(_ld,_le){var _lf=new T(function(){return B(A1(_le,new T1(1,new T(function(){return B(A1(_ld,_y));}))));}),_lg=function(_lh){var _li=E(_lh),_lj=E(_li.a);if(E(_lj)==34){if(!E(_li.b)){return E(_lf);}else{return new F(function(){return _lc(function(_lk){return new F(function(){return A1(_ld,new T2(1,_lj,_lk));});},_le);});}}else{return new F(function(){return _lc(function(_ll){return new F(function(){return A1(_ld,new T2(1,_lj,_ll));});},_le);});}};return new F(function(){return _kS(_lg);});},_lm=new T(function(){return B(unCStr("_\'"));}),_ln=function(_lo){var _lp=u_iswalnum(_lo);if(!E(_lp)){return new F(function(){return _eR(_b2,_lo,_lm);});}else{return true;}},_lq=function(_lr){return new F(function(){return _ln(E(_lr));});},_ls=new T(function(){return B(unCStr(",;()[]{}`"));}),_lt=new T(function(){return B(unCStr("=>"));}),_lu=new T2(1,_lt,_y),_lv=new T(function(){return B(unCStr("~"));}),_lw=new T2(1,_lv,_lu),_lx=new T(function(){return B(unCStr("@"));}),_ly=new T2(1,_lx,_lw),_lz=new T(function(){return B(unCStr("->"));}),_lA=new T2(1,_lz,_ly),_lB=new T(function(){return B(unCStr("<-"));}),_lC=new T2(1,_lB,_lA),_lD=new T(function(){return B(unCStr("|"));}),_lE=new T2(1,_lD,_lC),_lF=new T(function(){return B(unCStr("\\"));}),_lG=new T2(1,_lF,_lE),_lH=new T(function(){return B(unCStr("="));}),_lI=new T2(1,_lH,_lG),_lJ=new T(function(){return B(unCStr("::"));}),_lK=new T2(1,_lJ,_lI),_lL=new T(function(){return B(unCStr(".."));}),_lM=new T2(1,_lL,_lK),_lN=function(_lO){var _lP=new T(function(){return B(A1(_lO,_ca));}),_lQ=new T(function(){var _lR=new T(function(){var _lS=function(_lT){var _lU=new T(function(){return B(A1(_lO,new T1(0,_lT)));});return new T1(0,function(_lV){return (E(_lV)==39)?E(_lU):new T0(2);});};return B(_jE(_lS));}),_lW=function(_lX){var _lY=E(_lX);switch(E(_lY)){case 39:return new T0(2);case 92:return E(_lR);default:var _lZ=new T(function(){return B(A1(_lO,new T1(0,_lY)));});return new T1(0,function(_m0){return (E(_m0)==39)?E(_lZ):new T0(2);});}},_m1=new T(function(){var _m2=new T(function(){return B(_lc(_2u,_lO));}),_m3=new T(function(){var _m4=new T(function(){var _m5=new T(function(){var _m6=function(_m7){var _m8=E(_m7),_m9=u_iswalpha(_m8);return (E(_m9)==0)?(E(_m8)==95)?new T1(1,B(_bW(_lq,function(_ma){return new F(function(){return A1(_lO,new T1(3,new T2(1,_m8,_ma)));});}))):new T0(2):new T1(1,B(_bW(_lq,function(_mb){return new F(function(){return A1(_lO,new T1(3,new T2(1,_m8,_mb)));});})));};return B(_ad(new T1(0,_m6),new T(function(){return new T1(1,B(_bw(_d8,_eN,_lO)));})));}),_mc=function(_md){return (!B(_eR(_b2,_md,_eW)))?new T0(2):new T1(1,B(_bW(_eX,function(_me){var _mf=new T2(1,_md,_me);if(!B(_eR(_bb,_mf,_lM))){return new F(function(){return A1(_lO,new T1(4,_mf));});}else{return new F(function(){return A1(_lO,new T1(2,_mf));});}})));};return B(_ad(new T1(0,_mc),_m5));});return B(_ad(new T1(0,function(_mg){if(!B(_eR(_b2,_mg,_ls))){return new T0(2);}else{return new F(function(){return A1(_lO,new T1(2,new T2(1,_mg,_y)));});}}),_m4));});return B(_ad(new T1(0,function(_mh){return (E(_mh)==34)?E(_m2):new T0(2);}),_m3));});return B(_ad(new T1(0,function(_mi){return (E(_mi)==39)?E(new T1(0,_lW)):new T0(2);}),_m1));});return new F(function(){return _ad(new T1(1,function(_mj){return (E(_mj)._==0)?E(_lP):new T0(2);}),_lQ);});},_mk=0,_ml=function(_mm,_mn){var _mo=new T(function(){var _mp=new T(function(){var _mq=function(_mr){var _ms=new T(function(){var _mt=new T(function(){return B(A1(_mn,_mr));});return B(_lN(function(_mu){var _mv=E(_mu);return (_mv._==2)?(!B(_aR(_mv.a,_aQ)))?new T0(2):E(_mt):new T0(2);}));}),_mw=function(_mx){return E(_ms);};return new T1(1,function(_my){return new F(function(){return A2(_ku,_my,_mw);});});};return B(A2(_mm,_mk,_mq));});return B(_lN(function(_mz){var _mA=E(_mz);return (_mA._==2)?(!B(_aR(_mA.a,_aP)))?new T0(2):E(_mp):new T0(2);}));}),_mB=function(_mC){return E(_mo);};return function(_mD){return new F(function(){return A2(_ku,_mD,_mB);});};},_mE=function(_mF,_mG){var _mH=function(_mI){var _mJ=new T(function(){return B(A1(_mF,_mI));}),_mK=function(_mL){return new F(function(){return _ad(B(A1(_mJ,_mL)),new T(function(){return new T1(1,B(_ml(_mH,_mL)));}));});};return E(_mK);},_mM=new T(function(){return B(A1(_mF,_mG));}),_mN=function(_mO){return new F(function(){return _ad(B(A1(_mM,_mO)),new T(function(){return new T1(1,B(_ml(_mH,_mO)));}));});};return E(_mN);},_mP=function(_mQ,_mR){var _mS=function(_mT,_mU){var _mV=function(_mW){return new F(function(){return A1(_mU,new T(function(){return  -E(_mW);}));});},_mX=new T(function(){return B(_lN(function(_mY){return new F(function(){return A3(_mQ,_mY,_mT,_mV);});}));}),_mZ=function(_n0){return E(_mX);},_n1=function(_n2){return new F(function(){return A2(_ku,_n2,_mZ);});},_n3=new T(function(){return B(_lN(function(_n4){var _n5=E(_n4);if(_n5._==4){var _n6=E(_n5.a);if(!_n6._){return new F(function(){return A3(_mQ,_n5,_mT,_mU);});}else{if(E(_n6.a)==45){if(!E(_n6.b)._){return E(new T1(1,_n1));}else{return new F(function(){return A3(_mQ,_n5,_mT,_mU);});}}else{return new F(function(){return A3(_mQ,_n5,_mT,_mU);});}}}else{return new F(function(){return A3(_mQ,_n5,_mT,_mU);});}}));}),_n7=function(_n8){return E(_n3);};return new T1(1,function(_n9){return new F(function(){return A2(_ku,_n9,_n7);});});};return new F(function(){return _mE(_mS,_mR);});},_na=function(_nb){var _nc=E(_nb);if(!_nc._){var _nd=_nc.b,_ne=new T(function(){return B(_dZ(new T(function(){return B(_dF(E(_nc.a)));}),new T(function(){return B(_dw(_nd,0));},1),B(_dB(_dH,_nd))));});return new T1(1,_ne);}else{return (E(_nc.b)._==0)?(E(_nc.c)._==0)?new T1(1,new T(function(){return B(_eg(_dv,_nc.a));})):__Z:__Z;}},_nf=function(_ng,_nh){return new T0(2);},_ni=function(_nj){var _nk=E(_nj);if(_nk._==5){var _nl=B(_na(_nk.a));if(!_nl._){return E(_nf);}else{var _nm=new T(function(){return B(_fb(_nl.a));});return function(_nn,_no){return new F(function(){return A1(_no,_nm);});};}}else{return E(_nf);}},_np=function(_nq){var _nr=function(_ns){return E(new T2(3,_nq,_bn));};return new T1(1,function(_nt){return new F(function(){return A2(_ku,_nt,_nr);});});},_nu=new T(function(){return B(A3(_mP,_ni,_mk,_np));}),_nv=new T(function(){return B(unCStr("invalid key pressed"));}),_nw=function(_nx){var _ny=new T(function(){var _nz=E(_nx);return new T4(0,_nz.a,_nz.b,new T(function(){return E(_nz.c)+5;}),_nz.d);});return new T2(0,_ny,_0);},_nA=function(_nB){var _nC=new T(function(){var _nD=E(_nB);return new T4(0,_nD.a,_nD.b,new T(function(){return E(_nD.c)-5;}),_nD.d);});return new T2(0,_nC,_0);},_nE=new T(function(){return B(unCStr("Pattern match failure in do expression at breakout.hs:59:5-15"));}),_nF=new T6(0,_2e,_2f,_y,_nE,_2e,_2e),_nG=new T(function(){return B(_1H(_nF));}),_nH=new T(function(){return B(unCStr("height"));}),_nI=new T(function(){return B(unCStr("width"));}),_nJ=function(_nK){while(1){var _nL=E(_nK);if(!_nL._){_nK=new T1(1,I_fromInt(_nL.a));continue;}else{return new F(function(){return I_toString(_nL.a);});}}},_nM=function(_nN,_nO){return new F(function(){return _S(fromJSStr(B(_nJ(_nN))),_nO);});},_nP=function(_nQ,_nR){var _nS=E(_nQ);if(!_nS._){var _nT=_nS.a,_nU=E(_nR);return (_nU._==0)?_nT<_nU.a:I_compareInt(_nU.a,_nT)>0;}else{var _nV=_nS.a,_nW=E(_nR);return (_nW._==0)?I_compareInt(_nV,_nW.a)<0:I_compare(_nV,_nW.a)<0;}},_nX=new T1(0,0),_nY=function(_nZ,_o0,_o1){if(_nZ<=6){return new F(function(){return _nM(_o0,_o1);});}else{if(!B(_nP(_o0,_nX))){return new F(function(){return _nM(_o0,_o1);});}else{return new T2(1,_5V,new T(function(){return B(_S(fromJSStr(B(_nJ(_o0))),new T2(1,_5w,_o1)));}));}}},_o2=new T1(0,8),_o3=new T(function(){return B(_nY(0,_o2,_y));}),_o4=new T(function(){return B(unAppCStr("abc=",_o3));}),_o5=new T(function(){return B(_7Z(_o4,_5u));}),_o6=new T2(1,_5t,_o5),_o7=new T(function(){return B(_8u(0,7,_y));}),_o8=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_o9=new T(function(){return B(err(_o8));}),_oa=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_ob=new T(function(){return B(err(_oa));}),_oc=function(_od){return E(E(_od).b);},_oe=function(_of){return E(E(_of).a);},_og=function(_){return new F(function(){return nMV(_2e);});},_oh=new T(function(){return B(_5k(_og));}),_oi=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_oj=function(_ok,_ol,_om,_on,_oo,_op){var _oq=B(_5Y(_ok)),_or=B(_60(_oq)),_os=new T(function(){return B(_2V(_oq));}),_ot=new T(function(){return B(_8N(_or));}),_ou=new T(function(){return B(A2(_8C,_ol,_on));}),_ov=new T(function(){return B(A2(_oe,_om,_oo));}),_ow=function(_ox){return new F(function(){return A1(_ot,new T3(0,_ov,_ou,_ox));});},_oy=function(_oz){var _oA=new T(function(){var _oB=new T(function(){var _oC=__createJSFunc(2,function(_oD,_){var _oE=B(A2(E(_oz),_oD,_));return _68;}),_oF=_oC;return function(_){return new F(function(){return __app3(E(_oi),E(_ou),E(_ov),_oF);});};});return B(A1(_os,_oB));});return new F(function(){return A3(_62,_or,_oA,_ow);});},_oG=new T(function(){var _oH=new T(function(){return B(_2V(_oq));}),_oI=function(_oJ){var _oK=new T(function(){return B(A1(_oH,function(_){var _=wMV(E(_oh),new T1(1,_oJ));return new F(function(){return A(_oc,[_om,_oo,_oJ,_]);});}));});return new F(function(){return A3(_62,_or,_oK,_op);});};return B(A2(_69,_ok,_oI));});return new F(function(){return A3(_62,_or,_oG,_oy);});},_oL=function(_oM){while(1){var _oN=B((function(_oO){var _oP=E(_oO);if(!_oP._){return __Z;}else{var _oQ=_oP.b,_oR=E(_oP.a);if(!E(_oR.b)._){return new T2(1,_oR.a,new T(function(){return B(_oL(_oQ));}));}else{_oM=_oQ;return __continue;}}})(_oM));if(_oN!=__continue){return _oN;}}},_oS=new T(function(){return eval("(function(x){console.log(x);})");}),_oT=function(_oU,_oV){var _oW=function(_){var _oX=__app1(E(_oS),toJSStr(_oV));return new F(function(){return _1(_);});};return new F(function(){return A2(_2V,_oU,_oW);});},_oY=function(_,_oZ){var _p0=E(_oZ);if(!_p0._){return new F(function(){return die(_nG);});}else{var _p1=_p0.a,_p2=B(_59(_86,_o7,_)),_p3=B(A(_8P,[_3y,_2w,_p1,_nI,_])),_p4=B(_59(_86,_o6,_)),_p5=B(A(_8P,[_3y,_2w,_p1,_nI,_])),_p6=B(_59(_86,new T2(1,_5t,new T(function(){return B(_7Z(B(unAppCStr("width=",_p5)),_5u));})),_)),_p7=new T(function(){var _p8=B(_oL(B(_a3(_nu,_p5))));if(!_p8._){return E(_o9);}else{if(!E(_p8.b)._){return E(_p8.a);}else{return E(_ob);}}}),_p9=new T(function(){return B(_7Z(B(unAppCStr("canvasWidth=",new T(function(){return B(_8u(0,E(_p7),_y));}))),_5u));}),_pa=B(_59(_86,new T2(1,_5t,_p9),_)),_pb=new T(function(){return B(_7Z(B(unAppCStr("doItInt canvasWidth=",new T(function(){return B(_8u(0,E(_p7),_y));}))),_5u));}),_pc=B(_59(_86,new T2(1,_5t,_pb),_)),_pd=B(A(_8P,[_3y,_2w,_p1,_nH,_])),_pe=E(_p1),_pf=_pe.a,_pg=_pe.b,_ph=B(_4P(_pf,_pg,_96,_)),_pi=nMV(_96),_pj=_pi,_pk=function(_pl,_){var _pm=E(_pl),_pn=_pm.a,_po=_pm.b,_pp=_pm.c,_pq=_pm.d,_pr=_pm.e,_ps=function(_pt){var _pu=function(_pv){if(E(_pn)==83){if(!E(_po)){if(!E(_pp)){if(!E(_pq)){if(!E(_pr)){return new F(function(){return mMV(_pj,_nw);});}else{return new F(function(){return A3(_oT,_2w,_nv,_);});}}else{return new F(function(){return A3(_oT,_2w,_nv,_);});}}else{return new F(function(){return A3(_oT,_2w,_nv,_);});}}else{return new F(function(){return A3(_oT,_2w,_nv,_);});}}else{return new F(function(){return A3(_oT,_2w,_nv,_);});}};if(E(_pn)==68){if(!E(_po)){if(!E(_pp)){if(!E(_pq)){if(!E(_pr)){return new F(function(){return mMV(_pj,_nw);});}else{return new F(function(){return _pu(_);});}}else{return new F(function(){return _pu(_);});}}else{return new F(function(){return _pu(_);});}}else{return new F(function(){return _pu(_);});}}else{return new F(function(){return _pu(_);});}};if(E(_pn)==65){if(!E(_po)){if(!E(_pp)){if(!E(_pq)){if(!E(_pr)){return new F(function(){return mMV(_pj,_nA);});}else{return new F(function(){return _ps(_);});}}else{return new F(function(){return _ps(_);});}}else{return new F(function(){return _ps(_);});}}else{return new F(function(){return _ps(_);});}}else{return new F(function(){return _ps(_);});}},_pw=B(A(_oj,[_3z,_3y,_3p,_pe,_8z,_pk,_])),_px=B(_89(_pf,_pg,_pj,_));return _68;}},_py=new T(function(){return B(unCStr("#canvas"));}),_pz=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_pA=function(_){var _pB=__createJSFunc(0,function(_){var _pC=B(A(_2X,[_2w,_2M,_py,_])),_pD=B(_2J(_pC,0)),_pE=__app1(E(_3),_pD);if(!_pE){return new F(function(){return _oY(_,_2e);});}else{var _pF=__app1(E(_2),_pD);return new F(function(){return _oY(_,new T1(1,new T2(0,_pF,_pD)));});}}),_pG=__app2(E(_pz),"breakoutHsMain",_pB);return new F(function(){return _1(_);});},_pH=function(_){return new F(function(){return _pA(_);});};
var hasteMain = function() {B(A(_pH, [0]));};hasteMain(); breakoutMain()