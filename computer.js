#!/usr/bin/env node
"use strict";

// (function(){

const $JSRTS = {
    throw: function (x) {
        throw x;
    },
    Lazy: function (e) {
        this.js_idris_lazy_calc = e;
        this.js_idris_lazy_val = void 0;
    },
    force: function (x) {
        if (x === undefined || x.js_idris_lazy_calc === undefined) {
            return x
        } else {
            if (x.js_idris_lazy_val === undefined) {
                x.js_idris_lazy_val = x.js_idris_lazy_calc()
            }
            return x.js_idris_lazy_val
        }
    },
    prim_strSubstr: function (offset, len, str) {
        return str.substr(Math.max(0, offset), Math.max(0, len))
    }
};
$JSRTS.os = require('os');

$JSRTS.fs = require('fs');

$JSRTS.prim_systemInfo = function (index) {
    switch (index) {
        case 0:
            return "node";
        case 1:
            return $JSRTS.os.platform();
    }
    return "";
};

$JSRTS.prim_writeStr = function (x) { return process.stdout.write(x) };

$JSRTS.prim_readStr = function () {
    var ret = '';
    var b = Buffer.alloc(1024);
    var i = 0;
    while (true) {
        $JSRTS.fs.readSync(0, b, i, 1)
        if (b[i] == 10) {
            ret = b.toString('utf8', 0, i);
            break;
        }
        i++;
        if (i == b.length) {
            var nb = Buffer.alloc(b.length * 2);
            b.copy(nb)
            b = nb;
        }
    }
    return ret;
};

$JSRTS.die = function (message) {
    console.error(message);
    process.exit(-1);
};

$JSRTS.jsbn = (function () {

  // Copyright (c) 2005  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Basic JavaScript BN library - subset useful for RSA encryption.

  // Bits per digit
  var dbits;

  // JavaScript engine analysis
  var canary = 0xdeadbeefcafe;
  var j_lm = ((canary & 0xffffff) == 0xefcafe);

  // (public) Constructor
  function BigInteger(a, b, c) {
    if (a != null)
      if ("number" == typeof a) this.fromNumber(a, b, c);
      else if (b == null && "string" != typeof a) this.fromString(a, 256);
      else this.fromString(a, b);
  }

  // return new, unset BigInteger
  function nbi() { return new BigInteger(null); }

  // am: Compute w_j += (x*this_i), propagate carries,
  // c is initial carry, returns final carry.
  // c < 3*dvalue, x < 2*dvalue, this_i < dvalue
  // We need to select the fastest one that works in this environment.

  // am1: use a single mult and divide to get the high bits,
  // max digit bits should be 26 because
  // max internal value = 2*dvalue^2-2*dvalue (< 2^53)
  function am1(i, x, w, j, c, n) {
    while (--n >= 0) {
      var v = x * this[i++] + w[j] + c;
      c = Math.floor(v / 0x4000000);
      w[j++] = v & 0x3ffffff;
    }
    return c;
  }
  // am2 avoids a big mult-and-extract completely.
  // Max digit bits should be <= 30 because we do bitwise ops
  // on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
  function am2(i, x, w, j, c, n) {
    var xl = x & 0x7fff, xh = x >> 15;
    while (--n >= 0) {
      var l = this[i] & 0x7fff;
      var h = this[i++] >> 15;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff);
      c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
      w[j++] = l & 0x3fffffff;
    }
    return c;
  }
  // Alternately, set max digit bits to 28 since some
  // browsers slow down when dealing with 32-bit numbers.
  function am3(i, x, w, j, c, n) {
    var xl = x & 0x3fff, xh = x >> 14;
    while (--n >= 0) {
      var l = this[i] & 0x3fff;
      var h = this[i++] >> 14;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x3fff) << 14) + w[j] + c;
      c = (l >> 28) + (m >> 14) + xh * h;
      w[j++] = l & 0xfffffff;
    }
    return c;
  }
  var inBrowser = typeof navigator !== "undefined";
  if (inBrowser && j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
    BigInteger.prototype.am = am2;
    dbits = 30;
  }
  else if (inBrowser && j_lm && (navigator.appName != "Netscape")) {
    BigInteger.prototype.am = am1;
    dbits = 26;
  }
  else { // Mozilla/Netscape seems to prefer am3
    BigInteger.prototype.am = am3;
    dbits = 28;
  }

  BigInteger.prototype.DB = dbits;
  BigInteger.prototype.DM = ((1 << dbits) - 1);
  BigInteger.prototype.DV = (1 << dbits);

  var BI_FP = 52;
  BigInteger.prototype.FV = Math.pow(2, BI_FP);
  BigInteger.prototype.F1 = BI_FP - dbits;
  BigInteger.prototype.F2 = 2 * dbits - BI_FP;

  // Digit conversions
  var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
  var BI_RC = new Array();
  var rr, vv;
  rr = "0".charCodeAt(0);
  for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
  rr = "a".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
  rr = "A".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

  function int2char(n) { return BI_RM.charAt(n); }
  function intAt(s, i) {
    var c = BI_RC[s.charCodeAt(i)];
    return (c == null) ? -1 : c;
  }

  // (protected) copy this to r
  function bnpCopyTo(r) {
    for (var i = this.t - 1; i >= 0; --i) r[i] = this[i];
    r.t = this.t;
    r.s = this.s;
  }

  // (protected) set from integer value x, -DV <= x < DV
  function bnpFromInt(x) {
    this.t = 1;
    this.s = (x < 0) ? -1 : 0;
    if (x > 0) this[0] = x;
    else if (x < -1) this[0] = x + this.DV;
    else this.t = 0;
  }

  // return bigint initialized to value
  function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

  // (protected) set from string and radix
  function bnpFromString(s, b) {
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 256) k = 8; // byte array
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else { this.fromRadix(s, b); return; }
    this.t = 0;
    this.s = 0;
    var i = s.length, mi = false, sh = 0;
    while (--i >= 0) {
      var x = (k == 8) ? s[i] & 0xff : intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-") mi = true;
        continue;
      }
      mi = false;
      if (sh == 0)
        this[this.t++] = x;
      else if (sh + k > this.DB) {
        this[this.t - 1] |= (x & ((1 << (this.DB - sh)) - 1)) << sh;
        this[this.t++] = (x >> (this.DB - sh));
      }
      else
        this[this.t - 1] |= x << sh;
      sh += k;
      if (sh >= this.DB) sh -= this.DB;
    }
    if (k == 8 && (s[0] & 0x80) != 0) {
      this.s = -1;
      if (sh > 0) this[this.t - 1] |= ((1 << (this.DB - sh)) - 1) << sh;
    }
    this.clamp();
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) clamp off excess high words
  function bnpClamp() {
    var c = this.s & this.DM;
    while (this.t > 0 && this[this.t - 1] == c)--this.t;
  }

  // (public) return string representation in given radix
  function bnToString(b) {
    if (this.s < 0) return "-" + this.negate().toString(b);
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else return this.toRadix(b);
    var km = (1 << k) - 1, d, m = false, r = "", i = this.t;
    var p = this.DB - (i * this.DB) % k;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) > 0) { m = true; r = int2char(d); }
      while (i >= 0) {
        if (p < k) {
          d = (this[i] & ((1 << p) - 1)) << (k - p);
          d |= this[--i] >> (p += this.DB - k);
        }
        else {
          d = (this[i] >> (p -= k)) & km;
          if (p <= 0) { p += this.DB; --i; }
        }
        if (d > 0) m = true;
        if (m) r += int2char(d);
      }
    }
    return m ? r : "0";
  }

  // (public) -this
  function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this, r); return r; }

  // (public) |this|
  function bnAbs() { return (this.s < 0) ? this.negate() : this; }

  // (public) return + if this > a, - if this < a, 0 if equal
  function bnCompareTo(a) {
    var r = this.s - a.s;
    if (r != 0) return r;
    var i = this.t;
    r = i - a.t;
    if (r != 0) return (this.s < 0) ? -r : r;
    while (--i >= 0) if ((r = this[i] - a[i]) != 0) return r;
    return 0;
  }

  // returns bit length of the integer x
  function nbits(x) {
    var r = 1, t;
    if ((t = x >>> 16) != 0) { x = t; r += 16; }
    if ((t = x >> 8) != 0) { x = t; r += 8; }
    if ((t = x >> 4) != 0) { x = t; r += 4; }
    if ((t = x >> 2) != 0) { x = t; r += 2; }
    if ((t = x >> 1) != 0) { x = t; r += 1; }
    return r;
  }

  // (public) return the number of bits in "this"
  function bnBitLength() {
    if (this.t <= 0) return 0;
    return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ (this.s & this.DM));
  }

  // (protected) r = this << n*DB
  function bnpDLShiftTo(n, r) {
    var i;
    for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i];
    for (i = n - 1; i >= 0; --i) r[i] = 0;
    r.t = this.t + n;
    r.s = this.s;
  }

  // (protected) r = this >> n*DB
  function bnpDRShiftTo(n, r) {
    for (var i = n; i < this.t; ++i) r[i - n] = this[i];
    r.t = Math.max(this.t - n, 0);
    r.s = this.s;
  }

  // (protected) r = this << n
  function bnpLShiftTo(n, r) {
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << cbs) - 1;
    var ds = Math.floor(n / this.DB), c = (this.s << bs) & this.DM, i;
    for (i = this.t - 1; i >= 0; --i) {
      r[i + ds + 1] = (this[i] >> cbs) | c;
      c = (this[i] & bm) << bs;
    }
    for (i = ds - 1; i >= 0; --i) r[i] = 0;
    r[ds] = c;
    r.t = this.t + ds + 1;
    r.s = this.s;
    r.clamp();
  }

  // (protected) r = this >> n
  function bnpRShiftTo(n, r) {
    r.s = this.s;
    var ds = Math.floor(n / this.DB);
    if (ds >= this.t) { r.t = 0; return; }
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << bs) - 1;
    r[0] = this[ds] >> bs;
    for (var i = ds + 1; i < this.t; ++i) {
      r[i - ds - 1] |= (this[i] & bm) << cbs;
      r[i - ds] = this[i] >> bs;
    }
    if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
    r.t = this.t - ds;
    r.clamp();
  }

  // (protected) r = this - a
  function bnpSubTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] - a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c -= a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c -= a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c -= a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c < -1) r[i++] = this.DV + c;
    else if (c > 0) r[i++] = c;
    r.t = i;
    r.clamp();
  }

  // (protected) r = this * a, r != this,a (HAC 14.12)
  // "this" should be the larger one if appropriate.
  function bnpMultiplyTo(a, r) {
    var x = this.abs(), y = a.abs();
    var i = x.t;
    r.t = i + y.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
    r.s = 0;
    r.clamp();
    if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
  }

  // (protected) r = this^2, r != this (HAC 14.16)
  function bnpSquareTo(r) {
    var x = this.abs();
    var i = r.t = 2 * x.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < x.t - 1; ++i) {
      var c = x.am(i, x[i], r, 2 * i, 0, 1);
      if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
        r[i + x.t] -= x.DV;
        r[i + x.t + 1] = 1;
      }
    }
    if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
    r.s = 0;
    r.clamp();
  }

  // (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
  // r != q, this != m.  q or r may be null.
  function bnpDivRemTo(m, q, r) {
    var pm = m.abs();
    if (pm.t <= 0) return;
    var pt = this.abs();
    if (pt.t < pm.t) {
      if (q != null) q.fromInt(0);
      if (r != null) this.copyTo(r);
      return;
    }
    if (r == null) r = nbi();
    var y = nbi(), ts = this.s, ms = m.s;
    var nsh = this.DB - nbits(pm[pm.t - 1]);   // normalize modulus
    if (nsh > 0) { pm.lShiftTo(nsh, y); pt.lShiftTo(nsh, r); }
    else { pm.copyTo(y); pt.copyTo(r); }
    var ys = y.t;
    var y0 = y[ys - 1];
    if (y0 == 0) return;
    var yt = y0 * (1 << this.F1) + ((ys > 1) ? y[ys - 2] >> this.F2 : 0);
    var d1 = this.FV / yt, d2 = (1 << this.F1) / yt, e = 1 << this.F2;
    var i = r.t, j = i - ys, t = (q == null) ? nbi() : q;
    y.dlShiftTo(j, t);
    if (r.compareTo(t) >= 0) {
      r[r.t++] = 1;
      r.subTo(t, r);
    }
    BigInteger.ONE.dlShiftTo(ys, t);
    t.subTo(y, y);  // "negative" y so we can replace sub with am later
    while (y.t < ys) y[y.t++] = 0;
    while (--j >= 0) {
      // Estimate quotient digit
      var qd = (r[--i] == y0) ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);
      if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {   // Try it out
        y.dlShiftTo(j, t);
        r.subTo(t, r);
        while (r[i] < --qd) r.subTo(t, r);
      }
    }
    if (q != null) {
      r.drShiftTo(ys, q);
      if (ts != ms) BigInteger.ZERO.subTo(q, q);
    }
    r.t = ys;
    r.clamp();
    if (nsh > 0) r.rShiftTo(nsh, r); // Denormalize remainder
    if (ts < 0) BigInteger.ZERO.subTo(r, r);
  }

  // (public) this mod a
  function bnMod(a) {
    var r = nbi();
    this.abs().divRemTo(a, null, r);
    if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
    return r;
  }

  // Modular reduction using "classic" algorithm
  function Classic(m) { this.m = m; }
  function cConvert(x) {
    if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
    else return x;
  }
  function cRevert(x) { return x; }
  function cReduce(x) { x.divRemTo(this.m, null, x); }
  function cMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }
  function cSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  Classic.prototype.convert = cConvert;
  Classic.prototype.revert = cRevert;
  Classic.prototype.reduce = cReduce;
  Classic.prototype.mulTo = cMulTo;
  Classic.prototype.sqrTo = cSqrTo;

  // (protected) return "-1/this % 2^DB"; useful for Mont. reduction
  // justification:
  //         xy == 1 (mod m)
  //         xy =  1+km
  //   xy(2-xy) = (1+km)(1-km)
  // x[y(2-xy)] = 1-k^2m^2
  // x[y(2-xy)] == 1 (mod m^2)
  // if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
  // should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
  // JS multiply "overflows" differently from C/C++, so care is needed here.
  function bnpInvDigit() {
    if (this.t < 1) return 0;
    var x = this[0];
    if ((x & 1) == 0) return 0;
    var y = x & 3;       // y == 1/x mod 2^2
    y = (y * (2 - (x & 0xf) * y)) & 0xf; // y == 1/x mod 2^4
    y = (y * (2 - (x & 0xff) * y)) & 0xff;   // y == 1/x mod 2^8
    y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff;    // y == 1/x mod 2^16
    // last step - calculate inverse mod DV directly;
    // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
    y = (y * (2 - x * y % this.DV)) % this.DV;       // y == 1/x mod 2^dbits
    // we really want the negative inverse, and -DV < y < DV
    return (y > 0) ? this.DV - y : -y;
  }

  // Montgomery reduction
  function Montgomery(m) {
    this.m = m;
    this.mp = m.invDigit();
    this.mpl = this.mp & 0x7fff;
    this.mph = this.mp >> 15;
    this.um = (1 << (m.DB - 15)) - 1;
    this.mt2 = 2 * m.t;
  }

  // xR mod m
  function montConvert(x) {
    var r = nbi();
    x.abs().dlShiftTo(this.m.t, r);
    r.divRemTo(this.m, null, r);
    if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
    return r;
  }

  // x/R mod m
  function montRevert(x) {
    var r = nbi();
    x.copyTo(r);
    this.reduce(r);
    return r;
  }

  // x = x/R mod m (HAC 14.32)
  function montReduce(x) {
    while (x.t <= this.mt2) // pad x so am has enough room later
      x[x.t++] = 0;
    for (var i = 0; i < this.m.t; ++i) {
      // faster way of calculating u0 = x[i]*mp mod DV
      var j = x[i] & 0x7fff;
      var u0 = (j * this.mpl + (((j * this.mph + (x[i] >> 15) * this.mpl) & this.um) << 15)) & x.DM;
      // use am to combine the multiply-shift-add into one call
      j = i + this.m.t;
      x[j] += this.m.am(0, u0, x, i, 0, this.m.t);
      // propagate carry
      while (x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
    }
    x.clamp();
    x.drShiftTo(this.m.t, x);
    if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = "x^2/R mod m"; x != r
  function montSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = "xy/R mod m"; x,y != r
  function montMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Montgomery.prototype.convert = montConvert;
  Montgomery.prototype.revert = montRevert;
  Montgomery.prototype.reduce = montReduce;
  Montgomery.prototype.mulTo = montMulTo;
  Montgomery.prototype.sqrTo = montSqrTo;

  // (protected) true iff this is even
  function bnpIsEven() { return ((this.t > 0) ? (this[0] & 1) : this.s) == 0; }

  // (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
  function bnpExp(e, z) {
    if (e > 0xffffffff || e < 1) return BigInteger.ONE;
    var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e) - 1;
    g.copyTo(r);
    while (--i >= 0) {
      z.sqrTo(r, r2);
      if ((e & (1 << i)) > 0) z.mulTo(r2, g, r);
      else { var t = r; r = r2; r2 = t; }
    }
    return z.revert(r);
  }

  // (public) this^e % m, 0 <= e < 2^32
  function bnModPowInt(e, m) {
    var z;
    if (e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
    return this.exp(e, z);
  }

  // protected
  BigInteger.prototype.copyTo = bnpCopyTo;
  BigInteger.prototype.fromInt = bnpFromInt;
  BigInteger.prototype.fromString = bnpFromString;
  BigInteger.prototype.clamp = bnpClamp;
  BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
  BigInteger.prototype.drShiftTo = bnpDRShiftTo;
  BigInteger.prototype.lShiftTo = bnpLShiftTo;
  BigInteger.prototype.rShiftTo = bnpRShiftTo;
  BigInteger.prototype.subTo = bnpSubTo;
  BigInteger.prototype.multiplyTo = bnpMultiplyTo;
  BigInteger.prototype.squareTo = bnpSquareTo;
  BigInteger.prototype.divRemTo = bnpDivRemTo;
  BigInteger.prototype.invDigit = bnpInvDigit;
  BigInteger.prototype.isEven = bnpIsEven;
  BigInteger.prototype.exp = bnpExp;

  // public
  BigInteger.prototype.toString = bnToString;
  BigInteger.prototype.negate = bnNegate;
  BigInteger.prototype.abs = bnAbs;
  BigInteger.prototype.compareTo = bnCompareTo;
  BigInteger.prototype.bitLength = bnBitLength;
  BigInteger.prototype.mod = bnMod;
  BigInteger.prototype.modPowInt = bnModPowInt;

  // "constants"
  BigInteger.ZERO = nbv(0);
  BigInteger.ONE = nbv(1);

  // Copyright (c) 2005-2009  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Extended JavaScript BN functions, required for RSA private ops.

  // Version 1.1: new BigInteger("0", 10) returns "proper" zero
  // Version 1.2: square() API, isProbablePrime fix

  // (public)
  function bnClone() { var r = nbi(); this.copyTo(r); return r; }

  // (public) return value as integer
  function bnIntValue() {
    if (this.s < 0) {
      if (this.t == 1) return this[0] - this.DV;
      else if (this.t == 0) return -1;
    }
    else if (this.t == 1) return this[0];
    else if (this.t == 0) return 0;
    // assumes 16 < DB < 32
    return ((this[1] & ((1 << (32 - this.DB)) - 1)) << this.DB) | this[0];
  }

  // (public) return value as byte
  function bnByteValue() { return (this.t == 0) ? this.s : (this[0] << 24) >> 24; }

  // (public) return value as short (assumes DB>=16)
  function bnShortValue() { return (this.t == 0) ? this.s : (this[0] << 16) >> 16; }

  // (protected) return x s.t. r^x < DV
  function bnpChunkSize(r) { return Math.floor(Math.LN2 * this.DB / Math.log(r)); }

  // (public) 0 if this == 0, 1 if this > 0
  function bnSigNum() {
    if (this.s < 0) return -1;
    else if (this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
    else return 1;
  }

  // (protected) convert to radix string
  function bnpToRadix(b) {
    if (b == null) b = 10;
    if (this.signum() == 0 || b < 2 || b > 36) return "0";
    var cs = this.chunkSize(b);
    var a = Math.pow(b, cs);
    var d = nbv(a), y = nbi(), z = nbi(), r = "";
    this.divRemTo(d, y, z);
    while (y.signum() > 0) {
      r = (a + z.intValue()).toString(b).substr(1) + r;
      y.divRemTo(d, y, z);
    }
    return z.intValue().toString(b) + r;
  }

  // (protected) convert from radix string
  function bnpFromRadix(s, b) {
    this.fromInt(0);
    if (b == null) b = 10;
    var cs = this.chunkSize(b);
    var d = Math.pow(b, cs), mi = false, j = 0, w = 0;
    for (var i = 0; i < s.length; ++i) {
      var x = intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-" && this.signum() == 0) mi = true;
        continue;
      }
      w = b * w + x;
      if (++j >= cs) {
        this.dMultiply(d);
        this.dAddOffset(w, 0);
        j = 0;
        w = 0;
      }
    }
    if (j > 0) {
      this.dMultiply(Math.pow(b, j));
      this.dAddOffset(w, 0);
    }
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) alternate constructor
  function bnpFromNumber(a, b, c) {
    if ("number" == typeof b) {
      // new BigInteger(int,int,RNG)
      if (a < 2) this.fromInt(1);
      else {
        this.fromNumber(a, c);
        if (!this.testBit(a - 1))    // force MSB set
          this.bitwiseTo(BigInteger.ONE.shiftLeft(a - 1), op_or, this);
        if (this.isEven()) this.dAddOffset(1, 0); // force odd
        while (!this.isProbablePrime(b)) {
          this.dAddOffset(2, 0);
          if (this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a - 1), this);
        }
      }
    }
    else {
      // new BigInteger(int,RNG)
      var x = new Array(), t = a & 7;
      x.length = (a >> 3) + 1;
      b.nextBytes(x);
      if (t > 0) x[0] &= ((1 << t) - 1); else x[0] = 0;
      this.fromString(x, 256);
    }
  }

  // (public) convert to bigendian byte array
  function bnToByteArray() {
    var i = this.t, r = new Array();
    r[0] = this.s;
    var p = this.DB - (i * this.DB) % 8, d, k = 0;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) != (this.s & this.DM) >> p)
        r[k++] = d | (this.s << (this.DB - p));
      while (i >= 0) {
        if (p < 8) {
          d = (this[i] & ((1 << p) - 1)) << (8 - p);
          d |= this[--i] >> (p += this.DB - 8);
        }
        else {
          d = (this[i] >> (p -= 8)) & 0xff;
          if (p <= 0) { p += this.DB; --i; }
        }
        if ((d & 0x80) != 0) d |= -256;
        if (k == 0 && (this.s & 0x80) != (d & 0x80))++k;
        if (k > 0 || d != this.s) r[k++] = d;
      }
    }
    return r;
  }

  function bnEquals(a) { return (this.compareTo(a) == 0); }
  function bnMin(a) { return (this.compareTo(a) < 0) ? this : a; }
  function bnMax(a) { return (this.compareTo(a) > 0) ? this : a; }

  // (protected) r = this op a (bitwise)
  function bnpBitwiseTo(a, op, r) {
    var i, f, m = Math.min(a.t, this.t);
    for (i = 0; i < m; ++i) r[i] = op(this[i], a[i]);
    if (a.t < this.t) {
      f = a.s & this.DM;
      for (i = m; i < this.t; ++i) r[i] = op(this[i], f);
      r.t = this.t;
    }
    else {
      f = this.s & this.DM;
      for (i = m; i < a.t; ++i) r[i] = op(f, a[i]);
      r.t = a.t;
    }
    r.s = op(this.s, a.s);
    r.clamp();
  }

  // (public) this & a
  function op_and(x, y) { return x & y; }
  function bnAnd(a) { var r = nbi(); this.bitwiseTo(a, op_and, r); return r; }

  // (public) this | a
  function op_or(x, y) { return x | y; }
  function bnOr(a) { var r = nbi(); this.bitwiseTo(a, op_or, r); return r; }

  // (public) this ^ a
  function op_xor(x, y) { return x ^ y; }
  function bnXor(a) { var r = nbi(); this.bitwiseTo(a, op_xor, r); return r; }

  // (public) this & ~a
  function op_andnot(x, y) { return x & ~y; }
  function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a, op_andnot, r); return r; }

  // (public) ~this
  function bnNot() {
    var r = nbi();
    for (var i = 0; i < this.t; ++i) r[i] = this.DM & ~this[i];
    r.t = this.t;
    r.s = ~this.s;
    return r;
  }

  // (public) this << n
  function bnShiftLeft(n) {
    var r = nbi();
    if (n < 0) this.rShiftTo(-n, r); else this.lShiftTo(n, r);
    return r;
  }

  // (public) this >> n
  function bnShiftRight(n) {
    var r = nbi();
    if (n < 0) this.lShiftTo(-n, r); else this.rShiftTo(n, r);
    return r;
  }

  // return index of lowest 1-bit in x, x < 2^31
  function lbit(x) {
    if (x == 0) return -1;
    var r = 0;
    if ((x & 0xffff) == 0) { x >>= 16; r += 16; }
    if ((x & 0xff) == 0) { x >>= 8; r += 8; }
    if ((x & 0xf) == 0) { x >>= 4; r += 4; }
    if ((x & 3) == 0) { x >>= 2; r += 2; }
    if ((x & 1) == 0)++r;
    return r;
  }

  // (public) returns index of lowest 1-bit (or -1 if none)
  function bnGetLowestSetBit() {
    for (var i = 0; i < this.t; ++i)
      if (this[i] != 0) return i * this.DB + lbit(this[i]);
    if (this.s < 0) return this.t * this.DB;
    return -1;
  }

  // return number of 1 bits in x
  function cbit(x) {
    var r = 0;
    while (x != 0) { x &= x - 1; ++r; }
    return r;
  }

  // (public) return number of set bits
  function bnBitCount() {
    var r = 0, x = this.s & this.DM;
    for (var i = 0; i < this.t; ++i) r += cbit(this[i] ^ x);
    return r;
  }

  // (public) true iff nth bit is set
  function bnTestBit(n) {
    var j = Math.floor(n / this.DB);
    if (j >= this.t) return (this.s != 0);
    return ((this[j] & (1 << (n % this.DB))) != 0);
  }

  // (protected) this op (1<<n)
  function bnpChangeBit(n, op) {
    var r = BigInteger.ONE.shiftLeft(n);
    this.bitwiseTo(r, op, r);
    return r;
  }

  // (public) this | (1<<n)
  function bnSetBit(n) { return this.changeBit(n, op_or); }

  // (public) this & ~(1<<n)
  function bnClearBit(n) { return this.changeBit(n, op_andnot); }

  // (public) this ^ (1<<n)
  function bnFlipBit(n) { return this.changeBit(n, op_xor); }

  // (protected) r = this + a
  function bnpAddTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] + a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c += a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c += a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c > 0) r[i++] = c;
    else if (c < -1) r[i++] = this.DV + c;
    r.t = i;
    r.clamp();
  }

  // (public) this + a
  function bnAdd(a) { var r = nbi(); this.addTo(a, r); return r; }

  // (public) this - a
  function bnSubtract(a) { var r = nbi(); this.subTo(a, r); return r; }

  // (public) this * a
  function bnMultiply(a) { var r = nbi(); this.multiplyTo(a, r); return r; }

  // (public) this^2
  function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

  // (public) this / a
  function bnDivide(a) { var r = nbi(); this.divRemTo(a, r, null); return r; }

  // (public) this % a
  function bnRemainder(a) { var r = nbi(); this.divRemTo(a, null, r); return r; }

  // (public) [this/a,this%a]
  function bnDivideAndRemainder(a) {
    var q = nbi(), r = nbi();
    this.divRemTo(a, q, r);
    return new Array(q, r);
  }

  // (protected) this *= n, this >= 0, 1 < n < DV
  function bnpDMultiply(n) {
    this[this.t] = this.am(0, n - 1, this, 0, 0, this.t);
    ++this.t;
    this.clamp();
  }

  // (protected) this += n << w words, this >= 0
  function bnpDAddOffset(n, w) {
    if (n == 0) return;
    while (this.t <= w) this[this.t++] = 0;
    this[w] += n;
    while (this[w] >= this.DV) {
      this[w] -= this.DV;
      if (++w >= this.t) this[this.t++] = 0;
      ++this[w];
    }
  }

  // A "null" reducer
  function NullExp() { }
  function nNop(x) { return x; }
  function nMulTo(x, y, r) { x.multiplyTo(y, r); }
  function nSqrTo(x, r) { x.squareTo(r); }

  NullExp.prototype.convert = nNop;
  NullExp.prototype.revert = nNop;
  NullExp.prototype.mulTo = nMulTo;
  NullExp.prototype.sqrTo = nSqrTo;

  // (public) this^e
  function bnPow(e) { return this.exp(e, new NullExp()); }

  // (protected) r = lower n words of "this * a", a.t <= n
  // "this" should be the larger one if appropriate.
  function bnpMultiplyLowerTo(a, n, r) {
    var i = Math.min(this.t + a.t, n);
    r.s = 0; // assumes a,this >= 0
    r.t = i;
    while (i > 0) r[--i] = 0;
    var j;
    for (j = r.t - this.t; i < j; ++i) r[i + this.t] = this.am(0, a[i], r, i, 0, this.t);
    for (j = Math.min(a.t, n); i < j; ++i) this.am(0, a[i], r, i, 0, n - i);
    r.clamp();
  }

  // (protected) r = "this * a" without lower n words, n > 0
  // "this" should be the larger one if appropriate.
  function bnpMultiplyUpperTo(a, n, r) {
    --n;
    var i = r.t = this.t + a.t - n;
    r.s = 0; // assumes a,this >= 0
    while (--i >= 0) r[i] = 0;
    for (i = Math.max(n - this.t, 0); i < a.t; ++i)
      r[this.t + i - n] = this.am(n - i, a[i], r, 0, 0, this.t + i - n);
    r.clamp();
    r.drShiftTo(1, r);
  }

  // Barrett modular reduction
  function Barrett(m) {
    // setup Barrett
    this.r2 = nbi();
    this.q3 = nbi();
    BigInteger.ONE.dlShiftTo(2 * m.t, this.r2);
    this.mu = this.r2.divide(m);
    this.m = m;
  }

  function barrettConvert(x) {
    if (x.s < 0 || x.t > 2 * this.m.t) return x.mod(this.m);
    else if (x.compareTo(this.m) < 0) return x;
    else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
  }

  function barrettRevert(x) { return x; }

  // x = x mod m (HAC 14.42)
  function barrettReduce(x) {
    x.drShiftTo(this.m.t - 1, this.r2);
    if (x.t > this.m.t + 1) { x.t = this.m.t + 1; x.clamp(); }
    this.mu.multiplyUpperTo(this.r2, this.m.t + 1, this.q3);
    this.m.multiplyLowerTo(this.q3, this.m.t + 1, this.r2);
    while (x.compareTo(this.r2) < 0) x.dAddOffset(1, this.m.t + 1);
    x.subTo(this.r2, x);
    while (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = x^2 mod m; x != r
  function barrettSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = x*y mod m; x,y != r
  function barrettMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Barrett.prototype.convert = barrettConvert;
  Barrett.prototype.revert = barrettRevert;
  Barrett.prototype.reduce = barrettReduce;
  Barrett.prototype.mulTo = barrettMulTo;
  Barrett.prototype.sqrTo = barrettSqrTo;

  // (public) this^e % m (HAC 14.85)
  function bnModPow(e, m) {
    var i = e.bitLength(), k, r = nbv(1), z;
    if (i <= 0) return r;
    else if (i < 18) k = 1;
    else if (i < 48) k = 3;
    else if (i < 144) k = 4;
    else if (i < 768) k = 5;
    else k = 6;
    if (i < 8)
      z = new Classic(m);
    else if (m.isEven())
      z = new Barrett(m);
    else
      z = new Montgomery(m);

    // precomputation
    var g = new Array(), n = 3, k1 = k - 1, km = (1 << k) - 1;
    g[1] = z.convert(this);
    if (k > 1) {
      var g2 = nbi();
      z.sqrTo(g[1], g2);
      while (n <= km) {
        g[n] = nbi();
        z.mulTo(g2, g[n - 2], g[n]);
        n += 2;
      }
    }

    var j = e.t - 1, w, is1 = true, r2 = nbi(), t;
    i = nbits(e[j]) - 1;
    while (j >= 0) {
      if (i >= k1) w = (e[j] >> (i - k1)) & km;
      else {
        w = (e[j] & ((1 << (i + 1)) - 1)) << (k1 - i);
        if (j > 0) w |= e[j - 1] >> (this.DB + i - k1);
      }

      n = k;
      while ((w & 1) == 0) { w >>= 1; --n; }
      if ((i -= n) < 0) { i += this.DB; --j; }
      if (is1) {    // ret == 1, don't bother squaring or multiplying it
        g[w].copyTo(r);
        is1 = false;
      }
      else {
        while (n > 1) { z.sqrTo(r, r2); z.sqrTo(r2, r); n -= 2; }
        if (n > 0) z.sqrTo(r, r2); else { t = r; r = r2; r2 = t; }
        z.mulTo(r2, g[w], r);
      }

      while (j >= 0 && (e[j] & (1 << i)) == 0) {
        z.sqrTo(r, r2); t = r; r = r2; r2 = t;
        if (--i < 0) { i = this.DB - 1; --j; }
      }
    }
    return z.revert(r);
  }

  // (public) gcd(this,a) (HAC 14.54)
  function bnGCD(a) {
    var x = (this.s < 0) ? this.negate() : this.clone();
    var y = (a.s < 0) ? a.negate() : a.clone();
    if (x.compareTo(y) < 0) { var t = x; x = y; y = t; }
    var i = x.getLowestSetBit(), g = y.getLowestSetBit();
    if (g < 0) return x;
    if (i < g) g = i;
    if (g > 0) {
      x.rShiftTo(g, x);
      y.rShiftTo(g, y);
    }
    while (x.signum() > 0) {
      if ((i = x.getLowestSetBit()) > 0) x.rShiftTo(i, x);
      if ((i = y.getLowestSetBit()) > 0) y.rShiftTo(i, y);
      if (x.compareTo(y) >= 0) {
        x.subTo(y, x);
        x.rShiftTo(1, x);
      }
      else {
        y.subTo(x, y);
        y.rShiftTo(1, y);
      }
    }
    if (g > 0) y.lShiftTo(g, y);
    return y;
  }

  // (protected) this % n, n < 2^26
  function bnpModInt(n) {
    if (n <= 0) return 0;
    var d = this.DV % n, r = (this.s < 0) ? n - 1 : 0;
    if (this.t > 0)
      if (d == 0) r = this[0] % n;
      else for (var i = this.t - 1; i >= 0; --i) r = (d * r + this[i]) % n;
    return r;
  }

  // (public) 1/this % m (HAC 14.61)
  function bnModInverse(m) {
    var ac = m.isEven();
    if ((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
    var u = m.clone(), v = this.clone();
    var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
    while (u.signum() != 0) {
      while (u.isEven()) {
        u.rShiftTo(1, u);
        if (ac) {
          if (!a.isEven() || !b.isEven()) { a.addTo(this, a); b.subTo(m, b); }
          a.rShiftTo(1, a);
        }
        else if (!b.isEven()) b.subTo(m, b);
        b.rShiftTo(1, b);
      }
      while (v.isEven()) {
        v.rShiftTo(1, v);
        if (ac) {
          if (!c.isEven() || !d.isEven()) { c.addTo(this, c); d.subTo(m, d); }
          c.rShiftTo(1, c);
        }
        else if (!d.isEven()) d.subTo(m, d);
        d.rShiftTo(1, d);
      }
      if (u.compareTo(v) >= 0) {
        u.subTo(v, u);
        if (ac) a.subTo(c, a);
        b.subTo(d, b);
      }
      else {
        v.subTo(u, v);
        if (ac) c.subTo(a, c);
        d.subTo(b, d);
      }
    }
    if (v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
    if (d.compareTo(m) >= 0) return d.subtract(m);
    if (d.signum() < 0) d.addTo(m, d); else return d;
    if (d.signum() < 0) return d.add(m); else return d;
  }

  var lowprimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997];
  var lplim = (1 << 26) / lowprimes[lowprimes.length - 1];

  // (public) test primality with certainty >= 1-.5^t
  function bnIsProbablePrime(t) {
    var i, x = this.abs();
    if (x.t == 1 && x[0] <= lowprimes[lowprimes.length - 1]) {
      for (i = 0; i < lowprimes.length; ++i)
        if (x[0] == lowprimes[i]) return true;
      return false;
    }
    if (x.isEven()) return false;
    i = 1;
    while (i < lowprimes.length) {
      var m = lowprimes[i], j = i + 1;
      while (j < lowprimes.length && m < lplim) m *= lowprimes[j++];
      m = x.modInt(m);
      while (i < j) if (m % lowprimes[i++] == 0) return false;
    }
    return x.millerRabin(t);
  }

  // (protected) true if probably prime (HAC 4.24, Miller-Rabin)
  function bnpMillerRabin(t) {
    var n1 = this.subtract(BigInteger.ONE);
    var k = n1.getLowestSetBit();
    if (k <= 0) return false;
    var r = n1.shiftRight(k);
    t = (t + 1) >> 1;
    if (t > lowprimes.length) t = lowprimes.length;
    var a = nbi();
    for (var i = 0; i < t; ++i) {
      //Pick bases at random, instead of starting at 2
      a.fromInt(lowprimes[Math.floor(Math.random() * lowprimes.length)]);
      var y = a.modPow(r, this);
      if (y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
        var j = 1;
        while (j++ < k && y.compareTo(n1) != 0) {
          y = y.modPowInt(2, this);
          if (y.compareTo(BigInteger.ONE) == 0) return false;
        }
        if (y.compareTo(n1) != 0) return false;
      }
    }
    return true;
  }

  // protected
  BigInteger.prototype.chunkSize = bnpChunkSize;
  BigInteger.prototype.toRadix = bnpToRadix;
  BigInteger.prototype.fromRadix = bnpFromRadix;
  BigInteger.prototype.fromNumber = bnpFromNumber;
  BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
  BigInteger.prototype.changeBit = bnpChangeBit;
  BigInteger.prototype.addTo = bnpAddTo;
  BigInteger.prototype.dMultiply = bnpDMultiply;
  BigInteger.prototype.dAddOffset = bnpDAddOffset;
  BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
  BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
  BigInteger.prototype.modInt = bnpModInt;
  BigInteger.prototype.millerRabin = bnpMillerRabin;

  // public
  BigInteger.prototype.clone = bnClone;
  BigInteger.prototype.intValue = bnIntValue;
  BigInteger.prototype.byteValue = bnByteValue;
  BigInteger.prototype.shortValue = bnShortValue;
  BigInteger.prototype.signum = bnSigNum;
  BigInteger.prototype.toByteArray = bnToByteArray;
  BigInteger.prototype.equals = bnEquals;
  BigInteger.prototype.min = bnMin;
  BigInteger.prototype.max = bnMax;
  BigInteger.prototype.and = bnAnd;
  BigInteger.prototype.or = bnOr;
  BigInteger.prototype.xor = bnXor;
  BigInteger.prototype.andNot = bnAndNot;
  BigInteger.prototype.not = bnNot;
  BigInteger.prototype.shiftLeft = bnShiftLeft;
  BigInteger.prototype.shiftRight = bnShiftRight;
  BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
  BigInteger.prototype.bitCount = bnBitCount;
  BigInteger.prototype.testBit = bnTestBit;
  BigInteger.prototype.setBit = bnSetBit;
  BigInteger.prototype.clearBit = bnClearBit;
  BigInteger.prototype.flipBit = bnFlipBit;
  BigInteger.prototype.add = bnAdd;
  BigInteger.prototype.subtract = bnSubtract;
  BigInteger.prototype.multiply = bnMultiply;
  BigInteger.prototype.divide = bnDivide;
  BigInteger.prototype.remainder = bnRemainder;
  BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
  BigInteger.prototype.modPow = bnModPow;
  BigInteger.prototype.modInverse = bnModInverse;
  BigInteger.prototype.pow = bnPow;
  BigInteger.prototype.gcd = bnGCD;
  BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

  // JSBN-specific extension
  BigInteger.prototype.square = bnSquare;

  // Expose the Barrett function
  BigInteger.prototype.Barrett = Barrett

  // BigInteger interfaces not implemented in jsbn:

  // BigInteger(int signum, byte[] magnitude)
  // double doubleValue()
  // float floatValue()
  // int hashCode()
  // long longValue()
  // static BigInteger valueOf(long val)

  // Random number generator - requires a PRNG backend, e.g. prng4.js

  // For best results, put code like
  // <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
  // in your main HTML document.

  var rng_state;
  var rng_pool;
  var rng_pptr;

  // Mix in a 32-bit integer into the pool
  function rng_seed_int(x) {
    rng_pool[rng_pptr++] ^= x & 255;
    rng_pool[rng_pptr++] ^= (x >> 8) & 255;
    rng_pool[rng_pptr++] ^= (x >> 16) & 255;
    rng_pool[rng_pptr++] ^= (x >> 24) & 255;
    if (rng_pptr >= rng_psize) rng_pptr -= rng_psize;
  }

  // Mix in the current time (w/milliseconds) into the pool
  function rng_seed_time() {
    rng_seed_int(new Date().getTime());
  }

  // Initialize the pool with junk if needed.
  if (rng_pool == null) {
    rng_pool = new Array();
    rng_pptr = 0;
    var t;
    if (typeof window !== "undefined" && window.crypto) {
      if (window.crypto.getRandomValues) {
        // Use webcrypto if available
        var ua = new Uint8Array(32);
        window.crypto.getRandomValues(ua);
        for (t = 0; t < 32; ++t)
          rng_pool[rng_pptr++] = ua[t];
      }
      else if (navigator.appName == "Netscape" && navigator.appVersion < "5") {
        // Extract entropy (256 bits) from NS4 RNG if available
        var z = window.crypto.random(32);
        for (t = 0; t < z.length; ++t)
          rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
      }
    }
    while (rng_pptr < rng_psize) {  // extract some randomness from Math.random()
      t = Math.floor(65536 * Math.random());
      rng_pool[rng_pptr++] = t >>> 8;
      rng_pool[rng_pptr++] = t & 255;
    }
    rng_pptr = 0;
    rng_seed_time();
    //rng_seed_int(window.screenX);
    //rng_seed_int(window.screenY);
  }

  function rng_get_byte() {
    if (rng_state == null) {
      rng_seed_time();
      rng_state = prng_newstate();
      rng_state.init(rng_pool);
      for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr)
        rng_pool[rng_pptr] = 0;
      rng_pptr = 0;
      //rng_pool = null;
    }
    // TODO: allow reseeding after first request
    return rng_state.next();
  }

  function rng_get_bytes(ba) {
    var i;
    for (i = 0; i < ba.length; ++i) ba[i] = rng_get_byte();
  }

  function SecureRandom() { }

  SecureRandom.prototype.nextBytes = rng_get_bytes;

  // prng4.js - uses Arcfour as a PRNG

  function Arcfour() {
    this.i = 0;
    this.j = 0;
    this.S = new Array();
  }

  // Initialize arcfour context from key, an array of ints, each from [0..255]
  function ARC4init(key) {
    var i, j, t;
    for (i = 0; i < 256; ++i)
      this.S[i] = i;
    j = 0;
    for (i = 0; i < 256; ++i) {
      j = (j + this.S[i] + key[i % key.length]) & 255;
      t = this.S[i];
      this.S[i] = this.S[j];
      this.S[j] = t;
    }
    this.i = 0;
    this.j = 0;
  }

  function ARC4next() {
    var t;
    this.i = (this.i + 1) & 255;
    this.j = (this.j + this.S[this.i]) & 255;
    t = this.S[this.i];
    this.S[this.i] = this.S[this.j];
    this.S[this.j] = t;
    return this.S[(t + this.S[this.i]) & 255];
  }

  Arcfour.prototype.init = ARC4init;
  Arcfour.prototype.next = ARC4next;

  // Plug in your RNG constructor here
  function prng_newstate() {
    return new Arcfour();
  }

  // Pool size must be a multiple of 4 and greater than 32.
  // An array of bytes the size of the pool will be passed to init()
  var rng_psize = 256;

  return {
    BigInteger: BigInteger,
    SecureRandom: SecureRandom
  };

}).call(this);



function $partial_5_6$io_95_bind(x1, x2, x3, x4, x5){
    return (function(x6){
        return io_95_bind(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_0_2$Computer__Example1__backward(){
    return (function(x1){
        return (function(x2){
            return Computer__Example1__backward(x1, x2);
        });
    });
}

function $partial_8_9$Computer__Computer__compute_39_(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return Computer__Computer__compute_39_(x1, x2, x3, x4, x5, x6, x7, x8, x9);
    });
}

function $partial_13_14$GraphFunctor__GraphEmbedding__extractMorphism(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13){
    return (function(x14){
        return GraphFunctor__GraphEmbedding__extractMorphism(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14);
    });
}

function $partial_0_2$Computer__Example1__forward(){
    return (function(x1){
        return (function(x2){
            return Computer__Example1__forward(x1, x2);
        });
    });
}

function $partial_1_2$Typedefs__Typedefs__shiftVars(x1){
    return (function(x2){
        return Typedefs__Typedefs__shiftVars(x1, x2);
    });
}

function $partial_2_4$Monad__VerifiedMonadAsMonad__verifiedMonadMultiplication(x1, x2){
    return (function(x3){
        return (function(x4){
            return Monad__VerifiedMonadAsMonad__verifiedMonadMultiplication(x1, x2, x3, x4);
        });
    });
}

function $partial_2_3$Monad__VerifiedMonadAsMonad__verifiedMonadUnit(x1, x2){
    return (function(x3){
        return Monad__VerifiedMonadAsMonad__verifiedMonadUnit(x1, x2, x3);
    });
}

function $partial_2_3$Typedefs__Typedefs___123_ap_95_0_125_(x1, x2){
    return (function(x3){
        return Typedefs__Typedefs___123_ap_95_0_125_(x1, x2, x3);
    });
}

function $partial_2_3$Typedefs__Typedefs___123_ap_95_1_125_(x1, x2){
    return (function(x3){
        return Typedefs__Typedefs___123_ap_95_1_125_(x1, x2, x3);
    });
}

function $partial_0_1$Computer__Example1___123_applyReflect_39__95_4_125_(){
    return (function(x1){
        return Computer__Example1___123_applyReflect_39__95_4_125_(x1);
    });
}

function $partial_1_4$GraphFunctor__GraphEmbedding___123_assembleElemM_95_6_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return GraphFunctor__GraphEmbedding___123_assembleElemM_95_6_125_(x1, x2, x3, x4);
            });
        });
    });
}

function $partial_2_5$GraphFunctor__GraphEmbedding___123_assembleElemM_95_7_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return GraphFunctor__GraphEmbedding___123_assembleElemM_95_7_125_(x1, x2, x3, x4, x5);
            });
        });
    });
}

function $partial_2_3$GraphFunctor__GraphEmbedding___123_assembleElemM_95_8_125_(x1, x2){
    return (function(x3){
        return GraphFunctor__GraphEmbedding___123_assembleElemM_95_8_125_(x1, x2, x3);
    });
}

function $partial_3_4$GraphFunctor__GraphEmbedding___123_assembleElemM_95_9_125_(x1, x2, x3){
    return (function(x4){
        return GraphFunctor__GraphEmbedding___123_assembleElemM_95_9_125_(x1, x2, x3, x4);
    });
}

function $partial_0_3$GraphFunctor__GraphEmbedding___123_assembleElemM_95_10_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return GraphFunctor__GraphEmbedding___123_assembleElemM_95_10_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_2$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_11_125_(){
    return (function(x1){
        return (function(x2){
            return GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_11_125_(x1, x2);
        });
    });
}

function $partial_0_6$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_12_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return (function(x5){
                        return (function(x6){
                            return GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_12_125_(x1, x2, x3, x4, x5, x6);
                        });
                    });
                });
            });
        });
    });
}

function $partial_1_2$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_13_125_(x1){
    return (function(x2){
        return GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_13_125_(x1, x2);
    });
}

function $partial_1_6$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_16_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return (function(x6){
                        return GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_16_125_(x1, x2, x3, x4, x5, x6);
                    });
                });
            });
        });
    });
}

function $partial_2_3$Computer__Computer___123_compute_39__95_17_125_(x1, x2){
    return (function(x3){
        return Computer__Computer___123_compute_39__95_17_125_(x1, x2, x3);
    });
}

function $partial_0_2$Computer__Computer___123_compute_39__95_18_125_(){
    return (function(x1){
        return (function(x2){
            return Computer__Computer___123_compute_39__95_18_125_(x1, x2);
        });
    });
}

function $partial_0_4$Computer__Computer___123_compute_39__95_19_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Computer__Computer___123_compute_39__95_19_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$Computer__Computer___123_compute_39__95_20_125_(){
    return (function(x1){
        return (function(x2){
            return Computer__Computer___123_compute_39__95_20_125_(x1, x2);
        });
    });
}

function $partial_0_1$Computer__Computer___123_compute_39__95_22_125_(){
    return (function(x1){
        return Computer__Computer___123_compute_39__95_22_125_(x1);
    });
}

function $partial_3_5$Computer__Computer___123_compute_39__95_23_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Computer__Computer___123_compute_39__95_23_125_(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_2_5$Free__FreeFunctor___123_freeFunctor_95_24_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return Free__FreeFunctor___123_freeFunctor_95_24_125_(x1, x2, x3, x4, x5);
            });
        });
    });
}

function $partial_2_3$Basic__Functor___123_functorComposition_95_25_125_(x1, x2){
    return (function(x3){
        return Basic__Functor___123_functorComposition_95_25_125_(x1, x2, x3);
    });
}

function $partial_2_5$Basic__Functor___123_functorComposition_95_26_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return Basic__Functor___123_functorComposition_95_26_125_(x1, x2, x3, x4, x5);
            });
        });
    });
}

function $partial_1_4$Idris__FunctorAsCFunctor___123_functorToCFunctor_95_27_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return Idris__FunctorAsCFunctor___123_functorToCFunctor_95_27_125_(x1, x2, x3, x4);
            });
        });
    });
}

function $partial_0_3$Monad__IOMonad___123_ioMonad_95_28_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Monad__IOMonad___123_ioMonad_95_28_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Monad__IOMonad___123_ioMonad_95_29_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Monad__IOMonad___123_ioMonad_95_29_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_5$Monad__IOMonad___123_ioMonad_95_31_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return (function(x5){
                        return Monad__IOMonad___123_ioMonad_95_31_125_(x1, x2, x3, x4, x5);
                    });
                });
            });
        });
    });
}

function $partial_2_7$Monad__KleisliCategory___123_kleisliCategory_95_32_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return (function(x6){
                    return (function(x7){
                        return Monad__KleisliCategory___123_kleisliCategory_95_32_125_(x1, x2, x3, x4, x5, x6, x7);
                    });
                });
            });
        });
    });
}

function $partial_0_1$Typedefs__Typedefs___123_shiftVars_95_33_125_(){
    return (function(x1){
        return Typedefs__Typedefs___123_shiftVars_95_33_125_(x1);
    });
}

function $partial_0_1$Monad__VerifiedMonadAsMonad___123_verifiedMonadMultiplication_95_34_125_(){
    return (function(x1){
        return Monad__VerifiedMonadAsMonad___123_verifiedMonadMultiplication_95_34_125_(x1);
    });
}

function $partial_0_2$Decidable__Equality___123_Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0_95_lam_95_36_125_(){
    return (function(x1){
        return (function(x2){
            return Decidable__Equality___123_Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0_95_lam_95_36_125_(x1, x2);
        });
    });
}

const $HC_0_0$MkFFI = ({type: 0});
const $HC_0_0$MkUnit = ({type: 0});
const $HC_0_0$Refl = ({type: 0});
const $HC_0_0$TheWorld = ({type: 0});
const $HC_0_65558$Unit = ({type: 65558});
function $HC_3_1$Free__Path___58__58_($1, $2, $3){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_1$Data__Vect___58__58_($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_65669$Prelude__Either__Either($1, $2){
    this.type = 65669;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_65669$Prelude__Either__Either1() {
    return function ($1) {
        return function($2){
            return new $HC_2_65669$Prelude__Either__Either($1, $2);
        }
    }
}

function $HC_1_1$Data__Fin__FS($1){
    this.type = 1;
    this.$1 = $1;
}

const $HC_0_0$Data__Fin__FZ = ({type: 0});
const $HC_0_0$Data__Vect__Here = ({type: 0});
function $HC_1_1$Prelude__Maybe__Just($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_0$Prelude__Either__Left($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_2_0$Basic__Functor__MkCFunctor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Basic__Category__MkCategory($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Builtins__MkDPair($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Free__FreeFunctor__MkGraphEmbedding($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Monad__Monad__MkMonad($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_0$Builtins__MkPair($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Free__Path__Nil = ({type: 0});
const $HC_0_0$Data__Vect__Nil = ({type: 0});
const $HC_0_1$Prelude__Basics__No = ({type: 1});
const $HC_0_0$Prelude__Maybe__Nothing = ({type: 0});
function $HC_2_65595$Builtins__Pair($1, $2){
    this.type = 65595;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_65595$Builtins__Pair1(){
    return (function(x1){
        return (function(x2){
            return new $HC_2_65595$Builtins__Pair(x1, x2);
        });
    });
}

function $HC_1_1$Prelude__Either__Right($1){
    this.type = 1;
    this.$1 = $1;
}

const $HC_0_1$Typedefs__Typedefs__T1 = ({type: 1});
function $HC_3_6$Typedefs__Typedefs__TApp($1, $2, $3){
    this.type = 6;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_5$Typedefs__Typedefs__TMu($1, $2){
    this.type = 5;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_3$Typedefs__Typedefs__TProd($1, $2){
    this.type = 3;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_2$Typedefs__Typedefs__TSum($1, $2){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_4$Typedefs__Typedefs__TVar($1){
    this.type = 4;
    this.$1 = $1;
}

function $HC_1_1$Data__Vect__There($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_0$Prelude__Basics__Yes($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_2_0$Prelude__Applicative__Alternative_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Prelude__Monad__Monad_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Interfaces__Verified__VerifiedApplicative_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Interfaces__Verified__VerifiedMonad_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

// io_bind

function io_95_bind($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_k, $_5_w){
    return $_4_k($_3_arg($_5_w))($_5_w);
}

// Typedefs.Typedefs.Tnary

function Typedefs__Typedefs__Tnary($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    const $cg$3 = $_3_arg.$2;
    const $cg$5 = $cg$3.$2;
    if(($cg$5.type === 1)) {
        return $_4_arg(Typedefs__Typedefs__Ty($_0_arg, $_2_arg, $_3_arg.$1))(Typedefs__Typedefs__Tnary($_0_arg, null, $_2_arg, new $HC_2_1$Data__Vect___58__58_($cg$3.$1, new $HC_2_1$Data__Vect___58__58_($cg$5.$1, $cg$5.$2)), $_4_arg));
    } else {
        return $_4_arg(Typedefs__Typedefs__Ty($_0_arg, $_2_arg, $_3_arg.$1))(Typedefs__Typedefs__Ty($_0_arg, $_2_arg, $cg$3.$1));
    }
}

// Typedefs.Typedefs.Ty

function Typedefs__Typedefs__Ty($_0_arg, $_1_arg, $_2_arg){
    let $tco$$_2_arg = $_2_arg;
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            return $HC_0_65558$Unit;
        } else if(($_2_arg.type === 6)) {
            let $cg$2 = null;
            null;
            $tco$$_2_arg = Typedefs__Typedefs__ap($_0_arg, null, $cg$2, $_2_arg.$3);
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = $tco$$_2_arg;
        } else if(($_2_arg.type === 5)) {
            return null;
        } else if(($_2_arg.type === 3)) {
            return Typedefs__Typedefs__Tnary($_0_arg, null, $_1_arg, $_2_arg.$2, new $HC_2_65595$Builtins__Pair1());
        } else if(($_2_arg.type === 2)) {
            return Typedefs__Typedefs__Tnary($_0_arg, null, $_1_arg, $_2_arg.$2, new $HC_2_65669$Prelude__Either__Either1());
        } else {
            return Data__Vect__index(null, null, $_2_arg.$1, $_1_arg);
        }
    }
}

// Typedefs.Typedefs.ap

function Typedefs__Typedefs__ap($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    let $tco$$_3_arg = $_3_arg;
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            return $_2_arg;
        } else if(($_2_arg.type === 6)) {
            let $cg$2 = null;
            null;
            $tco$$_3_arg = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs__Typedefs___123_ap_95_0_125_($_0_arg, $_3_arg), $_2_arg.$3);
            $_0_arg = $_0_arg;
            $_1_arg = null;
            $_2_arg = $cg$2;
            $_3_arg = $tco$$_3_arg;
        } else if(($_2_arg.type === 5)) {
            return new $HC_2_5$Typedefs__Typedefs__TMu($_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs__Typedefs___123_ap_95_1_125_($_0_arg, $_3_arg), $_2_arg.$2));
        } else if(($_2_arg.type === 3)) {
            return new $HC_2_3$Typedefs__Typedefs__TProd($_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs__Typedefs___123_ap_95_0_125_($_0_arg, $_3_arg), $_2_arg.$2));
        } else if(($_2_arg.type === 2)) {
            return new $HC_2_2$Typedefs__Typedefs__TSum($_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Typedefs__Typedefs___123_ap_95_0_125_($_0_arg, $_3_arg), $_2_arg.$2));
        } else {
            return Data__Vect__index(null, null, $_2_arg.$1, $_3_arg);
        }
    }
}

// Computer.Example1.applyReflect'

function Computer__Example1__applyReflect_39_(){
    return $partial_8_9$Computer__Computer__compute_39_(
        null,
        
        Computer__Example1__twoLoopsGraph(),
        
        $HC_0_0$MkUnit,
        $HC_0_0$MkUnit,
        
        $partial_0_1$Computer__Example1___123_applyReflect_39__95_4_125_(),
        
        new $HC_2_1$Data__Vect___58__58_(
            Computer__Example1__rgbTypedef(),
            $HC_0_0$Data__Vect__Nil
        ),
        
        new $HC_2_1$Data__Vect___58__58_(
            new $HC_2_0$Builtins__MkDPair(
                Computer__Example1__rgbTypedef(),
                new $HC_2_0$Builtins__MkDPair(
                    Computer__Example1__rgbTypedef(),
                    $partial_0_2$Computer__Example1__forward()
                )
            ),
            
            new $HC_2_1$Data__Vect___58__58_(
                new $HC_2_0$Builtins__MkDPair(
                    Computer__Example1__rgbTypedef(),
                    new $HC_2_0$Builtins__MkDPair(
                        Computer__Example1__rgbTypedef(),
                        $partial_0_2$Computer__Example1__backward()
                    )
                ),
                $HC_0_0$Data__Vect__Nil
            )
        ),
        
        Computer__Example1__succsPath()
    );
}

// GraphFunctor.GraphEmbedding.assembleElemM

function GraphFunctor__GraphEmbedding__assembleElemM($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg){
    
    if(($_6_arg.type === 1)) {
        const $cg$4 = $_6_arg.$1;
        
        return $_5_arg.$2(null)(null)($_9_arg($cg$4.$1)($cg$4.$2)($HC_0_0$Data__Vect__Here))($partial_3_4$GraphFunctor__GraphEmbedding___123_assembleElemM_95_9_125_($_5_arg, $_6_arg.$2, $_9_arg));
    } else {
        
        return $_5_arg.$1(null)($partial_0_3$GraphFunctor__GraphEmbedding___123_assembleElemM_95_10_125_());
    }
}

// Computer.Example1.backward

function Computer__Example1__backward($_0_arg, $_2_in){
    
    if(($_0_arg.type === 0)) {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_1$Prelude__Either__Right($HC_0_0$MkUnit));
    } else {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 0)) {
            return new $HC_1_0$Prelude__Either__Left($HC_0_0$MkUnit);
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_1$Prelude__Either__Right($HC_0_0$MkUnit));
        }
    }
}

// GraphFunctor.ClosedTypedefsAsCategory.closedTypedefsAsKleisliCategory

function GraphFunctor__ClosedTypedefsAsCategory__closedTypedefsAsKleisliCategory($_0_arg){
    return new $HC_2_0$Basic__Category__MkCategory($partial_1_2$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_13_125_($_0_arg), $partial_1_6$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_16_125_($_0_arg));
}

// Computer.Computer.compute'

function Computer__Computer__compute_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    const $cg$2 = GraphFunctor__GraphEmbedding__assembleElemM(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor($partial_0_2$Computer__Computer___123_compute_39__95_18_125_(), $partial_0_4$Computer__Computer___123_compute_39__95_19_125_()), $_1_arg, null, null, $partial_3_5$Computer__Computer___123_compute_39__95_23_125_($_4_arg, $_5_arg, $_6_arg));
    if(($cg$2.type === 1)) {
        const $cg$4 = Free__FreeFunctor__freeFunctor(GraphFunctor__ClosedTypedefsAsCategory__closedTypedefsAsKleisliCategory(Monad__IOMonad__ioMonad($HC_0_0$MkFFI)), null, new $HC_2_0$Free__FreeFunctor__MkGraphEmbedding($partial_2_3$Computer__Computer___123_compute_39__95_17_125_($_4_arg, $_5_arg), $cg$2.$1));
        let $cg$3 = null;
        $cg$3 = $cg$4.$2($_3_arg)($_2_arg)($_7_arg)($_8_arg);
        return new $HC_1_1$Prelude__Maybe__Just($cg$3);
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// GraphFunctor.GraphEmbedding.elem2Fin

function GraphFunctor__GraphEmbedding__elem2Fin($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 0)) {
        return $HC_0_0$Data__Fin__FZ;
    } else {
        return new $HC_1_1$Data__Fin__FS(GraphFunctor__GraphEmbedding__elem2Fin(null, null, null, null, $_4_arg.$1));
    }
}

// GraphFunctor.GraphEmbedding.extractMorphism

function GraphFunctor__GraphEmbedding__extractMorphism($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg, $_10_arg, $_11_arg, $_12_arg, $_13_arg){
    const $cg$2 = Data__Vect__index(null, null, GraphFunctor__GraphEmbedding__elem2Fin(null, null, null, null, $_13_arg), $_12_arg);
    const $cg$4 = $cg$2.$2;
    const $cg$6 = $_8_arg($cg$2.$1)(Data__Vect__index(null, null, $_10_arg($_5_arg), $_11_arg));
    if(($cg$6.type === 0)) {
        const $cg$9 = $_8_arg($cg$4.$1)(Data__Vect__index(null, null, $_10_arg($_4_arg), $_11_arg));
        if(($cg$9.type === 0)) {
            
            return $_9_arg.$1(null)($cg$4.$2);
        } else {
            
            return $_9_arg.$2(null);
        }
    } else {
        
        return $_9_arg.$2(null);
    }
}

// Free.FreeFunctor.foldPath

function Free__FreeFunctor__foldPath($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        
        let $cg$5 = null;
        $cg$5 = $_4_arg.$1($_3_arg);
        let $cg$6 = null;
        $cg$6 = $_4_arg.$1($_5_arg.$1);
        let $cg$7 = null;
        $cg$7 = $_4_arg.$1($_2_arg);
        let $cg$8 = null;
        $cg$8 = $_4_arg.$2($_3_arg)($_5_arg.$1)($_5_arg.$2);
        return $_0_arg.$2($cg$5)($cg$6)($cg$7)($cg$8)(Free__FreeFunctor__foldPath($_0_arg, null, $_2_arg, $_5_arg.$1, $_4_arg, $_5_arg.$3));
    } else {
        
        let $cg$3 = null;
        $cg$3 = $_4_arg.$1($_2_arg);
        return $_0_arg.$1($cg$3);
    }
}

// Computer.Example1.forward

function Computer__Example1__forward($_0_arg, $_2_in){
    
    if(($_0_arg.type === 0)) {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_0$Prelude__Either__Left($HC_0_0$MkUnit));
    } else {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 0)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_1$Prelude__Either__Right($HC_0_0$MkUnit));
        } else {
            return new $HC_1_0$Prelude__Either__Left($HC_0_0$MkUnit);
        }
    }
}

// Free.FreeFunctor.freeFunctor

function Free__FreeFunctor__freeFunctor($_0_arg, $_1_arg, $_2_arg){
    let $cg$1 = null;
    $cg$1 = $_2_arg.$1;
    return new $HC_2_0$Basic__Functor__MkCFunctor($cg$1, $partial_2_5$Free__FreeFunctor___123_freeFunctor_95_24_125_($_0_arg, $_2_arg));
}

// Basic.Functor.functorComposition

function Basic__Functor__functorComposition($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return new $HC_2_0$Basic__Functor__MkCFunctor($partial_2_3$Basic__Functor___123_functorComposition_95_25_125_($_4_arg, $_3_arg), $partial_2_5$Basic__Functor___123_functorComposition_95_26_125_($_4_arg, $_3_arg));
}

// Idris.FunctorAsCFunctor.functorToCFunctor

function Idris__FunctorAsCFunctor__functorToCFunctor($_0_arg, $_1_arg){
    return new $HC_2_0$Basic__Functor__MkCFunctor($_0_arg, $partial_1_4$Idris__FunctorAsCFunctor___123_functorToCFunctor_95_27_125_($_1_arg));
}

// Data.Vect.index

function Data__Vect__index($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = $_2_arg.$1;
            $_3_arg = $_3_arg.$2;
        } else {
            
            return $_3_arg.$1;
        }
    }
}

// Data.Fin.integerToFin

function Data__Fin__integerToFin($_0_arg, $_1_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        let $cg$2 = null;
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_arg, (new $JSRTS.jsbn.BigInteger(("0")))) > 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = $_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))));
        }
        
        
        if($cg$2) {
            return Data__Fin__natToFin($_0_arg, $_1_arg);
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    }
}

// Monad.IOMonad.ioMonad

function Monad__IOMonad__ioMonad($_0_arg){
    return Monad__VerifiedMonadAsMonad__verifiedMonadToExtMonad(null, new $HC_2_0$Interfaces__Verified__VerifiedMonad_95_ictor(new $HC_2_0$Prelude__Monad__Monad_95_ictor($partial_0_3$Monad__IOMonad___123_ioMonad_95_28_125_(), $partial_0_4$Monad__IOMonad___123_ioMonad_95_29_125_()), new $HC_2_0$Interfaces__Verified__VerifiedApplicative_95_ictor($partial_0_3$Monad__IOMonad___123_ioMonad_95_28_125_(), $partial_0_5$Monad__IOMonad___123_ioMonad_95_31_125_())));
}

// Monad.KleisliCategory.kleisliCategory

function Monad__KleisliCategory__kleisliCategory($_0_arg, $_1_arg){
    let $cg$1 = null;
    $cg$1 = $_1_arg.$2;
    return new $HC_2_0$Basic__Category__MkCategory($cg$1, $partial_2_7$Monad__KleisliCategory___123_kleisliCategory_95_32_125_($_0_arg, $_1_arg));
}

// Main.main

function Main__main($_0_in){
    const $_1_in = Computer__Example1__applyReflect_39_()(new $HC_1_0$Prelude__Either__Left($HC_0_0$MkUnit));
    return $HC_0_0$MkUnit;
}

// Data.Fin.natToFin

function Data__Fin__natToFin($_0_arg, $_1_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_0$Prelude__Maybe__Nothing;
        } else {
            const $_2_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            return new $HC_1_1$Prelude__Maybe__Just($HC_0_0$Data__Fin__FZ);
        }
    } else {
        const $_3_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_0$Prelude__Maybe__Nothing;
        } else {
            const $_4_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            const $cg$5 = Data__Fin__natToFin($_3_in, $_4_in);
            if(($cg$5.type === 1)) {
                return new $HC_1_1$Prelude__Maybe__Just(new $HC_1_1$Data__Fin__FS($cg$5.$1));
            } else {
                return $HC_0_0$Prelude__Maybe__Nothing;
            }
        }
    }
}

// Computer.Example1.rgbTypedef

function Computer__Example1__rgbTypedef(){
    return new $HC_2_2$Typedefs__Typedefs__TSum(
        (new $JSRTS.jsbn.BigInteger(("1"))),
        new $HC_2_1$Data__Vect___58__58_(
            $HC_0_1$Typedefs__Typedefs__T1,
            new $HC_2_1$Data__Vect___58__58_(
                $HC_0_1$Typedefs__Typedefs__T1,
                new $HC_2_1$Data__Vect___58__58_(
                    $HC_0_1$Typedefs__Typedefs__T1,
                    $HC_0_0$Data__Vect__Nil
                )
            )
        )
    );
}

// Data.Fin.shift

function Data__Fin__shift($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $_2_arg;
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_1_1$Data__Fin__FS(Data__Fin__shift(null, $_3_in, $_2_arg));
    }
}

// Typedefs.Typedefs.shiftVars

function Typedefs__Typedefs__shiftVars($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return $_1_arg;
    } else if(($_1_arg.type === 6)) {
        return new $HC_3_6$Typedefs__Typedefs__TApp($_1_arg.$1, $_1_arg.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__Typedefs__shiftVars(null), $_1_arg.$3));
    } else if(($_1_arg.type === 5)) {
        return new $HC_2_5$Typedefs__Typedefs__TMu($_1_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs__Typedefs___123_shiftVars_95_33_125_(), $_1_arg.$2));
    } else if(($_1_arg.type === 3)) {
        return new $HC_2_3$Typedefs__Typedefs__TProd($_1_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__Typedefs__shiftVars(null), $_1_arg.$2));
    } else if(($_1_arg.type === 2)) {
        return new $HC_2_2$Typedefs__Typedefs__TSum($_1_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__Typedefs__shiftVars(null), $_1_arg.$2));
    } else {
        return new $HC_1_4$Typedefs__Typedefs__TVar(Data__Fin__shift(null, (new $JSRTS.jsbn.BigInteger(("1"))), $_1_arg.$1));
    }
}

// Computer.Example1.succsPath

function Computer__Example1__succsPath(){
    return new $HC_3_1$Free__Path___58__58_(
        $HC_0_0$MkUnit,
        $HC_0_0$Data__Vect__Here,
        new $HC_3_1$Free__Path___58__58_(
            $HC_0_0$MkUnit,
            new $HC_1_1$Data__Vect__There($HC_0_0$Data__Vect__Here),
            new $HC_3_1$Free__Path___58__58_(
                $HC_0_0$MkUnit,
                $HC_0_0$Data__Vect__Here,
                new $HC_3_1$Free__Path___58__58_(
                    $HC_0_0$MkUnit,
                    $HC_0_0$Data__Vect__Here,
                    $HC_0_0$Free__Path__Nil
                )
            )
        )
    );
}

// Computer.Example1.twoLoopsGraph

function Computer__Example1__twoLoopsGraph(){
    return new $HC_2_1$Data__Vect___58__58_(
        new $HC_2_0$Builtins__MkPair(
            $HC_0_0$MkUnit, 
            $HC_0_0$MkUnit
        ),
        
        new $HC_2_1$Data__Vect___58__58_(
            new $HC_2_0$Builtins__MkPair(
                $HC_0_0$MkUnit,
                $HC_0_0$MkUnit
            ),
            
            $HC_0_0$Data__Vect__Nil
        )
    );
}

// Monad.VerifiedMonadAsMonad.verifiedMonadMultiplication

function Monad__VerifiedMonadAsMonad__verifiedMonadMultiplication($_0_arg, $_1_arg, $_2_arg, $_3_x){
    
    const $cg$3 = $_1_arg.$1;
    return $cg$3.$2(null)(null)($_3_x)($partial_0_1$Monad__VerifiedMonadAsMonad___123_verifiedMonadMultiplication_95_34_125_());
}

// Monad.VerifiedMonadAsMonad.verifiedMonadToExtMonad

function Monad__VerifiedMonadAsMonad__verifiedMonadToExtMonad($_0_arg, $_1_arg){
    let $cg$1 = null;
    const $cg$3 = $_1_arg.$2;
    $cg$1 = $cg$3.$2;
    return new $HC_3_0$Monad__Monad__MkMonad(Idris__FunctorAsCFunctor__functorToCFunctor($_0_arg, $cg$1), $partial_2_3$Monad__VerifiedMonadAsMonad__verifiedMonadUnit(null, $_1_arg), $partial_2_4$Monad__VerifiedMonadAsMonad__verifiedMonadMultiplication(null, $_1_arg));
}

// Monad.VerifiedMonadAsMonad.verifiedMonadUnit

function Monad__VerifiedMonadAsMonad__verifiedMonadUnit($_0_arg, $_1_arg, $_2_arg){
    
    const $cg$3 = $_1_arg.$2;
    return $cg$3.$1(null);
}

// Typedefs.Typedefs.{ap_0}

function Typedefs__Typedefs___123_ap_95_0_125_($_0_lift, $_1_lift, $_2_lift){
    return Typedefs__Typedefs__ap($_0_lift, null, $_2_lift, $_1_lift);
}

// Typedefs.Typedefs.{ap_1}

function Typedefs__Typedefs___123_ap_95_1_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = Data__Fin__integerToFin((new $JSRTS.jsbn.BigInteger(("0"))), $_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))));
    let $cg$2 = null;
    $cg$2 = $cg$3.$1;
    return new $HC_2_0$Builtins__MkPair($_2_lift.$1, Typedefs__Typedefs__ap($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), null, $_2_lift.$2, new $HC_2_1$Data__Vect___58__58_(new $HC_1_4$Typedefs__Typedefs__TVar($cg$2), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Typedefs__Typedefs__shiftVars(null), $_1_lift))));
}

// Computer.Example1.{applyReflect'_4}

function Computer__Example1___123_applyReflect_39__95_4_125_($_0_lift){
    return $HC_0_0$Data__Fin__FZ;
}

// GraphFunctor.GraphEmbedding.{assembleElemM_6}

function GraphFunctor__GraphEmbedding___123_assembleElemM_95_6_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_0_lift($_1_lift)($_2_lift)(new $HC_1_1$Data__Vect__There($_3_lift));
}

// GraphFunctor.GraphEmbedding.{assembleElemM_7}

function GraphFunctor__GraphEmbedding___123_assembleElemM_95_7_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 0)) {
        return $_0_lift;
    } else {
        return $_1_lift($_2_lift)($_3_lift)($_4_lift.$1);
    }
}

// GraphFunctor.GraphEmbedding.{assembleElemM_8}

function GraphFunctor__GraphEmbedding___123_assembleElemM_95_8_125_($_0_lift, $_1_lift, $_2_lift){
    
    return $_0_lift.$1(null)($partial_2_5$GraphFunctor__GraphEmbedding___123_assembleElemM_95_7_125_($_1_lift, $_2_lift));
}

// GraphFunctor.GraphEmbedding.{assembleElemM_9}

function GraphFunctor__GraphEmbedding___123_assembleElemM_95_9_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    return $_0_lift.$2(null)(null)(GraphFunctor__GraphEmbedding__assembleElemM(null, null, null, null, null, $_0_lift, $_1_lift, null, null, $partial_1_4$GraphFunctor__GraphEmbedding___123_assembleElemM_95_6_125_($_2_lift)))($partial_2_3$GraphFunctor__GraphEmbedding___123_assembleElemM_95_8_125_($_0_lift, $_3_lift));
}

// GraphFunctor.GraphEmbedding.{assembleElemM_10}

function GraphFunctor__GraphEmbedding___123_assembleElemM_95_10_125_($_0_lift, $_1_lift, $_2_lift){
    return null;
}

// GraphFunctor.ClosedTypedefsAsCategory.{closedTypedefsAsKleisliCategory_11}

function GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_11_125_($_0_lift, $_1_lift){
    return $_1_lift;
}

// GraphFunctor.ClosedTypedefsAsCategory.{closedTypedefsAsKleisliCategory_12}

function GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_12_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $_4_lift($_3_lift($_5_lift));
}

// GraphFunctor.ClosedTypedefsAsCategory.{closedTypedefsAsKleisliCategory_13}

function GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_13_125_($_0_lift, $_1_lift){
    const $cg$2 = Monad__KleisliCategory__kleisliCategory(new $HC_2_0$Basic__Category__MkCategory($partial_0_2$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_11_125_(), $partial_0_6$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_12_125_()), $_0_lift);
    return $cg$2.$1(Typedefs__Typedefs__Ty((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Data__Vect__Nil, $_1_lift));
}

// GraphFunctor.ClosedTypedefsAsCategory.{closedTypedefsAsKleisliCategory_16}

function GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_16_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    const $cg$2 = Monad__KleisliCategory__kleisliCategory(new $HC_2_0$Basic__Category__MkCategory($partial_0_2$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_11_125_(), $partial_0_6$GraphFunctor__ClosedTypedefsAsCategory___123_closedTypedefsAsKleisliCategory_95_12_125_()), $_0_lift);
    return $cg$2.$2(Typedefs__Typedefs__Ty((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Data__Vect__Nil, $_1_lift))(Typedefs__Typedefs__Ty((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Data__Vect__Nil, $_2_lift))(Typedefs__Typedefs__Ty((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Data__Vect__Nil, $_3_lift))($_4_lift)($_5_lift);
}

// Computer.Computer.{compute'_17}

function Computer__Computer___123_compute_39__95_17_125_($_0_lift, $_1_lift, $_2_lift){
    return Data__Vect__index(null, null, $_0_lift($_2_lift), $_1_lift);
}

// Computer.Computer.{compute'_18}

function Computer__Computer___123_compute_39__95_18_125_($_0_lift, $_1_lift){
    return new $HC_1_1$Prelude__Maybe__Just($_1_lift);
}

// Computer.Computer.{compute'_19}

function Computer__Computer___123_compute_39__95_19_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    if(($_2_lift.type === 1)) {
        return $_3_lift($_2_lift.$1);
    } else {
        return $_2_lift;
    }
}

// Computer.Computer.{compute'_20}

function Computer__Computer___123_compute_39__95_20_125_($_0_lift, $_1_lift){
    return Decidable__Equality__Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0(null, $_0_lift, $_1_lift);
}

// Computer.Computer.{compute'_22}

function Computer__Computer___123_compute_39__95_22_125_($_0_lift){
    return $HC_0_0$Prelude__Maybe__Nothing;
}

// Computer.Computer.{compute'_23}

function Computer__Computer___123_compute_39__95_23_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return $partial_13_14$GraphFunctor__GraphEmbedding__extractMorphism(null, null, null, null, $_4_lift, $_3_lift, null, null, $partial_0_2$Computer__Computer___123_compute_39__95_20_125_(), new $HC_2_0$Prelude__Applicative__Alternative_95_ictor($partial_0_2$Computer__Computer___123_compute_39__95_18_125_(), $partial_0_1$Computer__Computer___123_compute_39__95_22_125_()), $_0_lift, $_1_lift, $_2_lift);
}

// Free.FreeFunctor.{freeFunctor_24}

function Free__FreeFunctor___123_freeFunctor_95_24_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Free__FreeFunctor__foldPath($_0_lift, null, $_3_lift, $_2_lift, $_1_lift, $_4_lift);
}

// Basic.Functor.{functorComposition_25}

function Basic__Functor___123_functorComposition_95_25_125_($_0_lift, $_1_lift, $_2_lift){
    
    let $cg$2 = null;
    $cg$2 = $_1_lift.$2($_2_lift);
    return $_0_lift.$2($cg$2);
}

// Basic.Functor.{functorComposition_26}

function Basic__Functor___123_functorComposition_95_26_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    let $cg$2 = null;
    $cg$2 = $_1_lift.$1($_2_lift);
    let $cg$3 = null;
    $cg$3 = $_1_lift.$1($_3_lift);
    let $cg$4 = null;
    $cg$4 = $_1_lift.$2($_2_lift)($_3_lift)($_4_lift);
    return $_0_lift.$2($cg$2)($cg$3)($cg$4);
}

// Idris.FunctorAsCFunctor.{functorToCFunctor_27}

function Idris__FunctorAsCFunctor___123_functorToCFunctor_95_27_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_0_lift(null)(null)($_3_lift);
}

// Monad.IOMonad.{ioMonad_28}

function Monad__IOMonad___123_ioMonad_95_28_125_($_0_lift, $_1_lift, $_2_lift){
    return $_1_lift;
}

// Monad.IOMonad.{ioMonad_29}

function Monad__IOMonad___123_ioMonad_95_29_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_5_6$io_95_bind(null, null, null, $_2_lift, $_3_lift);
}

// Monad.IOMonad.{ioMonad_31}

function Monad__IOMonad___123_ioMonad_95_31_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    const $_16_in = $_3_lift($_4_lift);
    return $_2_lift($_16_in);
}

// Monad.KleisliCategory.{kleisliCategory_32}

function Monad__KleisliCategory___123_kleisliCategory_95_32_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    
    let $cg$2 = null;
    $cg$2 = $_1_lift.$1;
    let $cg$3 = null;
    $cg$3 = $_1_lift.$1;
    const $cg$5 = Basic__Functor__functorComposition(null, null, null, $cg$2, $cg$3);
    let $cg$4 = null;
    $cg$4 = $cg$5.$1($_4_lift);
    let $cg$6 = null;
    const $cg$8 = $_1_lift.$1;
    $cg$6 = $cg$8.$2($_4_lift);
    let $cg$9 = null;
    let $cg$10 = null;
    const $cg$12 = $_1_lift.$1;
    $cg$10 = $cg$12.$2($_3_lift);
    let $cg$13 = null;
    const $cg$15 = $_1_lift.$1;
    let $cg$16 = null;
    const $cg$18 = $_1_lift.$1;
    $cg$16 = $cg$18.$2($_4_lift);
    $cg$13 = $cg$15.$2($cg$16);
    let $cg$19 = null;
    const $cg$21 = $_1_lift.$1;
    let $cg$22 = null;
    const $cg$24 = $_1_lift.$1;
    $cg$22 = $cg$24.$2($_4_lift);
    $cg$19 = $cg$21.$2($_3_lift)($cg$22)($_6_lift);
    $cg$9 = $_0_lift.$2($_2_lift)($cg$10)($cg$13)($_5_lift)($cg$19);
    let $cg$25 = null;
    $cg$25 = $_1_lift.$3($_4_lift);
    return $_0_lift.$2($_2_lift)($cg$4)($cg$6)($cg$9)($cg$25);
}

// Typedefs.Typedefs.{shiftVars_33}

function Typedefs__Typedefs___123_shiftVars_95_33_125_($_0_lift){
    
    return new $HC_2_0$Builtins__MkPair($_0_lift.$1, Typedefs__Typedefs__shiftVars(null, $_0_lift.$2));
}

// Monad.VerifiedMonadAsMonad.{verifiedMonadMultiplication_34}

function Monad__VerifiedMonadAsMonad___123_verifiedMonadMultiplication_95_34_125_($_0_lift){
    return $_0_lift;
}

// Decidable.Equality.{Typedefs.TypedefsDecEq.@Decidable.Equality.DecEq$TDef n:!decEq:0_lam_36}

function Decidable__Equality___123_Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0_95_lam_95_36_125_($_0_lift, $_1_lift){
    
    
    const $cg$4 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_String_58__33_decEq_58_0($_0_lift.$1, $_1_lift.$1);
    if(($cg$4.type === 1)) {
        const $cg$8 = Decidable__Equality__Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0(null, $_0_lift.$2, $_1_lift.$2);
        if(($cg$8.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        const $cg$6 = Decidable__Equality__Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0(null, $_0_lift.$2, $_1_lift.$2);
        if(($cg$6.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        }
    }
}

// Decidable.Equality.Data.Fin.Fin n implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Data__Fin___64_Decidable__Equality__DecEq_36_Fin_32_n_58__33_decEq_58_0($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        
        if(($_1_arg.type === 1)) {
            const $cg$5 = Decidable__Equality__Data__Fin___64_Decidable__Equality__DecEq_36_Fin_32_n_58__33_decEq_58_0(null, $_1_arg.$1, $_2_arg.$1);
            if(($cg$5.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
            }
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        
        if(($_1_arg.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        }
    }
}

// Decidable.Equality.Decidable.Equality.Nat implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_0_arg, $_1_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        
        if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        } else {
            const $_2_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        
        if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            const $_4_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_4_in, $_3_in);
            if(($cg$5.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
            }
        }
    }
}

// Decidable.Equality.Decidable.Equality.String implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_String_58__33_decEq_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg == $_1_arg)) ? 1|0 : 0|0) === 0)) {
        return $HC_0_1$Prelude__Basics__No;
    } else {
        return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
    }
}

// Decidable.Equality.Typedefs.TypedefsDecEq.TDef n implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        
        if(($_1_arg.type === 1)) {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        } else if(($_1_arg.type === 6)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 5)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 3)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 2)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else if(($_2_arg.type === 6)) {
        
        if(($_1_arg.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 6)) {
            const $cg$22 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_1_arg.$1, $_2_arg.$1);
            if(($cg$22.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                
                null;
            }
        } else if(($_1_arg.type === 5)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 3)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 2)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else if(($_2_arg.type === 5)) {
        
        if(($_1_arg.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 6)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 5)) {
            const $cg$17 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_1_arg.$1, $_2_arg.$1);
            if(($cg$17.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                const $cg$19 = Decidable__Equality__Data__Vect___64_Decidable__Equality__DecEq_36_Vect_32_n_32_a_58__33_decEq_58_0(null, null, $partial_0_2$Decidable__Equality___123_Typedefs__TypedefsDecEq___64_Decidable__Equality__DecEq_36_TDef_32_n_58__33_decEq_58_0_95_lam_95_36_125_(), $_1_arg.$2, $_2_arg.$2);
                if(($cg$19.type === 1)) {
                    return $HC_0_1$Prelude__Basics__No;
                } else {
                    return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
                }
            }
        } else if(($_1_arg.type === 3)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 2)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else if(($_2_arg.type === 3)) {
        
        if(($_1_arg.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 6)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 5)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 3)) {
            const $cg$12 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_1_arg.$1, $_2_arg.$1);
            if(($cg$12.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                const $cg$14 = Decidable__Equality__Data__Vect___64_Decidable__Equality__DecEq_36_Vect_32_n_32_a_58__33_decEq_58_0(null, null, $partial_0_2$Computer__Computer___123_compute_39__95_20_125_(), $_1_arg.$2, $_2_arg.$2);
                if(($cg$14.type === 1)) {
                    return $HC_0_1$Prelude__Basics__No;
                } else {
                    return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
                }
            }
        } else if(($_1_arg.type === 2)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else if(($_2_arg.type === 2)) {
        
        if(($_1_arg.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 6)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 5)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 3)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 2)) {
            const $cg$7 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Nat_58__33_decEq_58_0($_1_arg.$1, $_2_arg.$1);
            if(($cg$7.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                const $cg$9 = Decidable__Equality__Data__Vect___64_Decidable__Equality__DecEq_36_Vect_32_n_32_a_58__33_decEq_58_0(null, null, $partial_0_2$Computer__Computer___123_compute_39__95_20_125_(), $_1_arg.$2, $_2_arg.$2);
                if(($cg$9.type === 1)) {
                    return $HC_0_1$Prelude__Basics__No;
                } else {
                    return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
                }
            }
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        
        if(($_1_arg.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 6)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 5)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 3)) {
            return $HC_0_1$Prelude__Basics__No;
        } else if(($_1_arg.type === 2)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            const $cg$4 = Decidable__Equality__Data__Fin___64_Decidable__Equality__DecEq_36_Fin_32_n_58__33_decEq_58_0(null, $_1_arg.$1, $_2_arg.$1);
            if(($cg$4.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
            }
        }
    }
}

// Decidable.Equality.Data.Vect.Vect n a implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Data__Vect___64_Decidable__Equality__DecEq_36_Vect_32_n_32_a_58__33_decEq_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        
        const $cg$4 = $_2_arg($_3_arg.$1)($_4_arg.$1);
        if(($cg$4.type === 1)) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            const $cg$6 = Decidable__Equality__Data__Vect___64_Decidable__Equality__DecEq_36_Vect_32_n_32_a_58__33_decEq_58_0(null, null, $_2_arg, $_3_arg.$2, $_4_arg.$2);
            if(($cg$6.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
            }
        }
    } else {
        return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
    }
}

// Prelude.Functor.Data.Vect.Vect n implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_($_3_arg($_4_arg.$1), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $_3_arg, $_4_arg.$2));
    } else {
        return $_4_arg;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Integer implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if(((($_0_arg.equals($_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if(((((($_0_arg).compareTo(($_1_arg)) < 0)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// {runMain_0}

function $_0_runMain(){
    return $JSRTS.force(Main__main($HC_0_0$TheWorld));
}


// $_0_runMain();
// }.call(this))