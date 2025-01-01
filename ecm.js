/*jshint esversion:6,bitwise:false*/
/*global BigInt*/
"use strict";
//TODO:
//import gcd from './libs/gcd.js';

function primes(MAX) {
  const sieve = new Uint8Array(MAX + 1).fill(-1);
  const result = [];
  result.push(2);
  for (let i = 3; i <= MAX; i += 2) {
    if (sieve[i] !== 0) {
      result.push(i);
      if (i <= Math.floor(MAX / i)) {
        for (let j = i * i; j <= MAX; j += 2 * i) {
          sieve[j] = 0;
        }
      }
    }
  }
  return result;
}

//function invmod(a, m) {
//  return gcd.invmod(a, m);
//}

function gcdext(a, b) {
  if (typeof a !== 'bigint' || typeof b !== 'bigint') {
    throw new TypeError();
  }
  let B = BigInt(0);
  let D = BigInt(1);
  let x = a;
  let y = b;
  while (y !== BigInt(0)) {
    const q = BigInt(x / y);
    const y1 = x - q * y;
    x = y;
    y = y1;
    const D1 = B - q * D;
    B = D;
    D = D1;
  }
  return [undefined, B, x];
}

function invmod(a, m) {
  if (typeof a !== 'bigint' || typeof m !== 'bigint') {
    throw new TypeError();
  }
  if (a < BigInt(0)) {
    a += m;
  }
  if (a < BigInt(0) || a > m) {
    throw new RangeError();
  }
  const [A, B, g] = gcdext(m, a);
  if (BigInt(g) !== BigInt(1)) {
    return BigInt(0);
  }
  return BigInt(B) < BigInt(0) ? BigInt(B) + BigInt(m) : BigInt(B);
}

function gcd(a, b) {
  if (typeof a !== 'bigint' || typeof b !== 'bigint') {
    throw new TypeError();
  }
  if (a < BigInt(0) || a > b) {
    throw new RangeError();
  }
  while (b !== BigInt(0)) {
    const q = BigInt(a / b);
    const r = a - q * b;
    a = b;
    b = r;
  }
  return a;
}

function ecm(N, unlimited = false) {
  const factorDigits = unlimited ? 1/0 : (N.toString(2).length * Math.log10(2)) / 4;//TODO: !?
  // https://www.rieselprime.de/ziki/Elliptic_curve_method
  const B = Math.min(Math.round(Math.pow(5, factorDigits / 5) * 16), 1e300);
  const minB = N < BigInt(Math.pow(10, 10)) ? 16 : 400;
  let B1 = B;
  while (B1 > minB) {
    B1 = Math.floor(B1 / 5);
  }
  for (; B1 <= B; B1 *= 5) {
    const curves = Math.round(Math.sqrt(B1) / 16) * 16; //TODO: !?
    let curveIndex = 0;
    while (curveIndex < curves) {
      console.debug('curves: ', curveIndex + '/' + curves);
      const f = _ecm(N, B1, curveIndex);
      if (f !== BigInt(0)) {
        return f;
      }
      curveIndex += 1;
    }
    console.warn('failed to find a factor');
  }
  return BigInt(0);
}
ecm.modMuls = 0;

function makeBarrettReduction(N) {
  // Barrett Reduction
  // https://www.youtube.com/watch?v=SwYQeeBWlRo&list=PLhCN8H4P5Lvgx5MrIibav6KgbhYj-mn_D&index=7
  const k = N.toString(2).length;//TODO:
  const NInv = (BigInt(1) << BigInt(2 * k)) / N;
  const km1 = BigInt(k - 1);
  const kp1 = BigInt(k + 1);
  const useBarrettReduction = k > 128;//?
  return useBarrettReduction ? function (p) {
    let y = p - (((p >> km1) * NInv) >> kp1) * N;
    while (y < BigInt(0)) {
      y += N;
    }
    while (y >= N) {
      y -= N;
    }
    return y;
  } : null;
}

function makeSpecialReduction(N) {
  const k = N.toString(2).length;
  const NInv = BigInt(invmod(BigInt.asUintN(k - 1, N), BigInt(1) << BigInt(k - 1)));//?
  const sN = N * NInv;
  const k1 = sN.toString(2).length - 1;
  const bk1 = BigInt(k1);
  const c = sN - (BigInt(1) << bk1);
  if (c === BigInt(1)) {
    console.debug("reduction for numbers of form 2^n+1 will be used");
    //const mask = (BigInt(1) << bk1) - BigInt(1);
    return function (p) {
      let y = BigInt.asUintN(k1, p) - (p >> bk1);
      // (p & mask) is slightly faster somehow then BigInt.asUintN(k1, p):
      //let y = (p & mask) - (p >> bk1);
      //y = y % N;
      if (y < BigInt(0)) {
        y += sN;
      }
      return y;
    };
  }
  return null;
}

function _ecm(N, B = 50000, curveParam = 0) {
  // Lenstra elliptic-curve factorization
  // from https://trizenx.blogspot.com/2018/10/continued-fraction-factorization-method.html:
  // https://github.com/trizen/sidef-scripts/blob/master/Math/elliptic-curve_factorization_method.sf
  // and Cohen 93
  if (typeof N !== 'bigint') {
    throw new TypeError();
  }

  const useSuyamaParametrization = true;

  let failure = BigInt(1);
  let modMuls = 0;

  const reduction1 = makeSpecialReduction(N);
  const modreduction = reduction1 || makeBarrettReduction(N) || function (p) { if (typeof p !== 'bigint' || typeof N !== 'bigint') { throw new TypeError(); } return p % N; };
  const sN = reduction1 != null ? reduction1(BigInt(-1)) + BigInt(1) : N;//TODO: !?

  const modmul = function (a, b) {
    if (typeof a !== 'bigint' || typeof b !== 'bigint') {
      throw new TypeError();
    }
    modMuls += 1;
    return modreduction(a * b);
  };
  const modsub = function (a, b) {
    if (typeof a !== 'bigint' || typeof b !== 'bigint') {
      throw new TypeError();
    }
    let y = a - b;
    if (y < BigInt(0)) {
      y += sN;
    }
    return y;
  };
  const modadd = function (a, b) {
    if (typeof a !== 'bigint' || typeof b !== 'bigint') {
      throw new TypeError();
    }
    let y = a + b;
    if (y >= sN) {
      y -= sN;
    }
    return y;
  };
  const moddup = function (a) {
    let y = a << BigInt(1);
    if (y >= sN) {
      y -= sN;
    }
    return y;
  };
  const modneg = function (a) {
    if (typeof a !== 'bigint') {
      throw new TypeError();
    }
    return a === BigInt(0) ? a : sN - a;
  };
  const modmulsmall = function (a, b) {
    if (typeof a !== 'bigint' || typeof b !== 'bigint') {
      throw new TypeError();
    }
    let y = (a * b) % sN;
    if (y < BigInt(0)) {
      y += sN;
    }
    return y;
  };

  const modInvParallel = function (a) {
    // parallel modular inverse from Cohen 93
    const n = a.length;
    const c = new Array(n);
    c[0] = a[0];
    for (let i = 1; i < n; i += 1) {
      c[i] = modmul(c[i - 1], a[i]);
    }
    let u = BigInt(invmod(BigInt(c[n - 1]) % N, N));
    for (let i = n - 1; i >= 1; i -= 1) {
      c[i] = modmul(u, c[i - 1]);
      u = modmul(u, a[i]);
    }
    c[0] = u;
    u = BigInt(1);
    return c;
  };

  // https://en.wikipedia.org/wiki/Twisted_Edwards_curve#Addition_in_projective_twisted_curves
  function TwistedEdwardsCurve(a, d) {
    this.a = a;
    this.d = d;
  }
  TwistedEdwardsCurve.prototype.addPoints = function (P1, P2) {
    // https://hyperelliptic.org/EFD/g1p/auto-twisted-extended.html#addition-add-2008-hwcd-2
    const A = modmul(P1.x, P2.x);
    const B = modmul(P1.y, P2.y);
    const C = modmul(P1.z, P2.t);
    const D = modmul(P1.t, P2.z);
    const E = modadd(D, C);
    const F = modsub(modadd(modmul(modsub(P1.x, P1.y), modadd(P2.x, P2.y)), B), A);
    const G = modadd(B, modmulsmall(this.a, A));
    const H = modsub(D, C);
    const x = modmul(E, F);
    const y = modmul(G, H);
    const z = modmul(F, G);
    const t = modmul(E, H);
    return {x: x, y: y, z: z, t: t};
  };
  TwistedEdwardsCurve.prototype.doublePoint = function (P, u, extended = true) {
    // https://hyperelliptic.org/EFD/g1p/auto-twisted-extended.html#doubling-dbl-2008-hwcd
    const A = modadd(P.x, P.y);
    const B = modmul(A, A);
    const C = modmul(P.x, P.x);
    const D = modmul(P.y, P.y);
    const E = modmulsmall(this.a, C);
    const F = modadd(E, D);
    const H = modmul(P.z, P.z);
    const J = modsub(F, moddup(H));
    const K = modsub(modsub(B, C), D);
    const L = modsub(E, D);
    const x = modmul(K, J);
    const y = modmul(F, L);
    const z = modmul(F, J);
    const t = extended ? modmul(K, L) : undefined;
    return {x: x, y: y, z: z, t: t};
  };
  TwistedEdwardsCurve.prototype.negatePoint = function (P) {
    return {x: modneg(P.x), y: P.y, z: P.z, t: modneg(P.t)};
  };
  TwistedEdwardsCurve.prototype.phi = function (points) {
    const v = new Array(points.length);
    for (let i = 0; i < points.length; i += 1) {
      const P = points[i];
      //v[i] = modsub(P.z, P.y);
      v[i] = P.z;
    }
    const invs = modInvParallel(v);
    const res = new Array(points.length);
    for (let i = 0; i < points.length; i += 1) {
      const P = points[i];
      //const x = modmul(modadd(P.z, P.y), invs[i]);
      //res[i] = x % N;
      const y = BigInt(modmul(P.y, invs[i]));
      res[i] = y % N;
      if (invs[i] === BigInt(0)) {
        const u = gcd(v[i], N);
        if (u !== BigInt(1) && u !== BigInt(N)) {
          failure = u;
          return [];
        }
      }
    }
    return res;
  };

  const MontgomeryToTwistedEdwards = function (x_m, y_m, A, B, N) {
    if (typeof N !== 'bigint') {
      throw new TypeError();
    }
    let x_e = x_m * BigInt(invmod(y_m, N)) % N;
    let y_e = (x_m - BigInt(1)) * invmod(x_m + BigInt(1), N) % N;
    const Binv = invmod(B, N);
    let a = (A + BigInt(2)) * Binv % N;
    let d = (A - BigInt(2)) * Binv % N;
    if (x_e == BigInt(0) || y_e === BigInt(0) || a === BigInt(0) || d === BigInt(0)) {
      return null;
    }
    console.assert((a * x_e * x_e + y_e * y_e - (BigInt(1) + d * x_e * x_e * y_e * y_e)) % N === BigInt(0)); // Twisted Edwards Curve

    x_e = x_e < BigInt(0) ? x_e + N : x_e;
    y_e = y_e < BigInt(0) ? y_e + N : y_e;
    //a = a < BigInt(0) ? a + N : a;
    d = d < BigInt(0) ? d + N : d;

    return {x: x_e, y: y_e, a: a, d: d};
  };


  const wAryNonAdjacentFormMultiplication = function (curve, P, s) {
    function wNAF(d, w) {
      // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication#w-ary_non-adjacent_form_(wNAF)_method
      const da = [];
      let pos = d.length - 1;
      let carry = false;
      while (pos >= 0 || carry) {
        if ((pos >= 0 ? +d.charCodeAt(pos) - +'0'.charCodeAt(0) : 0) !== (carry ? 1 : 0)) {
          let x = 0;
          for (let i = pos + 1 - w; i <= pos; i += 1) {
            x <<= 1;
            x += (i >= 0 ? +d.charCodeAt(i) - +'0'.charCodeAt(0) : 0);
          }
          x += (carry ? 1 : 0);
          if (x >= (1 << (w - 1))) {
            x -= (1 << w);
          }
          da.push(x);
          pos -= 1;
          for (let i = 0; i < w - 1; i += 1) {
            da.push(0);
            pos -= 1;
          }
          carry = x < 0;
        } else {
          da.push(0);
          pos -= 1;
        }
      }
      while (da[da.length - 1] === 0) {
        da.pop();
      }
      return da;
    }
    let w = 2;
    const work = function (w, n) {
      return 1 + Math.pow(2, w - 2) - 1 + n + n / (w + 1);
    };
    while (+work(w + 1, s.length) < +work(w, s.length)) {
      w += 1;
    }
    const d = wNAF(s, w);
    const cache = new Array(Math.pow(2, w - 2)).fill(null);
    cache[0] = P;
    const twoP = curve.doublePoint(P);
    if (twoP == null) {
      return null;
    }
    for (let k = 1; k < cache.length; k += 1) {
      cache[k] = curve.addPoints(cache[k - 1], twoP);
      if (cache[k] == null) {
        return null;
      }
    }
    let Q = null;
    for (let j = d.length - 1; j >= 0; j -= 1) {
      if (Q != null) {
        Q = curve.doublePoint(Q, undefined, d[j] !== 0 || j === 0);
        if (Q == null) {
          return null;
        }
      }
      if (d[j] !== 0) {
        //let x = d[j] * P;
        let i = Math.abs(d[j]);
        console.assert((i - 1) % 2 === 0);
        const X = cache[(i - 1) >> 1];
        if (Q == null) {
          Q = X;
        } else {
          if (d[j] < 0) {
            Q = curve.addPoints(Q, curve.negatePoint(X));
            if (Q == null) {
              return null;
            }
          } else {
            Q = curve.addPoints(Q, X);
            if (Q == null) {
              return null;
            }
          }
        }
      }
    }
    return Q;
  };

  const scalePoint = function (curve, P, s) {
    // https://cs.au.dk/~ivan/FastExpproject.pdf
    return wAryNonAdjacentFormMultiplication(curve, P, s.toString(2));
  };

  const SuyamaParametrization = function (sigma, N) {
    if (typeof sigma !== 'bigint' || typeof N !== 'bigint') {
      throw new TypeError();
    }
    // Suyama’s parametrization - see https://members.loria.fr/PZimmermann/papers/ecm-submitted.pdf  
    //let sigma = BigInt(6) % N;
    const u = (sigma * sigma - BigInt(5)) % N;
    const v = (BigInt(4) * sigma) % N;
    const z0inv = invmod(v * v * v % N, N);
    if (z0inv === BigInt(0)) {
      return null;
    }
    const t = invmod(BigInt(4) * u * u * u * v % N, N);
    if (t === BigInt(0)) {
      return null;
    }
    let a = ((v - u) * (v - u) * (v - u) * (BigInt(3) * u + v) * t - BigInt(2)) % N;
    let b = u * z0inv % N;
    let x = u * u * u % N;
    let y = (sigma * sigma - BigInt(1)) * (sigma * sigma - BigInt(25)) * (sigma * sigma * sigma * sigma - BigInt(25)) % N;
    x = x * z0inv % N;
    y = y * z0inv % N;
    console.assert((b * y * y - (x * x * x + a * x * x + x)) % N === BigInt(0)); // Montgomery form

    if (true) {
      // to make TwistedEdwardsCurve param a smaller:
      // Let a = s**2 * a_0:
      const s = (v - u) * v * invmod(BigInt(2) * u * u % N, N) % N; // a === (v - u) * (3 * u + v) * invmod(4 * u**4, N) * v**2 * (v - u)**2 mod N;
      const sInv = invmod(s, N);
      if (sInv !== BigInt(0)) {
        b = b * s * s % N;
        y = y * sInv % N;
        console.assert((b * y * y - (x * x * x + a * x * x + x)) % N === BigInt(0)); // Montgomery form
      }
    }

    return {x: x, y: y, a: a, b: b};
  };

  const product = function (array) {
    if (array.length > 16) {
      const middle = Math.floor(array.length / 2);
      return BigInt(product(array.slice(0, middle))) * BigInt(product(array.slice(middle)));
    }
    let p = BigInt(1);
    for (let i = 0; i < array.length; i += 1) {
      p *= BigInt(array[i]);
    }
    return p;
  };

  const generateCurveAndStartingPoint = function (curveIndex, flag = false) {
    if (typeof curveIndex !== 'number') {
      throw new TypeError();
    }
    if (useSuyamaParametrization) {
      const tmp1 = SuyamaParametrization(BigInt(6) + BigInt(curveIndex), N);
      if (tmp1 != null) {
        if (true) {
          const tmp3 = MontgomeryToTwistedEdwards(tmp1.x, tmp1.y, tmp1.a, tmp1.b, N);
          if (tmp3 != null) {
            return {curve: new TwistedEdwardsCurve(tmp3.a, tmp3.d), startingPoint: {x: tmp3.x, y: tmp3.y, z: BigInt(1), t: modmul(tmp3.x, tmp3.y)}};
          }
        }
      }
    }
    if (true) {
      const d = BigInt(curveIndex + 2);
      const a = d * BigInt(2) * BigInt(2) + BigInt(1) - BigInt(2) * BigInt(2);
      return {curve: new TwistedEdwardsCurve(a, d), startingPoint: {x: BigInt(1), y: BigInt(2), z: BigInt(1), t: BigInt(1) * BigInt(2)}};
    }
  };

  const restoreNulls = function (values, points) {
    const res = new Array(points.length);
    let k = 0;
    for (let i = 0; i < points.length; i += 1) {
      if (points[i] == null) {
        res[i] = null;
      } else {
        res[i] = values[k];
        k += 1;
      }
    }
    return res;
  };

  const pointsRange = function (curve, P, to) {
    // 1P, 2P, 3P, 4P, ...
    let Q = null;
    const array = new Array(to + 1).fill(null);
    for (let j = 1; j <= to; j += 1) {
      Q = j === 1 ? P : (j === 2 ? curve.doublePoint(Q) : curve.addPoints(Q, P));
      if (Q == null) {
        return null;
      }
      array[j] = Q;
    }
    return array;
  };

  const pointsRangeFiltered = function (curve, P, to, filter) {
    const twoP = curve.doublePoint(P);
    if (twoP == null) {
      return null;
    }
    const gaps = pointsRange(curve, twoP, 7);
    let Q = null;
    let last = 0;
    const array = new Array(to + 1).fill(null);
    for (let j = 1; j <= to; j += 1) {
      if (filter(j)) {
        if (j === 1) {
          Q = P;
        } else if (j === 2) {
          Q = gaps[1];
        } else {
          if ((j - last) % 2 !== 0 || (j - last) / 2 >= gaps.length) {
            throw new Error();
          }
          Q = curve.addPoints(Q, gaps[(j - last) >> 1]);
        }
        if (Q == null) {
          return null;
        }
        array[j] = Q;
        last = j;
      }
    }
    return array;
  };

  const verbose = true;//TODO: ?
  const B2 = Math.ceil(B * Math.log2(B) * Math.log(B));// !?

  if (true) {
    const tmp = generateCurveAndStartingPoint(curveParam);
    const curve = tmp.curve;
    if (curve == null) {
      return BigInt(0);
    }
    let P = tmp.startingPoint;
    if (verbose) {
      console.debug('B1: ', B, 'B2: ', B2, 'curveParam: ', curveParam);
    }
    // Phase 1 / Stage 1:
    if (verbose) {
      console.time('stage1');
    }
    const s = product(primes(B).map(p => Math.pow(p, Math.floor(Math.log2(B) / Math.log2(p)))));
    const modMuls0 = modMuls;
    const start = +Date.now();
    let sP = scalePoint(curve, P, s);
    const end = +Date.now();
    if (verbose) {
      console.timeEnd('stage1');
    }
    if (verbose) {
      console.debug('modmuls per second: ', (modMuls - modMuls0) * 1000 / (end - start));
    }
    ecm.modMuls = modMuls;

    if (true && sP != null && sP.z != null) {
      let g = BigInt(gcd(BigInt(sP.x) % BigInt(N), N));
      let B1 = B;
      while (BigInt(g) === BigInt(N) && B1 >= 2) {
        //TODO: what to do here?
        if (B === B1) {
          console.warn('N!', N);
        }
        B1 = Math.ceil(B1 / 2);
        const s = product(primes(B1).map(p => Math.pow(p, Math.floor(Math.log2(B1) / Math.log2(p)))));
        sP = scalePoint(curve, P, s);
        if (sP == null) {// done
          g = BigInt(1);
        } else {
          g = gcd(BigInt(sP.x) % BigInt(N), N);
        }
      }
      if (g > BigInt(1) && g < BigInt(N)) {
        sP = null;
        failure = g;
      }
    }

    if (sP == null) {
      if (failure !== BigInt(1) && failure !== BigInt(N)) {
        if (verbose) {
          console.debug('stage1 success');
        }
        return failure;
      }
      console.warn('N');
      return BigInt(0);
    }

    if (true) {
      // Phase 2 / Stage 2:
      if (verbose) {
        console.time('stage2');
      }
      // Stage 2 has an optimization to reduce number of curve operations:
      // It is some very-very simplified idea from https://www.hyperelliptic.org/tanja/SHARCS/talks06/Gaj.pdf :

      // We want to compute p * P, where p is prime and check if computation fails
      // if we choose some d, then p can be represted using Eucidean division as:
      // p = i * d + j
      // If we choose d ~= sqrt(B2), i and j are limited to have only O(sqrt(B2)) values
      // and we can precalculate (i * d) * P and j * P.
      // Then we only need to check if addition fails for (i * d) * P and j * P.

      const useMultipointPolynomialEvaluation = true;//TODO: !?
      const primorial = 210 * (B2 > Math.pow(2, 27) ? 11 : 1);
      const x = 48 * (B2 > Math.pow(2, 27) ? 10 : 1); // 48 - the number of prime candidates out of 210 integers when sieving with basis {2, 3, 5, 7}
      const d = Math.round(Math.sqrt((primorial / x) * 2 * B2) / primorial) * primorial;
      const dsP = scalePoint(curve, sP, d);
      if (dsP != null) {

        console.assert(d % 210 === 0);
        const filter = function (j) { return j % 2 !== 0 && j % 3 !== 0 && j % 5 !== 0 && j % 7 !== 0 && (d % 11 !== 0 || j % 11 !== 0); }; //TODO: smallgcd(d / 210, j) !== 1
        const P1array = pointsRange(curve, dsP, Math.round(B2 / d));
        const P2array = pointsRangeFiltered(curve, sP, d / 2, filter);

        for (let i = Math.max(1, Math.round(B / d)) - 1; i >= 0; i -= 1) {
          P1array[i] = null;
        }

        if (false) {
          // check:
          for (let i = 0; i < P1array.length; i += 1) {
            for (let j = 0; j < P2array.length; j += 1) {
              const P1 = P1array[i];
              const P2 = P2array[j];
              if (P1 != null && P2 != null) {
                const p = i * d + j;
                const S = curve.addPoints(P1, P2);
                const E = scalePoint(curve, sP, p);
                console.assert(S.x + '' === E.x + '' && S.y + '' === E.y + '');
              }
            }
          }
        }

        do {
          if (failure !== BigInt(1)) {
            break;
          }
          const x1array = restoreNulls(curve.phi(P1array.filter(P => P != null)), P1array);
          const x2array = restoreNulls(curve.phi(P2array.filter(P => P != null)), P2array);
          if (failure !== BigInt(1)) {
            break;
          }

          // now we want to calc gcd(prod_i prod_j (x_(1,i)-x_(2,j)) mod N, N)

          if (useMultipointPolynomialEvaluation) {
            let x2s = x2array.filter(x => x != null);
            let x1s = x1array.filter(x => x != null);
            //console.debug('x1s, x2s', x1s.length, x2s.length, d, B);
            if (+x1s.length < +x2s.length) {
              //console.warn('<');
              const tmp = x1s;
              x1s = x2s;
              x2s = tmp;
            }
            //console.time('products');
            const polynomial = Polynomial.fromRoots(x1s, N);
            const products = Polynomial.evaluateModP(polynomial, x2s, N);
            //console.timeEnd('products');
            let p = BigInt(1);
            for (let j = 0; j < products.length; j += 1) {
              p = modmul(p, products[j]);
            }
            if (BigInt(gcd(BigInt(p) % BigInt(N), N)) !== BigInt(1)) {
              for (let j = 0; j < products.length; j += 1) {
                const product = products[j];
                const u = BigInt(gcd(product, N));
                if (u < 1 || u > N) throw new Error();
                if (u !== BigInt(1) && u !== BigInt(N)) {
                  failure = u;
                  break;
                }
                //TODO: - ?
                if (u !== BigInt(1)) {
                  console.warn('N');
                }
              }
            }
          } else {
            let product = BigInt(1);
            let count = 0;
            for (const p of primes(B2)) {
              if (failure !== BigInt(1)) {
                break;
              }
              if (+p >= +B) {
                // p = i * d + j
                const i = Math.round(p / d);
                let j = p - d * i;
                j = j < 0 ? -j : j;
                // only check if point addition fails:
                // Note: is is also possible to remove -j or j as x_coordinate(j*P) === x_coordinate(-j*P), this is <20% of cases
                const x1 = x1array[i];
                const x2 = x2array[j];
                if (x1 != null && x2 != null) {
                  product = modmul(product, modsub(x1, x2));
                  count += 1;
                  if (count % 1024 === 0) {
                    const u = BigInt(gcd(BigInt(product) % BigInt(N), N));
                    if (u !== BigInt(1) && u !== BigInt(N)) {
                      failure = u;
                      break;
                    }
                    //TODO: - ?
                    if (u !== BigInt(1)) {
                      console.warn('N');
                    }
                    product = BigInt(1);
                  }
                }
              }
            }
            //console.debug('count', count / primes(B2).length, x1array.filter(x => x != null).length * x2array.filter(x => x != null).length / count);
          }
        } while (false);
      }
      if (verbose) {
        console.timeEnd('stage2');
      }
      ecm.modMuls = modMuls;
      if (failure !== BigInt(1) && failure !== BigInt(N)) {
        if (verbose) {
          console.debug('stage2 success');
        }
        return failure;
      }
    }
  }

  return BigInt(0);
}


globalThis._ecm = _ecm;
globalThis.ecm = ecm;//TODO:


export default ecm;

// mini polynomial library:

function Polynomial() {
}
Polynomial.fromRoots = fromRoots;
Polynomial.evaluateModP = evaluateModP;

function fromRoots(roots, p) {
  if (roots.length === 0) {
    return [BigInt(1)];
  }
  if (roots.length === 1) {
    return [p - BigInt(roots[0]), BigInt(1)];
  }
  const middle = Math.floor(roots.length / 2);
  const A = fromRoots(roots.slice(0, middle), p);
  const B = fromRoots(roots.slice(middle), p);
  return mod(multiply(A, B), p);
}
function degree(A) {
  return A.length - 1;
}
function height(A) {
  let max = BigInt(0);
  let min = BigInt(0);
  for (let i = 0; i < A.length; i += 1) {
    const a = BigInt(A[i]);
    if (a > max) {
      max = a;
    } else if (min > a) {
      min = a;
    }
  }
  return -min > max ? -min : max;
}

function multiplyKS(A, B) {

  function bitLength(a) {
    const n = Number(BigInt(a));
    if (n < 1/0) {
      return Math.ceil(Math.log2(n + 0.5)) + 1;//?
    }
    return a.toString(16).length * 4;
  }

  function toInteger(coefficients, blockSize) {
    const bigIntCache = new Array(coefficients.length).fill(null);
    function toIntegerInternal(start, end) {
      const k = (end | 0) - (start | 0);
      if (k >= 2) {
        const m = Math.ceil(k / 2);
        if (bigIntCache[m] == null) {
          bigIntCache[m] = BigInt(blockSize * m);
        }
        return (BigInt(toIntegerInternal(start + m, end)) << bigIntCache[m]) + BigInt(toIntegerInternal(start, start + m));
      } else if (k === 1) {
        return coefficients[start];
      } else {
        throw new RangeError();
      }
    }
    let n = toIntegerInternal(0, coefficients.length);
    return n;
  }

  function toPolynomial(bigint, blockSize, blocksCount) {
    const bigIntCache = new Array(blocksCount).fill(null);
    const k = blocksCount;
    const coefficients = new Array(k);
    function toPolynomialInternal(C, start, end) {
      const k = (end | 0) - (start | 0);
      if (k >= 2) {
        const m = Math.ceil(k / 2);
        const r = BigInt.asUintN(blockSize * m, C);
        toPolynomialInternal(r, start, start + m);
        if (bigIntCache[m] == null) {
          bigIntCache[m] = BigInt(blockSize * m);
        }
        const q = BigInt(C) >> bigIntCache[m];
        toPolynomialInternal(q, start + m, end);
      } else if (k === 1) {
        coefficients[start] = C;
      } else {
        throw new RangeError();
      }
    }
    toPolynomialInternal(BigInt(bigint), 0, k);
    return coefficients;
  }

  const blockSize = (bitLength(height(A)) + bitLength(height(B))) + Math.ceil(Math.log2(Math.min(degree(A) + 1, degree(B) + 1)));
  const blocksCount = degree(A) + degree(B) + 1;
  const Ai = BigInt(toInteger(A, blockSize));
  const Bi = BigInt(toInteger(B, blockSize));
  const P = Ai * Bi;
  return toPolynomial(P, blockSize, blocksCount);
}

function multiplySchoolbook(a, b) {
  const c = new Array(a.length - 1 + b.length - 1 + 1).fill(BigInt(0));
  for (let i = 0; i < a.length; i += 1) {
    for (let j = 0; j < b.length; j += 1) {
      c[i + j] += BigInt(a[i]) * BigInt(b[j]);
    }
  }
  return c;
}

function multiply(A, B) {
  if (A.length < 16 || B.length < 16) {
    return multiplySchoolbook(A, B, -1);
  }
  return multiplyKS(A, B, -1);
}

function mod(A, p) {
  return A.map(function (a) {
    const t = BigInt(a) % p;
    return t < BigInt(0) ? BigInt(t) + p : t;
  });
}

function calcAtMod(A, point, p) {
  let y = BigInt(0);
  for (let i = A.length - 1; i >= 0; i -= 1) {
    y = (y * point + A[i]) % p;
  }
  return y;
}

//function scale(A, s) {
//  return A.map(e => e * s);
//}
function subtract(a, b) {
  const c = new Array(Math.max(a.length, b.length));
  const min = Math.min(a.length, b.length);
  for (let i = 0; i < min; i += 1) {
    c[i] = BigInt(a[i]) - BigInt(b[i]);
  }
  for (let i = min; i < a.length; i += 1) {
    c[i] = a[i];
  }
  for (let i = min; i < b.length; i += 1) {
    c[i] = -BigInt(b[i]);
  }
  return c;
}

function reversal(A) {
  return A.slice(0).reverse();
}
function low(A, k) {
  if (k < 0) throw new RangeError();
  return A.slice(0, k);
}
function high(A, k) {
  if (k < 0) throw new RangeError();
  return A.slice(k);
}
function shift(A, k) {
  return new Array(k).fill(BigInt(0)).concat(A);
}

const inv = function (A, k, p) {
  let H = [invmod(A[0], p)];
  let e = 1;
  while (e < k) {
    e *= 2;
    // H - (AH-1)H
    H = subtract(H, shift(low(multiply(mod(high(low(multiply(low(A, e), H), e), e >> 1), p), H), e >> 1), e >> 1));
    // 2H - A(HH)
    //H = low(subtract(scale(H, BigInt(2)), mod(low(multiply(low(A, e), mod(multiply(H, H), p)), e), p)), e);
    H = mod(H, p);
    let c = 1;
    while (e * c < k) {
      c *= 2;
    }
    if ((e - 1) * c >= k) {
      e -= 1;
      H = low(H, e);
    }
  }
  return low(H, e);
};

function LaurentSeries(coefficients, lowestDegree) {
  this.coefficients = coefficients;
  this.lowestDegree = lowestDegree;
}
LaurentSeries.inverse = function (polynomial, precision, p) {
  const revQ = inv(reversal(polynomial), precision, p);
  const Q = shift(reversal(revQ), precision - 1 - degree(revQ));
  return new LaurentSeries(Q, 0 - degree(polynomial) - (precision - 1));//TODO: verify?
};
LaurentSeries.prototype.multiplyMod1 = function (polynomial, precision, p) {
  const e = this.lowestDegree;
  if (0 - precision - e < degree(polynomial)) {
    throw new RangeError('inacurracy');
  }
  //TODO: multiplyMiddle - ?
  // if to split "this" and use multiplyLow two times it works slower
  let c = multiply(this.coefficients, polynomial);
  c = low(c, 0 - e);
  c = high(c, 0 - precision - e);
  c = mod(c, p);
  return new LaurentSeries(c, 0 - precision);
};
LaurentSeries.prototype.multiplyTrunc = function (polynomial) {
  const e = this.lowestDegree;
  let c = multiply(this.coefficients, polynomial);
  c = high(c, Math.max(0 - e, 0));
  return c;
};
LaurentSeries.prototype.toString = function () {
  let s = '';
  for (let i = this.coefficients.length - 1; i >= 0; i -= 1) {
    let c = this.coefficients[i];
    s += (c >= BigInt(0) ? '+' : '') + c + 'x^' + (i + this.lowestDegree);
  }
  return s + '+...';
};

function evaluateModP(A, points, p) {
  // https://en.wikipedia.org/wiki/Polynomial_evaluation#Multipoint_evaluation
  const simple = false;
  if (simple) {
    const results = new Array(points.length);
    for (let i = 0; i < points.length; i += 1) {
      results[i] = calcAtMod(A, points[i], p);
    }
    return results;
  }
  const makeProductsTree = function (points) {
    if (points.length <= 8) {
      return {left: null, right: null, product: fromRoots(points, p), points: points};
    }
    const middle = Math.floor(points.length / 2);
    const left = makeProductsTree(points.slice(0, middle));
    const right = makeProductsTree(points.slice(middle));
    const product = mod(multiply(left.product, right.product), p);
    return {
      left: left,
      right: right,
      product: product,
      points: points
    };
  };
  const node = makeProductsTree(points);
  // a simple version of scaled remainder three from https://cr.yp.to/arith/scaledmod-20040820.pdf
  const f = function (UoverPmod1, node, p) {
    if (node.left == null || node.right == null) {
      const R = mod(UoverPmod1.multiplyTrunc(node.product), p);
      const results = new Array(node.points.length);
      for (let i = 0; i < node.points.length; i += 1) {
        results[i] = calcAtMod(R, node.points[i], p);
      }
      return results;
    }
    const P0 = node.left.product;
    const P1 = node.right.product;
    const UoverP0mod1 = UoverPmod1.multiplyMod1(P1, degree(P0), p);
    const UoverP1mod1 = UoverPmod1.multiplyMod1(P0, degree(P1), p);
    //console.assert(UoverP0mod1.toString() === LaurentSeries.inverse(P0, degree(A) + 1, p).multiplyMod1(A, degree(P0), p).toString());
    //console.assert(UoverP1mod1.toString() === LaurentSeries.inverse(P1, degree(A) + 1, p).multiplyMod1(A, degree(P1), p).toString());
    return f(UoverP0mod1, node.left, p).concat(f(UoverP1mod1, node.right, p));
  };
  const U = A;
  const P = node.product;
  const Pinv = LaurentSeries.inverse(P, degree(U) + 1, p);
  const UoverPmod1 = Pinv.multiplyMod1(U, degree(P), p);
  return f(UoverPmod1, node, p);
}

if (false) {

  console.assert(multiplyKS([BigInt(1), BigInt(1), BigInt(1), BigInt(1)], [BigInt(1), BigInt(1), BigInt(1), BigInt(1)]).toString() === '1,2,3,4,3,2,1');
  console.assert(multiplySchoolbook([BigInt(1), BigInt(1), BigInt(1), BigInt(1)], [BigInt(1), BigInt(1), BigInt(1), BigInt(1)]).toString() === '1,2,3,4,3,2,1');

  var p = Polynomial.fromRoots([BigInt(1), BigInt(2), BigInt(3), BigInt(4), BigInt(5)], BigInt(17));
  var vals = Polynomial.evaluateModP(p, [BigInt(7), BigInt(8), BigInt(9), BigInt(10), BigInt(1)], BigInt(17));
  console.assert(vals.toString() === '6,4,5,7,0');

  var P = [BigInt(24), -BigInt(50), BigInt(35), -BigInt(10), BigInt(1)]; // x4-10x^3+35x^2-50^x+24
  var Pinv = LaurentSeries.inverse(P, 4, BigInt(1) << BigInt(1024));
  console.assert(Pinv.toString() === '+1x^-4+10x^-5+65x^-6+350x^-7+...');

  var Pinv2 = LaurentSeries.inverse(P, 5, BigInt(1) << BigInt(1024));
  console.assert(Pinv2.toString() === '+1x^-4+10x^-5+65x^-6+350x^-7+1701x^-8+...');

  var U = [BigInt(1), BigInt(4), BigInt(1), BigInt(3)]; //  3x^3 + 1x^2 + 4^x+1
  var UoverPmod1 = Pinv.multiplyMod1(U, degree(P), BigInt(1) << BigInt(1024));
  console.assert(UoverPmod1.toString() === '+3x^-1+31x^-2+209x^-3+1156x^-4+...');

  var P1 = [BigInt(12), -BigInt(7), BigInt(1)]; //  x^2 - 7^x + 12
  var X = UoverPmod1.multiplyMod1(P1, degree(P1), BigInt(1) << BigInt(1024));
  console.assert(X.toString() === '+28x^-1+65x^-2+...');

  var P0 = [BigInt(2), -BigInt(3), BigInt(1)]; // x^2-3x+2
  var P0inv = LaurentSeries.inverse(P0, 4, BigInt(1) << BigInt(1024));
  var X2 = P0inv.multiplyMod1(U, degree(P0), BigInt(1) << BigInt(1024));
  console.assert(String(X.toString()) === String(X2.toString()));//???

  var R = X.multiplyTrunc(P0);
  console.assert(R.toString() === '-19,28', R);


  var vals = Polynomial.evaluateModP(U, [BigInt(1), BigInt(2), BigInt(3), BigInt(4)], BigInt(1) << BigInt(1024));
  console.assert(String(vals.toString()) === String([BigInt(9), BigInt(37), BigInt(103), BigInt(225)].toString()));


  var tests = [
    {A: [1, 2, 3], e: 0, B: [1, 2, 3], precision: 3, result: null},
    {A: [1, 2, 3], e: -1, B: [1], precision: 3, result: null},  
    {A: [1, 2, 3], e: -1, B: [1, 2, 3], precision: 3, result: null},
    {A: [1, 0, 2, 3], e: -2, B: [1, 2, 3], precision: 3, result: null},

    {A: [1, 2, 3, 4, 5, 6], e: -6, B: [1, 2, 3], precision: 3, result: [16, 22, 28]},
    {A: [1, 2, 3, 4, 5, 6], e: -6, B: [1, 2, 3, 4, 5, 6], precision: 3, result: null},
    {A: [1, 2, 3, 4, 5, 6, 7], e: -7, B: [1, 2, 3, 4, 5, 6], precision: 3, result: null},
    {A: [1, 2, 3, 4, 5, 6, 7, 8], e: -8, B: [1, 2, 3, 4, 5, 6], precision: 3, result: [56, 77, 98]},

    {A: [1, 2, 3, 4], e: -4, B: [1, 2], precision: 4, result: null},
    {A: [2, 2, 3, 4], e: -4, B: [1, 2], precision: 4, result: null},
    
    {A: [1, 2, 3, 4], e: -4, B: [1, 2], precision: 3, result: [4, 7, 10]},
    {A: [2, 2, 3, 4], e: -4, B: [1, 2], precision: 3, result: [6, 7, 10]},

    {A: [1, 2, 3, 4], e: -4, B: [1, 2], precision: 2, result: [7, 10]},
    {A: [2, 2, 3, 4], e: -4, B: [1, 2], precision: 2, result: [7, 10]},

    //{A: [1, 2, 3], e: 0, B: [], precision: 1, result: []},
  ];

  for (var test of tests) {
    try {
      var result = new LaurentSeries(test.A.map(n => BigInt(n)), test.e).multiplyMod1(test.B.map(n => BigInt(n)), test.precision, BigInt(1) << BigInt(1024));
      console.assert(test.result != null && String(new LaurentSeries(test.result.map(n => BigInt(n)), 0 - test.precision).toString()) === String(result.toString()));
    } catch (error) {
      console.assert(test.result == null, error);
    }
  }

}
