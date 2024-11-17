/*jshint esversion:6*/
/*global BigInt*/
"use strict";
//TODO:
import gcd from './libs/gcd.js';

function primes(MAX) {
  const sieve = new Uint8Array(MAX + 1).fill(1);
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

function invmod(a, m) {
  const [A, B, g] = gcd.gcdext(m, a);
  if (BigInt(g) !== BigInt(1)) {
    return BigInt(0);
  }
  let inv = B;
  inv = inv < BigInt(0) ? inv + m : inv;
  return inv;
}

function wAryNonAdjacentFormMultiplicationChain(s, w = 9) {
  function wNAF(d) {
    // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication#w-ary_non-adjacent_form_(wNAF)_method
    const da = [];
    while (d > BigInt(0)) {
      if ((d & BigInt(1)) !== BigInt(0)) {
        const x = BigInt.asIntN(w, d);
        da.push(Number(x));
        d = d - x;
      } else {
        da.push(0);
      }
      d = d >> BigInt(1);
    }
    return da;
  }
  const d = wNAF(s, w);
  const chain = [];
  const cache = {};
  let Q = -1;
  for (let j = d.length - 1; j >= 0; j -= 1) {
    if (Q !== -1) {
      chain.push([Q, Q]);
      Q = chain.length;
    }
    if (d[j] !== 0) {
      //let x = d[j] * P;
      let i = Math.abs(d[j]);
      if (cache[i] == null) {
        cache[1] = 0;
        for (let k = 3; k <= i; k += 2) {
          if (cache[k] == null) {
            if (cache[2] == null) {
              chain.push([0, 0]);
              cache[2] = chain.length;
            }
            chain.push([cache[k - 2], cache[2]]);
            cache[k] = chain.length;
          }
        }
      }
      const x = cache[i];
      if (Q === -1) {
        Q = x;
      } else {
        if (d[j] < 0) {
          chain.push([Q, -1 - x]);
          Q = chain.length;
        } else {
          chain.push([Q, x]);
          Q = chain.length;
        }
      }
    }
  }
  return chain;
}

function ecm(N, unlimited = false) {
  const factorDigits = unlimited ? 1/0 : (N.toString(2).length * Math.log10(2)) / 4;//TODO: !?
  // https://www.rieselprime.de/ziki/Elliptic_curve_method
  const B = Math.min(Math.round(Math.pow(5, factorDigits / 5) * 16), 1e300);
  let B1 = B;
  while (B1 > 400) {
    B1 = Math.floor(B1 / 5);
  }
  for (; B1 <= B; B1 *= 5) {
    const curves = Math.floor(Math.sqrt(B1)); //TODO: !?
    const f = _ecm(N, curves, B1);//???
    if (f !== BigInt(0)) {
      return f;
    }
  }
  return BigInt(0);
}
ecm.modMuls = 0;

function _ecm(N, curves = 200, B = 50000, parallelCurves = 16) {
  // Lenstra elliptic-curve factorization
  // from https://trizenx.blogspot.com/2018/10/continued-fraction-factorization-method.html:
  // https://github.com/trizen/sidef-scripts/blob/master/Math/elliptic-curve_factorization_method.sf
  // and Cohen 93

  let failure = BigInt(1);
  let modMuls = 0;

  // Barrett Reduction
  // https://www.youtube.com/watch?v=SwYQeeBWlRo&list=PLhCN8H4P5Lvgx5MrIibav6KgbhYj-mn_D&index=7
  const k = BigInt(N.toString(2).length);//TODO:
  const NInv = (BigInt(1) << (k + k)) / N;
  const km1 = k - BigInt(1);
  const kp1 = k + BigInt(1);
  const useBarrettReduction = k > 256;//?

  const modmul = function (a, b) {
    modMuls += 1;
    if (useBarrettReduction) {
      const p = a * b;
      let y = p - (((p >> km1) * NInv) >> kp1) * N;
      while (y < BigInt(0)) {
        y += N;
      }
      while (y >= N) {
        y -= N;
      }
      return y;
    }
    return (a * b) % N;
  };
  const modsub = function (a, b) {
    let y = a - b;
    if (y < BigInt(0)) {
      y += N;
    }
    return y;
  };
  const moddup = function (a) {
    let y = a << BigInt(1);
    if (y >= N) {
      y -= N;
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
    let u = BigInt(invmod(c[n - 1], N));
    for (let i = n - 1; i >= 1; i -= 1) {
      c[i] = modmul(u, c[i - 1]);
      u = modmul(u, a[i]);
    }
    c[0] = u;
    u = BigInt(1);
    return c;
  };

  // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication#Point_operations
  const addPoints = function (a, P1, P2) { // P1 !== P2
    const x1 = P1.x;
    const y1 = P1.y;
    const x2 = P2.x;
    const y2 = P2.y;
    const curves = a.length;
    const v = new Array(curves);
    for (let i = 0; i < curves; i += 1) {
      v[i] = modsub(x1[i], x2[i]);
    }
    const u = modInvParallel(v);
    for (let i = 0; i < curves; i += 1) {
      if (u[i] === BigInt(0)) {
        const g = gcd(v[i], N);
        if (g !== BigInt(1)) {
          failure = g;
          return null;
        }
      }
    }
    const x = new Array(curves);
    const y = new Array(curves);
    for (let i = 0; i < curves; i += 1) {
      const m_i = modmul(u[i], modsub(y1[i], y2[i]));
      const x_i = modsub(modsub(modmul(m_i, m_i), x1[i]), x2[i]);
      const y_i = modsub(modmul(m_i, modsub(x1[i], x_i)), y1[i]);
      x[i] = x_i;
      y[i] = y_i;
    }
    return {x: x, y: y};
  };

  const checkPointsAdd = function (points) { // P1 !== P2
    // like add, but only check if it fails or not
    const buffer = [];
    for (let j = 0; j < points.length; j += 1) {
      const x1 = points[j].P1.x;
      const x2 = points[j].P2.x;
      const curves = Math.min(x1.length, x2.length);
      for (let i = 0; i < curves; i += 1) {
        buffer.push(modsub(x1[i], x2[i]));
      }
    }
    let product = BigInt(1);
    for (let i = 0; i < buffer.length; i += 1) {
      product = modmul(product, buffer[i]);
    }
    const u = BigInt(gcd(product, N));
    if (u !== BigInt(1)) {
      for (let i = 0; i < buffer.length; i += 1) {
        const g = gcd(buffer[i], N);
        if (g !== BigInt(1)) {
          failure = g;
          return false;
        }
      }
    }
    return true;
  };

  const doublePoint = function (a, P) {
    const x = P.x;
    const y = P.y;
    const curves = a.length;
    const v = new Array(curves);
    for (let i = 0; i < curves; i += 1) {
      v[i] = moddup(y[i]);
    }
    const u = modInvParallel(v);
    for (let i = 0; i < curves; i += 1) {
      if (u[i] === BigInt(0)) {
        const g = gcd(v[i], N);
        if (g !== BigInt(1)) {
          failure = g;
          return null;
        }
      }
    }
    const rx = new Array(curves);
    const ry = new Array(curves);
    for (let i = 0; i < curves; i += 1) {
      const t = modmul(x[i], x[i]);
      const m_i = modmul(u[i], modsub(moddup(moddup(t)), modsub(t, a[i])));
      const x_i = modsub(modmul(m_i, m_i), moddup(x[i]));
      const y_i = modsub(modmul(m_i, modsub(x[i], x_i)), y[i]);
      rx[i] = x_i;
      ry[i] = y_i;
    }
    return {x: rx, y: ry};
  };

  const negatePoint = function (P) {
    if (P == null) {
      return null;
    }
    return {x: P.x, y: P.y.map(e => e === BigInt(0) ? BigInt(0) : N - e)};
  };

  const scalePoint = function (a, P, s) {
    // https://cs.au.dk/~ivan/FastExpproject.pdf
    const chain = wAryNonAdjacentFormMultiplicationChain(BigInt(s), 9);
    const g = [];
    g.push(P);
    for (const e of chain) {
      const P1 = g[e[0]];
      const P2 = e[1] < 0 ? negatePoint(g[-1 - e[1]]) : g[e[1]];
      let P3 = null;
      if (e[0] === e[1]) { // P1 === P2
        P3 = doublePoint(a, P1);
      } else {
        P3 = addPoints(a, P1, P2);
      }
      if (P3 == null) {
        return null;
      }
      g.push(P3);
    }
    return g[g.length - 1];
  };

  const SuyamaParametrization = function (sigma, N) {
    // Suyama’s parametrization - see https://members.loria.fr/PZimmermann/papers/ecm-submitted.pdf  
    //let sigma = BigInt(6) % N;
    const u = (sigma * sigma - BigInt(5)) % N;
    const v = (BigInt(4) * sigma) % N;
    const z0inv = invmod(v * v * v, N);
    if (z0inv === BigInt(0)) {
      return null;
    }
    const t = invmod(BigInt(4) * u * u * u * v, N);
    if (t === BigInt(0)) {
      return null;
    }
    let a = ((v - u) * (v - u) * (v - u) * (BigInt(3) * u + v) * t - BigInt(2)) % N;
    let b = u * z0inv % N;
    let x0 = u * u * u % N;
    let y0 = (sigma * sigma - BigInt(1)) * (sigma * sigma - BigInt(25)) * (sigma * sigma * sigma * sigma - BigInt(25)) % N;
    x0 = x0 * z0inv % N;
    y0 = y0 * z0inv % N;
    console.assert((b * y0 * y0 - (x0 * x0 * x0 + a * x0 * x0 + x0)) % N === BigInt(0)); // Montgomery form

    const bInv = invmod(b, N);
    if (bInv === BigInt(0)) {
      return null;
    }
    a = a * bInv % N;
    b = BigInt(1) * bInv * bInv % N;
    x0 = x0 * bInv % N;
    y0 = y0 * bInv % N;
    console.assert((y0 * y0 - (x0 * x0 * x0 + a * x0 * x0 + b * x0)) % N === BigInt(0));

    const _3Inv = invmod(BigInt(3), N);
    if (_3Inv === BigInt(0)) {
      return null;
    }
    const a1 = (BigInt(3) * b - a * a) * _3Inv % N;
    const b1 = (BigInt(2) * a * a * a - BigInt(9) * a * b) * _3Inv * _3Inv * _3Inv % N;
    x0 = (x0 + a * _3Inv) % N;
    y0 = y0;
    a = a1;
    b = b1;
    console.assert((y0 * y0 - (x0 * x0 * x0 + a * x0 + b)) % N === BigInt(0)); // Weierstrass form

    x0 = x0 < BigInt(0) ? x0 + N : x0;
    y0 = y0 < BigInt(0) ? y0 + N : y0;
    a = a < BigInt(0) ? a + N : a;
    b = b < BigInt(0) ? b + N : b;

    return {x0: x0, y0: y0, a: a};
  };

  const C = Math.min(curves, parallelCurves);
  let curveIndex = 0;
  while (curveIndex < curves) {
    const curvesArray = new Array(C);
    const x = new Array(C);
    const y = new Array(C);
    for (let i = 0; i < C; i += 1) {
      let a = BigInt(curveIndex % 2 === 0 ? 3 + Math.floor(curveIndex / 2) : -(3 + Math.floor((curveIndex - 1) / 2)));
      let x0 = BigInt(0);
      let y0 = BigInt(1);
      if (true) {
        const tmp = SuyamaParametrization(BigInt(6) + BigInt(curveIndex), N);
        if (tmp != null) {
          a = tmp.a;
          x0 = tmp.x0;
          y0 = tmp.y0;
        }
      }
      curvesArray[i] = a;
      x[i] = x0;
      y[i] = y0;
      curveIndex += 1;
    }
    const P = {x: x, y: y};
    //console.debug('curves', curvesArray.join(' '));
    // Phase 1 / Stage 1:
    console.time('stage1');
    let s = BigInt(1);
    for (const p of primes(B)) {
      const k = Math.floor(Math.log2(B) / Math.log2(p));
      s *= BigInt(Math.pow(p, k));
    }
    const sP = scalePoint(curvesArray, P, s);
    console.timeEnd('stage1');
    ecm.modMuls = modMuls;
    if (sP == null) {
      if (failure !== BigInt(1) && failure !== BigInt(N)) {
        console.log('stage1 success');
        return failure;
      }
      continue;
    }

    if (true) {
      // Phase 2 / Stage 2:
      console.time('stage2');
      const B2 = Math.ceil(B * Math.log2(B) * 7 * 1.5);// !?
      // Stage 2 has an optimization to reduce number of curve operations:
      // It is some very-very simplified idea from https://www.hyperelliptic.org/tanja/SHARCS/talks06/Gaj.pdf .
      const d = Math.round(Math.sqrt(4 * B2) / 2) * 2;
      const dsP = scalePoint(curvesArray, sP, d);
      if (dsP != null) {
        const makeCache = function (P) {
          const cache = [];
          return function (i) {
            if (cache.length === 0) {
              const Q = doublePoint(curvesArray, P);
              if (Q == null) {
                return null;
              }
              cache.push(null);
              cache.push(P);
              cache.push(Q);
            }
            while (cache.length <= i) {
              cache.push(null);
            }
            const step = i % 2 === 0 ? 1 : 2;
            let j = i;
            while (j >= 0 && cache[j] == null) {
              j -= step;
            }
            while (j < i) {
              const Q = addPoints(curvesArray, cache[j], cache[step]);
              if (Q == null) {
                return null;
              }
              cache[j + step] = Q;
              j += step;
            }
            return cache[i];
          };
        };
        const cache1 = makeCache(dsP);
        const cache2 = makeCache(sP);
        const toadd = [];
        for (const p of primes(B2)) {
          if (p >= B) {
            // p = i * d + j
            const i = Math.round(p / d);
            const j = p - d * i;
            if (i !== 0 && j !== 0) {
              const P1 = cache1(i);
              if (P1 == null) {
                break;
              }
              const P2 = j < 0 ? negatePoint(cache2(-j)) : cache2(j);
              if (P2 == null) {
                break;
              }
              if (false) {
                // check:
                const S = addPoints(curvesArray, P1, P2);
                const E = scalePoint(curvesArray, sP, p);
                console.assert(S.x + '' === E.x + '' && S.y + '' === E.y + '');
              }
              toadd.push({P1: P1, P2: P2});
              if (toadd.length >= 32) {
                //Note: is is also possible to remove -j or j as x_coordinate(j*P) === x_coordinate(-j*P), this is <20% of cases
                if (!checkPointsAdd(toadd)) {
                  if (failure !== BigInt(1) && failure !== BigInt(N)) {
                    break;
                  }
                }
                toadd.length = 0;
              }
            }
          }
        }
      }
      console.timeEnd('stage2');
      ecm.modMuls = modMuls;
      if (failure !== BigInt(1) && failure !== BigInt(N)) {
        console.log('stage2 success');
        return failure;
      }
    }
  }

  console.warn('failed to find a factor');
  return BigInt(0);
}

globalThis._ecm = _ecm;
globalThis.ecm = ecm;//TODO:


export default ecm;
