1. Lenstra elliptic-curve factorization

Usage:

npm install @yaffle/ecm

```

import ecm from './ecm.js';

console.log(ecm(2n**128n + 1n, true)); // 59649589127497217n, it takes about 2 seconds

function factors(n, count) {
  const f = ecm(n, true);
  return [f].concat(count === 2 ? [n / f] : factors(n / f, count - 1));
}

console.time();
console.log(factors(2n**2048n+1n, 5)); //  ~3 minutes
console.timeEnd();

console.time();
console.log(factors(2n**1024n+1n, 4)); //  ~2 days
console.timeEnd();

```

By default it searches for small factors only. The second argument unlimits the search to look for bigger factors.
If a factor is not found 0n is returned.

Do not call for prime numbers.
