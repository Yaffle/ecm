1. Lenstra elliptic-curve factorization

Usage:

```

import ecm from './ecm.js';

console.log(ecm(2n**128n + 1n, true)); // 59649589127497217n, it takes about 2 seconds

```

By default it searches for small factors only. The second argument unlimits the search to look for bigger factors.
If a factor is not found 0n is returned.

Do not call for prime numbers.
