"""Exact transition certificates for the colossally abundant numbers through 5040."""
from collections import Counter
from math import isqrt, prod


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def first_unused_primes(exponents):
    p = 2
    unused = []
    while len(unused) < 2:
        if p not in exponents and is_prime(p):
            unused.append(p)
        p += 1
    return unused


def crosses(p, exponent, a, b):
    """Compare sigma(p^(e+1))/sigma(p^e) with p^(a/b), by exact powers."""
    left = (p**(exponent + 2) - 1)**b
    right = (p**(exponent + 1) - 1)**b * p**a
    return (left > right) - (left < right)


# Each rational a/b strictly separates the next transition from every competitor.
events = [(2,3,2), (3,5,4), (2,6,5), (5,10,9), (2,12,11),
          (3,15,14), (7,16,15), (2,23,22), (11,29,28)]
exponents = Counter()
prefix = []
for winner, a, b in events:
    candidates = sorted(exponents) + first_unused_primes(exponents)
    assert a > b > 0 and winner in candidates
    for p in candidates:
        assert crosses(p, exponents[p], a, b) == (1 if p == winner else -1)
    exponents[winner] += 1
    prefix.append(prod(p**e for p, e in exponents.items()))
assert prefix == [2, 6, 12, 60, 120, 360, 2520, 5040, 55440]
print("Uniquely ordered CA transitions:", *prefix)
