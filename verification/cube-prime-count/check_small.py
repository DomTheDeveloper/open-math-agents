"""Check the strict cube intervals below the analytic cutoff using an integer sieve."""
from math import isqrt

limit = 64**3
prime = bytearray([1]) * (limit + 1)
prime[0:2] = b"\x00\x00"
for p in range(2, isqrt(limit) + 1):
    if prime[p]:
        start = p*p
        prime[start::p] = bytes((limit - start)//p + 1)

equal = []
for n in range(1, 64):
    count = sum(prime[n**3 + 1:(n+1)**3])
    assert count >= 2*n + 1, (n, count)
    if count == 2*n + 1:
        equal.append(n)
assert equal == [2], equal
print("63 strict cube intervals checked. Unique equality at n=2 (5 primes).")
