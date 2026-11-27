"""Compare a=1 representations with the exact prime formula, integer by integer."""
from argparse import ArgumentParser
from math import isqrt


def check(limit: int) -> int:
    if limit < 15:
        raise ValueError("the reported counting formula applies from 15 onward")
    end = limit + 1
    prime = bytearray(b"\x01") * (end + 1)
    prime[:2] = b"\x00\x00"
    for p in range(2, isqrt(end) + 1):
        if prime[p]:
            size = (end - p*p) // p + 1
            prime[p*p::p] = bytes(size)

    # Mark n+1 by its exceptional factorization.
    exceptional = prime.copy()
    exceptional[:1] = b"\x00"
    exceptional[8] = exceptional[16] = 1
    exceptional[::2] = bytes(x | y for x, y in zip(exceptional[::2], prime[:end//2+1]))
    for p in range(2, isqrt(end) + 1):
        if prime[p]:
            exceptional[p*p] = 1

    # Independently eliminate every n+1 admitting 3 <= d < e and n+1 = d*e.
    uncovered = bytearray(b"\x01") * (end + 1)
    uncovered[:2] = b"\x00\x00"
    for d in range(3, isqrt(end) + 1):
        start = d*(d+1)
        if start <= end:
            uncovered[start::d] = bytes((end-start)//d + 1)
    if uncovered != exceptional:
        first = next(i for i, pair in enumerate(zip(uncovered, exceptional)) if pair[0] != pair[1])
        raise ArithmeticError(f"first discrepancy at n={first-1}")

    one = prime.count(1)
    twice = prime.count(1, 0, end//2 + 1)
    square = prime.count(1, 0, isqrt(end) + 1)
    total = uncovered.count(1)
    if total != one + twice + square + 1:
        raise ArithmeticError("prime counting formula disagrees")
    return total


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1_000_000)
    args = parser.parse_args()
    print(f"No first-term-one representation through {args.limit:,}: {check(args.limit):,}")
