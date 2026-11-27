"""Check both formulas for OEIS A251328 using exact integer arithmetic.

Usage: python3 check_A251328.py b251328.txt
The reference table is https://oeis.org/A251328/b251328.txt.
"""
import sys
from itertools import product
from pathlib import Path


def direct_count(n):
    rows = list(product(range(3), repeat=2))
    return sum(
        all(sum(first) + sum(second) in (2, 4, 6)
            for first, second in zip(array, array[1:]))
        for array in product(rows, repeat=n + 1)
    )


def verify(reference):
    expected = dict(
        map(int, line.split()) for line in reference.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    )
    assert sorted(expected) == list(range(1, 211))
    counts = []
    odd = extreme = middle = 1
    for _ in range(211):
        counts.append(4 * odd + 2 * extreme + 3 * middle)
        odd, extreme, middle = 4 * odd, extreme + 3 * middle, 2 * extreme + 3 * middle

    for n in range(1, 6):
        assert direct_count(n) == counts[n], n
    for n, value in expected.items():
        assert counts[n] == value, n

    # The series starts at index 1. Convolve with 1 - 8X + 13X² + 12X³.
    series = [0, *counts[1:]]
    for n in range(len(series)):
        coefficient = sum(
            c * series[n - degree] for degree, c in enumerate((1, -8, 13, 12))
            if degree <= n
        )
        assert coefficient == {1: 39, 2: -141, 3: -108}.get(n, 0), n

    # (2 + sqrt(7))^n = u + v sqrt(7). Adding conjugates eliminates sqrt(7).
    u, v = 1, 0
    for n, value in enumerate(counts):
        assert 56 * 4**n + 70 * u + 182 * v == 14 * value, n
        u, v = 2 * u + 7 * v, u + 2 * v
    print("Exhaustive array counts for n = 1 through 5:", *counts[1:6])
    print("Both formulas and all 210 published terms passed exact integer checks.")


if __name__ == "__main__":
    verify(Path(sys.argv[1]).read_text(encoding="utf-8"))
