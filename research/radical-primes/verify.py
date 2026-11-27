"""Exact certificates for the coefficient sequences. Run with Python 3.10+."""
from __future__ import annotations

import argparse
import csv
from functools import lru_cache
from math import isqrt, prod
from pathlib import Path
from typing import Iterable


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def multiply(family: str, left: tuple[int, ...], right: tuple[int, ...], modulus: int = 0):
    """Multiply independently in the quotient ring using the defining monomial relations."""
    result = [0] * len(left)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            if family == "quadratic":
                index = i ^ j
                factor = (2 if i & j & 1 else 1) * (3 if i & j & 2 else 1)
            elif family == "cubic":
                exponent, index = divmod(i + j, 3)
                factor = 2 ** exponent
            else:
                raise ValueError(family)
            result[index] += factor * a * b
    return tuple(x % modulus if modulus else x for x in result)


def initial(family: str, c: int):
    if family == "quadratic":
        return (1, 0, 0, 0), (c, 1, 1, 0)
    return (1, 0, 0), (0, 1, 1)


WITNESSES = ((1, 23, 5, 7, 5), (2, 241, 22, 56, 231), (3, 167, 13, 62, 153))
GROUPS = ((188570, "quadratic", 1, 6), (377109, "quadratic", 2, 7),
          (377113, "quadratic", 3, 4), (377117, "cubic", 0, 6))
PRIMES = (2, 3, 5, 7, 11, 13, 17)


def scalar_certificates():
    for c, p, r, s, expected_product in WITNESSES:
        assert is_prime(p) and r * r % p == 2 and s * s % p == 3
        bases = [(c + i * r + j * s) % p for i in (-1, 1) for j in (-1, 1)]
        assert all(bases)
        state, alpha = initial("quadratic", c)
        first = state
        residues = []
        for n in range(p - 1):
            trace = sum(pow(u, n, p) for u in bases) % p
            assert 4 * state[0] % p == trace
            residues.append(state[0])
            state = multiply("quadratic", state, alpha, p)
        assert state == first and 0 not in residues
        assert prod(residues) % p == expected_product
        print(f"c={c}: prime {p}, block {p-1}, product {expected_product} modulo {p}")


def first_scalar_hit(c: int, p: int) -> int:
    state, alpha = initial("quadratic", c)
    seen = set()
    while state not in seen:
        if state[0] == 0:
            return len(seen)
        seen.add(state)
        state = multiply("quadratic", state, alpha, p)
    raise AssertionError(f"no zero at c={c}, p={p}")


@lru_cache(maxsize=100)
def cycle(family: str, c: int, p: int):
    state, alpha = initial(family, c)
    seen = {}
    states = []
    while state not in seen:
        seen[state] = len(states)
        states.append(state)
        state = multiply(family, state, alpha, p)
    start = seen[state]
    return start, len(states) - start, states


def shortest_word(word: list[int]) -> list[int]:
    for d in range(1, len(word) + 1):
        if len(word) % d == 0 and word[:d] * (len(word) // d) == word:
            return word[:d]
    raise ValueError("empty word")


def gap_record(family: str, c: int, p: int, coordinate: int):
    start, length, states = cycle(family, c, p)
    hits = [i for i in range(start, start + length) if not states[i][coordinate]]
    assert hits, (family, c, p, coordinate)
    gaps = [b-a for a, b in zip(hits, hits[1:] + [hits[0]+length])]
    word = shortest_word(gaps)
    early = [i for i in range(start) if states[i][coordinate] == 0]
    if early:
        finite_gaps = [b-a for a, b in zip(early, early[1:] + [hits[0]])]
    else:
        finite_gaps = []
    return start, length, early, hits[0], finite_gaps, word


def mapping() -> Iterable[tuple[str, str, int, int, tuple[int, ...]]]:
    for base, family, c, count in GROUPS:
        for j in range(4 if family == "quadratic" else 3):
            yield f"A{base+j:06d}", family, c, j, PRIMES[:count]


def write_csv(output: Path, header, rows):
    with output.open("w", newline="", encoding="utf8") as f:
        wr = csv.writer(f)
        wr.writerow(header)
        wr.writerows(rows)


def generate(directory: Path):
    directory.mkdir(parents=True, exist_ok=True)
    first_hits = []
    for c, bound, *_ in WITNESSES:
        for p in range(2, bound):
            if is_prime(p):
                first_hits.append((c, p, first_scalar_hit(c, p)))
    write_csv(directory / "smaller-prime-witnesses.csv", ("c", "prime", "first_hit_index"), first_hits)
    rows = []
    for seq, family, c, j, primes in mapping():
        for p in primes:
            start, length, early, first, prefix, word = gap_record(family, c, p, j)
            join = lambda xs: " ".join(map(str, xs))
            rows.append((seq, p, start, length, join(early), first, join(prefix), len(word), join(word)))
    write_csv(directory / "gap-cycles.csv",
              ("sequence", "prime", "state_preperiod", "state_period", "hits_before_cycle",
               "first_hit_in_cycle", "gaps_before_first_cyclic_hit", "least_gap_period", "repeating_gaps"), rows)
    print(f"{len(first_hits)} smaller-prime witnesses; {len(rows)} exact gap cycles.")


def check_exceptions():
    for c in (1, 3):
        assert cycle("quadratic", c, 2)[:2] == (2, 1)
        assert cycle("quadratic", c, 2)[2][-1] == (0, 0, 0, 0)
    start, period, states = cycle("quadratic", 2, 23)
    assert (start, period) == (1, 22)
    for n, coord in ((3, 1), (5, 2), (1, 3)):
        assert states[n][coord] == 0
    for p in (2, 3):
        start, period, states = cycle("cubic", 0, p)
        assert start <= 3 and period == 1 and states[-1] == (0, 0, 0)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    args = ap.parse_args()
    scalar_certificates()
    check_exceptions()
    generate(args.output)
