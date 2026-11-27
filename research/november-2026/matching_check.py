"""Check the block-hafnian specialization by two independent exact enumerations."""
from functools import lru_cache
from itertools import permutations
from math import prod
from random import Random


def permanent(matrix):
    n = len(matrix)
    return sum(prod(matrix[i][j] for i, j in enumerate(p)) for p in permutations(range(n)))


def hafnian(matrix):
    @lru_cache(None)
    def match(indices):
        if not indices:
            return 1
        i, *rest = indices
        return sum(matrix[i][j] * match(tuple(k for k in rest if k != j)) for j in rest)
    return match(tuple(range(len(matrix))))


def main():
    rng = Random(20261127)
    count = 0
    for n in range(1, 7):
        for _ in range(48):
            a = [[rng.randrange(-4, 5) for _ in range(n)] for _ in range(n)]
            c = [[0]*(2*n) for _ in range(2*n)]
            for i in range(n):
                for j in range(n):
                    c[i][n+j] = c[n+j][i] = a[i][j]
            actual = hafnian(c)
            if actual != permanent(a):
                raise RuntimeError((n, a, actual))
            for i in range(2*n):
                c[i][i] = 1 + sum(abs(v) for v in c[i])
            if hafnian(c) != actual:
                raise RuntimeError('The diagonal altered the loopless hafnian')
            count += 1
    print(f'Checked the block identity and positive-definite diagonal completion for {count} signed matrices.')

if __name__ == '__main__':
    main()
