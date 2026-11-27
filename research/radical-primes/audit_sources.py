"""Check the OEIS statements against the coefficient definitions and calculate period tables.

An optional --source-dir supplies the 15 .seq files from the specified oeisdata revision.
Without it, the program downloads those public text files at that revision.
"""
import argparse
from pathlib import Path
import re
from urllib.request import urlopen

from verify import gap_record, initial, is_prime, mapping, multiply, write_csv


REVISION = "976b0c73e00453b1c1e6f16d83108cb9bb744c3b"


def source(sequence, directory):
    if directory is not None:
        return (directory / f"{sequence}.seq").read_text(encoding="utf8")
    url = (f"https://raw.githubusercontent.com/oeis/oeisdata/{REVISION}/"
           f"seq/{sequence[:4]}/{sequence}.seq")
    with urlopen(url, timeout=30) as response:
        return response.read().decode("utf8")


def matches(word, proposed):
    return len(word) == len(proposed) and any(
        proposed == word[i:] + word[:i] for i in range(len(word)))


def main(directory, output):
    rows = []
    wrong_terms = []
    tested_terms = 0
    primes_to_59 = [p for p in range(2, 60) if is_prime(p)]
    for seq, family, c, j, primes in mapping():
        lines = source(seq, directory).splitlines()
        terms = [int(x) for line in lines if line.startswith(("%S ", "%T ", "%U "))
                 for x in line.split(" ", 2)[2].strip(",").split(",")]
        state, alpha = initial(family, c)
        for n, value in enumerate(terms):
            if state[j] != value:
                wrong_terms.append((seq, n, value, state[j]))
            state = multiply(family, state, alpha)
        tested_terms += len(terms)
        header = next(line for line in lines if line.startswith("%C ") and "period lengths" in line)
        lengths = list(map(int, re.search(r"period lengths ([\d, ]+)", header)[1].strip().split(",")))
        assert len(lengths) == len(primes)
        proposed = {}
        for line in lines:
            if line.startswith("%C "):
                m = re.search(r"p\s*=\s*(\d+)\s*:\s*\(\s*([\d,\s]+)\)", line)
                if m:
                    proposed[int(m[1])] = list(map(int, m[2].strip().strip(",").split(",")))
        for p, length in zip(primes, lengths):
            word = gap_record(family, c, p, j)[-1]
            q = primes_to_59[p-1]
            lifted = gap_record(family, c, q, j)[-1]
            shows = p in proposed
            rows.append((seq, p, length, len(word), q, len(lifted), shows,
                         matches(word, proposed[p]) if shows else "",
                         matches(lifted, proposed[p]) if shows else ""))
    assert wrong_terms == [("A377117", 1, 1, 0)]
    assert len(rows) == 86
    assert sum(r[6] for r in rows) == 81
    assert sum(r[7] is True for r in rows) == 2
    assert sum(r[8] is True for r in rows) == 75
    output.mkdir(parents=True, exist_ok=True)
    write_csv(output / "source-cycle-audit.csv",
              ("sequence", "labeled_prime", "stated_gap_period_length", "actual_gap_period_length",
               "prime_at_labeled_prime_index", "gap_period_length_at_reindexed_prime",
               "has_explicit_source_block", "block_matches_at_label_up_to_rotation",
               "block_matches_at_reindexed_prime_up_to_rotation"), rows)
    print(f"{tested_terms} displayed terms checked; discrepancy (entry, n, listed, defined): {wrong_terms}")
    print("81 explicit blocks: 2 match the label, 75 match the prime indexed by the label.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-dir", type=Path)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    options = parser.parse_args()
    main(options.source_dir, options.output)
