# The greatest Robin exception is 5040

[OEIS A067698](https://oeis.org/A067698) contains the integers n ≥ 2 for which exp(γ)n log log n ≤ σ(n). Its greatest member is 5040.

Exact divisor arithmetic gives σ(5040) = 19344. The 256th harmonic number and a lower bound on log 2 give γ < 0.58. Taylor bounds then give exp(γ) < 1.787 and log log 5040 < 2.144. Their product with 5040 is below 19309.894, proving strict failure at 5040. For every larger integer the strict Robin bound follows from RH. The Lean project also proves the converse implication between greatestness and the Robin tail.

Lean 4.33.1 compiled the endpoint and `leanchecker` replayed it. Its printed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The included interface check compares the local theorem to the fully elaborated Robin inequality from the published verification. The published verification supplied RH to the same Robin criterion. [Arithmetic verification](https://math.mit.edu/~drew/grh/)

Run `lake update && lake build` for the full pinned import, or `lake build Endpoint && lake env leanchecker Endpoint` to replay the finite endpoint alone.
