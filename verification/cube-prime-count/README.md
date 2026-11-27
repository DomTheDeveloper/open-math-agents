# A linear lower bound for primes between consecutive cubes

For every integer n ≥ 1, at least 2n+1 primes lie strictly between n³ and (n+1)³. Equality occurs exactly when n = 2, where the primes are 11, 13, 17, 19 and 23. This proves claim (B) in [Primes Between Consecutive Cubes](https://www.mathaddict.net/primecubes.htm). [Schoenfeld's explicit bound](https://doi.org/10.1090/S0025-5718-1976-0457374-X)

Write y=n+1 and L=log y. When n ≥ 64, both endpoints exceed Schoenfeld's threshold 2657. The difference of their logarithmic integrals is at least (y³−n³)/(3L), hence at least n²/L. Schoenfeld bounds each endpoint error by 3y√y L/(8π). The count is consequently greater than n²/L − 3y√y L/(4π).

The elementary estimate L ≤ (3/2)y^(1/4) follows from log z ≤ z/e at z=y^(1/4). Consequently (3/(4π))y√y L² ≤ (9/16)y². Also L ≤ n/8 by applying log t ≤ t−1 at t=y/64. Direct expansion gives (2n+1)n/8 + 9(n+1)²/16 < n² when n ≥ 64. These inequalities give strict excess above 2n+1.

Lean 4.36.0 checked the tail deduction from the explicit prime-counting and logarithmic-integral estimates and the finite range separately. The analytic deduction uses the three standard axioms. The finite table uses `native_decide`; the independent sieve can be run with `python3 check_small.py`. The upper cube is composite, so the prime-counting difference agrees with the open-interval count.

The final module imports Schoenfeld's constant 1/(8π) and the supplied RH proof, and prints the axioms of the combined result. Its upstream audit records native finite checks. Run `lake update && lake build` from this directory for the complete dependency build. [Pinned Schoenfeld project](https://github.com/senamakel/schoenfeld-rh/tree/0d24a0c5eac14301655ed2c65163404560e07892)
