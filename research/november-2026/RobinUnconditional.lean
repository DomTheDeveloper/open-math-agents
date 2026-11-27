import ArithSolution
import RobinTransfer

/-- `ArithSolution.robin_inequality` is declared at the root of the MIT verification file. -/
theorem robin_for_all_odd_inputs {n : ℕ} (hn : Odd n) :
    16383 * ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
      Real.exp Real.eulerMascheroniConstant * (8192 * (n : ℝ)) * Real.log (Real.log (8192 * (n : ℝ))) :=
  NovemberRobin.odd_bound _root_.robin_inequality hn
