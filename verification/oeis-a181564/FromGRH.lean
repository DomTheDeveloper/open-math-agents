import Classification
import Main
import Weinberger.Main

theorem semiprime_idoneals (n : ℕ) :
    (Idoneal.IsIdoneal n ∧ n.primeFactorsList.length = 2) ↔
      n ∈ SemiprimeIdoneal.listed :=
  SemiprimeIdoneal.classify _ (fun m => Weinberger.isIdoneal_iff_of_GRH
    LFunction_ne_zero_of_half_lt_re m) n

#print axioms semiprime_idoneals
