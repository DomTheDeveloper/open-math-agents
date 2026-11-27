import Endpoint
import Robin1984.Equivalence.Equivalence

namespace RobinExceptions

/-- The statement about the last exception is exactly equivalent to Mathlib's RH. -/
theorem greatest_iff_RH : IsGreatest exceptions 5040 ↔ RiemannHypothesis :=
  greatest_iff_robin.trans Robin1984.riemannHypothesis_iff_nativeRobinInequalityAll.symm

#print axioms greatest_iff_RH
end RobinExceptions
