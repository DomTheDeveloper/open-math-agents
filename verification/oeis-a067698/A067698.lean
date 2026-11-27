import Endpoint
import Main
import Solution

namespace RobinExceptions

/-- The greatest member of OEIS A067698 is 5040. -/
theorem a067698_greatest : IsGreatest exceptions 5040 :=
  greatest_of_robin (Robin1984.robin_inequality_iff_riemannHypothesis.mpr _root_.riemannHypothesis)

#print axioms a067698_greatest

end RobinExceptions
