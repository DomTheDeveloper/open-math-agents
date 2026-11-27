import RegistryStatement
import FromRH

theorem OMA.solution : type_of% @OMA.S_oeis_a070548.main := by
  exact MobiusSigns.sign_counts

#print axioms OMA.solution
