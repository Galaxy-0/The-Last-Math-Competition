import Conjecture9028

-- Definition, declaration-type and transitive dependency audit.

#print Conjecture9028.IntegerEven
#print Conjecture9028.IntegralLattice
#print Conjecture9028.EvenLattice
#print Conjecture9028.gramMatrix
#print Conjecture9028.EvenDeterminant
#print Conjecture9028.EvenDeterminantNecessary
#print Conjecture9028.EvenDeterminantSufficient
#print Conjecture9028.ClaimedEvennessCriterion
#print Conjecture9028.A2.Ambient
#print Conjecture9028.A2.space
#print Conjecture9028.A2.coordinatesEquiv
#print Conjecture9028.A2.realBasis
#print Conjecture9028.A2.lattice
#print Conjecture9028.A2.intBasis
#print Conjecture9028.A2.lattice_discrete
#print Conjecture9028.A2.lattice_isZLattice
#print Conjecture9028.A2.coord
#print Conjecture9028.A2.integerPairing
#print Conjecture9028.A2.gram
#print Conjecture9028.A2.realGram
#print Conjecture9028.Diagonal.Ambient
#print Conjecture9028.Diagonal.plane
#print Conjecture9028.Diagonal.parametrization
#print Conjecture9028.Diagonal.realBasis
#print Conjecture9028.Diagonal.lattice
#print Conjecture9028.Diagonal.intBasis
#print Conjecture9028.Diagonal.lattice_discrete
#print Conjecture9028.Diagonal.lattice_isZLattice

#check Conjecture9028.A2.intBasis_coe
#print axioms Conjecture9028.A2.intBasis_coe
#check Conjecture9028.A2.lattice_discrete
#print axioms Conjecture9028.A2.lattice_discrete
#check Conjecture9028.A2.lattice_isZLattice
#print axioms Conjecture9028.A2.lattice_isZLattice
#check Conjecture9028.A2.space_finrank
#print axioms Conjecture9028.A2.space_finrank
#check Conjecture9028.A2.lattice_finrank
#print axioms Conjecture9028.A2.lattice_finrank
#check Conjecture9028.A2.realBasis_apply
#print axioms Conjecture9028.A2.realBasis_apply
#check Conjecture9028.A2.lattice_coordinates
#print axioms Conjecture9028.A2.lattice_coordinates
#check Conjecture9028.A2.integerPairing_eq_inner
#print axioms Conjecture9028.A2.integerPairing_eq_inner
#check Conjecture9028.A2.integral_pairing
#print axioms Conjecture9028.A2.integral_pairing
#check Conjecture9028.A2.even_norm
#print axioms Conjecture9028.A2.even_norm
#check Conjecture9028.A2.even_inner
#print axioms Conjecture9028.A2.even_inner
#check Conjecture9028.A2.positive_definite
#print axioms Conjecture9028.A2.positive_definite
#check Conjecture9028.A2.lattice_positive_definite
#print axioms Conjecture9028.A2.lattice_positive_definite
#check Conjecture9028.A2.gram_eq
#print axioms Conjecture9028.A2.gram_eq
#check Conjecture9028.A2.gram_real
#print axioms Conjecture9028.A2.gram_real
#check Conjecture9028.A2.gram_det
#print axioms Conjecture9028.A2.gram_det
#check Conjecture9028.A2.gram_det_odd
#print axioms Conjecture9028.A2.gram_det_odd
#check Conjecture9028.A2.realGram_eq
#print axioms Conjecture9028.A2.realGram_eq
#check Conjecture9028.A2.realGram_det
#print axioms Conjecture9028.A2.realGram_det
#check Conjecture9028.A2.realGram_det_not_even
#print axioms Conjecture9028.A2.realGram_det_not_even
#check Conjecture9028.Diagonal.mem_plane
#print axioms Conjecture9028.Diagonal.mem_plane
#check Conjecture9028.Diagonal.intBasis_coe
#print axioms Conjecture9028.Diagonal.intBasis_coe
#check Conjecture9028.Diagonal.lattice_discrete
#print axioms Conjecture9028.Diagonal.lattice_discrete
#check Conjecture9028.Diagonal.lattice_isZLattice
#print axioms Conjecture9028.Diagonal.lattice_isZLattice
#check Conjecture9028.Diagonal.plane_finrank
#print axioms Conjecture9028.Diagonal.plane_finrank
#check Conjecture9028.Diagonal.lattice_finrank
#print axioms Conjecture9028.Diagonal.lattice_finrank
#check Conjecture9028.Diagonal.plane_inner
#print axioms Conjecture9028.Diagonal.plane_inner
#check Conjecture9028.Diagonal.realBasis_zero
#print axioms Conjecture9028.Diagonal.realBasis_zero
#check Conjecture9028.Diagonal.realBasis_one
#print axioms Conjecture9028.Diagonal.realBasis_one
#check Conjecture9028.Diagonal.gram_eq
#print axioms Conjecture9028.Diagonal.gram_eq
#check Conjecture9028.Diagonal.gram_det
#print axioms Conjecture9028.Diagonal.gram_det
#check Conjecture9028.Diagonal.basis_repr
#print axioms Conjecture9028.Diagonal.basis_repr
#check Conjecture9028.Diagonal.integral_pairings
#print axioms Conjecture9028.Diagonal.integral_pairings
#check Conjecture9028.Diagonal.first_basis_inner
#print axioms Conjecture9028.Diagonal.first_basis_inner
#check Conjecture9028.Diagonal.first_basis_norm_sq
#print axioms Conjecture9028.Diagonal.first_basis_norm_sq
#check Conjecture9028.Diagonal.lattice_vector_norm_sq
#print axioms Conjecture9028.Diagonal.lattice_vector_norm_sq
#check Conjecture9028.Diagonal.even_determinant
#print axioms Conjecture9028.Diagonal.even_determinant
#check Conjecture9028.Diagonal.not_even
#print axioms Conjecture9028.Diagonal.not_even
#check Conjecture9028.Diagonal.plane_positive
#print axioms Conjecture9028.Diagonal.plane_positive
#check Conjecture9028.Diagonal.counterexample
#print axioms Conjecture9028.Diagonal.counterexample
#check Conjecture9028.a2_integral
#print axioms Conjecture9028.a2_integral
#check Conjecture9028.a2_even
#print axioms Conjecture9028.a2_even
#check Conjecture9028.a2_determinant_not_even
#print axioms Conjecture9028.a2_determinant_not_even
#check Conjecture9028.determinant_not_necessary
#print axioms Conjecture9028.determinant_not_necessary
#check Conjecture9028.determinant_not_sufficient
#print axioms Conjecture9028.determinant_not_sufficient
#check Conjecture9028.both_directions_fail
#print axioms Conjecture9028.both_directions_fail
#check Conjecture9028.conjecture_false
#print axioms Conjecture9028.conjecture_false
