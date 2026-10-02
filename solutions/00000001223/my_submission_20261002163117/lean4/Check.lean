import Main

-- Echo every audited quantity so the log shows the computations themselves.
#eval twoCopTable K4nbr 4
#eval twoCopTable PetersenNbr 10
#eval twoCopTable Q3nbr 8
#eval twoCopTable K33nbr 6
#eval twoCopTable prismNbr 6
#eval (List.range 4).all (fun v => surrounded K4nbr (K4nbr v) v)
#eval cubicTable K4nbr 4
#eval cubicTable PetersenNbr 10
#eval cubicTable Q3nbr 8
#eval cubicTable K33nbr 6
#eval cubicTable prismNbr 6
#eval symmetricTable K4nbr 4
#eval symmetricTable PetersenNbr 10
#eval symmetricTable Q3nbr 8
#eval symmetricTable K33nbr 6
#eval symmetricTable prismNbr 6

-- Axiom audit: every theorem must come out "does not depend on any axioms".
#print axioms K4_is_cubic
#print axioms K4_is_symmetric
#print axioms K4_two_cops_never_surround
#print axioms K4_three_cops_surround
#print axioms Petersen_is_cubic
#print axioms Petersen_is_symmetric
#print axioms Petersen_two_cops_never_surround
#print axioms Q3_is_cubic
#print axioms Q3_is_symmetric
#print axioms Q3_two_cops_never_surround
#print axioms K33_is_cubic
#print axioms K33_is_symmetric
#print axioms K33_two_cops_never_surround
#print axioms prism_is_cubic
#print axioms prism_is_symmetric
#print axioms prism_two_cops_never_surround
#print axioms all_five_two_cops_never_surround
