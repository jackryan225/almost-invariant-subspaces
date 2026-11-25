import KPFull

/-! Prints the axioms of the results on the full original statement (families). Expected for each: `propext`,
`Classical.choice`, `Quot.sound`. (`Check/Axioms.lean` does the same for the results on one orbit.) -/

-- The five statements of `Challenge/StatementFull.lean`: S1, S2, S2', S3, S4
#print axioms KPFamilies.kp_family_one_sided
#print axioms KPFullFinal.kp_family_finite_form
#print axioms KPFullFinal.kp_family_finite_form_sharp
#print axioms KPFamilies.kp_single_orbit
#print axioms KPFullFinal.kp_family_canonical
-- Variants: modules over any ring (lengths); automorphisms of the lattice of submodules (covers semilinear actions)
#print axioms KPFamilies.kp_family_one_sided_module
#print axioms KPFamilies.kp_family_lattice
#print axioms KPFullFinal.kp_family_finite_form_lattice
#print axioms KPFull.PartB.partB
