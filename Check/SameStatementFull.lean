import Challenge.StatementFull
import KPFull

/-! Compares each statement in `Challenge/StatementFull.lean` (Mathlib only, proof `sorry`) with the proved theorem: the two
types must be the same term, up to the names of the universe parameters. Then the kernel checks the same thing once more. -/

open Lean in
run_meta do
  let env ← getEnv
  for (a, b) in [(`KPFull.kp_family_one_sided, `KPFamilies.kp_family_one_sided),
      (`KPFull.kp_family_finite_form, `KPFullFinal.kp_family_finite_form),
      (`KPFull.kp_family_finite_form_sharp, `KPFullFinal.kp_family_finite_form_sharp),
      (`KPFull.kp_single_orbit, `KPFamilies.kp_single_orbit),
      (`KPFull.kp_family_canonical, `KPFullFinal.kp_family_canonical)] do
    let some x := env.find? a | throwError "statement {a} not found"
    let some y := env.find? b | throwError "theorem {b} not found"
    unless x.levelParams.length == y.levelParams.length do
      throwError "the numbers of universe parameters of {a} and {b} differ"
    -- the names of the universe parameters can differ; rename those of the statement
    let t := x.type.instantiateLevelParams x.levelParams (y.levelParams.map mkLevelParam)
    unless t == y.type do throwError "the statements {a} and {b} differ"
    unless (y matches .thmInfo _) do throwError "{b} is not a theorem"
    -- the proved theorem must not depend on `sorryAx`
    let axs ← collectAxioms b
    if axs.contains ``sorryAx then throwError "{b} depends on sorryAx"
  logInfo "the five statements of the full form are equal as terms; no proved theorem uses sorryAx"

/-! The same checks by the kernel: each proved theorem has the type of the challenge statement. -/
example : type_of% @KPFull.kp_family_one_sided := @KPFamilies.kp_family_one_sided
example : type_of% @KPFull.kp_family_finite_form := @KPFullFinal.kp_family_finite_form
example : type_of% @KPFull.kp_family_finite_form_sharp := @KPFullFinal.kp_family_finite_form_sharp
example : type_of% @KPFull.kp_single_orbit := @KPFamilies.kp_single_orbit
example : type_of% @KPFull.kp_family_canonical := @KPFullFinal.kp_family_canonical
