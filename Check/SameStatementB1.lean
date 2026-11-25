import Challenge.StatementB1
import KPLower

/-! Compares each statement in `Challenge/StatementB1.lean` (Mathlib only, proof `sorry`) with the proved theorem in
`KPLower/`: the two types must be the same term, up to the names of the universe parameters. Then the kernel checks the
same thing once more. -/

open Lean in
run_meta do
  let env ← getEnv
  for (a, b) in [(`KPLower.kp_one_sided_lower_bound, `KPB1.kp_one_sided_lower_bound),
      (`KPLower.kp_one_sided_bound_ge_sq, `KPB1.kp_one_sided_bound_ge_sq),
      (`KPLower.kp_one_sided_not_linear, `KPB1.kp_one_sided_not_linear),
      (`KPLower.kp_one_sided_not_linear_complex, `KPB1.kp_one_sided_not_linear_complex)] do
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
  logInfo "the four statements of remark B1 are equal as terms; no proved theorem uses sorryAx"

/-! The same checks by the kernel: each proved theorem has the type of the challenge statement. -/
example : type_of% @KPLower.kp_one_sided_lower_bound := @KPB1.kp_one_sided_lower_bound
example : type_of% @KPLower.kp_one_sided_bound_ge_sq := @KPB1.kp_one_sided_bound_ge_sq
example : type_of% @KPLower.kp_one_sided_not_linear := @KPB1.kp_one_sided_not_linear
example : type_of% @KPLower.kp_one_sided_not_linear_complex := @KPB1.kp_one_sided_not_linear_complex
