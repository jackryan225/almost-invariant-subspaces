import Challenge.Statement
import AlmostInvariant

/-! Compares each statement in `Challenge/Statement.lean` (Mathlib only) with the proved theorem: the two types must be the same
term, up to the names of the universe parameters. This runs a few lines of Lean code. -/

open Lean in
run_meta do
  let env ← getEnv
  for (a, b) in [(`almost_invariant, `AlmostInvariant.almost_invariant),
      (`almost_invariant_module, `AlmostInvariant.almost_invariant_module),
      (`almost_invariant_one_sided, `AlmostInvariant.OneSided.almost_invariant_subspace_one_sided),
      (`question_negative_complex, `AlmostInvariant.question_negative_complex),
      (`almost_invariant_all_groups, `AlmostInvariant.AllGroups.almost_invariant_subspace_all)] do
    let some x := env.find? a | throwError "statement {a} not found"
    let some y := env.find? b | throwError "theorem {b} not found"
    unless x.levelParams.length == y.levelParams.length do
      throwError "the numbers of universe parameters of {a} and {b} differ"
    -- the names of the universe parameters can differ; rename those of the statement
    let t := x.type.instantiateLevelParams x.levelParams (y.levelParams.map mkLevelParam)
    unless t == y.type do throwError "the statements {a} and {b} differ"
    unless (y matches .thmInfo _) do throwError "{b} is not a theorem"
  logInfo "the five statements are equal as terms"
