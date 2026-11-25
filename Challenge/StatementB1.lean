import Mathlib

/-!
# Remark B1 in Lean: the one-sided bound of Theorem A needs order `r^2` (the statements)

This file imports Mathlib only and uses no definition of ours. Each proof is `sorry` here. The proofs are in the folder
`KPLower` (namespace `KPB1`). `Check/SameStatementB1.lean` checks that each statement below and its proved twin are the
same term, and `Check/AxiomsB1.lean` prints the axioms of each proved twin.

The quantities are those of `Challenge/StatementFull.lean` (statement S3, one orbit):
`B.submoduleOf A` is `A ∩ B` as a subspace of `A`, so `A ⧸ B.submoduleOf A` is `A / (A ∩ B)`, and `Module.rank` is the
dimension. With `d(A, B) = dim A / (A ∩ B)`, S3 says: if `d(A, gA) ≤ r` for every `g`, there is an invariant `W` with
`d(W, A) ≤ r` and `d(A, W) ≤ r (r + 1)`. The statements below say that the second bound cannot be smaller than `r^2`
when `r` is a prime power, already for finite groups and finite-dimensional spaces, so that no linear bound exists.

Scalars: any division ring `K` with `2 ≠ 0`, for example `ℂ` or any field of characteristic other than `2`. The example
(the projective plane over the field with `q` elements, with sign changes of coordinates) needs `2 ≠ 0`: over a field of
characteristic `2` the sign changes are trivial, and for `q = 2` over `F_2` the bound of that example is only `3`
(exact computation; see `REMARKS.md`, B1). Characteristic `2` is not covered here.
-/

open Module

universe u

namespace KPLower

/-- **(B1) The quadratic lower bound.** For every division ring `K` with `2 ≠ 0` and every prime power `q` there are a
finite-dimensional `K`-vector space `V`, a finite group `G` acting linearly on `V` and a subspace `A` such that
`dim A / (A ∩ gA) ≤ q` for every `g` (the hypothesis of S3 with `r = q`), and every `G`-invariant subspace `W` with
`dim W / (W ∩ A) ≤ q` has `dim A / (W ∩ A) = q^2`. -/
theorem kp_one_sided_lower_bound (K : Type u) [DivisionRing K] (hK : (2 : K) ≠ 0) (q : ℕ) (hq : IsPrimePow q) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (G : Type) (_ : Group G) (_ : Finite G) (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V),
      (∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ q) ∧
      ∀ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) →
        Module.rank K (W ⧸ A.submoduleOf W) ≤ q →
        Module.rank K (A ⧸ W.submoduleOf A) = (q ^ 2 : ℕ) := by
  sorry

/-- **(B1, every valid bound is at least `q^2`.)** Let `f` be any function such that S3 holds with `f r` in place of
`r (r + 1)` for every finite-dimensional space over `K` and every finite group. Then `q^2 ≤ f q` for every prime
power `q`. (S3 shows that `f r = r (r + 1)` is such a function.) -/
theorem kp_one_sided_bound_ge_sq (K : Type u) [DivisionRing K] (hK : (2 : K) ≠ 0) (f : ℕ → ℕ)
    (hf : ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (G : Type) [Group G] [Finite G]
      (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ),
      (∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) →
      ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
        Module.rank K (W ⧸ A.submoduleOf W) ≤ r ∧ Module.rank K (A ⧸ W.submoduleOf A) ≤ (f r : ℕ))
    (q : ℕ) (hq : IsPrimePow q) : q ^ 2 ≤ f q := by
  sorry

/-- **(B1, no linear bound.)** There are no constants `a` and `b` such that S3 holds with `a r + b` in place of
`r (r + 1)`, already for finite-dimensional spaces over `K` and finite groups. This answers the words "possibly linear"
in the conjecture after Theorem A for the one-sided form. -/
theorem kp_one_sided_not_linear (K : Type u) [DivisionRing K] (hK : (2 : K) ≠ 0) :
    ¬ ∃ a b : ℕ, ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (G : Type) [Group G] [Finite G]
      (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ),
      (∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) →
      ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
        Module.rank K (W ⧸ A.submoduleOf W) ≤ r ∧ Module.rank K (A ⧸ W.submoduleOf A) ≤ (a * r + b : ℕ) := by
  sorry

/-- **(B1 over `ℂ`.)** The case of complex vector spaces, as in the remark. -/
theorem kp_one_sided_not_linear_complex :
    ¬ ∃ a b : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (G : Type) [Group G] [Finite G]
      (ρ : G →* (V ≃ₗ[ℂ] V)) (A : Submodule ℂ V) (r : ℕ),
      (∀ g : G, Module.rank ℂ (A ⧸ (A.map (ρ g : V →ₗ[ℂ] V)).submoduleOf A) ≤ r) →
      ∃ W : Submodule ℂ V, (∀ g : G, W.map (ρ g : V →ₗ[ℂ] V) = W) ∧
        Module.rank ℂ (W ⧸ A.submoduleOf W) ≤ r ∧ Module.rank ℂ (A ⧸ W.submoduleOf A) ≤ (a * r + b : ℕ) := by
  sorry

end KPLower
