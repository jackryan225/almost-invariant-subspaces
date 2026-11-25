import Mathlib

/-!
# The statements

This file imports Mathlib only and uses no definition of ours. Each proof is `sorry` here. The proofs are in the folder
`AlmostInvariant`, and `Check/SameStatement.lean` compares the statements.

Source of the problem: D. Kazhdan and A. Polishchuk, *Almost invariant subspaces and operators*, arXiv 2107.08085,
Pure Appl. Math. Q. 19 (2023), 1975-1983.

Notation: `A.map (ρ g)` is the image `gA`. `B.submoduleOf A` is `A ∩ B` as a subspace of `A`, so
`A ⧸ B.submoduleOf A` is `A / (A ∩ B)`.
-/

open Module

/-- **Total error less than `2r`.** `G` is a finite group that acts linearly on a vector space `V` of any dimension over a
division ring, and `dim A / (A ∩ gA) ≤ r` for all `g`. Then there is an invariant subspace `W` such that
`dim A / (A ∩ W) + dim W / (A ∩ W)` is at most `2r`, and less than `2r` if `r > 0`. -/
theorem almost_invariant {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Group G] [Finite G]
    (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∃ a b : ℕ, Module.rank K (A ⧸ W.submoduleOf A) = a ∧ Module.rank K (W ⧸ A.submoduleOf W) = b ∧
        a + b ≤ 2 * r ∧ (0 < r → a + b < 2 * r) := by
  sorry

/-- **Modules over any ring**, with the length in place of the dimension: `|G| (ℓ(A / A ∩ W) + ℓ(W / A ∩ W)) ≤ 2 r (|G| - 1)`. -/
theorem almost_invariant_module {R M G : Type*} [Ring R] [AddCommGroup M] [Module R M] [Group G] [Finite G]
    (ρ : G →* (M ≃ₗ[R] M)) (A : Submodule R M) (r : ℕ)
    (hr : ∀ g, Module.length R (A ⧸ (A.map (ρ g : M →ₗ[R] M)).submoduleOf A) ≤ r) :
    ∃ W : Submodule R M, (∀ g, W.map (ρ g : M →ₗ[R] M) = W) ∧
      (Nat.card G : ℕ∞) * (Module.length R (A ⧸ W.submoduleOf A) + Module.length R (W ⧸ A.submoduleOf W))
        ≤ 2 * r * (Nat.card G - 1 : ℕ) := by
  sorry

/-- **The form of Theorem A of Kazhdan and Polishchuk**, with `r (r + 1)` in place of `r (r + 1)^(r + 1)`. Here `V` has finite
dimension. The hypothesis says `dim A / (A ∩ gA) ≤ r`; the conclusion says `dim W / (W ∩ A) ≤ r` and `dim A / (W ∩ A) ≤ r (r + 1)`. -/
theorem almost_invariant_one_sided {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] [Finite G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1) := by
  sorry

/-- **The question at the end of Section 3 of the paper has a negative answer.** For each number `c` there are a finite group `H`
that acts on some `ℂ^n` and a subspace `A` with `dim A / (A ∩ gA) ≤ 1` for all `g`, such that the subspace
`A₀ = ∑_{|S| > |H|/2} ⋂_{g ∈ S} gA` of formula (3) has `dim A / (A ∩ A₀) > c`. -/
theorem question_negative_complex (c : ℕ) :
    ∃ (n : ℕ) (H : Type) (_ : Group H) (_ : Finite H) (ρ : H →* ((Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))) (A : Submodule ℂ (Fin n → ℂ)),
      (∀ g, Module.rank ℂ (A ⧸ (A.map (ρ g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))).submoduleOf A) ≤ 1) ∧
      ∀ A₀ : Submodule ℂ (Fin n → ℂ),
        A₀ = (⨆ S : {S : Finset H // Nat.card H < 2 * S.card}, ⨅ g ∈ S.1, A.map (ρ g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) →
          c < finrank ℂ (A ⧸ A₀.submoduleOf A) := by
  sorry

/-- **All groups**, finite or infinite, for `V` of finite dimension over a field. The bounds do not depend on the dimension of `V`:
total error at most `2r`, and the form of Theorem A with `r` and `r (r + 1)`. -/
theorem almost_invariant_all_groups {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r) ∧
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1)) := by
  sorry
