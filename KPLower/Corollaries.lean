import KPLower.LowerBound

/-!
# Remark B1: consequences of the quadratic lower bound

From `KPB1.kp_one_sided_lower_bound` (`KPLower/LowerBound.lean`): every function `f` for which the one-sided form S3
holds with `f r` in place of `r (r + 1)` has `f q ≥ q^2` for every prime power `q`, so no bound `a r + b` exists.
The statements are those of `Challenge/StatementB1.lean`.
-/

open Module

universe u

namespace KPB1

/-- Every valid second bound `f` in the one-sided form S3 satisfies `q^2 ≤ f q` for every prime power `q`. -/
theorem kp_one_sided_bound_ge_sq (K : Type u) [DivisionRing K] (hK : (2 : K) ≠ 0) (f : ℕ → ℕ)
    (hf : ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (G : Type) [Group G] [Finite G]
      (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ),
      (∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) →
      ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
        Module.rank K (W ⧸ A.submoduleOf W) ≤ r ∧ Module.rank K (A ⧸ W.submoduleOf A) ≤ (f r : ℕ))
    (q : ℕ) (hq : IsPrimePow q) : q ^ 2 ≤ f q := by
  obtain ⟨V, _, _, _, G, _, _, ρ, A, hr, hW⟩ := kp_one_sided_lower_bound K hK q hq
  obtain ⟨W, hWinv, h1, h2⟩ := hf V G ρ A q hr
  rw [hW W hWinv h1] at h2
  exact_mod_cast h2

/-- No linear bound `a r + b` in the one-sided form S3, already for finite-dimensional spaces and finite groups. -/
theorem kp_one_sided_not_linear (K : Type u) [DivisionRing K] (hK : (2 : K) ≠ 0) :
    ¬ ∃ a b : ℕ, ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (G : Type) [Group G] [Finite G]
      (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ),
      (∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) →
      ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
        Module.rank K (W ⧸ A.submoduleOf W) ≤ r ∧ Module.rank K (A ⧸ W.submoduleOf A) ≤ (a * r + b : ℕ) := by
  rintro ⟨a, b, h⟩
  have hq : IsPrimePow (2 ^ (a + b + 1)) := ⟨2, a + b + 1, Nat.prime_two.prime, Nat.succ_pos _, rfl⟩
  have key := kp_one_sided_bound_ge_sq K hK (fun r => a * r + b) h _ hq
  have hlt : a + b + 1 < 2 ^ (a + b + 1) := Nat.lt_two_pow_self
  nlinarith

/-- The same over `ℂ`. -/
theorem kp_one_sided_not_linear_complex :
    ¬ ∃ a b : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (G : Type) [Group G] [Finite G]
      (ρ : G →* (V ≃ₗ[ℂ] V)) (A : Submodule ℂ V) (r : ℕ),
      (∀ g : G, Module.rank ℂ (A ⧸ (A.map (ρ g : V →ₗ[ℂ] V)).submoduleOf A) ≤ r) →
      ∃ W : Submodule ℂ V, (∀ g : G, W.map (ρ g : V →ₗ[ℂ] V) = W) ∧
        Module.rank ℂ (W ⧸ A.submoduleOf W) ≤ r ∧ Module.rank ℂ (A ⧸ W.submoduleOf A) ≤ (a * r + b : ℕ) :=
  kp_one_sided_not_linear ℂ two_ne_zero

end KPB1
