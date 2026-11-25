import Challenge.Statement
import KPFull.SingleOrbit

/-!
# The new statements contain the old one-sided statement

`Challenge/Statement.lean` states `almost_invariant_one_sided` for one orbit: a field, `V` of finite dimension, a finite
group, dimensions as `finrank`. Here that statement is derived from S3 (`KPFamilies.kp_single_orbit`, proved in
`KPFull/SingleOrbit.lean`), which has no condition on the dimension and no condition on the group. The derivation does not
use the finiteness of the group, so the same bounds hold for every group (`one_sided_of_single_orbit`).

The last lines check that the derived theorem has exactly the type of the statement in `Challenge/Statement.lean`, and
print its axioms. Expected: `propext`, `Classical.choice`, `Quot.sound`.
-/

open Module

namespace KPContains

/-- `dim B / (B ∩ C) + dim (C ∩ B) = dim B` in finite dimension. -/
theorem finrank_quotient_submoduleOf {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B C : Submodule K V) :
    finrank K (B ⧸ C.submoduleOf B) + finrank K (C ⊓ B : Submodule K V) = finrank K B := by
  rw [← Submodule.finrank_quotient_add_finrank (C.submoduleOf B)]
  congr 1
  have hmap : (C.submoduleOf B).map B.subtype = C ⊓ B := by
    rw [Submodule.submoduleOf, Submodule.map_comap_subtype]
    exact inf_comm _ _
  rw [← hmap]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype B) (C.submoduleOf B))).symm

theorem rank_quotient_submoduleOf_le_iff {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B C : Submodule K V) (n : ℕ) :
    Module.rank K (B ⧸ C.submoduleOf B) ≤ n ↔ finrank K B ≤ finrank K (C ⊓ B : Submodule K V) + n := by
  rw [← Module.finrank_eq_rank, Nat.cast_le]
  have := finrank_quotient_submoduleOf B C
  constructor <;> intro h <;> omega

/-- The one-sided bounds in finite dimension, for every group, from S3. -/
theorem one_sided_of_single_orbit {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1) := by
  obtain ⟨W, hW, h1, h2⟩ :=
    KPFamilies.kp_single_orbit ρ A r (fun g => (rank_quotient_submoduleOf_le_iff _ _ _).mpr (hr g))
  refine ⟨W, hW, ?_, ?_⟩
  · have := (rank_quotient_submoduleOf_le_iff W A r).mp h1
    rwa [inf_comm] at this
  · exact (rank_quotient_submoduleOf_le_iff A W (r * (r + 1))).mp h2

/-- The statement `almost_invariant_one_sided` of `Challenge/Statement.lean`, derived from S3. -/
theorem almost_invariant_one_sided {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] [Finite G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1) :=
  one_sided_of_single_orbit ρ A r hr

end KPContains

/-- The kernel check: the derived theorem has the type of the statement in `Challenge/Statement.lean`. -/
example : type_of% @_root_.almost_invariant_one_sided := @KPContains.almost_invariant_one_sided

#print axioms KPContains.one_sided_of_single_orbit
#print axioms KPContains.almost_invariant_one_sided
