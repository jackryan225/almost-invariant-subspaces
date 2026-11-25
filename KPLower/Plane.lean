import Mathlib

namespace KPB1.Astra

open scoped LinearAlgebra.Projectivization

theorem exists_plane_field (q : ℕ) (hq : IsPrimePow q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q := by
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p n, inferInstance, inferInstance, (GaloisField.card p n hn.ne').trans hpn⟩

abbrev PlaneVec (F : Type) := (Fin 2 → F) × F
abbrev PlanePoint (F : Type) [Field F] := ℙ F (PlaneVec F)
abbrev PlaneGroup (F : Type) [Field F] := PlaneVec F ≃ₗ[F] PlaneVec F

variable (F : Type) [Field F]

theorem planeVec_finrank : Module.finrank F (PlaneVec F) = 3 := by
  simp [PlaneVec, Module.finrank_prod]

def planePerm : PlaneGroup F →* Equiv.Perm (PlanePoint F) :=
  MulAction.toPermHom _ _

theorem planePerm_transitive (a b : PlanePoint F) : ∃ g : PlaneGroup F, planePerm F g a = b := by
  let : MulAction.IsPretransitive (PlaneGroup F) (PlanePoint F) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact MulAction.exists_smul_eq (PlaneGroup F) a b

abbrev planeInl : (Fin 2 → F) →ₗ[F] PlaneVec F := LinearMap.inl F (Fin 2 → F) F

def planeInclusion : ℙ F (Fin 2 → F) ↪ PlanePoint F where
  toFun := Projectivization.map (planeInl F) LinearMap.inl_injective
  inj' := Projectivization.map_injective (τ := RingHom.id F) (planeInl F) LinearMap.inl_injective

variable [Finite F]

theorem planeGroup_finite : Finite (PlaneGroup F) :=
  Finite.of_injective (fun g : PlaneGroup F => (g : PlaneVec F → PlaneVec F)) DFunLike.coe_injective

theorem planePoint_card : Nat.card (PlanePoint F) = Nat.card F ^ 2 + Nat.card F + 1 := by
  rw [Projectivization.card_of_finrank F (PlaneVec F) (planeVec_finrank F)]
  simp [Finset.sum_range_succ]
  ring

/-- The projective line of points represented by (w, 0). -/
noncomputable def planeLine : Finset (PlanePoint F) := by
  letI := Fintype.ofFinite (ℙ F (Fin 2 → F))
  exact Finset.univ.map (planeInclusion F)

theorem planeLine_card : (planeLine F).card = Nat.card F + 1 := by
  let : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  unfold planeLine
  rw [Finset.card_map, Finset.card_univ, Fintype.card_eq_nat_card]
  exact Projectivization.card_of_finrank_two F _ (by simp)

theorem mk_mem_planeLine (v : PlaneVec F) (hv : v ≠ 0) (hm : v ∈ (planeInl F).range) :
    Projectivization.mk F v hv ∈ planeLine F := by
  let : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  obtain ⟨w, rfl⟩ := hm
  have hw : w ≠ 0 := fun h => hv (by rw [h, map_zero])
  unfold planeLine
  exact Finset.mem_map.mpr ⟨Projectivization.mk F w hw, Finset.mem_univ _, rfl⟩

theorem planeLine_meets (g : PlaneGroup F) :
    ∃ a ∈ planeLine F, planePerm F g a ∈ planeLine F := by
  let U := (planeInl F).range
  let T := U.map g.toLinearMap
  have hU : Module.finrank F U = 2 := by
    dsimp only [U]
    rw [LinearMap.finrank_range_of_inj (f := planeInl F) LinearMap.inl_injective]
    simp
  have hT : Module.finrank F T = 2 := (g.finrank_map_eq U).trans hU
  have hne : U ⊓ T ≠ ⊥ := by
    intro he
    have h := U.finrank_sup_add_finrank_inf_eq T
    rw [he, finrank_bot, hU, hT] at h
    have hle := (U ⊔ T).finrank_le
    rw [planeVec_finrank] at hle
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hzU, w, hwU, rfl⟩ := hz
  have hw : w ≠ 0 := fun h => hz0 (by rw [h, map_zero])
  refine ⟨Projectivization.mk F w hw, mk_mem_planeLine F w hw hwU, ?_⟩
  change g • Projectivization.mk F w hw ∈ planeLine F
  rw [Projectivization.smul_mk]
  exact mk_mem_planeLine F _ _ hzU

theorem planeLine_sdiff [DecidableEq (PlanePoint F)] (g : PlaneGroup F) :
    (((planeLine F).map (planePerm F g).toEmbedding) \ planeLine F).card ≤ Nat.card F := by
  let X := planeLine F
  let Y := X.map (planePerm F g).toEmbedding
  obtain ⟨a, ha, hga⟩ := planeLine_meets F g
  have hi : (X ∩ Y).Nonempty :=
    ⟨planePerm F g a, Finset.mem_inter.mpr ⟨hga, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩⟩
  have hy : Y.card = Nat.card F + 1 := by
    rw [show Y = X.map (planePerm F g).toEmbedding from rfl, Finset.card_map]
    exact planeLine_card F
  change (Y \ X).card ≤ Nat.card F
  rw [Finset.card_sdiff, hy]
  have := Finset.card_pos.mpr hi
  omega

end KPB1.Astra
