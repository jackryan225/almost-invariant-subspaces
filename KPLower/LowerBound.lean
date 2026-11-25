import KPLower.Invariant
import KPLower.Plane

open KPB1.Astra

universe u

namespace KPB1

theorem kp_one_sided_lower_bound (K : Type u) [DivisionRing K] (hK : (2 : K) ≠ 0) (q : ℕ) (hq : IsPrimePow q) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (G : Type) (_ : Group G) (_ : Finite G) (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V),
      (∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ q) ∧
      ∀ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) →
        Module.rank K (W ⧸ A.submoduleOf W) ≤ q →
        Module.rank K (A ⧸ W.submoduleOf A) = (q ^ 2 : ℕ) := by
  classical
  obtain ⟨F, instF, finF, hF⟩ := exists_plane_field q hq
  let : Field F := instF
  let : Finite F := finF
  let : Fintype (PlanePoint F) := Fintype.ofFinite _
  let : Finite (PlaneGroup F) := planeGroup_finite F
  let τ := planePerm F
  let X := planeLine F
  have hX : X.card = q + 1 := by
    change (planeLine F).card = q + 1
    rw [planeLine_card, hF]
  have hcard : Fintype.card (PlanePoint F) = q ^ 2 + q + 1 := by
    rw [Fintype.card_eq_nat_card, planePoint_card, hF]
  have hcompl : ((Finset.univ : Finset (PlanePoint F)) \ X).card = q ^ 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_univ, hcard, hX]
    omega
  refine ⟨PlanePoint F → K, inferInstance, inferInstance, inferInstance,
    SignedGroup τ, inferInstance, signedGroup_finite τ, signedRep τ K, zeroOn K X, ?_, ?_⟩
  · intro g
    rw [signedRep_map_zeroOn, rank_zeroOn_quot, Nat.cast_le]
    have hg := planeLine_sdiff F g.right
    rw [hF] at hg
    exact hg
  · intro W hInv hsmall
    rcases signed_invariant_eq_bot_or_top τ K hK (planePerm_transitive F) W hInv with hW | hW
    · subst W
      rw [← zeroOn_univ (P := PlanePoint F) K, rank_zeroOn_quot, hcompl]
    · subst W
      rw [← zeroOn_empty (P := PlanePoint F) K, rank_zeroOn_quot,
        Finset.sdiff_empty, Nat.cast_le] at hsmall
      omega

end KPB1
