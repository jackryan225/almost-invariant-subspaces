import KPLower.Group

universe u

namespace KPB1.Astra

variable {P H : Type} [Group H] (τ : H →* Equiv.Perm P)
variable (K : Type u) [DivisionRing K]

private theorem isolate_coordinate [DecidableEq P] (hK : (2 : K) ≠ 0) (W : Submodule K (P → K))
    (hstable : ∀ (g : SignedGroup τ) (v : P → K), v ∈ W → signedRep τ K g v ∈ W)
    (v : P → K) (hv : v ∈ W) (i : P) (hi : v i ≠ 0) :
    Pi.single i (1 : K) ∈ W := by
  let s (j : P) : ℤˣ := if j = i then -1 else 1
  have he : v - signedRep τ K (SemidirectProduct.inl s) v = Pi.single i (2 * v i) := by
    funext j
    by_cases hj : j = i
    · subst j
      have hs : s i = -1 := by simp [s]
      rw [Pi.sub_apply, signedRep_sign, hs, Units.smul_def, Units.coe_neg_one,
        neg_one_smul, sub_neg_eq_add, Pi.single_eq_same, two_mul]
    · simp only [Pi.sub_apply, signedRep_sign, s, ite_eq_right hj, one_smul, sub_self,
        Pi.single_eq_of_ne hj]
  have hdiff := W.sub_mem hv (hstable (SemidirectProduct.inl s) v hv)
  rw [he] at hdiff
  simpa only [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero hK hi)] using
    W.smul_mem (2 * v i)⁻¹ hdiff

theorem signed_invariant_eq_bot_or_top [Fintype P] (hK : (2 : K) ≠ 0)
    (htrans : ∀ i j : P, ∃ h : H, τ h i = j) (W : Submodule K (P → K))
    (hInv : ∀ g : SignedGroup τ, W.map (signedRep τ K g : (P → K) →ₗ[K] (P → K)) = W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hf0
  have hstable (g : SignedGroup τ) (v : P → K) (hv : v ∈ W) : signedRep τ K g v ∈ W := by
    rw [← hInv g]
    exact Submodule.mem_map_of_mem hv
  have hall (j : P) : Pi.single j (1 : K) ∈ W := by
    obtain ⟨h, hh⟩ := htrans i j
    let g : SignedGroup τ := SemidirectProduct.inr h
    apply isolate_coordinate τ K hK W hstable (signedRep τ K g f) (hstable g f hf) j
    change signedRep τ K (SemidirectProduct.inr h) f j ≠ 0
    rw [signedRep_perm, ← hh, Equiv.symm_apply_apply]
    exact hi
  apply top_unique
  intro x _
  rw [pi_eq_sum_univ' x]
  exact W.sum_mem fun j _ => W.smul_mem (x j) (hall j)

end KPB1.Astra
