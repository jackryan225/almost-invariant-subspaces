import KPLower.Coord

universe u

namespace KPB1.Astra

variable {P H : Type} [Group H] (τ : H →* Equiv.Perm P)

/-- A permutation acts on sign functions by precomposition with its inverse. -/
def signsAction : H →* MulAut (P → ℤˣ) where
  toFun h := MulEquiv.arrowCongr (τ h) (MulEquiv.refl ℤˣ)
  map_one' := by
    apply MulEquiv.ext
    intro s
    funext p
    change s ((τ 1).symm p) = s p
    simp only [map_one, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro s
    funext p
    change s ((τ (a * b)).symm p) = s ((τ b).symm ((τ a).symm p))
    simp only [map_mul, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

abbrev SignedGroup := (P → ℤˣ) ⋊[signsAction τ] H

theorem signedGroup_finite [Finite P] [Finite H] : Finite (SignedGroup τ) :=
  Finite.of_equiv ((P → ℤˣ) × H) SemidirectProduct.equivProd.symm

variable (K : Type u) [DivisionRing K]

def signedTransform (s : P → ℤˣ) (e : Equiv.Perm P) : (P → K) ≃ₗ[K] (P → K) :=
  (LinearEquiv.piCongrLeft' K (fun _ : P => K) e).trans
    (LinearEquiv.piCongrRight (fun p : P => DistribMulAction.toLinearEquiv K K (s p)))

def signedRep : SignedGroup τ →* ((P → K) ≃ₗ[K] (P → K)) where
  toFun g := signedTransform K g.left (τ g.right)
  map_one' := by
    apply LinearEquiv.ext
    intro f
    funext p
    change (1 : ℤˣ) • f ((τ 1).symm p) = f p
    simp only [map_one, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply, one_smul]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro f
    funext p
    change (g.left p * h.left ((τ g.right).symm p)) • f ((τ (g.right * h.right)).symm p) =
      g.left p • (h.left ((τ g.right).symm p) • f ((τ h.right).symm ((τ g.right).symm p)))
    simp only [map_mul, Equiv.Perm.mul_def, Equiv.symm_trans_apply, mul_smul]

theorem signedRep_apply (g : SignedGroup τ) (f : P → K) (p : P) :
    signedRep τ K g f p = g.left p • f ((τ g.right).symm p) := rfl

theorem signedRep_sign (s : P → ℤˣ) (f : P → K) (p : P) :
    signedRep τ K (SemidirectProduct.inl s) f p = s p • f p := by
  change s p • f ((τ 1).symm p) = s p • f p
  simp only [map_one, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply]

theorem signedRep_perm (h : H) (f : P → K) (p : P) :
    signedRep τ K (SemidirectProduct.inr h) f p = f ((τ h).symm p) := by
  change (1 : ℤˣ) • f ((τ h).symm p) = _
  exact one_smul _ _

theorem signedRep_map_zeroOn (g : SignedGroup τ) (X : Finset P) :
    (zeroOn K X).map (signedRep τ K g : (P → K) →ₗ[K] (P → K)) =
      zeroOn K (X.map (τ g.right).toEmbedding) := by
  apply Submodule.ext
  intro v
  obtain ⟨f, rfl⟩ := (signedRep τ K g).surjective v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  change (∀ p ∈ X, f p = 0) ↔ ∀ p ∈ X.map (τ g.right).toEmbedding, signedRep τ K g f p = 0
  constructor
  · intro hf p hp
    rw [signedRep_apply, hf _ (Finset.mem_map_equiv.mp hp), smul_zero]
  · intro hf p hp
    have h := hf ((τ g.right) p) (Finset.mem_map_of_mem _ hp)
    rw [signedRep_apply, Equiv.symm_apply_apply] at h
    exact (smul_eq_zero_iff_eq _).mp h

end KPB1.Astra
