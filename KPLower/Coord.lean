import Mathlib

universe u

namespace KPB1.Astra

variable (K : Type u) [DivisionRing K] {P : Type}

/-- Functions vanishing on a specified finite set of coordinates. -/
def zeroOn (X : Finset P) : Submodule K (P → K) where
  carrier := {f | ∀ p ∈ X, f p = 0}
  zero_mem' := by intro p hp; rfl
  add_mem' := by
    intro f g hf hg p hp
    change f p + g p = 0
    rw [hf p hp, hg p hp, add_zero]
  smul_mem' := by
    intro a f hf p hp
    change a * f p = 0
    rw [hf p hp, mul_zero]

theorem zeroOn_empty : zeroOn K (∅ : Finset P) = ⊤ := by
  apply top_unique
  intro f hf p hp
  exact (Finset.notMem_empty p hp).elim

theorem zeroOn_univ [Fintype P] : zeroOn K (Finset.univ : Finset P) = ⊥ := by
  apply bot_unique
  intro f hf
  change f = 0
  funext p
  exact hf p (Finset.mem_univ p)

variable [DecidableEq P] (X Y : Finset P)

def coordRestrict : zeroOn K X →ₗ[K] (↥(Y \ X) → K) where
  toFun f i := f.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordRestrict_ker :
    (coordRestrict K X Y).ker = (zeroOn K Y).submoduleOf (zeroOn K X) := by
  apply Submodule.ext
  intro f
  change (fun i : ↥(Y \ X) => f.val i.val) = 0 ↔ ∀ p ∈ Y, f.val p = 0
  constructor
  · intro hf p hp
    by_cases hx : p ∈ X
    · exact f.property p hx
    · exact congrFun hf ⟨p, Finset.mem_sdiff.mpr ⟨hp, hx⟩⟩
  · intro hf
    funext i
    exact hf i.val (Finset.mem_sdiff.mp i.property).1

theorem coordRestrict_surjective : Function.Surjective (coordRestrict K X Y) := by
  intro g
  let f (p : P) : K := if h : p ∈ Y \ X then g ⟨p, h⟩ else 0
  have hf : f ∈ zeroOn K X := by
    intro p hp
    have h : p ∉ Y \ X := fun h' => (Finset.mem_sdiff.mp h').2 hp
    exact dite_eq_right h
  refine ⟨⟨f, hf⟩, ?_⟩
  funext i
  change f i.val = g i
  simp only [f, dite_eq_left i.property]

theorem rank_zeroOn_quot [Fintype P] :
    Module.rank K (zeroOn K X ⧸ (zeroOn K Y).submoduleOf (zeroOn K X)) =
      ((Y \ X).card : Cardinal) := by
  have h := ((coordRestrict K X Y).quotKerEquivOfSurjective
    (coordRestrict_surjective K X Y)).finrank_eq
  rw [coordRestrict_ker] at h
  rw [← Module.finrank_eq_rank, h, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

end KPB1.Astra
