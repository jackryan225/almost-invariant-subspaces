import KPFull.Families
import AlmostInvariant.AllGroups
import AlmostInvariant.OneSided

/-!
# The lattice theorems in the setting of a modular lattice of finite rank

Setting: a modular lattice of finite rank, with least element `⊥`, and the rank `ρ x = ℓ[⊥, x]` (the length of the
interval). Standard facts: `ρ ⊥ = 0`, `ρ` is strictly monotone, `ρ` adds `1` on a cover, and
`ρ (x ⊔ y) + ρ (x ⊓ y) = ρ x + ρ y` (the valuation identity). Here these four facts are the hypothesis `IsRankFn ρ`; the theorem that
`ℓ[⊥, ·]` has them in a modular lattice of finite length is classical (Birkhoff) and is NOT formalized here (Mathlib has no
such lemma for abstract modular lattices).

From `IsRankFn ρ` we prove in Lean: the lattice is modular (`IsRankFn.isModularLattice`), and every order automorphism
keeps `ρ` (`IsRankFn.map_orderIso`). Then the lattice theorems of `KPFull` and `AlmostInvariant` apply with `rk = ρ`:
* `family_one_sided`: families, any group, one-sided bounds `r` and `r (r + 1)` (from `KPFamLat.exists_fixed_family_one_sided`);
* `single_orbit_one_sided`: one orbit (from `AlmostInvariant.AllGroups.exists_fixed_one_sided`);
* `single_orbit_total`: one orbit, any group, total error at most `2 r` (from `AlmostInvariant.AllGroups.exists_fixed_total`);
* `finite_group_total`: one orbit of a finite group, `|G| δ(a, w) ≤ 2 ∑_g d(a, g a)` (from `AlmostInvariant.OneSided.lattice_form`).
The group acts by order automorphisms, `act : G →* (L ≃o L)`; no finiteness of `G` (except in the last theorem) and no
upper bound element is used.
-/

namespace KPLattice

variable {L : Type*} [Lattice L] [OrderBot L]

/-- A rank function. For a modular lattice of finite length, `x ↦ ℓ[⊥, x]` is one. -/
structure IsRankFn (ρ : L → ℕ) : Prop where
  bot : ρ ⊥ = 0
  strictMono : StrictMono ρ
  covBy : ∀ {x y : L}, x ⋖ y → ρ y = ρ x + 1
  val : ∀ x y : L, ρ (x ⊔ y) + ρ (x ⊓ y) = ρ x + ρ y

namespace IsRankFn

variable {ρ : L → ℕ} (hρ : IsRankFn ρ)
include hρ

/-- A lattice with a strictly monotone valuation is modular. -/
theorem isModularLattice : IsModularLattice L := by
  refine ⟨fun {x} y {z} hxz => ?_⟩
  have hle : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
    le_inf (sup_le_sup_left inf_le_left x) (sup_le hxz inf_le_right)
  have e1 := hρ.val x (y ⊓ z)
  have e2 := hρ.val (x ⊔ y) z
  have e3 := hρ.val y z
  have e4 := hρ.val x y
  have i1 : x ⊓ (y ⊓ z) = x ⊓ y := by
    rw [← inf_assoc, inf_right_comm, inf_eq_left.mpr hxz]
  have i2 : x ⊔ y ⊔ z = y ⊔ z := by
    rw [sup_assoc, sup_eq_right.mpr (hxz.trans le_sup_right)]
  rw [i1] at e1
  rw [i2] at e2
  by_contra h
  have hlt : x ⊔ y ⊓ z < (x ⊔ y) ⊓ z := lt_of_le_of_ne hle (fun heq => h (le_of_eq heq.symm))
  have := hρ.strictMono hlt
  omega

/-- Below every `x ≠ ⊥` there is a cover. -/
theorem exists_covBy_of_bot_lt {x : L} (hx : ⊥ < x) : ∃ y, y ⋖ x := by
  classical
  let P : ℕ → Prop := fun n => ∃ y, y < x ∧ ρ y = n
  have h0 : P (ρ ⊥) := ⟨⊥, hx, rfl⟩
  have hb : ∀ n, P n → n ≤ ρ x := by
    rintro n ⟨y, hy, rfl⟩
    exact (hρ.strictMono hy).le
  obtain ⟨y, hy, hyN⟩ := Nat.findGreatest_spec (hb _ h0) h0
  refine ⟨y, (show y < x ∧ ∀ ⦃c⦄, y < c → ¬c < x from ⟨hy, ?_⟩)⟩
  intro z hyz hzx
  have hPz : P (ρ z) := ⟨z, hzx, rfl⟩
  have h1 := Nat.le_findGreatest (hb _ hPz) hPz
  have h2 := hρ.strictMono hyz
  omega

/-- Every order automorphism keeps the rank. -/
theorem map_orderIso (φ : L ≃o L) (x : L) : ρ (φ x) = ρ x := by
  have key : ∀ n : ℕ, ∀ x : L, ρ x = n → ρ (φ x) = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn
      rcases eq_bot_or_bot_lt x with rfl | hx
      · rw [OrderIso.map_bot]
        exact hn
      · obtain ⟨y, hy⟩ := hρ.exists_covBy_of_bot_lt hx
        have h1 := hρ.covBy hy
        have h2 := hρ.covBy ((apply_covBy_apply_iff φ).mpr hy)
        have h3 := ih (ρ y) (by omega) y rfl
        omega
  exact key (ρ x) x rfl

end IsRankFn

variable {G : Type*} [Group G]

theorem act_mul (act : G →* (L ≃o L)) (g h : G) (x : L) : act (g * h) x = act g (act h x) := by
  simp [map_mul]

section rank
variable {ρ : L → ℕ} (hρ : IsRankFn ρ)
include hρ

theorem strictMono_int : StrictMono (fun z : L => (ρ z : ℤ)) := fun p q h => by
  show (ρ p : ℤ) < ρ q
  exact_mod_cast hρ.strictMono h

theorem val_int (p q : L) :
    (fun z : L => (ρ z : ℤ)) (p ⊔ q) + (fun z : L => (ρ z : ℤ)) (p ⊓ q) =
      (fun z : L => (ρ z : ℤ)) p + (fun z : L => (ρ z : ℤ)) q := by
  show (ρ (p ⊔ q) : ℤ) + ρ (p ⊓ q) = ρ p + ρ q
  exact_mod_cast hρ.val p q

theorem inv_int (act : G →* (L ≃o L)) (g : G) (p : L) :
    (fun z : L => (ρ z : ℤ)) (act g p) = (fun z : L => (ρ z : ℤ)) p := by
  show (ρ (act g p) : ℤ) = ρ p
  exact_mod_cast hρ.map_orderIso (act g) p

end rank

/-- **Families, one-sided form (S1), for a modular lattice of finite rank and any group.** If the group maps members to
members and `ρ (a x) - ρ (a x ⊓ a y) ≤ r` for all `x, y`, there is a fixed `w` with `ρ w - ρ (w ⊓ a x) ≤ r` and
`ρ (a x) - ρ (a x ⊓ w) ≤ r (r + 1)` for every `x`. -/
theorem family_one_sided {X : Type*} (act : G →* (L ≃o L)) {ρ : L → ℕ} (hρ : IsRankFn ρ) (a : X → L)
    (ha : ∀ g x, ∃ y, act g (a x) = a y) (r : ℕ) (hr : ∀ x y, ρ (a x) ≤ ρ (a x ⊓ a y) + r) :
    ∃ w : L, (∀ g, act g w = w) ∧ ∀ x, ρ w ≤ ρ (w ⊓ a x) + r ∧ ρ (a x) ≤ ρ (a x ⊓ w) + r * (r + 1) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x0⟩⟩
  · exact ⟨⊥, fun g => OrderIso.map_bot _, fun x => isEmptyElim x⟩
  have hr0 : ∀ g, (ρ (a x0) : ℤ) - ρ (act g (a x0) ⊓ a x0) ≤ (r : ℤ) := by
    intro g
    obtain ⟨y, hy⟩ := ha g x0
    have := hr x0 y
    rw [hy, inf_comm]
    omega
  obtain ⟨w, hw, hB, -⟩ := KPFamLat.exists_fixed_family_one_sided (⇑act) (act_mul act)
    (fun z : L => (ρ z : ℤ)) (strictMono_int hρ) (val_int hρ) (inv_int hρ act) (a x0) (r : ℤ) hr0
  refine ⟨w, hw, fun x => ?_⟩
  have hB1 : ∀ g, (ρ (a x) : ℤ) - ρ (a x ⊓ act g (a x0)) ≤ (r : ℤ) := by
    intro g
    obtain ⟨y, hy⟩ := ha g x0
    rw [hy]
    have := hr x y
    omega
  have hB2 : ∀ g, (ρ (act g (a x0)) : ℤ) - ρ (act g (a x0) ⊓ a x) ≤ (r : ℤ) := by
    intro g
    obtain ⟨y, hy⟩ := ha g x0
    rw [hy]
    have := hr y x
    omega
  obtain ⟨h1, h2⟩ := hB (a x) hB1 hB2
  have h1' : (ρ w : ℤ) - ρ (w ⊓ a x) ≤ r := h1
  have h2' : (ρ (a x) : ℤ) - ρ (a x ⊓ w) ≤ (r : ℤ) * ((r : ℤ) + 1) := h2
  constructor
  · omega
  · have h3 : ((ρ (a x) : ℕ) : ℤ) ≤ ((ρ (a x ⊓ w) + r * (r + 1) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h3

/-- **One orbit, one-sided form (S3), any group.** -/
theorem single_orbit_one_sided (act : G →* (L ≃o L)) {ρ : L → ℕ} (hρ : IsRankFn ρ) (a : L) (r : ℕ)
    (hr : ∀ g, ρ a ≤ ρ (a ⊓ act g a) + r) :
    ∃ w : L, (∀ g, act g w = w) ∧ ρ w ≤ ρ (w ⊓ a) + r ∧ ρ a ≤ ρ (a ⊓ w) + r * (r + 1) := by
  have hr0 : ∀ g, (ρ a : ℤ) - ρ (act g a ⊓ a) ≤ (r : ℤ) := by
    intro g
    have := hr g
    rw [inf_comm]
    omega
  obtain ⟨w, hw, h1, h2⟩ := AlmostInvariant.AllGroups.exists_fixed_one_sided (⇑act) (act_mul act)
    (fun z : L => (ρ z : ℤ)) (strictMono_int hρ) (val_int hρ) (inv_int hρ act) a (r : ℤ) hr0
  have h1' : (ρ w : ℤ) - ρ (w ⊓ a) ≤ r := h1
  have h2' : (ρ a : ℤ) - ρ (w ⊓ a) ≤ (r : ℤ) * ((r : ℤ) + 1) := h2
  refine ⟨w, hw, by omega, ?_⟩
  have h3 : ((ρ a : ℕ) : ℤ) ≤ ((ρ (a ⊓ w) + r * (r + 1) : ℕ) : ℤ) := by
    rw [inf_comm]
    push_cast
    linarith
  exact_mod_cast h3

/-- **One orbit, total error at most `2 r`, any group.** -/
theorem single_orbit_total (act : G →* (L ≃o L)) {ρ : L → ℕ} (hρ : IsRankFn ρ) (a : L) (r : ℕ)
    (hr : ∀ g, ρ a ≤ ρ (a ⊓ act g a) + r) :
    ∃ w : L, (∀ g, act g w = w) ∧ ρ a + ρ w ≤ 2 * ρ (a ⊓ w) + 2 * r := by
  have hr0 : ∀ g, (ρ a : ℤ) - ρ (act g a ⊓ a) ≤ (r : ℤ) := by
    intro g
    have := hr g
    rw [inf_comm]
    omega
  obtain ⟨w, hw, h⟩ := AlmostInvariant.AllGroups.exists_fixed_total (⇑act) (act_mul act)
    (fun z : L => (ρ z : ℤ)) (strictMono_int hρ) (val_int hρ) (inv_int hρ act) a (r : ℤ) hr0
  have h' : ((ρ a : ℤ) - ρ (w ⊓ a)) + ((ρ w : ℤ) - ρ (w ⊓ a)) ≤ 2 * (r : ℤ) := h
  refine ⟨w, hw, ?_⟩
  rw [inf_comm]
  omega

/-- **One orbit of a finite group**, in summed form: `|G| δ(a, w) ≤ 2 ∑_g (ρ a - ρ (g a ⊓ a))`.
Dividing by the order of the stabilizer gives `m δ(a, w) ≤ 2 ∑_{c ∈ G a} (ρ a - ρ (c ⊓ a)) ≤ 2 r (m - 1)` for an orbit
of `m` elements. -/
theorem finite_group_total [Fintype G] (act : G →* (L ≃o L)) {ρ : L → ℕ} (hρ : IsRankFn ρ) (a : L) :
    ∃ w : L, (∀ g, act g w = w) ∧
      (Fintype.card G : ℤ) * (((ρ a : ℤ) - ρ (w ⊓ a)) + ((ρ w : ℤ) - ρ (w ⊓ a))) ≤
        2 * ∑ g, ((ρ a : ℤ) - ρ (act g a ⊓ a)) := by
  obtain ⟨w, hw, h⟩ := AlmostInvariant.OneSided.lattice_form (⇑act) (act_mul act)
    (fun z : L => (ρ z : ℤ)) (strictMono_int hρ) (val_int hρ) (inv_int hρ act) a 1 1 le_rfl zero_le_one
  refine ⟨w, hw, ?_⟩
  have h' : (Fintype.card G : ℤ) * (1 * ((ρ a : ℤ) - ρ (w ⊓ a)) + 1 * ((ρ w : ℤ) - ρ (w ⊓ a))) ≤
      (1 + 1) * ∑ g, ((ρ a : ℤ) - ρ (act g a ⊓ a)) := h
  have e : (1 : ℤ) + 1 = 2 := by norm_num
  rw [one_mul, one_mul, e] at h'
  exact h'

end KPLattice

#print axioms KPLattice.IsRankFn.isModularLattice
#print axioms KPLattice.IsRankFn.map_orderIso
#print axioms KPLattice.family_one_sided
#print axioms KPLattice.single_orbit_one_sided
#print axioms KPLattice.single_orbit_total
#print axioms KPLattice.finite_group_total
