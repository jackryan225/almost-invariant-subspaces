import KPFull.PartB
import KPLattice.FiniteRank

/-!
# The form of Theorem A (S2', S2, S4) for a modular lattice of finite rank

`KPFull/PartB.lean` proves part B for the lattice of submodules of a module. Here the same proof is written
for an abstract bounded lattice `L` with a rank function `ρ` (`IsRankFn ρ`, see `FiniteRank.lean`), with the distance
`ldist rk a b = rk a - rk (a ⊓ b)` (an integer, `rk = ρ`). The fixed element and inequality (1) of `PROOF.md`, section 2,
come from `KPFamLat.exists_fixed_family_one_sided` (abstract lattices); the descent, the greedy intersection,
the finite join and its invariance follow `KPFull/PartB.lean` step by step. The potential `pot` and `K_r` are reused.

Results (any group acting by order automorphisms; `X` nonempty; `ρ (a x) - ρ (a x ⊓ a y) ≤ r` for all `x, y`):
* `family_finite_form` (S2'): `W = ⨆_{s ∈ S} ⨅_{x ∈ s} a x` (finite, nonempty), fixed by the group, with
  `ρ W - ρ (W ⊓ a x) ≤ r` and `ρ (a x) - ρ (a x ⊓ W) ≤ r K_r`;
* `family_finite_form_cubic` (S2): the same with `r^2 (r + 1)`;
* `family_canonical` (S4): `W` fixed by every order automorphism of `L` that permutes the members.
-/

namespace KPLattice

open KPFull.PartB (Kr pot pot_mono pot_step pot_top Kr_le)

/-- The integer rank. -/
def rkOf {L : Type*} (ρ : L → ℕ) (z : L) : ℤ := ρ z

section dist

variable {L : Type*} [Lattice L] (rk : L → ℤ)

/-- `ldist rk a b = rk a - rk (a ⊓ b)`: the length of `[a ⊓ b, a]` when `rk` is a rank. -/
def ldist (a b : L) : ℤ := rk a - rk (a ⊓ b)

theorem ldist_nonneg (hs : StrictMono rk) (a b : L) : 0 ≤ ldist rk a b := by
  unfold ldist
  have := hs.monotone (inf_le_left : a ⊓ b ≤ a)
  omega

theorem ldist_eq_zero_iff (hs : StrictMono rk) {a b : L} : ldist rk a b = 0 ↔ a ≤ b := by
  unfold ldist
  constructor
  · intro h
    by_contra hab
    have hlt : a ⊓ b < a :=
      lt_of_le_of_ne inf_le_left (fun e => hab (by rw [← e]; exact inf_le_right))
    have := hs hlt
    omega
  · intro h
    rw [inf_eq_left.mpr h]
    omega

theorem ldist_mono_left (hs : StrictMono rk) (hm : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y)
    {l a : L} (h : l ≤ a) (b : L) : ldist rk l b ≤ ldist rk a b := by
  unfold ldist
  have e1 := hm l (a ⊓ b)
  have e2 : l ⊓ (a ⊓ b) = l ⊓ b := by rw [← inf_assoc, inf_eq_left.mpr h]
  have e3 : rk (l ⊔ (a ⊓ b)) ≤ rk a := hs.monotone (sup_le h inf_le_left)
  rw [e2] at e1
  omega

theorem ldist_anti_right (hs : StrictMono rk) (a : L) {b b' : L} (h : b ≤ b') :
    ldist rk a b' ≤ ldist rk a b := by
  unfold ldist
  have := hs.monotone (inf_le_inf_left a h)
  omega

theorem ldist_chain {a b c : L} (hcb : c ≤ b) (hba : b ≤ a) :
    ldist rk a c = ldist rk a b + ldist rk b c := by
  unfold ldist
  rw [inf_eq_right.mpr (hcb.trans hba), inf_eq_right.mpr hba, inf_eq_right.mpr hcb]
  ring

theorem ldist_inf_right (a b : L) : ldist rk a (a ⊓ b) = ldist rk a b := by
  unfold ldist
  rw [← inf_assoc, inf_idem]

theorem ldist_sup_left (hm : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y) (a b : L) :
    ldist rk (a ⊔ b) b = ldist rk a b := by
  unfold ldist
  rw [inf_eq_right.mpr (le_sup_right : b ≤ a ⊔ b)]
  have := hm a b
  omega

end dist

section fin

variable {L : Type*} [Lattice L] [BoundedOrder L]

theorem orderIso_finset_inf {X : Type*} (φ : L ≃o L) (a : X → L) (T : Finset X) :
    φ (T.inf a) = T.inf (fun x => φ (a x)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.inf_empty]; exact OrderIso.map_top φ
  | insert y T hy ih => rw [Finset.inf_insert, Finset.inf_insert, OrderIso.map_inf, ih]

theorem orderIso_finset_sup {Y : Type*} (φ : L ≃o L) (f : Y → L) (F : Finset Y) :
    φ (F.sup f) = F.sup (fun T => φ (f T)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sup_empty]; exact OrderIso.map_bot φ
  | insert y F hy ih => rw [Finset.sup_insert, Finset.sup_insert, OrderIso.map_sup, ih]

end fin

section main

variable {L : Type*} [Lattice L] [BoundedOrder L] {G X : Type*} [Group G]

/-- **S2' for a modular lattice of finite rank.** -/
theorem family_finite_form (act : G →* (L ≃o L)) {ρ : L → ℕ} (hρ : IsRankFn ρ) [Nonempty X] (a : X → L)
    (ha : ∀ g x, ∃ y, act g (a x) = a y) (r : ℕ) (hr : ∀ x y, ρ (a x) ≤ ρ (a x ⊓ a y) + r) :
    ∃ S : Finset (Finset X), S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧
      (∀ g, act g (S.sup (fun s => s.inf a)) = S.sup (fun s => s.inf a)) ∧
      ∀ x, ρ (S.sup (fun s => s.inf a)) ≤ ρ (S.sup (fun s => s.inf a) ⊓ a x) + r ∧
        ρ (a x) ≤ ρ (a x ⊓ S.sup (fun s => s.inf a)) + r * Kr r := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty X›
  have hs : StrictMono (rkOf ρ) := strictMono_int hρ
  have hm : ∀ p q : L, rkOf ρ (p ⊔ q) + rkOf ρ (p ⊓ q) = rkOf ρ p + rkOf ρ q := val_int hρ
  have hi : ∀ (g : G) (p : L), rkOf ρ (act g p) = rkOf ρ p := inv_int hρ act
  have hr' : ∀ x y, ldist (rkOf ρ) (a x) (a y) ≤ r := by
    intro x y
    have := hr x y
    show (ρ (a x) : ℤ) - ρ (a x ⊓ a y) ≤ r
    omega
  have hr0 : ∀ g, rkOf ρ (a x0) - rkOf ρ (act g (a x0) ⊓ a x0) ≤ (r : ℤ) := by
    intro g
    obtain ⟨y, hy⟩ := ha g x0
    rw [hy, inf_comm]
    exact hr' x0 y
  obtain ⟨w, hw, hB, t, τ, ι, hF, hN, σ, hτ, ht1, ht2, hE⟩ :=
    KPFamLat.exists_fixed_family_one_sided (⇑act) (act_mul act) (rkOf ρ) hs hm hi (a x0) (r : ℤ) hr0
  -- the two bounds for `w`
  have hwB : ∀ x, ldist (rkOf ρ) w (a x) ≤ r ∧ ldist (rkOf ρ) (a x) w ≤ (r : ℤ) * ((r : ℤ) + 1) := by
    intro x
    have hB1 : ∀ g, rkOf ρ (a x) - rkOf ρ (a x ⊓ act g (a x0)) ≤ (r : ℤ) := by
      intro g
      obtain ⟨y, hy⟩ := ha g x0
      rw [hy]
      exact hr' x y
    have hB2 : ∀ g, rkOf ρ (act g (a x0)) - rkOf ρ (act g (a x0) ⊓ a x) ≤ (r : ℤ) := by
      intro g
      obtain ⟨y, hy⟩ := ha g x0
      rw [hy]
      exact hr' y x
    exact hB (a x) hB1 hB2
  -- the conditions on the level, as in `KPFull.PartB.descent_of_export`
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have ht1' : (r : ℝ) / (r + 1) ≤ t := by push_cast at ht1; exact ht1
  have ht2' : (t - (r : ℝ) / (r + 1)) * ((r : ℝ) * (r + 1)) + τ < 1 / ((r : ℝ) + 1) := by
    push_cast at ht2; exact ht2
  have e : ((r : ℝ) + 1) * (r / (r + 1)) = r := by field_simp
  have htA : (r : ℝ) ≤ (r + 1) * t := by
    have h := mul_le_mul_of_nonneg_left ht1' hr1.le
    rwa [e] at h
  have htB : ((r : ℝ) + 1) * (t * ((r * (r + 1) : ℕ) : ℝ) + τ) < r * ((r * (r + 1) : ℕ) : ℝ) + 1 := by
    have h2 := mul_lt_mul_of_pos_left ht2' hr1
    have e2 : ((r : ℝ) + 1) * (1 / (r + 1)) = 1 := by field_simp
    have e3 : ((r : ℝ) + 1) * ((t - r / (r + 1)) * (r * (r + 1)) + τ) =
        (r + 1) * (t * (r * (r + 1)) + τ) - r * (r * (r + 1)) := by
      field_simp
      ring
    rw [e2, e3] at h2
    push_cast
    linarith
  -- the descent property (main lemma of docs/NOTE.tex, section 1.5)
  have hdesc : ∀ (l : L) (x : X) (n : ℕ), l ≤ a x → ldist (rkOf ρ) l w = n → 1 ≤ n → n ≤ r * (r + 1) →
      ∃ y, ((r : ℤ) + 1) * ldist (rkOf ρ) (l ⊓ a y) w ≤ (r : ℤ) * n := by
    intro l x n _ hn _ hnB
    have hwE : w ≤ l ⊔ w := le_sup_right
    have hEn : rkOf ρ (l ⊔ w) - rkOf ρ w = n := by
      have h1 := ldist_sup_left (rkOf ρ) hm l w
      unfold ldist at h1
      rw [inf_eq_right.mpr hwE] at h1
      rw [h1]
      exact hn
    let c : ι → ℤ := fun i => rkOf ρ (act (σ i) (a x0) ⊓ (l ⊔ w)) - rkOf ρ (act (σ i) (a x0) ⊓ w)
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
    have havg : ((c i0 : ℤ) : ℝ) ≤ KPFamLat.avg (fun i =>
        (rkOf ρ (act (σ i) (a x0) ⊓ (l ⊔ w)) : ℝ) - rkOf ρ (act (σ i) (a x0) ⊓ w)) := by
      have h := KPFamLat.avg_mono (φ := fun _ : ι => ((c i0 : ℤ) : ℝ))
        (ψ := fun i => (rkOf ρ (act (σ i) (a x0) ⊓ (l ⊔ w)) : ℝ) - rkOf ρ (act (σ i) (a x0) ⊓ w)) (fun i => by
          show ((c i0 : ℤ) : ℝ) ≤ (rkOf ρ (act (σ i) (a x0) ⊓ (l ⊔ w)) : ℝ) - rkOf ρ (act (σ i) (a x0) ⊓ w)
          have := hi0 i (Finset.mem_univ i)
          exact_mod_cast this)
      rwa [KPFamLat.avg_const] at h
    have hEn' : ((rkOf ρ (l ⊔ w) : ℝ) - rkOf ρ w) = n := by exact_mod_cast hEn
    have hcn : ((c i0 : ℤ) : ℝ) ≤ t * n + τ := by
      have := le_trans havg (hE (l ⊔ w))
      rw [hEn'] at this
      exact this
    have hnB' : (n : ℝ) ≤ ((r * (r + 1) : ℕ) : ℝ) := by exact_mod_cast hnB
    have hreal : ((r : ℝ) + 1) * ((c i0 : ℤ) : ℝ) < r * n + 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr htA) (sub_nonneg.mpr hnB'), mul_le_mul_of_nonneg_left hcn hr1.le]
    have hint : ((r : ℤ) + 1) * c i0 < (r : ℤ) * n + 1 := by exact_mod_cast hreal
    obtain ⟨y, hy⟩ := ha (σ i0) x0
    refine ⟨y, ?_⟩
    have hle : ldist (rkOf ρ) (l ⊓ a y) w ≤ c i0 := by
      have h1 : l ⊓ a y ≤ a y ⊓ (l ⊔ w) := le_inf inf_le_right (inf_le_left.trans le_sup_left)
      have h2 := ldist_mono_left (rkOf ρ) hs hm h1 w
      have h3 : ldist (rkOf ρ) (a y ⊓ (l ⊔ w)) w = c i0 := by
        show rkOf ρ (a y ⊓ (l ⊔ w)) - rkOf ρ (a y ⊓ (l ⊔ w) ⊓ w) =
          rkOf ρ (act (σ i0) (a x0) ⊓ (l ⊔ w)) - rkOf ρ (act (σ i0) (a x0) ⊓ w)
        rw [hy, inf_assoc, inf_eq_right.mpr hwE]
      rw [h3] at h2
      exact h2
    have hr0' : (0 : ℤ) ≤ (r : ℤ) + 1 := by positivity
    have h4 := mul_le_mul_of_nonneg_left hle hr0'
    exact Int.lt_add_one_iff.mp (lt_of_le_of_lt h4 hint)
  -- greedy intersection (docs/NOTE.tex, section 1.6)
  have hgreedy : ∀ n : ℕ, ∀ (x : X) (T : Finset X), x ∈ T → ldist (rkOf ρ) (T.inf a) w = n →
      n ≤ r * (r + 1) → ∃ T' : Finset X, T ⊆ T' ∧ T'.inf a ≤ w ∧
        ldist (rkOf ρ) (T.inf a) (T'.inf a) ≤ (r : ℤ) * (pot r n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x T hxT hn hnB
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have hz : ldist (rkOf ρ) (T.inf a) w = 0 := by exact_mod_cast hn
        refine ⟨T, Finset.Subset.refl T, (ldist_eq_zero_iff (rkOf ρ) hs).mp hz, ?_⟩
        have : ldist (rkOf ρ) (T.inf a) (T.inf a) = 0 := (ldist_eq_zero_iff (rkOf ρ) hs).mpr le_rfl
        rw [this]
        positivity
      · obtain ⟨y, hy⟩ := hdesc (T.inf a) x n (Finset.inf_le (f := a) hxT) hn hpos hnB
        have hmnn : 0 ≤ ldist (rkOf ρ) (T.inf a ⊓ a y) w := ldist_nonneg (rkOf ρ) hs _ _
        obtain ⟨m, hm'⟩ : ∃ m : ℕ, ldist (rkOf ρ) (T.inf a ⊓ a y) w = m :=
          ⟨_, (Int.toNat_of_nonneg hmnn).symm⟩
        rw [hm'] at hy
        have hy' : (r + 1) * m ≤ r * n := by exact_mod_cast hy
        have hmn : m < n := by
          by_contra hcon
          have h1 : (r + 1) * n ≤ (r + 1) * m := Nat.mul_le_mul_left _ (by omega)
          have h2 : (r + 1) * n = r * n + n := by ring
          omega
        have hT1 : (insert y T).inf a = T.inf a ⊓ a y := by rw [Finset.inf_insert, inf_comm]
        obtain ⟨T', hsub, hT'w, hcost⟩ := ih m hmn x (insert y T) (Finset.mem_insert_of_mem hxT)
          (by rw [hT1, hm']) (hmn.le.trans hnB)
        refine ⟨T', (Finset.subset_insert y T).trans hsub, hT'w, ?_⟩
        have hchain := ldist_chain (rkOf ρ) (Finset.inf_mono (f := a) hsub)
          (Finset.inf_mono (f := a) (Finset.subset_insert y T))
        have hstep : ldist (rkOf ρ) (T.inf a) ((insert y T).inf a) ≤ r := by
          rw [hT1, ldist_inf_right]
          exact (ldist_mono_left (rkOf ρ) hs hm (Finset.inf_le (f := a) hxT) (a y)).trans (hr' x y)
        have hP := pot_step hpos hnB hy'
        have hP' : (r : ℤ) + (r : ℤ) * (pot r m : ℤ) ≤ (r : ℤ) * (pot r n : ℤ) := by
          have h1 : r * (pot r m + 1) ≤ r * pot r n := Nat.mul_le_mul_left r hP
          have h2 : r * (pot r m + 1) = r * pot r m + r := by ring
          have h3 : r + r * pot r m ≤ r * pot r n := by omega
          exact_mod_cast h3
        rw [hchain]
        linarith
  -- for every member, a finite intersection inside `w` at cost at most `r K_r`
  have hTx : ∀ x, ∃ T : Finset X, x ∈ T ∧ T.inf a ≤ w ∧
      ldist (rkOf ρ) (a x) (T.inf a) ≤ (r : ℤ) * (Kr r : ℤ) := by
    intro x
    have hnn : 0 ≤ ldist (rkOf ρ) (a x) w := ldist_nonneg (rkOf ρ) hs _ _
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ldist (rkOf ρ) (a x) w = n := ⟨_, (Int.toNat_of_nonneg hnn).symm⟩
    have hnB : n ≤ r * (r + 1) := by
      have h := (hwB x).2
      rw [hn] at h
      have h' : (n : ℤ) ≤ ((r * (r + 1) : ℕ) : ℤ) := by push_cast; exact h
      exact_mod_cast h'
    obtain ⟨T', hsub, hT'w, hc⟩ := hgreedy n x {x} (Finset.mem_singleton_self x)
      (by rw [Finset.inf_singleton]; exact hn) hnB
    refine ⟨T', hsub (Finset.mem_singleton_self x), hT'w, ?_⟩
    rw [Finset.inf_singleton] at hc
    have hpot : pot r n ≤ Kr r := by
      rw [← pot_top r]
      exact pot_mono r hnB
    have hpot' : (r : ℤ) * (pot r n : ℤ) ≤ (r : ℤ) * (Kr r : ℤ) := by
      have h := Nat.mul_le_mul_left r hpot
      exact_mod_cast h
    linarith
  -- a finite join of the eligible intersections that is their least upper bound (`PartB.sumInter_eq_finite`)
  obtain ⟨T0, hxT0, hT0w, -⟩ := hTx x0
  have hN0 : 0 ≤ rkOf ρ w - rkOf ρ (T0.inf a) := by
    have := hs.monotone hT0w
    omega
  have hSw : ∀ F : Finset (Finset X), (∀ T ∈ F, T.Nonempty ∧ T.inf a ≤ w) →
      F.sup (fun T => T.inf a) ≤ w := fun F hF => Finset.sup_le fun T hT => (hF T hT).2
  let N : ℕ := (rkOf ρ w - rkOf ρ (T0.inf a)).toNat
  have hNdef : (N : ℤ) = rkOf ρ w - rkOf ρ (T0.inf a) := Int.toNat_of_nonneg hN0
  let Q : ℕ → Prop := fun k => ∃ F : Finset (Finset X), T0 ∈ F ∧ (∀ T ∈ F, T.Nonempty ∧ T.inf a ≤ w) ∧
    rkOf ρ (F.sup (fun T => T.inf a)) - rkOf ρ (T0.inf a) = k
  have hQle : ∀ k, Q k → k ≤ N := by
    rintro k ⟨F, -, hF, hk⟩
    have := hs.monotone (hSw F hF)
    omega
  have hQ0 : Q 0 := by
    refine ⟨{T0}, Finset.mem_singleton_self _, fun T hT => ?_, ?_⟩
    · rw [Finset.mem_singleton.mp hT]
      exact ⟨⟨x0, hxT0⟩, hT0w⟩
    · rw [Finset.sup_singleton]
      simp
  obtain ⟨F, hT0F, hF, hFk⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  have hmax : ∀ T : Finset X, T.Nonempty → T.inf a ≤ w → T.inf a ≤ F.sup (fun T => T.inf a) := by
    intro T hTne hTw
    have hF' : ∀ T' ∈ insert T F, T'.Nonempty ∧ T'.inf a ≤ w := by
      intro T' hT'
      rcases Finset.mem_insert.mp hT' with h | h
      · rw [h]
        exact ⟨hTne, hTw⟩
      · exact hF T' h
    have hle1 : F.sup (fun T => T.inf a) ≤ (insert T F).sup (fun T => T.inf a) :=
      Finset.sup_mono (Finset.subset_insert T F)
    have hle0 : T0.inf a ≤ F.sup (fun T => T.inf a) := Finset.le_sup (f := fun T => T.inf a) hT0F
    have hk'nn : 0 ≤ rkOf ρ ((insert T F).sup (fun T => T.inf a)) - rkOf ρ (T0.inf a) := by
      have := hs.monotone (hle0.trans hle1)
      omega
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ,
        rkOf ρ ((insert T F).sup (fun T => T.inf a)) - rkOf ρ (T0.inf a) = k' :=
      ⟨_, (Int.toNat_of_nonneg hk'nn).symm⟩
    have hQk' : Q k' := ⟨insert T F, Finset.mem_insert_of_mem hT0F, hF', hk'⟩
    have hk'le : k' ≤ Nat.findGreatest Q N := Nat.le_findGreatest (hQle k' hQk') hQk'
    have heq : F.sup (fun T => T.inf a) = (insert T F).sup (fun T => T.inf a) := by
      by_contra hne
      have hlt := lt_of_le_of_ne hle1 hne
      have := hs hlt
      omega
    have h := Finset.le_sup (f := fun T => T.inf a) (Finset.mem_insert_self T F)
    rw [← heq] at h
    exact h
  -- invariance (`PartB.sumInter_map_le`)
  have hinvle : ∀ g, act g (F.sup (fun T => T.inf a)) ≤ F.sup (fun T => T.inf a) := by
    intro g
    choose σg hσg using ha g
    rw [orderIso_finset_sup (act g) (fun T => T.inf a) F]
    refine Finset.sup_le fun T hT => ?_
    show act g (T.inf a) ≤ F.sup (fun T => T.inf a)
    have himg : act g (T.inf a) = (T.image σg).inf a := by
      rw [orderIso_finset_inf, Finset.inf_image]
      exact Finset.inf_congr rfl fun x _ => hσg x
    have hTw : (T.image σg).inf a ≤ w := by
      rw [← himg]
      calc act g (T.inf a) ≤ act g w := (act g).monotone (hF T hT).2
        _ = w := hw g
    rw [himg]
    exact hmax _ ((hF T hT).1.image σg) hTw
  have hfix : ∀ g, act g (F.sup (fun T => T.inf a)) = F.sup (fun T => T.inf a) := by
    intro g
    refine le_antisymm (hinvle g) ?_
    have h := (act g).monotone (hinvle g⁻¹)
    rwa [map_inv, RelIso.apply_inv_self] at h
  -- the bounds
  refine ⟨F, ⟨T0, hT0F⟩, fun T hT => (hF T hT).1, hfix, fun x => ?_⟩
  have hDw : F.sup (fun T => T.inf a) ≤ w := hSw F hF
  obtain ⟨Tx, hxTx, hTxw, hcx⟩ := hTx x
  have hTxD : Tx.inf a ≤ F.sup (fun T => T.inf a) := hmax Tx ⟨x, hxTx⟩ hTxw
  have h1 : ldist (rkOf ρ) (F.sup (fun T => T.inf a)) (a x) ≤ r :=
    (ldist_mono_left (rkOf ρ) hs hm hDw (a x)).trans (hwB x).1
  have h2 : ldist (rkOf ρ) (a x) (F.sup (fun T => T.inf a)) ≤ (r : ℤ) * (Kr r : ℤ) :=
    (ldist_anti_right (rkOf ρ) hs (a x) hTxD).trans hcx
  unfold ldist rkOf at h1 h2
  constructor
  · omega
  · have h3 : ((ρ (a x) : ℕ) : ℤ) ≤ ((ρ (a x ⊓ F.sup (fun T => T.inf a)) + r * Kr r : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h3

/-- **S2 for a modular lattice of finite rank:** the bound `r^2 (r + 1)`. -/
theorem family_finite_form_cubic (act : G →* (L ≃o L)) {ρ : L → ℕ} (hρ : IsRankFn ρ) [Nonempty X]
    (a : X → L) (ha : ∀ g x, ∃ y, act g (a x) = a y) (r : ℕ) (hr : ∀ x y, ρ (a x) ≤ ρ (a x ⊓ a y) + r) :
    ∃ S : Finset (Finset X), S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧
      (∀ g, act g (S.sup (fun s => s.inf a)) = S.sup (fun s => s.inf a)) ∧
      ∀ x, ρ (S.sup (fun s => s.inf a)) ≤ ρ (S.sup (fun s => s.inf a) ⊓ a x) + r ∧
        ρ (a x) ≤ ρ (a x ⊓ S.sup (fun s => s.inf a)) + r ^ 2 * (r + 1) := by
  obtain ⟨S, h1, h2, h3, h4⟩ := family_finite_form act hρ a ha r hr
  refine ⟨S, h1, h2, h3, fun x => ⟨(h4 x).1, ?_⟩⟩
  have hK : r * Kr r ≤ r ^ 2 * (r + 1) := by
    calc r * Kr r ≤ r * (r * (r + 1)) := Nat.mul_le_mul_left r (Kr_le r)
      _ = r ^ 2 * (r + 1) := by ring
  have := (h4 x).2
  omega

/-- The group of all order automorphisms of `L` that permute the members. -/
def permGroupL (a : X → L) : Subgroup (L ≃o L) where
  carrier := {φ | (∀ x, ∃ y, φ (a x) = a y) ∧ (∀ y, ∃ x, φ (a x) = a y)}
  mul_mem' := by
    rintro φ ψ ⟨hφ1, hφ2⟩ ⟨hψ1, hψ2⟩
    refine ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, hy⟩ := hψ1 x
      obtain ⟨z, hz⟩ := hφ1 y
      exact ⟨z, by rw [RelIso.mul_apply, hy, hz]⟩
    · obtain ⟨x1, hx1⟩ := hφ2 y
      obtain ⟨x2, hx2⟩ := hψ2 x1
      exact ⟨x2, by rw [RelIso.mul_apply, hx2, hx1]⟩
  one_mem' := ⟨fun x => ⟨x, rfl⟩, fun y => ⟨y, rfl⟩⟩
  inv_mem' := by
    rintro φ ⟨hφ1, hφ2⟩
    refine ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨x', hx'⟩ := hφ2 x
      exact ⟨x', by rw [← hx', RelIso.inv_apply_self]⟩
    · obtain ⟨x', hx'⟩ := hφ1 y
      exact ⟨x', by rw [← hx', RelIso.inv_apply_self]⟩

theorem mem_permGroupL {a : X → L} {φ : L ≃o L} :
    φ ∈ permGroupL a ↔ (∀ x, ∃ y, φ (a x) = a y) ∧ (∀ y, ∃ x, φ (a x) = a y) := Iff.rfl

/-- **S4 for a modular lattice of finite rank (canonical form).** No group: `W` is fixed by every order automorphism
of `L` that permutes the members. -/
theorem family_canonical {ρ : L → ℕ} (hρ : IsRankFn ρ) [Nonempty X] (a : X → L) (r : ℕ)
    (hr : ∀ x y, ρ (a x) ≤ ρ (a x ⊓ a y) + r) :
    ∃ S : Finset (Finset X), S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧
      (∀ φ : L ≃o L, (∀ x, ∃ y, φ (a x) = a y) → (∀ y, ∃ x, φ (a x) = a y) →
        φ (S.sup (fun s => s.inf a)) = S.sup (fun s => s.inf a)) ∧
      ∀ x, ρ (S.sup (fun s => s.inf a)) ≤ ρ (S.sup (fun s => s.inf a) ⊓ a x) + r ∧
        ρ (a x) ≤ ρ (a x ⊓ S.sup (fun s => s.inf a)) + r * Kr r := by
  obtain ⟨S, h1, h2, h3, h4⟩ := family_finite_form (permGroupL a).subtype hρ a
    (fun g x => (mem_permGroupL.mp g.2).1 x) r hr
  exact ⟨S, h1, h2, fun φ hφ1 hφ2 => h3 ⟨φ, mem_permGroupL.mpr ⟨hφ1, hφ2⟩⟩, h4⟩

end main

end KPLattice

#print axioms KPLattice.family_finite_form
#print axioms KPLattice.family_finite_form_cubic
#print axioms KPLattice.family_canonical
