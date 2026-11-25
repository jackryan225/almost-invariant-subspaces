import Mathlib

/-!
# Theorem A of Kazhdan and Polishchuk in its original form: the statements

This file imports Mathlib only and uses no definition of ours. Each proof is `sorry` here. The proofs are in the folder
`KPFull`. `Check/SameStatementFull.lean` checks that each statement below and its proved twin are the same term, and
`Check/AxiomsFull.lean` prints the axioms of each proved twin. (`Challenge/Statement.lean` has the statements for one orbit.)

Source: D. Kazhdan and A. Polishchuk, *Almost invariant subspaces and operators*, arXiv 2107.08085,
Pure Appl. Math. Q. 19 (2023), 1975-1983, Theorem A. In our words: a group `G` acts linearly on a vector space `V` over a
field and maps a collection `X` of subspaces `A_x` to itself, and `dim A_x / (A_x ∩ A_y) ≤ r` for all `x, y`, with `r ≥ 1`.
Then there is a `G`-invariant subspace `W`, a finite sum of finite intersections of members of `X`, with
`dim W / (W ∩ A_x) ≤ r` and `dim A_x / (W ∩ A_x) ≤ r (r + 1)^(r + 1)` for every `x`.

Notation. `X` is a `G`-set and `A : X → Submodule K V` is equivariant: `A (g • x) = g A_x`. (A `G`-stable collection of
subspaces is the case `X ⊆ Submodule K V`, `A = Subtype.val`; conversely the image of an equivariant `A` is a
`G`-stable collection with the same hypotheses and conclusions. See FIDELITY.md.)
`B.submoduleOf A` is `A ∩ B` as a subspace of `A`, so `A ⧸ B.submoduleOf A` is `A / (A ∩ B)`, and
`Module.rank` is the dimension (a cardinal; `V` may have infinite dimension).

The scalars are a division ring (every field is one). No finiteness of `G`, `X` or `dim V` is assumed. `r = 0` is allowed.
-/

open Module

namespace KPFull

/-- **(S1) Theorem A, one-sided form, families, with a polynomial bound.** Any group `G`, any `G`-set `X`, any
equivariant family `A_x`, any dimension. If `dim A_x / (A_x ∩ A_y) ≤ r` for all `x, y`, there is a `G`-invariant `W`
with `dim W / (W ∩ A_x) ≤ r` and `dim A_x / (W ∩ A_x) ≤ r (r + 1)` for every `x`.
Here `W` is any subspace (the form of `W` is required in S2). -/
theorem kp_family_one_sided {K V G X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Group G] [MulAction G X] (ρ : G →* (V ≃ₗ[K] V)) (A : X → Submodule K V)
    (hA : ∀ (g : G) (x : X), A (g • x) = (A x).map (ρ g : V →ₗ[K] V)) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤ (r * (r + 1) : ℕ) := by
  sorry

/-- **(S2) Theorem A exactly as printed, with `r^2 (r + 1)` in place of `r (r + 1)^(r + 1)`.** As S1, and moreover `W` is a
finite sum of finite intersections of members: `W = ∑_{s ∈ S} ⋂_{x ∈ s} A_x` for a finite nonempty set `S` of finite
nonempty sets of indices. `X` is nonempty (for `X = ∅` the printed statement is degenerate). -/
theorem kp_family_finite_form {K V G X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Group G] [MulAction G X] [Nonempty X] (ρ : G →* (V ≃ₗ[K] V)) (A : X → Submodule K V)
    (hA : ∀ (g : G) (x : X), A (g • x) = (A x).map (ρ g : V →ₗ[K] V)) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤ (r ^ 2 * (r + 1) : ℕ) := by
  sorry

/-- **(S2') The same with the sharper bound `r K_r`, `K_r = ∑_{j=1}^{r} ⌈(r + 1)/j⌉`** (`K_r ≤ r (r + 1)`, and
`K_r = O(r log r)`). S2 follows from S2' because `K_r ≤ r (r + 1)`. -/
theorem kp_family_finite_form_sharp {K V G X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Group G] [MulAction G X] [Nonempty X] (ρ : G →* (V ≃ₗ[K] V)) (A : X → Submodule K V)
    (hA : ∀ (g : G) (x : X), A (g • x) = (A x).map (ρ g : V →ₗ[K] V)) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤
          (r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ : ℕ) := by
  sorry

/-- **(S3) The single-orbit corollary**, for any group, any division ring and any dimension: the family of all `gA`.
If `dim A / (A ∩ gA) ≤ r` for all `g`, there is an invariant `W` with `dim W / (W ∩ A) ≤ r` and
`dim A / (W ∩ A) ≤ r (r + 1)`. `KPFull/SingleOrbit.lean` proves S3 from S1. `Check/Contains.lean` derives from S3 the
statement `almost_invariant_one_sided` of `Challenge/Statement.lean` (field, `dim V < ∞`, `G` finite). -/
theorem kp_single_orbit {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Group G]
    (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g : G, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) :
    ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      Module.rank K (W ⧸ A.submoduleOf W) ≤ r ∧
      Module.rank K (A ⧸ W.submoduleOf A) ≤ (r * (r + 1) : ℕ) := by
  sorry

/-- **(S4, stronger) Canonical form.** No group: `W` (a finite sum of finite intersections) is fixed by EVERY
order automorphism `φ` of the lattice of subspaces that permutes the members of the family. This contains S2' (take
`φ = map (ρ g)`), and it contains the semilinear case that Theorem B (Galois groups) needs, because a semilinear
bijection also acts on the lattice of subspaces. -/
theorem kp_family_canonical {K V X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Nonempty X]
    (A : X → Submodule K V) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ φ : Submodule K V ≃o Submodule K V,
        (∀ x, ∃ y, φ (A x) = A y) → (∀ y, ∃ x, φ (A x) = A y) → φ W = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤
          (r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ : ℕ) := by
  sorry

/-! The statement that the one-sided bound cannot be linear (the projective-plane example) is a paper remark in this
repository, not a Lean theorem; see REMARKS.md, item B1. -/

end KPFull
