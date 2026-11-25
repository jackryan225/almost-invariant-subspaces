# Fidelity note: Theorem A of Kazhdan and Polishchuk against the Lean statements

Source: D. Kazhdan, A. Polishchuk, *Almost invariant subspaces and operators*, arXiv 2107.08085 (version 1 of
16 July 2021, the only version), Pure Appl. Math. Q. 19 (2023), 1975-1983. We read the arXiv PDF. Below, the clauses
of Theorem A are restated in our notation, not quoted.

Notation: `d(A, B) = dim A/(A ∩ B)`. In Lean, `(A y).submoduleOf (A x)` is `A_x ∩ A_y` as a subspace of `A_x`, so
`Module.rank K (A x ⧸ (A y).submoduleOf (A x))` is `d(A_x, A_y)`. `Module.rank` is a cardinal, so the dimension may be
infinite. `W.map (ρ g)` is `gW`.

## The Lean statements and their proofs

`Challenge/StatementFull.lean` imports Mathlib only and has five statements in the namespace `KPFull`, each with `sorry`.
(`Challenge/Statement.lean` has the five single-orbit statements of the first version of this repository; it is unchanged.)

| Id | Statement in `Challenge/StatementFull.lean` | Proved twin | File of the proof |
|---|---|---|---|
| S1 | `KPFull.kp_family_one_sided` | `KPFamilies.kp_family_one_sided` | `KPFull/Families.lean` |
| S2 | `KPFull.kp_family_finite_form` | `KPFullFinal.kp_family_finite_form` | `KPFull/FinalS2.lean` |
| S2' | `KPFull.kp_family_finite_form_sharp` | `KPFullFinal.kp_family_finite_form_sharp` | `KPFull/FinalS2.lean` |
| S3 | `KPFull.kp_single_orbit` | `KPFamilies.kp_single_orbit` | `KPFull/SingleOrbit.lean` |
| S4 | `KPFull.kp_family_canonical` | `KPFullFinal.kp_family_canonical` | `KPFull/FinalS2.lean` |

`Check/SameStatementFull.lean` checks for each line that the type of the statement and the type of the proved twin are equal
as Lean terms, up to the names of the universe parameters, and the kernel checks it again with an `example`.
`Check/AxiomsFull.lean` prints the axioms of each proved twin: `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
The proofs of S2, S2' and S4 use the theorems `KPFamilies.kp_family_export` and `KPFamilies.kp_family_export_linear` of
`KPFull/Families.lean`. They give the invariant `W` of S1 together with the first-order inequality (1) of `PROOF.md`,
Section 2. `KPFull/PartB.lean` (theorem `KPFull.PartB.partB`) turns that inequality into the finite sum of finite
intersections.

## 1. Theorem A, clause by clause

| # | Theorem A (restated) | Lean | Comparison |
|---|---|---|---|
| 1 | `V` is a vector space over a field `k` | `[DivisionRing K] [AddCommGroup V] [Module K V]` | **More general.** Every field is a division ring. The proof uses only the lattice of subspaces and the additivity of the dimension. |
| 2 | no condition on the dimension of `V` | no `FiniteDimensional`; dimensions are `Module.rank` | **Same.** |
| 3 | `X` is a collection of subspaces of `V` | a type `X` with `[MulAction G X]` and `A : X → Submodule K V` | **Equivalent.** From a collection: take `X` = the collection and `A` = the inclusion. From `A`: its image is a collection that `G` preserves, with the same hypotheses and conclusions. Repeated members change nothing, because `d(A_x, A_x) = 0`. |
| 4 | `G` is a group that acts linearly on `V` | `[Group G] (ρ : G →* (V ≃ₗ[K] V))` | **Same.** `G` can be finite or infinite, and the action need not be faithful. |
| 5 | `G` preserves the collection | `hA : ∀ g x, A (g • x) = (A x).map (ρ g)` | **Equivalent** (see row 3). |
| 6 | `r ≥ 1` | `(r : ℕ)` | **More general.** `r = 0` is allowed; then all members are equal. |
| 7 | `d(A_x, A_y) ≤ r` for all `x, y` | `hr : ∀ x y, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r` | **Same.** Both orders of `x, y` are in the hypothesis, as in the paper. |
| 8 | there is a `G`-invariant subspace `W` | `∃ W, ∀ g, W.map (ρ g) = W` | **Same.** |
| 9 | `W` is a finite sum of finite intersections of members | S2, S2', S4: `∃ S : Finset (Finset X), S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = ⨆ s ∈ S, ⨅ x ∈ s, A x`, with `[Nonempty X]` | **Same in S2, S2', S4.** The sum has at least one summand, and each intersection has at least one member, so neither the empty sum `0` nor the empty intersection `V` is allowed. `[Nonempty X]` removes only the degenerate case `X = ∅`. **S1 and S3 do not ask for this clause.** |
| 10 | `d(W, A_x) ≤ r` | `∀ x, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r` | **Same**, for every `x`. |
| 11 | `d(A_x, W) ≤ r (r+1)^(r+1)` | S1, S3: `≤ r * (r + 1)`; S2: `≤ r ^ 2 * (r + 1)`; S2', S4: `≤ r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊` | **Smaller bound** in all forms: `r (r+1) ≤ r^2 (r+1) ≤ r (r+1)^(r+1)` for `r ≥ 1`, and `r K_r ≤ r^2 (r+1)` because `K_r ≤ r (r+1)`. Same side as in the paper. |

Two remarks on the printed statement. In the proof of the paper, one case gives `r (r+1)^r` and the other case gives
`r (r+1)^(r+1)`; the theorem states the larger one. In one case the paper first gets `W` as a sum of possibly infinitely
many intersections and then reduces it to a finite sum. The Lean statements ask for the finite sum directly.

## 2. The conjecture after Theorem A

The paper conjectures that the bound `r (r+1)^(r+1)` can be improved to a polynomial, possibly linear, function of `r`,
at least when `G` is finite.

| Part | Status here |
|---|---|
| polynomial, in the exact form of Theorem A | **Proved in Lean** for every group: S2 (`r^2 (r+1)`), S2' (`r K_r = O(r^2 log r)`), S4. |
| polynomial, without the form of `W` | **Proved in Lean**: S1 (`r (r+1)`). |
| possibly linear, in the one-sided form of Theorem A | **False** (paper remark B1 in `REMARKS.md`): for each prime power `q` there is one orbit of a finite group with `r = q` in which every invariant `W` with `d(W, A_x) ≤ r` has `d(A_x, W) = r^2`. |
| linear, for the total error `δ = d(A_x, W) + d(W, A_x)` | Different statement, not in the paper. With any invariant `W`: true for families with `3r` (B3), and `2r` is false for families (B3). With `W` of the form of Theorem A: false, the total error can be at least `c r log r / log log r` (B4). |

## 3. Lemma 2.1 and Theorem B

- **Lemma 2.1** (almost invariant operators `T : V → V'`). The printed hypothesis is `rk(gTg^{-1} − g) ≤ r`. This is a
  misprint: the proof uses `rk(gTg^{-1} − T) ≤ r`. The proof applies Theorem A to one orbit, the graphs of the
  operators `gTg^{-1}` in `V ⊕ V'`, and `V` can have any dimension. Lemma 2.1 is not stated or proved in this repository.
- **Theorem B** (Galois descent). Here a finite Galois group acts on `V_0 ⊗_k E` by `E`-semilinear maps. A linear
  statement over `k` would give bounds that depend on the degree `[E : k]`. S4 is the form that avoids this: it is stated
  over `E`, and every semilinear bijection that permutes the members acts on the lattice of `E`-subspaces. Theorem B is not
  stated or proved in this repository.

## 4. The Question of Section 3

The paper asks whether the explicit subspace `A_0` of its formula (3) satisfies a polynomial bound. Statement 4 of the
single-orbit case (`question_negative_complex` in `Challenge/Statement.lean`) shows in Lean that it does not, already for
`r = 1`. The new statements do not change this.

## 5. Summary

- **More general than the paper:** a division ring instead of a field (row 1); `r = 0` (row 6); the bound (row 11); in S4,
  invariance under every lattice automorphism that permutes the members, which covers semilinear actions.
- **Less general than the paper:** S1 and S3 do not give the form of `W` (row 9). S2, S2' and S4 assume `X ≠ ∅`
  (degenerate case only).
- **Equal:** any group, any dimension, families with any number of orbits, the same sides of both bounds, the same
  quantifiers (one `W` for all `x`, both bounds for every `x`).

Against the first version of this repository: its section "Relation to the original statement" listed four
restrictions (one orbit; `W` a minimizer; only a total error below `4r` for families; finite dimension for the one-sided
form). S1, S2, S2', S3 and S4 remove all four. `KPContains.almost_invariant_one_sided` (`Check/Contains.lean`) derives
the one-sided single-orbit statement `almost_invariant_one_sided` of `Challenge/Statement.lean` from S3.

## 6. What is machine-checked

Machine-checked: S1, S2, S2', S3, S4 and the theorems listed in `README.md` under "More Lean theorems". Not
machine-checked: everything in `REMARKS.md`, and the statements about Lemma 2.1 and Theorem B above. The build and kernel
records are in `logs/`.
