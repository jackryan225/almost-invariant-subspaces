# Almost invariant subspaces are close to invariant subspaces, in Lean 4

**A machine-checked proof of the single-orbit case of a conjecture of Kazhdan and Polishchuk, with a linear bound: for finite groups, and for all groups when the space has finite dimension. The conjecture in its full original generality is not claimed here; see "Relation to the original statement".**
Published on 25 November 2026.

AI agents (Claude, by Anthropic) found and wrote the proofs, under the direction of the owner of this account. The Lean
proof checker accepts them. No human mathematician has reviewed this repository.

## The problem

A finite group `G` acts on a vector space `V` by linear maps. A subspace `A` is *invariant* if `gA = A` for every `g`
in `G`. Suppose that `A` is only *almost invariant*: each `g` moves it by at most `r` dimensions, that is,
`dim A / (A ∩ gA) ≤ r` for every `g`. Is `A` then near an invariant subspace `W`, with an error that depends only on `r`?

D. Kazhdan and A. Polishchuk proved that it is (*Almost invariant subspaces and operators*, arXiv 2107.08085,
Pure Appl. Math. Q. 19 (2023), 1975-1983, Theorem A, for every group `G`). Their theorem is more general than the
question above: it is about a family of subspaces `A_x` that `G` permutes, with `dim A_x / (A_x ∩ A_y) ≤ r` for all
members `x`, `y`. It gives an invariant `W` that is a finite sum of finite intersections of members of the family, with

    dim W / (W ∩ A_x) ≤ r     and     dim A_x / (W ∩ A_x) ≤ r (r + 1)^(r + 1)     for every x.

The question above is the case of one orbit: the family of all `gA`.

Their theorem gives an explicit bound for a theorem of F. Wagner. They wrote: "We conjecture that it should be possible
to improve the bound `r (r + 1)^(r + 1)` to a polynomial (possibly linear) function of `r`, at least in the case when `G`
is finite."

## What this repository proves (all in Lean)

In statements 1 to 4 the group `G` is finite.

1. **Total error less than `2r`.** There is an invariant subspace `W` with

       dim A / (A ∩ W) + dim W / (A ∩ W) ≤ 2r (1 - 1/|G|) < 2r.

   This holds over every field and every division ring, and `V` can have infinite dimension.
2. **The form of Theorem A.** There is an invariant `W` with `dim W / (W ∩ A) ≤ r` and `dim A / (W ∩ A) ≤ r (r + 1)`
   (here `V` has finite dimension).
3. **Modules.** Statement 1 holds for submodules of a module over any ring, with the length of a module in place of the
   dimension. The proof uses only the lattice of submodules, so it also holds for semilinear actions (for example a Galois
   group, as in Theorem B of the paper).
4. **A question in the paper has a negative answer.** For finite `G` the paper proposes the explicit subspace
   `A₀ = ∑ A_S`, the sum over all sets `S` of more than half of the group, where `A_S` is the intersection of the `gA`
   with `g` in `S` (formula (3)). It asks whether `A₀` is near `A`, with a polynomial bound in `r`. It is not: for each
   `c` there is an example with `r = 1`, `A₀ = 0` and `dim A > c`.

5. **All groups.** For every group `G`, finite or infinite, and `V` of finite dimension over a field, there is an invariant
   `W` with total error at most `2r`, and there is an invariant `W` with `dim W / (W ∩ A) ≤ r` and
   `dim A / (W ∩ A) ≤ r (r + 1)`. The bounds do not depend on the dimension of `V`.

## Relation to the original statement

This repository does not prove the conjecture in the full generality of Theorem A. The differences:

- **One orbit, not a family.** All Lean statements are about the orbit of one subspace `A` (the family of all `gA`). This is the
  case that the paper uses for operators (its Lemma 2.1) and for Galois descent (its Theorem B).
- **The form of `W`.** In Theorem A the subspace `W` is a finite sum of finite intersections of members of the family. Our `W`
  is the smallest minimizer of a function on the lattice of subspaces. We do not prove that it has that form.
- **Families.** For a family as in Theorem A, statement 1 for one orbit and the triangle inequality give one invariant `W` with
  total error less than `4r` for every member. This step is a paper argument of two lines and is not in the Lean files. It does
  not give the one-sided form of Theorem A (`dim W / (W ∩ A_x) ≤ r` together with a polynomial bound for the other side).
- **Dimension.** Statement 2 (the form of Theorem A for one orbit) and statement 5 (all groups) are proved in Lean for `V` of
  finite dimension only. Statements 1 and 3 allow infinite dimension.

### The main statement in Lean

`Challenge/Statement.lean` imports Mathlib only and uses no definition of ours. It has the five statements. The first:

```lean
theorem almost_invariant {K V G : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [Group G] [Finite G]
    (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, Module.rank K (A ⧸ (A.map (ρ g : V →ₗ[K] V)).submoduleOf A) ≤ r) :
    ∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∃ a b : ℕ, Module.rank K (A ⧸ W.submoduleOf A) = a ∧ Module.rank K (W ⧸ A.submoduleOf W) = b ∧
        a + b ≤ 2 * r ∧ (0 < r → a + b < 2 * r)
```

Here `A.map (ρ g)` is `gA`, and `B.submoduleOf A` is `A ∩ B` as a subspace of `A`, so `A ⧸ B.submoduleOf A` is
`A / (A ∩ B)`.

## The proof, in ten lines

For subspaces put `d(A, S) = dim A / (A ∩ S)` and `δ(A, S) = d(A, S) + d(S, A)`. Let

    f(S) = ∑ δ(gA, S),   the sum over all g in G.

- `f` is *submodular*: `f(S ∩ T) + f(S + T) ≤ f(S) + f(T)`. This follows from the rules of the dimension.
- `f(hS) = f(S)` for every `h` in `G`, because `h` permutes the subspaces `gA`.
- Let `m` be the least value of `f`. If `f(S) = f(T) = m`, then `f(S ∩ T) = m` by the first rule. So the subspaces with
  the least value are closed under intersections, and there is a smallest one, `W`.
- By the second rule `hW` also has the least value, so `W ⊆ hW` for every `h`. So `hW = W`: the subspace `W` is invariant.
- Then `|G| δ(A, W) = f(W) ≤ f(A) = ∑ δ(gA, A) ≤ 2r (|G| - 1)`, because the term for `g = 1` is `0`.

Statement 2 uses the same argument for `∑ (d(gA, S) + r d(S, gA))`.

An infinite group has no uniform mean, so statement 5 needs more work. In place of the mean over the group the proof uses a
probability measure with finite support for which the least value of the weighted sum is nearly as large as possible, and it
uses several weights at the same time. The file `AlmostInvariant/AllGroups.lean` has the details.

The method (take the smallest minimizer of an invariant submodular function) is standard. The claim here is the theorem.

## Earlier work

- F. O. Wagner, *Almost invariant families*, Bull. London Math. Soc. 30 (1998): existence of `W`, without a bound.
- D. Kazhdan, A. Polishchuk, cited above: the bound `r (r + 1)^(r + 1)`, the conjecture and the question.
- P. M. Neumann, *Permutation groups and close-knit families of sets*, Arch. Math. 67 (1996); L. Brailovsky,
  D. V. Pasechnik, C. E. Praeger, Proc. Amer. Math. Soc. 123 (1995); G. M. Bergman, H. W. Lenstra,
  J. Algebra 127 (1989): the same problem for subsets of a set and for subgroups. For subsets the bound is `2r`, the same
  constant as in statement 1.
- M. Mastnak, M. Omladič, H. Radjavi, *Near-invariant subspaces for matrix groups are nearly invariant*,
  Linear Algebra Appl. 505 (2016), 269-281. To our knowledge this paper has the case `r = 1` for groups of matrices.
  We saw only summaries of it and did not read the full text.

We searched for an earlier proof of the conjecture: the papers that cite the paper of Kazhdan and Polishchuk, arXiv,
MathOverflow, and GitHub (repositories, issues, pull requests). We found none. A search cannot prove that there is none.
If you know an earlier proof, please open an issue, and we will correct this page.

## What is not claimed

- For infinite groups the Lean proof needs `V` of finite dimension. The theorem of Kazhdan and Polishchuk has no such condition.
- We do not claim that `2r` or `r (r + 1)` is the best possible bound.
- The conjecture for arbitrary invariant families, with `W` of the form in Theorem A, is not claimed (see above).

## How to check it

```
lake exe cache get      # downloads compiled Mathlib
lake build              # builds the six proof files (a few minutes)
lake env lean Check/Axioms.lean          # each result: propext, Classical.choice, Quot.sound
lake build Challenge && lake env lean Check/SameStatement.lean
```

The Lean version is in `lean-toolchain` (4.34.1) and Mathlib is pinned in `lake-manifest.json`. The workflow in
`.github/workflows/check.yml` runs these steps on each push. We also replayed the compiled proofs with `leanchecker`,
the separate kernel checker that comes with Lean.

| File | Content |
|---|---|
| `AlmostInvariant/Length.lean` | `d`, `δ`, the rules of the length, submodularity |
| `AlmostInvariant/Finite.lean` | the invariant smallest minimizer; statement 3 for automorphisms of the lattice of submodules |
| `AlmostInvariant/VectorSpace.lean` | statements 1 and 3 for linear actions |
| `AlmostInvariant/OneSided.lean` | statement 2, and a version for modular lattices with a rank function |
| `AlmostInvariant/Question.lean` | statement 4 |
| `AlmostInvariant/AllGroups.lean` | statement 5, and a version for modular lattices with a rank function |
| `Challenge/Statement.lean` | the five statements, Mathlib only, without proofs |

## Licence

Apache License 2.0, see `LICENSE`.
