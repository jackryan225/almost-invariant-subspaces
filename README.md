# Almost invariant subspaces are close to invariant subspaces, in Lean 4

**Machine-checked proofs of Theorem A of Kazhdan and Polishchuk in its original form, for every group and every dimension,
with the bound `r (r+1)^(r+1)` replaced by `r^2 (r+1)`, and of the single-orbit case with a linear bound.**
Published on 25 November 2026 (preprint, not yet peer reviewed). All main theorems below are machine-checked in Lean 4 with Mathlib (CI passing; standard axioms only).

Designed and directed by Jack Ryan, who built the multi-agent research and formal-verification harness, selected the problem, orchestrated proof search and adversarial review, and audited the Lean formalization, in collaboration with Claude (by Anthropic), GPT-6.2 Astra (by OpenAI), and Gemini 4 Neon (by Google).

## The full original statement (families, sums of intersections, polynomial bound)

### Terms

- `K` is a division ring. Every field is a division ring. `V` is a vector space over `K`. Its dimension can be infinite.
- For two subspaces `A` and `B` of `V`, put `d(A, B) = dim A/(A ∩ B)`. This number measures the part of `A` that is
  outside `B`. In general `d(A, B)` and `d(B, A)` are different. The *total error* is `δ(A, B) = d(A, B) + d(B, A)`.
- A group `G` *acts linearly* on `V`: each element `g` is an invertible linear map of `V`, and `(gh)v = g(hv)`.
- A *family* is a set `X` on which `G` acts, with a subspace `A_x` of `V` for each `x` in `X`, such that `A_{gx} = g A_x`.
  The members `A_x` are the subspaces of the family. A family can have several orbits. A collection of subspaces that `G`
  maps to itself is a family (take `X` = the collection). The single-orbit case below is the family of all `gA`.
- A subspace `W` is *invariant* if `gW = W` for every `g` in `G`.
- A *finite sum of finite intersections of members* is a subspace `∑_{s ∈ S} ⋂_{x ∈ s} A_x`, where `S` is a finite
  nonempty set of finite nonempty subsets of `X`.
- `K_r = ∑_{j=1}^{r} ⌈(r+1)/j⌉`. Then `K_r ≤ r (r+1)`. Also `K_r ≤ (r+1)(1 + 1/2 + ... + 1/r) + r`, so `K_r = O(r log r)`.

### Theorem A and the conjecture

D. Kazhdan and A. Polishchuk, *Almost invariant subspaces and operators*, arXiv 2107.08085 (one version, July 2021),
Pure Appl. Math. Q. 19 (2023), 1975-1983. Their Theorem A says the following (restated in the terms above).

**Theorem A.** Let a group `G` act linearly on a vector space `V` over a field. Let `(A_x)` be a family with
`d(A_x, A_y) ≤ r` for all `x` and `y` in `X`, where `r ≥ 1` is an integer. Then there is an invariant subspace `W` that is a
finite sum of finite intersections of members, such that

    d(W, A_x) ≤ r     and     d(A_x, W) ≤ r (r+1)^(r+1)     for every x.

There is no condition on the group or on the dimension. Their theorem gives an explicit bound for a theorem of F. Wagner. After stating Theorem A, they wrote: "We conjecture that it should be possible to improve the bound `r (r + 1)^(r + 1)` to a polynomial (possibly linear) function of `r`, at least in the case when `G` is finite."

### What is proved in Lean

`Challenge/StatementFull.lean` imports Mathlib only and uses no definition of ours. It states five theorems, with `sorry`
in place of each proof. Each statement has a proved twin in the folder `KPFull/`.

- `Check/SameStatementFull.lean` checks that each statement and its proved twin have the same type, as terms.
- `Check/AxiomsFull.lean` prints the axioms of each proved theorem. For each one the output is `propext`,
  `Classical.choice` and `Quot.sound`, the three standard axioms of Lean and Mathlib.

| Statement in `Challenge/StatementFull.lean` | Proved theorem | Content |
|---|---|---|
| `KPFull.kp_family_one_sided` (S1) | `KPFamilies.kp_family_one_sided` | There is an invariant `W` with `d(W, A_x) ≤ r` and `d(A_x, W) ≤ r (r+1)` for every `x`. |
| `KPFull.kp_family_finite_form` (S2) | `KPFullFinal.kp_family_finite_form` | As S1, and `W` is a finite sum of finite intersections of members. The bounds are `r` and `r^2 (r+1)`. This is Theorem A with `r^2 (r+1)` in place of `r (r+1)^(r+1)`. |
| `KPFull.kp_family_finite_form_sharp` (S2') | `KPFullFinal.kp_family_finite_form_sharp` | As S2 with the bound `r K_r`. |
| `KPFull.kp_single_orbit` (S3) | `KPFamilies.kp_single_orbit` | One orbit: the family of all `gA`. If `d(A, gA) ≤ r` for every `g`, there is an invariant `W` with `d(W, A) ≤ r` and `d(A, W) ≤ r (r+1)`. |
| `KPFull.kp_family_canonical` (S4) | `KPFullFinal.kp_family_canonical` | No group is given. There is a finite sum of finite intersections of members `W` with the bounds `r` and `r K_r`, and every order automorphism of the lattice of subspaces that permutes the members maps `W` to itself. |

The conditions in all five statements:

- `K` is any division ring, `G` is any group and `X` is any set with an action of `G`. Nothing is finite.
- `V` can have infinite dimension. Each dimension is `Module.rank`, a cardinal number.
- `r ≥ 0` is an integer.
- S2, S2' and S4 assume that `X` is not empty. For an empty `X` the statement of Theorem A is degenerate.

S4 contains S2'. A linear or semilinear bijection of `V` that permutes the members gives such a lattice automorphism.
So S4 also applies to semilinear actions, for example to a Galois group that acts on `V_0 ⊗_k E`.

More Lean theorems. They have no twin in the challenge file.

- `KPFamilies.kp_family_one_sided_module`: S1 for submodules of a module over any ring, with the length of a module in
  place of the dimension.
- `KPFamilies.kp_family_lattice`: the same for a group that acts by order automorphisms of the lattice of submodules.
- `KPFullFinal.kp_family_finite_form_lattice`: S2' for modules over any ring and a group of lattice automorphisms.
- `KPFull.PartB.partB`: the step from a subspace `W` with the two bounds of S1 and the descent property of `PROOF.md`,
  Section 3, to a finite sum of finite intersections of members, for modules over any ring.
- `KPContains.almost_invariant_one_sided` (in `Check/Contains.lean`): the statement `almost_invariant_one_sided` of
  `Challenge/Statement.lean` (statement 2 of the single-orbit case below), derived from S3. S3 has no condition on the
  dimension and no condition on the group.

### Remarks on paper (not in Lean)

These results are not theorems of the Lean files. `REMARKS.md` has each statement, its proof or a reference to it, and
the list of checks. "Paper proof" means a proof written by one model and read line by line by at least one other agent.

- **B1. The one-sided bound needs order `r^2`.** For each prime power `q` there is a finite group and one orbit of
  subspaces of a complex coordinate space with `r = q`, such that every invariant `W` with `d(W, A) ≤ r` has
  `d(A, W) = r^2`. The example uses the lines of the projective plane over the field with `q` elements. Paper proof,
  read by a second agent; exact check for `q = 2`.
- **B2. Total error `2r − 1` for one orbit.** For `r = 2^(k−2)` there is one orbit of `GL_k(F_2)` where every subspace has
  total error at least `2r − 1` to some member. So statement 1 of the single-orbit case is optimal. Paper proof, read by
  two agents.
- **B3. Total error for families.** Some invariant `W` has `δ(A_x, W) ≤ 3r` for every `x`. The constant 3 cannot be
  replaced by 2. Paper proof of `3r`, read line by line by a second agent. Two finite examples have the ratio
  `2 + 2/17475` (paper, read line by line) and `2.021` (exact integer computation, two independent programs).
- **B4. Total error with the form of Theorem A.** For some single orbits of finite groups, every invariant finite sum of
  finite intersections of members has total error at least `c r log r / log log r` from some member, with a constant
  `c > 0`. Paper proof, two blind checks by two other models, exact checks for small cases. In the other direction, for every
  family there is an invariant finite sum of finite intersections with total error at most
  `2r − 1 + r (1 + ⌊log₂ 2r⌋)` from every member. Paper proof, read line by line by a second agent. For one orbit of a
  finite group the best bound is of order `r log r / log log r`: the upper bound `(1 + o(1)) r log r / log log r` is a
  paper proof by GPT-6.2 Astra, read by a Claude agent and confirmed by a blind check of Gemini 4 Neon.
- **B5. The minimizer of the proof need not have the form of Theorem A.** For three members in `k^5` and also for an orbit
  of the Klein four group in `k^7`, the minimizer is not a finite sum of finite intersections of members. This is why
  the proof of S2 passes from `W` to a smaller subspace. Paper proof and exact computation over small fields.

### Relation to the paper of Kazhdan and Polishchuk, clause by clause

`FIDELITY.md` has the full comparison. In short, for Theorem A:

| Clause of Theorem A | Here | Comparison |
|---|---|---|
| a vector space over a field | a vector space over a division ring | more general |
| no condition on the dimension | no condition on the dimension | same |
| a collection of subspaces that `G` preserves | a `G`-set `X` and `A : X → Submodule K V` with `A(gx) = g A_x` | equivalent |
| any group, acting linearly | any group, a homomorphism `G → (V ≃ₗ[K] V)` | same |
| `r ≥ 1` | `r ≥ 0` | more general |
| `d(A_x, A_y) ≤ r` for all `x`, `y` | the same | same |
| `W` is invariant | the same | same |
| `W` is a finite sum of finite intersections of members | S2, S2', S4: the same, with at least one summand and no empty intersection; S1 and S3 do not ask for it | same in S2, S2', S4 |
| `d(W, A_x) ≤ r` | the same, for every `x` | same |
| `d(A_x, W) ≤ r (r+1)^(r+1)` | S2: `r^2 (r+1)`; S2' and S4: `r K_r`; S1 and S3: `r (r+1)` | smaller bound |

The conjecture after Theorem A has two parts.

- *Polynomial.* This part holds, for every group and not only for finite groups, in the exact form of Theorem A: S2 gives
  `r^2 (r+1)`, and S2' gives `O(r^2 log r)`.
- *Possibly linear.* This part is false in the one-sided form of Theorem A, already for finite groups and one orbit:
  by B1, the second bound must be at least `r^2` for infinitely many `r`. S1 shows that `r (r+1)` is enough when `W` can be
  any invariant subspace. With the form of Theorem A, the second bound lies between `r^2` and `r K_r`.

For the total error `δ`, linear bounds exist when `W` can be any invariant subspace: `δ < 2r` for one orbit of a finite
group (statement 1 below) and `δ ≤ 3r` for families (B3). With the form of Theorem A, B4 shows that no linear bound for
`δ` exists.

**A misprint in Lemma 2.1.** The paper prints the hypothesis of Lemma 2.1 (almost invariant operators) as
`rk(gTg^{-1} − g) ≤ r`. The proof uses `rk(gTg^{-1} − T) ≤ r`. Lemma 2.1 is not formalized in this repository.

### How the proof works

`PROOF.md` has the proof in prose. Here is an outline.

1. Fix one member `A_*`. All members and all subspaces below are commensurable with `A_*`: both `d(S, A_*)` and
   `d(A_*, S)` are finite. For a probability measure `μ` with finite support on `X` and a level `t` with `0 < t < 1`, put
   `f(S) = E_μ [ d(A_y, S) + t (d(S, A_y) − d(A_y, S)) ]`. This function is submodular:
   `f(S ∩ T) + f(S + T) ≤ f(S) + f(T)`.
2. Choose `μ` such that the sum of the minimum values of `f` over many levels is nearly as large as possible. Then at some
   level `t` just above `r/(r+1)` there is only one near-minimizer `W`. Because the group permutes the members, the
   group also permutes the near-minimizers. So `W` is invariant.
3. Compare `f(W)` with `f(W + A_x)` and with `f(W ∩ A_x)`. This gives `(1 − t) d(A_x, W) ≤ r + τ` and
   `t d(W, A_x) ≤ r + τ` with a small `τ`, for every member `A_x`, also when `x` is outside the support of `μ`.
   With `t` just above `r/(r+1)` this gives `d(W, A_x) ≤ r` and `d(A_x, W) ≤ r (r+1)`. This is S1.
4. For S2, start with `L = A_x`. The first comparison of step 3 gives a member `A_y` such that the part of `L ∩ A_y`
   outside `W` is at most `r/(r+1)` times the part of `L` outside `W`. Replace `L` by `L ∩ A_y` and repeat. After at most
   `K_r` steps `L` lies in `W`, and each step removed at most `r` dimensions from `L`. The sum `D` of all finite
   intersections of members inside `W` is invariant, it is a finite sum, `d(D, A_x) ≤ r` and `d(A_x, D) ≤ r K_r`.

## The single-orbit case and the Section 3 question (all in Lean)

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

### The main statement in Lean (`Challenge/Statement.lean`)

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

## The proof of the single-orbit case, in ten lines

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

## Earlier work and provenance

- F. O. Wagner, *Almost invariant families*, Bull. London Math. Soc. 30 (1998): existence of `W`, without a bound.
- D. Kazhdan, A. Polishchuk, cited above: the bound `r (r + 1)^(r + 1)`, the conjecture and the question.
- P. M. Neumann, *Permutation groups and close-knit families of sets*, Arch. Math. 67 (1996), 265-274. We know this
  paper from its review, zbMATH Zbl 0865.20004. By the review, Theorem 1.1 is about one set that each group element
  changes in at most `m` points: there is an invariant set within `2m − 1` of it, and this is best possible. This is the
  case of one orbit for sets. Theorem 3.4 has no group action: an infinite close-knit family of sets has some set within
  `2m − 1` of every member. The last section asks questions about families of subgroups and of vector subspaces. We do not
  claim an answer to these questions.
  The closing section of P. M. Neumann, Arch. Math. 67 (1996) 265-274, was available to us only through its zbMATH review.
- L. Brailovsky, D. V. Pasechnik, C. E. Praeger, Proc. Amer. Math. Soc. 123 (1995); G. M. Bergman, H. W. Lenstra,
  J. Algebra 127 (1989): the same problem for subsets of a set and for subgroups of a group. For subsets the bound is
  `2m − 1` (Neumann), the same as in statement 1.
- U. Dardano, D. Dikranjan, S. Rinauro, arXiv 1705.02954: a survey of inert subgroups. It states the theorem of Bergman
  and Lenstra with Neumann's bound `n^(n^n)`, and a version for abelian groups and groups of automorphisms.
- I. Ben Yaacov, F. O. Wagner, J. Symbolic Logic (2020), and C. Milliet, J. Algebra (2017): versions without bounds.
- M. Mastnak, M. Omladič, H. Radjavi, *Near-invariant subspaces for matrix groups are nearly invariant*,
  Linear Algebra Appl. 505 (2016), 269-281. To our knowledge this paper has the case `r = 1` for groups of matrices.
  We saw only summaries of it and did not read the full text.
- Papers on almost invariant half-spaces of operators on Banach spaces (A. I. Popov 2010; L. W. Marcoux, A. I. Popov,
  H. Radjavi 2013; A. I. Popov, A. Tcaciuc 2013; G. Sirotkin, B. Wallis 2016) study single operators and algebras of
  operators, without explicit bounds of this kind.
- N. Alon, B. Bukh, B. Sudakov, arXiv 0711.1604: universal sets. Remark B4 uses such sets.

Provenance. Single-orbit results: Claude. Full statement: GPT-6.2 Astra found the proof of the family theorem and of its
original form (the levels argument for one measure, the comparisons at the near-minimizer, and the descent to sums of
intersections); Claude agents checked that proof line by line with exact computations over `F_2` and `F_3` and formalized
it in Lean 4; Gemini 4 Neon and GPT-6.2 Astra ran blind checks of the lower bound in B4; Gemini 4 Neon ran a blind check
of the upper bound in B4 for one orbit; the examples in B3 come from GPT-6.2 Astra and a Claude agent.

We searched for an earlier proof: the papers that cite the paper of Kazhdan and Polishchuk, arXiv, zbMATH, Crossref,
OpenAlex, MathOverflow, Zenodo, GitHub (repositories, code, issues and pull requests), hexagonmath.org (full text), the
Kourovka Notebook, nilradical.ai, the Palomar registry, proofatlas.ai and vibemathed.com. We found none. A search cannot
prove that there is none. We could not read the full texts of Neumann (1996), Brailovsky, Pasechnik and Praeger (1995) and
Wagner (1998). If you know an earlier proof, please open an issue, and we will correct this page.

## What is not claimed

- A linear bound for `d(A_x, W)` in the one-sided form of Theorem A. It is false already for finite groups and one orbit (B1);
  in S1 and S3, `r (r + 1)` is optimal up to the factor `(r + 1)/r`.
- The best constants in all cases. These ranges are known:
  - `d(A_x, W)` with `W` of the form of Theorem A: at least `r^2` in some examples, at most `r K_r = O(r^2 log r)`;
  - the total error for families with any invariant `W`: at least `2.021 r` in one example, at most `3r`;
  - the total error with `W` of the form of Theorem A: at least `c r log r / log log r` in some examples, at most
    `2r − 1 + r (1 + ⌊log₂ 2r⌋) = O(r log r)` for families, and at most `(1 + o(1)) r log r / log log r` for one orbit of
    a finite group (while for one orbit of a finite group with any invariant `W`, statement 1's `< 2r` bound is optimal by B2).
- For infinite groups, the Lean proof of the total-error bound `2r` in statement 5 of `Challenge/Statement.lean` assumes `V`
  of finite dimension (whereas S1, S2, S2', S3, S4, and statement 1 have no finite-dimension restriction).
- Lemma 2.1 (operators) and Theorem B (Galois descent) of the paper. They are not formalized directly here (S1, S3, and S4
  apply to semilinear actions via lattice automorphisms).
- The remarks B1 to B5. They are paper proofs / exact finite-field checks and are not checked by Lean.

## How to check it

```
lake exe cache get      # downloads compiled Mathlib
lake build              # builds the proof files of both parts (a few minutes)
lake env lean Check/Axioms.lean          # single-orbit results: propext, Classical.choice, Quot.sound
lake env lean Check/AxiomsFull.lean      # full statement: propext, Classical.choice, Quot.sound
lake build Challenge && lake env lean Check/SameStatement.lean && lake env lean Check/SameStatementFull.lean
lake env lean Check/Contains.lean        # statement 2 of the single-orbit case, derived from S3
```

The Lean version is in `lean-toolchain` (4.34.1) and Mathlib is pinned in `lake-manifest.json`. The workflow in
`.github/workflows/check.yml` runs these steps on each push. We also replayed the compiled proofs with `leanchecker`,
the separate kernel checker that comes with Lean, and the proofs of the full statement also with `lean4lean`. The records
are in `logs/`.

| File | Content |
|---|---|
| `AlmostInvariant/Length.lean` | `d`, `δ`, the rules of the length, submodularity |
| `AlmostInvariant/Finite.lean` | the invariant smallest minimizer; statement 3 for automorphisms of the lattice of submodules |
| `AlmostInvariant/VectorSpace.lean` | statements 1 and 3 for linear actions |
| `AlmostInvariant/OneSided.lean` | statement 2, and a version for modular lattices with a rank function |
| `AlmostInvariant/Question.lean` | statement 4 |
| `AlmostInvariant/AllGroups.lean` | statement 5, and a version for modular lattices with a rank function |
| `Challenge/Statement.lean` | the five single-orbit statements, Mathlib only, without proofs |
| `KPFull/Families.lean` | S1 and its forms for modules and lattice automorphisms: the levels argument, the comparisons at the near-minimizer |
| `KPFull/PartB.lean` | from `W` to a finite sum of finite intersections, in at most `K_r` steps |
| `KPFull/FinalS2.lean` | S2, S2', S4, and the form of S2' for modules |
| `KPFull/SingleOrbit.lean` | S3, from S1 |
| `Challenge/StatementFull.lean` | the five statements of the full original statement, Mathlib only, without proofs |
| `Check/Axioms.lean`, `Check/SameStatement.lean` | the checks of the single-orbit statements |
| `Check/AxiomsFull.lean`, `Check/SameStatementFull.lean`, `Check/Contains.lean` | the checks of the full statement |
| `FIDELITY.md` | Theorem A against the Lean statements, clause by clause |
| `REMARKS.md` | the remarks B1 to B5 and their checks |
| `PROOF.md` | the proof of the full statement in prose |

## Licence

Apache License 2.0, see `LICENSE`.
