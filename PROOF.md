# The proof (paper text)

This is the proof of the full original statement (families). The Lean files in `KPFull/` formalize Sections 1 to 3.
Sections 4 to 6 have further results that are NOT formalized. GPT-6.2 Astra (OpenAI) wrote this text. Claude (Anthropic) checked Sections 1 to 5 line
by line, independently, with exact computer checks over the fields with 2 and 3 elements; it found no gap.

Map to the Lean files:

| Section | Content | Lean |
|---|---|---|
| 1 | a common measure; invariant near-minimizers (the levels lemma) | `KPFull/Families.lean`, `KPFamLat.exists_fixed_of_levels` |
| 2 | one-sided bounds `r` and `r(r+1)` for every member | `KPFamLat.first_order`, `KPFamilies.kp_family_one_sided` (S1) |
| 3 | finite sums of finite intersections, bound `r K_r` | `KPFull/PartB.lean`, `KPFull/FinalS2.lean` (S2', S2, S4) |
| 3, end | total error `2r - 1 + r(1 + floor(log2 2r))` with the prescribed form, formula (4) | paper only |
| 4 | an invariant subspace with total error at most `3r` for every member | paper only |
| 5 | a finite example: the constant `2` in the total error for families is false (ratio `2 + 2/17475`) | paper only |
| 6 | sharpness remarks (the one-sided order `r^2` is necessary) | paper only |

Notation: `d(A,B) = dim A/(A ∩ B)`, `δ(A,B) = d(A,B) + d(B,A)`, `[S:T] = d(S,T) - d(T,S)` (relative index of
commensurable subspaces).

Two points of exposition that the reader check added (they are not gaps): in Section 1, `h` maps the lattice `L` onto
itself and preserves `d`, so `a_{hμ,t} = a_{μ,t}` (`hμ` is the push-forward of `μ` on the set `X`); and the singleton
level set gives the UNIQUE exact minimizer, because `f_{μ,t}` takes values in a discrete set when `μ` has finite support.

---

The polynomial conjecture in the full form of Theorem A holds for arbitrary families, arbitrary groups, and arbitrary dimension. The optimal constant for canonical total distance is a separate question. I obtain bounds on that constant and a finite counterexample to $C=2$.

Let $r\ge1$ be an integer. In the table, each $W$ is fixed by every linear or semilinear bijection preserving the family, and each bound holds for **every** $x$.

| Choice of $W$ | Bounds |
|---|---|
| Arbitrary subspace | $d(W,A_x)\le r,\quad d(A_x,W)\le r(r+1)$ |
| Finite sum of finite intersections | $d(W,A_x)\le r,\quad d(A_x,W)\le r\displaystyle\sum_{j=1}^{r}\left\lceil\frac{r+1}{j}\right\rceil$ |
| Arbitrary subspace, optimized for total distance | $\delta(A_x,W)\le 3r$ |

The middle bound is $O(r^2\log(r+1))$. In particular, $r^2(r+1)$ is an explicit polynomial replacement for $r(r+1)^{r+1}$ in Theorem A, including its prescribed form of $W$.

For the best universal constant in the third row, I prove
$$
\boxed{\quad 2+\frac{2}{17475}\ \le\ C_{\rm can}\ \le\ 3.\quad}
$$
I do not determine its exact value. The lower bound holds for a finite linear group, a finite family of equal-dimensional subspaces, and a finite-dimensional complex vector space. Thus the proposed minimax argument cannot give the suggested uniform $2r$ conclusion. Without the canonicity requirement, the best universal coefficient is exactly $2$.

## 1. A common measure and nested invariant subspaces

Write $H$ for the full semilinear symmetry group of the family. Assume $X\ne\varnothing$ and fix $A_*\in X$. Work in the lattice $\mathcal L$ of subspaces commensurable with $A_*$. For a finitely supported probability measure $\mu$ on $X$, put
$$
f_{\mu,t}(S)=\mathbb E_\mu\bigl[d(A_y,S)+t[S:A_y]\bigr],
\qquad
a_{\mu,t}=\inf_{S\in\mathcal L}f_{\mu,t}(S).
$$
The integrand is $c_t(A_y,S)$. In particular $0\le a_{\mu,t}\le r$, by testing $S=A_*$.

We need a version of the levels argument that supplies several invariant subspaces for the **same** measure.

**Lemma.** Let $I_1,\ldots,I_m$ be disjoint closed intervals of positive length in $(0,1)$, in increasing order. For every $\tau>0$ there exist a finitely supported $\mu$, levels $t_j\in I_j$, and $H$-invariant subspaces
$$
S_1\supseteq S_2\supseteq\cdots\supseteq S_m
$$
such that $f_{\mu,t_j}(S_j)\le a_{\mu,t_j}+\tau$.

**Proof.** Two lattice identities will be used. First, $f_{\mu,t}$ is submodular. Indeed, the relative index is modular, and
$$
(A\cap S)+(A\cap T)\subseteq A\cap(S+T)
$$
gives submodularity of $S\mapsto d(A,S)$ by the dimension formula. Second, for $u>t$,
$$
\bigl(f_{\mu,u}(S)-f_{\mu,u}(T)\bigr)
-\bigl(f_{\mu,t}(S)-f_{\mu,t}(T)\bigr)=(u-t)[S:T].
$$
These identities also hold in infinite dimension. For the finitely many commensurable subspaces in an identity, quotienting their sum by their common intersection reduces the calculation to finite dimension.

Put $q=\min_{t\in\cup I_j}\min(t,1-t)>0$. If $f_{\mu,t}(S)\le r+1$, some point of the support satisfies $\delta(S,A_y)\le(r+1)/q$. The triangle inequality gives
$$
|[S:A_*]|\le\delta(S,A_*)\le D:=2r+(r+1)/q.
$$
Here the directed triangle inequality follows by passing from $A$ to $A\cap B$ and then to $A\cap B\cap C$.

Choose more than $2D$ distinct test levels in each interval. Let $\gamma>0$ be the minimum spacing of all test levels. Choose $\varepsilon>0$ with $16\varepsilon<\gamma$, $8\varepsilon<1$, and $4\varepsilon\le\tau$. Choose $\mu$ within $\varepsilon$ of maximizing the sum of the $a_{\mu,t}$ over all test levels. At each such level put
$$
N_t=\{S:f_{\mu,t}(S)\le a_{\mu,t}+4\varepsilon\}.
$$

For every $h\in H$, $N_t\cap hN_t\ne\varnothing$. To see this, set $\nu=(\mu+h\mu)/2$. Concavity in the measure and equivariance give $a_{\nu,u}\ge a_{\mu,u}$ at every test level $u$. Their sum can increase by at most $\varepsilon$, so $a_{\nu,t}\le a_{\mu,t}+\varepsilon$. Choose $S$ with $f_{\nu,t}(S)\le a_{\mu,t}+2\varepsilon$. The two summands whose average gives $f_{\nu,t}(S)$ are each at least $a_{\mu,t}$. Each is therefore at most $a_{\mu,t}+4\varepsilon$, as required.

There is also an ordering property. Suppose $t<u$, $P$ is an $8\varepsilon$-minimizer at $t$, and $Q$ is an $8\varepsilon$-minimizer at $u$. Write $f_t=f_{\mu,t}$. The change-of-level identity and submodularity give
$$
\begin{aligned}
(u-t)d(Q,P)-8\varepsilon
&\le f_t(P\cap Q)-f_t(Q)\\
&\le f_t(P)-f_t(P+Q)\le8\varepsilon.
\end{aligned}
$$
Since $d(Q,P)$ is an integer and $16\varepsilon<\gamma$, it follows that $Q\subseteq P$.

If every $N_t$ in one interval contained two distinct members, their intersection $P_t$ and sum $Q_t$ would both be $8\varepsilon$-minimizers by submodularity. We would have $P_t\subsetneq Q_t$, with these nontrivial intervals ordered disjointly by the ordering property. Their relative heights all lie in $[-D,D]$, whereas each nontrivial interval consumes at least one unit of height. This contradicts the number of test levels in that interval.

Thus each $I_j$ contains a level where $N_t$ is a singleton. Its member is fixed by $H$, since $N_t\cap hN_t\ne\varnothing$ for every $h$. The ordering property gives the asserted chain. $\square$

## 2. Uniform one-sided bounds

Let $W$ be a $\tau$-minimizer at level $t$ supplied by the lemma, and let $\pi:V\to V/W$. Comparing $W$ with larger and smaller subspaces gives
$$
\begin{aligned}
\mathbb E_\mu\dim(\pi A_y\cap E)&\le t\dim E+\tau
&&\text{for finite-dimensional }E\subset V/W,\\
\mathbb E_\mu d(A_y\cap W,R)&\ge t\dim(W/R)-\tau
&&\text{for finite-codimensional }R\subset W .
\end{aligned} \tag{1}
$$
Indeed, use $\pi^{-1}E$ and $R$ as competitors. Upon enlarging $W$, the decrease of $d(A_y,W)$ is exactly $\dim(\pi A_y\cap E)$. Upon shrinking $W$ to $R$, its increase is exactly $d(A_y\cap W,R)$.

Fix **any** $x$. Use $E=\pi A_x$ in the first inequality. The image of $A_x\cap A_y$ has codimension at most $d(A_x,A_y)\le r$ in $E$. Use $R=W\cap A_x$ in the second inequality. Then $d(A_y\cap W,R)\le d(A_y,A_x)\le r$. Consequently
$$
(1-t)d(A_x,W)\le r+\tau,\qquad
t\,d(W,A_x)\le r+\tau. \tag{2}
$$
This is the step that turns an average into bounds for every member. It uses $A_x$ as a lattice competitor and needs no lower bound on its mass under $\mu$.

Set $t_0=r/(r+1)$ and $B=r(r+1)$. Choose a small closed interval immediately above $t_0$, then choose $\tau>0$ sufficiently small that throughout the interval
$$
\frac{r+\tau}{t}<r+1,\qquad
\frac{r+\tau}{1-t}<B+1,\qquad
(t-t_0)B+\tau<\frac1{r+1}. \tag{3}
$$
These choices exist by first taking the interval sufficiently close to $t_0$ with its lower endpoint strictly above $t_0$. The lemma and integrality in (2) give
$$
d(W,A_x)\le r,\qquad d(A_x,W)\le r(r+1)
\quad\text{for all }x.
$$

For a finite family of $n$ distinct members there is a slight improvement. Use its uniform measure and $t=t_0$. The objective has discrete values, and its minimizers are closed under intersections. Their relative heights are bounded below by the same cost bound used in the lemma. A minimizer of least relative height is therefore the least minimizer and is fixed by $H$. In the comparisons proving (2), the directed pairwise error averages are now at most $r(1-1/n)$, because the term $y=x$ vanishes. Thus
$$
d(W,A_x)\le r,\qquad
d(A_x,W)\le \left\lfloor r(r+1)(1-1/n)\right\rfloor .
$$

## 3. Finite sums of finite intersections

Keep $W,\mu,t,\tau$ from (3). Define $D$ to be the sum of all finite nonempty intersections of family members which are contained in $W$. This definition is invariant under $H$.

Fix $x$ and start with $L=A_x$. If $n=\dim\pi L>0$, apply (1) to $E=\pi L$. Some $y$ in the support satisfies
$$
\dim(\pi L\cap\pi A_y)\le tn+\tau.
$$
We have $n\le B$. By (3) and the denominator $r+1$ of $t_0$, this integer is at most $\lfloor rn/(r+1)\rfloor$. Replacing $L$ by $L\cap A_y$ therefore reduces $\dim\pi L$ by at least
$$
\left\lceil\frac{n}{r+1}\right\rceil.
$$
Each replacement costs at most $r$ dimensions inside $L$, because $L\subset A_x$.

While $(j-1)(r+1)<n\le j(r+1)$, each step reduces $n$ by at least $j$. There are at most $\lceil(r+1)/j\rceil$ steps in that band. Since $n\le r(r+1)$, after at most
$$
K_r=\sum_{j=1}^r\left\lceil\frac{r+1}{j}\right\rceil
$$
steps we have a finite intersection $L_x\subseteq W\cap A_x$ with $\dim(A_x/L_x)\le rK_r$. It follows that
$$
d(D,A_x)\le d(W,A_x)\le r,\qquad d(A_x,D)\le rK_r.
$$

The sum defining $D$ is a **finite** sum. Fix one $x$. The quotient $W/L_x$ is finite-dimensional, since $d(W,A_x)\le r$ and $\dim(A_x/L_x)\le rK_r$. The images of the eligible intersections span $D/L_x$, so finitely many span it. Adding $L_x$ itself gives the required finite expression.

Finally, $K_r\le(r+1)H_r+r$, where $H_r=\sum_{j=1}^r1/j$, and also $K_r\le r(r+1)$. This proves both the logarithmically sharper estimate and the stated cubic polynomial.

The same construction gives a separate total-distance estimate **with** the prescribed form. Choose $t$ just above $1/2$ and $\tau$ small enough that (2) gives $d(W,A_x)\le2r-1,\ d(A_x,W)\le2r$, and $(t-\tfrac12)2r+\tau<\tfrac12$. The projected dimension then falls from $n$ to at most $\lfloor n/2\rfloor$ at each step. Hence a finite sum of finite intersections satisfies
$$
\delta(D,A_x)\le 2r-1+r\bigl(1+\lfloor\log_2(2r)\rfloor\bigr)
\quad\text{for every }x. \tag{4}
$$

There is a reason to do the conversion. Even a **unique** weighted minimizer can fail to have the prescribed form. Let $V=U\oplus k^3$, with $\dim U=2$, take three distinct lines $L_i\subset U$, and put $A_i=L_i\oplus ke_i$. Use equal weights and $1/3<t<1/2$. For any $S$, put $J=S\cap U$ and let $E$ be its projection to $k^3$. Then
$$
\frac13\sum_i\dim(A_i\cap S)\le \tfrac12\dim J+\tfrac13\dim E.
$$
Indeed, a line $J$ equals at most one $L_i$, the assertion for $J=0,U$ follows by counting, and $E$ contains at most $\dim E$ coordinate lines. Subtracting $t\dim S$ shows the unique maximum is attained at $S=U$, since the coefficient of $\dim J$ is positive and that of $\dim E$ is negative, with equality at $U$. This is precisely the unique minimizer of $f_{\mu,t}$. All pairwise intersections of the $A_i$ are zero, and none of the $A_i$ is contained in $U$. Thus no sum of finite intersections equals $U$.

## 4. A canonical center of total radius $3r$

Fix $m$, choose $0<\xi<1/2$, and use the lemma in small intervals about $j/(m+1)$. We get a common $\mu$ and invariant $S_1\supseteq\cdots\supseteq S_m$ with errors $\tau$ and
$$
\left|t_j-\frac{j}{m+1}\right|\le\frac{\xi}{m+1}.
$$
I first show that for every $x$,
$$
\frac1m\sum_{j=1}^m\delta(A_x,S_j)
\le \frac{2(m+1)}m\,\frac{r+m\tau}{1-\xi}. \tag{5}
$$

Append $S_0=V$ and $S_{m+1}=0$. On $S_i/S_{i+1}$, denote the induced image of $A_x\cap S_i$ by $X_i$, and the corresponding image for $A_y$ by $Y_i$. The filtration gives
$$
d(A_x,A_y)\ge\sum_{i=0}^m d(X_i,Y_i).
$$
Indeed, the induced image of $A_x\cap A_y$ on each piece is contained in $X_i\cap Y_i$, and the dimensions of the graded pieces of $A_x/(A_x\cap A_y)$ sum to its dimension. The reversed inequality with $x,y$ exchanged holds in the same direction.

For $0\le i<m$, apply the enlargement inequality in (1) at $S_{i+1}$, using $E=X_i$. Its intersection with the image of $A_y$ in $V/S_{i+1}$ is exactly $X_i\cap Y_i$. Hence
$$
\mathbb E d(X_i,Y_i)\ge(1-t_{i+1})\dim X_i-\tau.
$$
For $1\le i\le m$, apply the shrinking inequality at $S_i$ to the inverse image of $X_i$ in $S_i$. This gives
$$
\mathbb E d(Y_i,X_i)\ge t_i\operatorname{codim}_{S_i/S_{i+1}}X_i-\tau.
$$
Every dimension multiplied by a coefficient in these formulas is finite, including on the two end pieces.

Now $1-t_{i+1}\ge (1-\xi)(m-i)/(m+1)$ and $t_i\ge(1-\xi)i/(m+1)$. Also
$$
\begin{aligned}
\sum_{i=0}^{m-1}(m-i)\dim X_i&=\sum_{j=1}^m d(A_x,S_j),\\
\sum_{i=1}^{m}i\operatorname{codim}_{S_i/S_{i+1}} X_i
&=\sum_{j=1}^m d(S_j,A_x).
\end{aligned}
$$
Summing the two directional estimates and using the two pairwise bounds $r$ proves (5).

It remains to select one chain member for all $x$. For comparable $P\subset Q$,
$$
\delta(A_x,P)-\delta(A_x,Q)
=2\dim\frac{A_x\cap Q}{A_x\cap P}-\dim(Q/P).
$$
The middle dimension can differ by at most $r$ between any two family members. Indeed, the image of $A_x\cap A_y\cap Q$ in $Q/P$ has codimension at most $d(A_x,A_y)$ in the image for $x$, and the reverse bound holds for $y$. Thus the difference of the two distance costs has oscillation at most $2r$ over $x$.

Write $c_{ij}=\delta(A_{x_i},S_j)$, where $x_i$ maximizes the distance to $S_i$. Such a maximum exists because the distances are bounded integers. For $i\ne j$ the oscillation estimate says
$$
(c_{ii}-c_{ij})+(c_{jj}-c_{ji})\le2r.
$$
Sum over unordered pairs. It follows that
$$
\min_i\sup_x\delta(A_x,S_i)
\le \frac1m\sum_i c_{ii}
\le \sup_x\frac1m\sum_j\delta(A_x,S_j)+r(1-1/m).
$$
Together with (5), the right side can be made arbitrarily close to $3r$ by first taking $m$ large and then $\xi,\tau$ small. Taking it below $3r+1$ proves the integer bound $3r$.

## 5. A finite counterexample to canonical radius $2r$

The example has four coordinate blocks. Its symmetries force an invariant subspace to include or omit each whole block. For each of those choices we construct a family member at distance exactly half the ambient dimension, while all directed pairwise distances are strictly below one quarter of that dimension.

**Four density vectors indexed by block position.** Put $n_i=16^i$ for $0\le i\le3$, and $L=\sum_i n_i=4369$. For every sign choice $w\in\{-1,1\}^4$, split the four indices into its sign classes. In each nonempty class $J$, with largest index $j$, define
$$
v_i^w=1\quad(i\in J,\ i<j),\qquad
v_j^w=-\sum_{\substack{i\in J\\i<j}}4^{i-j}.
$$
Set $s_i^w=4^{-i}v_i^w$ and $p_i^w=(1+s_i^w)/2$. These are valid densities. On each sign class,
$$
\sum_{i\in J}n_i s_i^w=\sum_{i\in J}4^i v_i^w=0. \tag{6}
$$
For every pair $w,z$,
$$
\sum_i n_i s_i^w s_i^z=\sum_i v_i^w v_i^z\ge\tfrac13. \tag{7}
$$
To verify this, index $3$ is exceptional in both vectors, and each has at most one further exceptional index. Thus at least one coordinate contributes $1$. At most two coordinates contribute negatively, each by at most $1/3$, since every exceptional value lies in $[-1/3,0]$.

**Realizing the densities with control of every translate.** Let $q=8192$, $\Omega=\mathbb F_q^3\times\mathbb F_q^3$, and $M=|\Omega|=q^6$. Define
$$
F(u,v)=
\begin{cases}
u\cdot v,&u\ne0,\\
v_1,&u=0.
\end{cases}
$$
It is exactly uniform, by conditioning on $u$. For a nonzero translation $h=(a,b)$, the probability of any rectangle event for $(F(z),F(z+h))$ differs from its probability for two independent uniform field elements by at most $2/q^2$. If $a\ne0$, condition on $u\notin\langle a\rangle$. The two linear forms in $v$ are independent there, and the exceptional probability is $q^{-2}$. If $a=0,\ b\ne0$, first use the unmodified dot product and condition on $v\notin\langle b\rangle$. The same argument applies in $u$, and modifying the value at $u=0$ costs at most another $q^{-3}$.

Fix an order on $\mathbb F_q$. For every density $p$ used above, let $T_p$ be the initial segment of size $pq$, an integer because all denominators divide $8192$. At translation zero these sets are nested, so the directed difference probability is $\max(p-p',0)\le p(1-p')$. Consequently, for **every** translation $h$,
$$
\Pr\{F(z)\in T_p,\ F(z+h)\notin T_{p'}\}
\le p(1-p')+2/q^2. \tag{8}
$$

Take the complex coordinate space on four blocks $\Omega\times\{1,\ldots,n_i\}$. For each $w$ and each choice of translations $h_i\in\Omega$, include the coordinate subspace supported, in block $i$, where $F(z+h_i)\in T_{p_i^w}$.

For any two members $A,B$ of types $w,z$, (6)–(8) give
$$
\begin{aligned}
M^{-1}d(A,B)
&\le\sum_i n_i p_i^w(1-p_i^z)+2L/q^2\\
&=\tfrac14\left(L-\sum_i n_i s_i^w s_i^z\right)+2L/q^2\\
&\le L/4-1/12+2L/q^2<L/4-1/16 .
\end{aligned}
$$
Thus the hypothesis holds with the explicit integer $r=M(4L-1)/16$.

The family is preserved by independent coordinate sign changes, blockwise translations of $\Omega$, and permutations of the copy labels in each block. These generate a finite group. Invariance under the sign change at coordinate $j$ implies invariance under the coordinate projection $(1-D_j)/2$. Hence an invariant subspace is a coordinate subspace. Transitivity within each block makes it a union of whole blocks.

Given any such $W$, choose $w_i=1$ exactly on its included blocks. For a member of type $w$, (6) gives
$$
\delta(A,W)=\frac M2\left(L-\sum_i n_i w_i s_i^w\right)=ML/2.
$$
Every member has dimension $ML/2$, so $W=0$ attains this radius. The canonical radius is therefore exactly $ML/2$, and its ratio to the displayed $r$ is
$$
\frac{8L}{4L-1}=2+\frac2{17475}.
$$

This also disproves the proposed weighted conclusion throughout a sufficiently small interval around $1/2$, for sufficiently small $\varepsilon$, since $c_t(A,W)\ge(\tfrac12-|t-\tfrac12|)\delta(A,W)$.

The failure of the proposed uniqueness inference can already be seen in dimension one. For $X=\{0,k\}$, give $k$ mass $p$. Then $a_{\mu,t}=\min\{(1-t)p,t(1-p)\}$. At every interior level its unique maximizing measure has $p=t$, and both subspaces minimize. Maximizing a sum over levels supplies the invariance lemma in Section 1, but does not supply individual first-order optimality at the level where a minimizer becomes unique.

## 6. Sharpness and the status of the conjecture

**The one-sided bound requires quadratic growth.** For a prime power $q$, take the complex coordinate space on the $q^2+q+1$ points of the projective plane over $\mathbb F_q$. Take the coordinate subspaces supported off individual lines. Each has dimension $q^2$ and codimension $q+1$. Two distinct lines have $q+1$ points each and meet in one point, so their complements have directed difference $q$. Coordinate sign changes and the point-transitive projective linear group preserve the family. As in Section 5, their only invariant subspaces are $0,V$. The condition $d(W,A_x)\le q$ excludes $V$, and $W=0$ gives $d(A_x,W)=q^2$. In particular, if one asks for the **same** $W$ to satisfy the one-sided condition and a linear total-distance bound, no finite universal coefficient exists.

**The ordinary Jung coefficient is $2$.** Any family member is a center of radius at most $2r$. For sharpness, take the complex coordinate space on the nonzero vectors of $\mathbb F_2^k$, and the coordinate supports $\{\lambda=1\}$ for all nonzero linear forms $\lambda$. With $r=2^{k-2}$, each support has size $2r$, the ambient size is $4r-1$, and two distinct forms give directed difference $r$ by their linear independence. The average total-distance objective has a least minimizer by submodularity and minimum dimension. That minimizer is invariant under all coordinate sign changes and under $\mathrm{GL}_k(\mathbb F_2)$, hence equals $0$ or $V$. The minimum average is therefore $2r-1$. Every subspace has maximum distance at least its average, so even unrestricted centers require $2r-1$ for this sequence.

**What is settled.** The polynomial replacement in Kazhdan–Polishchuk Theorem A, with the finite-sum-of-finite-intersections requirement, holds in arbitrary dimension for every group. Its proposed linear improvement under the original one-sided condition is false already for finite groups. Without the expression requirement, the quadratic order is optimal. With the expression requirement, the bounds here leave a gap between $r^2$ and $O(r^2\log(r+1))$. For canonical total distance, the exact coefficient remains unresolved here, as does a linear total bound with the prescribed expression.

The delicate step in the uniform proof is obtaining actual invariant subspaces from near-minimizers in unbounded dimension. The bounded interval of **integer relative heights** is what makes that step work. The loss in the finite-expression proof comes from charging up to $r$ dimensions for every reduction of the projected intersection. The loss in the $3r$ proof is the additive $r$ spent selecting a single chain member from the averaged estimate (5). The counterexample shows that some loss in such a selection is unavoidable.
