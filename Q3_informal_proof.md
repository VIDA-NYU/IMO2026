# Q3 — Informal Proof (corrected sketch)

## Problem Statement

Stick $[0,1]$, $S=A\cup B$ with $A,B\subseteq(0,1)$, $|A|,|B|\le n$,
$A\cap B=\emptyset$. Pieces are consecutive differences of
$0< s_1<\dots<s_k<1$, i.e. `pieceLengths(S)`; they sum to $1$.
`firstPlayerShare` is the sum of the 1st,3rd,5th… pieces after sorting
decreasing, and $L(A,B)$ is that share. Define

$$V(n)=\sup_{|A|\le n}\inf_{\substack{|B|\le n\\B\cap A=\emptyset}}L(A,B),\qquad
  \text{answer}(n)=2^{n}/(2^{n+1}-1).$$

Prove $V(n)=\text{answer}(n)$ for $n\ge1$, via

* `lower_bound`: $\exists A\;\forall B\;L(A,B)\ge2^{n}/(2^{n+1}-1)$,
* `upper_bound`: $\forall A\;\exists B\;L(A,B)\le2^{n}/(2^{n+1}-1)$.

Equivalently, with `altSum` $=\sum(-1)^i l_i$ on the decreasing order,
$L=(1+\text{Alt})/2$, so $L\ge\text{answer}(n)\iff\text{Alt}\ge1/(2^{n+1}-1)$
(`answer_eq_half_one_add_inv`: $\text{answer}(n)=(1+1/(2^{n+1}-1))/2$).

## 1. Preliminaries

* `pieceLengths_sum`: pieces sum to $1$; `pieceLengths_nonneg`: each $\ge0$.
* `RefinesByAtMostNCuts base k Q`: $Q$ is obtained from `base` by at most $k$
  successive cuts of a piece $s=s_1+s_2$ (`cut` constructor). This is the
  abstract model of adding marks: `pieceLengths_union_refines` shows
  `pieceLengths(A\cup B)` is a $B.\text{card}$-cut refinement of
  `pieceLengths(A)`.
* Scaling: `refines_smul D` shows refinement commutes with multiplying every
  piece by $D>0$; `mergeSort_map_smul` and `altSum_smul` show sorting and
  `altSum` commute with scaling: $\text{Alt}(D\cdot Q)=D\cdot\text{Alt}(Q)$.

## 2. Lower bound — Liu's marks

### 2.1 The marks

Set $D=2^{n+1}-1$ and for $k\in\{1,\dots,n\}$

$$\text{lowerMark}(n,k)=\frac{2^{n+1}-2^{\,n+1-k}}{D},\qquad
  \text{lowerA}(n)=\{\text{lowerMark}(n,k):1\le k\le n\}.$$

This is **not** $1-2^{n+1-k}/D$ (which would be off by $1/D$); the correct
numerator is $2^{n+1}-2^{n+1-k}$ without the $-1$. Then

$$\text{lowerMark}(n,0)=0,\quad\text{lowerMark}(n,n+1)=1,$$

and `lowerMark_strictMonoOn` gives strict increase, so
`lowerA(n).sort` is `range' 1 n` mapped by `lowerMark`.

Consecutive differences (telescoping via `zipWith_diff_map_range'`) are

$$\text{lowerMark}(k+1)-\text{lowerMark}(k)=\frac{2^{\,n-k}}{D},
  \qquad k=0,\dots,n.$$

Hence (`pieceLengths_lowerA`)

$$\text{pieceLengths}(\text{lowerA}(n))\;\text{Perm}\;
  \frac1D\cdot\text{dyadicList}(n),\quad
  \text{dyadicList}(n)=[2^{n},2^{n-1},\dots,2,1].$$

Thus the $n+1$ gaps are $2^{n}/D,\,2^{n-1}/D,\dots,1/D$ (sum $=(2^{n+1}-1)/D=1$).
For $n=2$ these are $4/7,2/7,1/7$; their **decreasing** `altSum` is
$4/7-2/7+1/7=3/7$, **not** $1/7$. The claim in the previous draft that the
unrefined gaps have `altSum` $1/D$ was false; the correct invariant after
scaling is different (see 2.2).

### 2.2 Kernel: scaled altSum $\ge1$ (sketch, not asserted)

Scale by $D$. Let $P=\text{pieceLengths}(\text{lowerA}(n)\cup B)$ and
$P_D=D\cdot P$. By `refines_smul` and `pieceLengths_lowerA`, $P_D$ is an
$n$-cut refinement of the unscaled dyadic list $[2^{n},\dots,1]$:

$$\text{dyadicList}(n) \xrightarrow{\le n\text{ cuts}} P_D.$$

**Lemma `dyadic_refinement_alt_ge_one`:** any $\le n$-cut refinement $Q$ of
$[2^{n},\dots,1]$ with $Q\ge0$ satisfies
$\text{altSum}(Q_{\text{sorted}})\ge1$.

*Proof sketch.* Induction on $n$ with defect
$\operatorname{defect}(Q)=\sum|p_1-p_2|$ over paired equal pieces (zero for
equal pairs). The dyadic list satisfies $2^{n}=2^{n-1}+\cdots+1+1$, so
cutting the largest piece $2^{n}$ into $s_1+s_2$ with $s_1+s_2=2^{n}$ either
preserves a copy of the dyadic structure on one side or creates a pair
$[x,x]$ whose contribution to $\text{Alt}$ after sorting is $0$. The
formal induction (Lemmas `defect`, `paired`, `refines_halves`) shows each
cut can reduce $\text{Alt}$ by at most the defect, and the dyadic gaps are
chosen so the defect never exceeds the initial surplus
$2^{n}-2^{n-1}+\cdots\pm1-1$. For $n=2$, base Alt $=3$ and one cut of $4$
into $a+b=4$ yields sorted Alt $=|a-b|+1\ge1$; the general step is the
same with $2^{n}$ in place of $4$. The lemma does **not** claim the base
list has Alt $1$ (it is $2^{n}-2^{n-1}+\cdots\pm1$, $3$ for $n=2$).

Consequently

$$\text{altSum}(P_{D,\text{sorted}})\ge1\Longrightarrow
  \text{altSum}(P_{\text{sorted}})=\tfrac1D\text{altSum}(P_{D,\text{sorted}})
  \ge1/D.$$

Since $L(\text{lowerA}(n),B)=(1+\text{Alt}(P_{\text{sorted}}))/2$
(`L_eq_half_one_add_alt`),

$$L(\text{lowerA}(n),B)\ge(1+1/D)/2=2^{n}/(2^{n+1}-1)=\text{answer}(n)$$

for every admissible $B$ disjoint from $\text{lowerA}(n)$. This is
`lower_bound`.

## 3. Upper bound — Xiang's response

Fix $A$ with $k=|A|\le n$, `base = pieceLengths(A)` ($k+1$ pieces).
Xiang must produce $Q$ refining `base` with at most $n$ cuts and
$\text{Alt}(Q_{\text{sorted}})\le1/(2^{k+1}-1)$ (or $\le0$ when $k<n$), then
`upper_bound_from_altSum_le` turns $Q$ into a concrete $B$.

The construction is not a naive greedy “split the largest piece evenly’’;
it is a pairing construction via two combinatorial lemmas.

**Lemma `exists_subset_sum_gap_le` / `exists_equal_pairs_core`:** for
`base` ($k+1$ positive pieces, $k\le n$) there are disjoint $P,N\subseteq
\{0,\dots,k\}$ with $P\neq\emptyset$, $\sigma_P=\sum_{i\in P}a_i$,
$\sigma_N=\sum_{i\in N}a_i$, $\sigma_P\ge\sigma_N$, and
$\delta:=\sigma_P-\sigma_N$ satisfying $\delta\le1/(2^{k+1}-1)$ *and*
$\delta\le a_i$ for every $i$ (pigeonhole on $2^{k+1}$ subset sums into
$2^{k+1}-1$ boxes). Moreover with at most $k$ cuts `base` refines to

$$Q = ps.\text{flatMap}[x,x]\;+\!+\;[\delta]$$

where $ps$ is a common refinement of the $P$-part and $N$-part after
removing $\delta$; each $x$ appears as an equal pair $[x,x]$. The proof
uses `exists_exact_matching` to match the $P\setminus\{i_0\}$ and $N$ parts
and `refines_halves` for the outside part $O$, with budget
$|P|+|N|-1+|O|\le k$.

Crucially the bound is **$\delta\le1/(2^{k+1}-1)$**, not $\delta=$. And
the $Q$ above is only valid as stated when $\delta>0$; if the subset-sum
construction yields $\delta=0$ (the two subsets have equal sum), the
singleton $[\delta]=[0]$ must be **removed** before realizing as cuts:
$[0]$ is not a piece length (marks must be distinct, zero-length pieces
correspond to duplicate marks). The formal proof then takes
$Q_0=ps.\text{flatMap}[x,x]$ (no $\delta$) with budget $\le k$, whose sorted
$\text{Alt}=0$. This is the “$\delta=0$’’ branch: the zero piece is dropped
and `exists_marks_realizing_refinement` is applied to $Q_0$, not to
$Q$ with a zero part.

Two cases for Xiang:

* **$k=n$ (tight):** $Q=ps.\text{flatMap}[x,x]++[\delta]$ (or $Q_0$ if
  $\delta=0$ as above) refines `base` with $\le k$ cuts and, after sorting
  decreasing, equal pairs contribute $0$ to $\text{Alt}$, so
  $\text{Alt}(Q_{\text{sorted}})=\delta$ when $\delta>0$ and $0$ when
  $\delta=0$; in either case

  $$\text{Alt}(Q_{\text{sorted}})\le1/(2^{k+1}-1).$$

  Hence via `upper_bound_from_altSum_le` there is $B$ with
  $L(A,B)\le(1+1/(2^{k+1}-1))/2=2^{k}/(2^{k+1}-1)=2^{n}/(2^{n+1}-1)$
  when $k=n$.

* **$k<n$ (slack):** $A$ uses fewer than $n$ marks. Xiang has a spare cut.
  Starting from the same $Q$ (with $\delta\le1/(2^{k+1}-1)$), split the
  leftover $\delta$ (if $\delta>0$) into $\delta/2,\delta/2$ (one extra cut,
  total $k+1\le n$). The resulting
  $Q_1=ps.\text{flatMap}[x,x]++[\delta/2,\delta/2]$ is fully paired, so its
  sorted $\text{Alt}=0$. If $\delta=0$ we already have $Q_0$ fully paired
  with $\text{Alt}=0$ using $\le k<n$ cuts, no extra split needed. In either
  subcase $L(A,B)\le(1+0)/2=1/2\le2^{n}/(2^{n+1}-1)$.

In both cases `exists_marks_realizing_refinement` converts the abstract
refinement ($Q$ or $Q_0/Q_1$ with no zero part) into a concrete Finset $B$
with $|B|\le n$, $B\cap A=\emptyset$, and `pieceLengths(A∪B)` permuting that
$Q$, so the $\text{Alt}$ bound transfers to $L(A,B)$. The $1/(2^{k+1}-1)$
bound comes from the subset-sum pigeonhole, not from a generic pigeonhole
on $2n+1$ pieces.

No pigeonhole “among $2n+1$ pieces at least $n+1$ are $\le$ average’’ is
invoked; the exponential bound comes from the dyadic pairing structure and
the $1/(2^{k+1}-1)$ calculation via `answer_eq_half_one_add_inv`, not from a
generic averaging. The previous draft’s lines 97–99 pigeonhole remark did not
imply the $2^{n}$ denominator and has been removed.

## 4. Value $V(n)$

*Lower bound* gives $\sup_A\inf_B L(A,B)\ge\text{answer}(n)$.
*Upper bound* gives for each $A$, $\inf_B L(A,B)\le\text{answer}(n)$, so
$\sup_A\inf_B L(A,B)\le\text{answer}(n)$.
Hence $V(n)=\text{answer}(n)=2^{n}/(2^{n+1}-1)$.

The geometric series that appears is not “even positions of dyadic gaps sum
to $2^{n}/(2^{n+1}-1)$’’ directly; rather

$$\text{answer}(n)=\frac{1+1/(2^{n+1}-1)}2,\quad
  \sum_{i=0}^{n}2^{n-i}=2^{n+1}-1=D,$$

so the dyadic list sums to $D$ before scaling, and after scaling by $1/D$ the
kernel’s `altSum` lower bound $1/D$ yields the answer via
$(1+\text{Alt})/2$. For $n=2$, $D=7$, base gaps $4/7,2/7,1/7$ sum to $1$,
kernel guarantees any $\le2$-cut refinement has sorted Alt $\ge1/7$, giving
$L\ge(1+1/7)/2=4/7$, as required.

## 5. Corrections from previous draft

* Marks fixed to $(2^{n+1}-2^{n+1-k})/D$.
* Removed false “altSum of unrefined gaps $=1/D$’’; correct kernel is
  $\text{altSum}(P_D)\ge1$ after scaling, i.e. $\text{altSum}(P)\ge1/D$.
* Removed “Xiang splits each gap evenly’’ (impossible with $n$ cuts vs
  $n+1$ gaps); replaced by the pairing/duplication construction above.
* Removed unproved greedy and pigeonhole assertions; upper bound now cites
  the explicit $Q$ constructions and `upper_bound_from_altSum_le`.
* Fixed geometric-series calculation to the $(1+1/D)/2$ form.
