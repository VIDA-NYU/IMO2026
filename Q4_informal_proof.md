# Q4 — Informal Proof (corrected sketch)

## Problem Statement

A triangle is its multiset of three angles $>0$ summing to $180$.
An admissible cut chooses apex $\alpha$ and base angles $\beta,\gamma$
with $s=\{\alpha,\beta,\gamma\}$ and $x\in(\gamma,180-\beta)$, producing

$$L=\{\beta,x,180-\beta-x\},\quad
  R=\{\gamma,180-x,x-\gamma\}.$$

`MulanWins θ s` is the least predicate with `win` (θ∈s) and `move`
(cut $s→L,R$ with both $L,R$ winning). `MulanCanGuarantee θ` means
$\forall s$ valid, `MulanWins θ s`.

Prove for $0<θ<180$:

$$\text{MulanCanGuarantee }θ \iff θ=180/n\text{ for some }n\ge2.$$

This is `main_theorem` in `IMO2026/Q4/solution.lean` (520 lines).

## Overview

The cut parameter $x$ is an arbitrary real in an open interval, so
reachability is not an additive semigroup. The correct dichotomy is
arithmetic: whether $180$ is an integer multiple of $θ$.

* If $180=nθ$, every triangle can be forced to a multiple of $θ$ (sufficiency,
  `all_win_of_divides`).
* If $180$ is **not** an integer multiple of $θ$, there is a safe triangle
  (no angle is $kθ$) and safe is preserved under some child of any cut, so
  by induction safe triangles are never winning (necessity, `safe_child` +
  `safe_not_win`). The equilateral $\{60,60,60\}$ suffices as the
  initial counterexample **only** under that hypothesis; it is not a
  counterexample for $θ=45$ (which does divide $180$).

## 1. Sufficiency: $180=nθ\;(n\ge2)$ ⇒ every triangle wins

### 1.1 Lemma: a multiple of θ wins (`win_of_multiple`)

If $kθ∈s$ with $k\ge1$, then `MulanWins θ s`. Induction on $k$:

* $k=1$: already $θ∈s$.
* $k+1$: let $a=(k+1)θ$ be the apex, $s=\{a,β,γ\}$, so $a+β+γ=180$.
  Choose cut $x=γ+θ$. Admissibility: $γ<x$ and $x<180-β$
  because $180-β=γ+a=γ+kθ+θ$. The cut yields

  $$L=\{β,γ+θ,180-β-γ-θ\}=\{β,γ+θ,kθ\},\quad
    R=\{γ,180-γ-θ,θ\}.$$

  $L$ contains $kθ$ (induction hypothesis), $R$ contains $θ$ ($x-γ$).
  Both children win, so $s$ wins via `move`.

This uses only $θ>0$ and validity (`cut_preserves`).

### 1.2 Interval lemma (`interval_lemma`)

Let $r_1,r_2,r_3>0$, $r_1+r_2+r_3=n\ge2$ integer, none is integer.
Then after reordering $(\alpha',β',γ')$ of $(r_1,r_2,r_3)$,
$\exists m\in\mathbb N$, $1\le m\le n-1$, with

$$γ' < m < γ'+\alpha',\qquad \alpha'+β'+γ'=n.$$

Proof sketch: if some $r_i>1$, put it as $\alpha'$ and take
$m=\lfloor γ'\rfloor+1$ ($γ'$ is the normalized $c/θ$ in application);
$m$ lies in the open interval because $γ'\notin\mathbb Z$.
If all $r_i\le1$, then all $r_i<1$ (since none is $1$), and some pair sums
$>1$ (otherwise $r_1+r_2+r_3\le3/2<n$). Put the pair as $(α',γ')$ and take
$m=1$. This is the full case split `core1`/`core2` in the formal proof.

### 1.3 Every triangle wins when $180=nθ$ (`all_win_of_divides`)

Let $s=\{a,b,c\}$ valid, $a+b+c=nθ$, $θ>0$.

*Case A:* some $v\in s$ is an integer multiple of $θ$, i.e. $v=kθ$.
  Then `win_of_multiple` applies directly.

*Case B:* no angle is a multiple of $θ$. Normalize
$r_a=a/θ,\;r_b=b/θ,\;r_c=c/θ$, so $r_a+r_b+r_c=n$, each $>0$, none integer.
Apply `interval_lemma` to get reordered $(\alpha',β',γ')$ and $m$ with
$γ'<m<γ'+\alpha'$. Set actual angles $\alpha=\alpha'θ,\;β=β'θ,\;γ=γ'θ$.
Then $s=\{\alpha,β,γ\}$ (up to permutation, via `Multiset.map (·*θ)`),
$\alpha+β+γ=nθ=180$, and

$$γ < mθ < γ+\alpha.$$

Choose cut $x=mθ$. Then $γ<x<γ+\alpha=180-β$, so the cut is admissible and

$$L=\{β,mθ,180-β-mθ\}=\{β,mθ,(n-m)θ\!-\!γ\!\text{ part}\},\;
  R=\{γ,180-mθ,mθ-γ\}.$$

More precisely $L$ contains $mθ$ and $R$ contains $180-mθ=(n-m)θ$, both
positive integer multiples of $θ$ (since $1\le m\le n-1$ implies
$1\le n-m$). By `win_of_multiple` both children win, so $s$ wins via `move`.

This gives `MulanCanGuarantee θ` when $θ=180/n$. No real-valued potential
$\mu$ is needed; the winning tree depth is at most $n$ (the cut reduces
$k$ or creates $m$), and termination is by the inductive definition of
`MulanWins` (finite tree), not by a natural-valued measure. A real-valued
$\mu$ whose strict decrease does not imply well-foundedness would be
insufficient.

## 2. Necessity: not of form $180/n$ ⇒ Shan-Yu can avoid forever

Assume $θ>0$ and **not** $180=zθ$ for any $z\in\mathbb Z$ (call this $(*)$).

Define `Safe θ s` := no angle of $s$ is an integer multiple of $θ$.

### 2.1 Safe child (`safe_child`)

If $s$ is valid and safe and `IsCut s L R` with $180\neq zθ$, then
$L$ safe or $R$ safe.

Proof: write $s=\{\alpha,β,γ\}$, $L=\{β,x,180-β-x\}$, $R=\{γ,180-x,x-γ\}$.
Assume both $L,R$ not safe, so each contains some $z_Lθ$ and $z_Rθ$.
Since $β,γ$ are safe, the offending angle in $L$ cannot be $β$ and the
offending angle in $R$ cannot be $γ$; the only possibilities are
$x$ or $180-β-x$ in $L$, and $180-x$ or $x-γ$ in $R$. This leaves four
nontrivial combinations:

* $x=z_Lθ,\;180-x=z_Rθ$ ⇒ $180=(z_L+z_R)θ$, contradicts $(*)$;
* $x=z_Lθ,\;x-γ=z_Rθ$ ⇒ $γ=(z_L-z_R)θ$, contradiction;
* $180-β-x=z_Lθ,\;180-x=z_Rθ$ ⇒ $β=(z_R-z_L)θ$, contradiction;
* $180-β-x=z_Lθ,\;x-γ=z_Rθ$ ⇒ $\alpha=180-β-γ=(z_L+z_R)θ$, contradiction.

In each case a parent angle becomes a multiple, impossible. So at least one
child stays safe. This is the **for every cut, at least one child remains
safe** statement required; it is not enough to say “Shan-Yu can choose a
safe child’’ without proving the disjunction holds for every cut.

### 2.2 Safe never wins (`safe_not_win`)

By induction on `MulanWins θ t`: if $t$ valid and safe, `MulanWins θ t` is
impossible. Base `win` would need $θ=1·θ\in t$, contradicting safe.
Step `move s→L,R` with both $L,R$ winning: $s$ valid and safe implies by
`safe_child` one of $L,R$ is safe and valid (`cut_preserves`), contradicting
the induction hypothesis for that child.

### 2.3 Counterexample

Under $(*)$, the equilateral $e=\{60,60,60\}$ is valid and safe:
if $60=zθ$ then $180=3zθ$ would be a multiple, contradicting $(*)$.
Hence by `safe_not_win`, $\neg\text{MulanWins }θ\,e$, so
$\neg\text{MulanCanGuarantee }θ$. This is `equilateral_counterexample`.

**Not** a counterexample when $θ$ does divide $180$: e.g. $θ=45=180/4$,
$e$ is safe ($60\neq z·45$) but $(*)$ fails ($180=4·45$), so
`safe_not_win` does not apply, and indeed $e$ is winning via Case B above
with $m=2$ ($γ'=60/45=4/3$ after normalizing, so $4/3<2<4/3+4/3=8/3$). The previous draft’s
claim “equilateral is counterexample whenever $θ\neq60,90$’’ was false;
e.g. $θ=45$ is $180/4$ and must be winning.

### 2.4 Assembling necessity

If `MulanCanGuarantee θ` with $0<θ<180$, then $(*)$ must be false,
otherwise the equilateral counterexample contradicts it. So $\exists z$ with
$180=zθ$, $z>0$ (since $180,θ>0$), $z\neq1$ (since $θ<180$), hence $z\ge2$.
Put $n=z.\text{toNat}$, then $θ=180/n$, $n\ge2$.

## 3. Main theorem

Sufficiency (1) + necessity (2) give

$$0<θ<180\;\Longrightarrow\;
  \bigl(\text{MulanCanGuarantee }θ \iff \exists n\ge2,\;θ=180/n\bigr).$$

The $x$ parameter’s arbitrariness is handled not by a semigroup but by the
integer $m$ from the interval lemma; the $\mathbb Z$-module claim is false
($180/n$ is generally not an integer combination of $180$); termination
is by well-founded induction on $k$ ($kθ$) and on $n-m$, not by a
real-valued $\mu$.
