# Q6 — Informal Proof (corrected sketch)

## Problem Statement

$a:\mathbb N\to\mathbb N$ is *valid* (`IsValidSeq`) if $a(n)>1$,
$a(n+1)>a(n)$, $\gcd(a(n+1),a(i))>1$ for all $i\le n$, and
$a(n+1)$ is minimal with that property (no $b$ with $a(n)<b<a(n+1)$ is
$n$-good).  Define `Good a n b := ∀i≤n, gcd(b,a(i))>1`.

Prove every valid $a$ has purely periodic differences:
$\exists T>0,L>0\;\forall n\;a(n+T)=a(n)+L$.

Formally `main_theorem` in `IMO2026/Q6/solution.lean` (771 lines).

## Overview

The previous draft’s central claim — “the union of prime divisors stabilizes’’
— is false: $a(n)=2n+2=2,4,6,8,\dots$ is valid (each new term shares factor
$2$ with all earlier terms, the only odd intervening integer is not $n$-good)
but $\bigcup_{i\le n}P(a(i))$ contains arbitrarily large primes (every even
number’s odd prime factors), so the union never stabilizes.

The correct finite object is not the union but the *small* prime support.
Fix $a_0=a(0)$.  Only primes $\le a_0$ matter for goodness, and the set of
small primes is finite.  Goodness stabilizes to `Good a N` for some $N$,
and the modulus $M=\prod_{i\le N}a(i)$ absorbs exactly the needed primes.
Periodicity then follows from pigeonhole on residues mod $M$, not from a
circular choice of “eventual step size’’.

## 1. Preliminaries

* `StrictMono` and `pairwise_gcd`: $a$ strictly increasing and pairwise
  $\gcd>1$; hence each $a(i)>0$.
* `gaps_bounded`: $a(n+1)-a(n)\le a_0$.  Indeed $k a_0$ with
  $k=a(n)/a_0+1$ satisfies $a(n)<k a_0\le a(n)+a_0$ and is $n$-good
  (`mul_a0_good`: any multiple of $a_0$ shares with each $a(i)$ a prime
  dividing $\gcd(a(i),a_0)>1$), so by minimality $a(n+1)\le k a_0$.
* The example “$6,10,12,\dots$ is valid’’ was false: after $a(0)=6$, the
  greedy next term is $8$, not $10$, because $8>6$, $\gcd(8,6)=2>1$ and
  $7$ is not $0$-good ($\gcd(7,6)=1$), so the minimal $0$-good above $6$
  is $8$.  The arithmetic progression $2n+2$ *is* valid, but $6,10,12$
  skips $8$ and violates minimality.

## 2. Small support and good stabilization (replaces false union stabilization)

### 2.1 Small primes are enough

Define `smallPrimes = {p prime : p≤a_0}` (finite) and

$$\operatorname{ssupp}(a,i)=P(a(i))\cap\text{smallPrimes}.$$

Lemma `term_has_small_subsupport` (strong induction + `large_prime_not_min_support`):
for every $k$ there is $i\le k$ with $P(a(i))\subseteq P(a(k))$ and all
primes in $P(a(i))$ are $\le a_0$.  The proof is the arithmetic core:
if $P\mid a(i)$ with $P>a_0$, write $a(i)=P^{e}b_0$ ($P\nmid b_0$,
$b_0\ge2$). $b_0$ shares a small prime $q\le a_0$ with $a_0$ (hence
$q\mid b_0$, $q\neq P$). Set $g(t)=b_0q^{t}$. Lemma `hmul_good`:
**every positive multiple $b_0t$ is $(i-1)$-good** — for $l\le i-1$ the
IH gives a small-subsupport $a(l')\subseteq P(a(l))$; $a(i)$ shares a
small prime $r\neq P$ with $a(l')$ (pairwise gcd), so $r\in
P(a(i))\setminus\{P\}=P(b_0)$, hence $r\mid b_0\mid b_0t$ and
$\gcd(b_0t,a(l))>1$. Let $T$ be least with $g(T)=b_0q^{T}\ge a(i)$
(`Nat.find hg_unbounded`) and $c=g(T-1)=b_0q^{T-1}<a(i)$. Then $c$ is
$(i-1)$-good, $a_0\le c\le a(i-1)$ (by $c<a(i)=a((i-1)+1)$ minimality),
so $c=a(j)$ for some $j<i$ via `good_in_range_is_term`, and
$P(a(j))=P(c)=P(b_0)=P(a(i))\setminus\{P\}\subsetneq P(a(i))$.

Consequence `good_small_witness`: if $b$ is $n$-good then for each
$i\le n$ there is a *small* prime $p\le a_0$ with $p\mid b$ and $p\mid a(i)$.
Indeed pick the small-subsupport term $a(i')\subseteq a(i)$; $b$ shares a
prime $p$ with $a(i')$ (since $i'\le n$), that $p$ is small and lies in
$P(a(i))$.

Thus goodness depends on individual small supports, not merely on the
union $\bigcup P(a(i))$.  The union never stabilizes, but the *family* of
small supports does.

### 2.2 Finite-range pigeonhole

`ssupp(a,i)\subseteq\text{smallPrimes}`, so `ssupp` takes values in the
finite powerset `(smallPrimes).powerset`.  Hence `ssupp_cover`:

$$\exists N\;\forall j\;\exists i\le N\; \operatorname{ssupp}(a,i)=
  \operatorname{ssupp}(a,j).$$

Every small support occurring arbitrarily far out already occurs in the
prefix $0..N$.

### 2.3 Good stabilizes (`good_stabilizes_core`)

With $N$ from above, for all $n\ge N$ and all $b$:

$$\text{Good }a\,n\,b \iff \text{Good }a\,N\,b.$$

*Forward*: monotone (fewer constraints for $N$).
*Backward*: assume `Good a N b` and fix $j\le n$.  Get $i\le N$ with
$\operatorname{ssupp}(a,i)=\operatorname{ssupp}(a,j)$.  By
`good_small_witness`, $b$ shares a small prime $p$ with $a(i)$;
$p\in\operatorname{ssupp}(a,i)=\operatorname{ssupp}(a,j)$, so $p\mid a(j)$;
hence $p$ witnesses $\gcd(b,a(j))>1$.  Doing this for every $j\le n$ gives
`Good a n b`.  This is the “relevant finite family of gcd constraints’’
stabilization, not union stabilization.

## 3. From stable goodness to eventual periodicity

### 3.1 Modulus

Set `M = prefixMod a N = ∏_{i\le N} a(i)` (`prefixMod_absorbs`:
every prime dividing some $a(i),i\le N$ divides $M$).  For any $M\mid L$,

$$\text{Good }a\,N\,(b+L) \iff \text{Good }a\,N\,b$$

(`Good_periodic_of_modulus` via `gcd_constraint_periodic`: adding a multiple
of a common multiple of small primes does not change divisibility by those
primes).  With stabilization this upgrades to

$$\forall j\;\forall b\; \text{Good }a\,j\,(b+L)\iff\text{Good }a\,j\,b$$

(`Good_periodic_all`).

### 3.2 Pigeonhole on residues

For $n\ge N$, the greedy characterization is stable:

$$a(n+1)=\min\{b>a(n):\text{Good }a\,N\,b\}.$$

Consider the $M+1$ numbers $a(N),\dots,a(N+M)$ modulo $M$; they take values
in the $M$ residues, so two indices $u<v$ in $[N,N+M]$ satisfy
$a(u)\equiv a(v)\pmod M$ (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`).
Set

$$T=v-u>0,\qquad L=a(v)-a(u)>0,\qquad M\mid L.$$

Induction from $u$ upward (`eventual_periodicity_from_stable`): assume
$a(n+T)=a(n)+L$ for $n=u+d$.  Both $a(n+1)+L$ and $a(n+T+1)$ are the
least `Good a N` above $a(n+T)=a(n)+L$ (using translation invariance to
shift the “no good in between’’ condition by $\pm L$), so they coincide.
Hence

$$\forall n\ge u\; a(n+T)=a(n)+L.$$

The choice of $T,L$ comes from residues, not from an assumed eventual step
size — no circularity.

## 4. Pure periodicity (extension to all $n$)

Eventual periodicity holds from threshold $N'=u$.  To extend backwards to
all $n$, use `Good_periodic_all` for every $j$ and downward induction
(`pure_periodicity_from_stable`): if $a(k+1+T)=a(k+1)+L$ then

$$a(k+T)=a(k)+L$$

by comparing the two minimal `Good` intervals
$(a(k+T),a(k+T+1))$ and $(a(k),a(k+1))$ shifted by $L$, using minimality of
both $a(k+1)$ and $a(k+T+1)$.  The step is

$$a(k+T+1)=a(k+1)+L\;\Longrightarrow\;a(k+T)=a(k)+L,$$

proved by antisymmetry: $a(k)+L\le a(k+T)$ (otherwise $a(k)+L$ would be a
good strictly between $a(k+T)$ and $a(k+T+1)$) and $a(k+T)\le a(k)+L$
(otherwise $a(k+T)-L$ would be good strictly between $a(k)$ and $a(k+1)$).
Iterating downward covers $n<N'$.

Strict monotonicity alone does not give this; the two-sided minimality
arguments are needed.

## 5. Result

Combining `good_stabilizes_core`, the residue pigeonhole, and the
pure upgrade gives `main_theorem`:

$$\exists T>0,L>0\;\forall n\;a(n+T)=a(n)+L,$$

so consecutive differences are purely periodic.  The sequence $2n+2$ indeed
has $T=1,L=2$ from the start, consistent with the theorem; its failure to
have stabilizing union of primes did not obstruct the proof because only
small primes $\le a_0$ (here $\le2$) matter.

## 6. Corrections from previous draft

* Replaced false “prime-union stabilizes’’ with finite `ssupp` / `Good`
  stabilization.
* Clarified goodness uses per-index small supports, not the union.
* Replaced circular “choose period from eventual step’’ with residue
  pigeonhole on $M$.
* Replaced “extend by monotonicity’’ with two-sided `Good`-minimality
  downward induction.
* Fixed invalid example $6,10,12$ to $6,8,\dots$ and noted $2n+2$ as the
  true valid arithmetic progression.
