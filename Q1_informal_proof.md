# Q1 — Informal Proof

## Problem Statement

Board of 2026 integers, each >1. A *move* consists of choosing two entries
`m, n > 1` (at distinct positions, values may coincide) and replacing them by

```
g = gcd(m, n)    and    q = lcm(m, n) / g   (= m·n / g²)
```

keeping the other 2024 entries. A board is *terminal* if at most one entry is
>1 (no move possible). Let `B₀` be initial. Prove:

* **(a)** Every sequence of moves from `B₀` terminates, and every terminal
  board reachable from `B₀` has exactly one entry `>1` (so it is
  `[M,1,...,1]` for some `M>1`).

* **(b)** The terminal value `M` is independent of the choices: any two
  terminal boards reachable from `B₀` have the same `M`. Moreover

  ```
  M = Mval(B₀) = ∏_{p | ∏B₀} p^{g_p(B₀)},   where g_p(B) = gcd{ v_p(x) : x∈B }
  ```

  and `M>1`. Here `v_p` is the p-adic valuation and `g_p` is the gcd of the
  (positive) valuations, with `gcd(a,0)=a`.

We show every play terminates in `[M,1,...,1]` with `M` independent of choices
and `M = ∏ p^{g_p(B₀)}`.

## 1. p-adic picture

For prime p, let v_p(x) be exponent of p in x (0 if p∤x). For m,n>0:

* v_p(gcd(m,n)) = min(v_p(m), v_p(n))
* v_p(lcm(m,n)) = max(v_p(m), v_p(n))
* v_p(q) = max - min = |v_p(m)-v_p(n)|

So on the p-vector a move is (a,b) ↦ (min(a,b), |a-b|).

## 2. Invariant g_p

Define for a board B:

```
g_p(B) = gcd{ v_p(x) : x ∈ B }
```

with gcd(a,0)=a, so zeros are ignored — it is the gcd of the positive valuations.
Let G be the gcd of valuations of the other 2024 entries. Before the move the
gcd is gcd(a,b,G), after it is gcd(min(a,b), |a-b|, G).

Lemma: gcd(a,b) = gcd(min(a,b), |a-b|).
If a ≤ b then gcd(a,b)=gcd(a,b-a) by Euclid; symmetric otherwise.

Iterated Nat.gcd is associative/commutative, so

```
g_p(B) = g_p(B')
```

for any Move B → B'. Consequences:

* S(B) = {p : g_p(B) ≠ 0} = {p : p | ∏B} is invariant.
* M(B) = ∏_{p∈S(B)} p^{g_p(B)} is invariant along any play.

## 3. Termination

Let Ω(x) = total prime factors with multiplicity, Ω(B)=∑Ω(x), c(B)=#{x∈B : x>1}.

Since mn = g·lcm and lcm = g·q multiplicatively:

```
Ω(m)+Ω(n) = Ω(g)+Ω(lcm) = 2Ω(g)+Ω(q)
```

For B = m::n::s, B' = g::q::s:

```
Ω(B') = Ω(B) - Ω(g)          (1)
c(B) = 2 + c(s)
c(B') = [g>1] + [q>1] + c(s)
```

* If g>1 then Ω(g)≥1, so Ω(B') ≤ Ω(B)-1.
* If g=1 then Ω(g)=0, so Ω(B')=Ω(B), but q = mn >1 (m,n>1 coprime), so c(B')=1+c(s)=c(B)-1.

Either Ω strictly drops, or Ω stays and c strictly drops. Since c ≤ 2026,
the lexicographic measure

```
μ(B) = Ω(B)·2027 + c(B)
```

strictly decreases on every move. μ ∈ ℕ cannot descend infinitely, so no
infinite sequence f with f(0)=B0 and Move(f_k, f_{k+1}) exists. Card is preserved
(2 out, 2 in), so the bound 2027 stays valid.

## 4. Terminal boards have exactly one entry >1

For initial B0, pick a0>1 and p|a0. Then v_p(a0)≥1, so not all v_p are 0, so
g_p(B0)≠0. By invariance g_p(B')≠0 for any reachable B'. If B' were all 1's,
all v_p would be 0 and g_p would be 0, contradiction. Hence any reachable B'
has c(B')≥1.

Thus every reachable board has c(B')≥1. If B' is terminal, then c(B')≤1, and
consequently c(B')=1. I.e. B'=[M,1,...,1] with unique M>1.

This proves statement (a): termination and HasUniqueLarge.

## 5. Value of M

If B=[M,1,...,1] then the multiset of v_p is {v_p(M),0,...,0}, so g_p(B)=v_p(M)
and ∏B = M. Hence

```
M(B) = ∏_{p|M} p^{v_p(M)} = M
```

by unique factorization.

If B' is terminal reachable from B0, B'=[M,1,...,1], then M(B')=M while
M(B')=M(B0) by invariance. Hence

```
M = M(B0) = ∏_{p|∏B0} p^{g_p(B0)}.
```

Any two terminal boards from the same B0 have the same M, and M>1 because
some g_p(B0)≥1 gives p^{g_p}≥2 and all other factors ≥1.

This proves statement (b), terminal_value_eq_Mval, and Mval_gt_one. The number
2026 is irrelevant except to bound c — any finite n≥1 works (for n≥1 the same
argument gives termination of every maximal play, i.e. every sequence in which
moves continue whenever possible).
