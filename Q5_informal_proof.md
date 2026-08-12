# Q5 — Informal Proof (corrected sketch)

## Problem Statement

Let $\mathbb R_{>0}=\{x>0\}$. $f:\mathbb R_{>0}\to\mathbb R_{>0}$ is
*admissible* if for all $x,y>0$:

$$\sqrt{\frac{x^{2}+f(y)^{2}}{2}}\;\ge\;\frac{f(x)+y}{2}\;\ge\;
   \sqrt{x\,f(y)} \tag{*}$$

Prove $f$ is admissible iff $f(x)=x+c$ for some $c\ge0$.

This is `IsAdmissible` and `main_theorem` in `IMO2026/Q5/problem.lean`.

## 1. Squaring

Since all terms $>0$, square (*) to get polynomial bounds
(`admissible_quadratic_bounds`):

$$4x\,f(y)\le (f(x)+y)^{2}\le 2x^{2}+2f(y)^{2}\qquad\forall x,y>0. \tag{1}$$

Left is AM≥GM squared, right is AM≤QM squared.

## 2. Key orbit identity

Put $x:=f(y)$ in (1). Then $4f(y)^{2}\le(f(f(y))+y)^{2}\le4f(y)^{2}$, so

$$f(f(y))=2f(y)-y\quad\forall y>0. \tag{2}$$

This is `admissible_key_step`. Hence gap $g(y):=f(y)-y$ satisfies
$g(f(y))=g(y)$, and by induction (`admissible_orbit`)

$$f^{[n]}(y)=y+n\,g(y),\qquad f(f^{[n]}(y))=y+(n+1)g(y).$$

So the forward orbit is an arithmetic progression with step $g(y)$.

## 3. Gap is non-negative

If $g(x)<0$ then $f^{[n]}(x)=x+n\,g(x)<0$ for $n>x/(-g(x))$,
contradicting $f>0$ (`admissible_gap_nonneg`). Hence

$$g(x)=f(x)-x\ge0\quad\forall x>0. \tag{3}$$

## 4. Gap is constant — the missing lemma

Equation (2) shows $g$ constant **along each orbit**, not between different
orbits. The claim $g(x)=g(y)$ for arbitrary $x,y$ requires a global
argument; swapping (1) for $(x,y)$ and $(y,x)$ and subtracting does **not**
give $(g(x)-g(y))^{2}\le0$, and viewing (4) as a quadratic in $g(x)$ whose
discriminant must be $\le0$ is invalid because (4) is only assumed at the
single value $g(x)$, not for all values of that variable.

The formal proof splits into two cases.

### 4.1 Two positive gaps are equal (`admissible_positive_gap_constant`)

Assume $a=g(x_0)>0$ and $b=g(y_0)>0$. Let

$$X_n=x_0+n a,\quad Y_k=y_0+k b,\quad f(X_n)=X_n+a,\;f(Y_k)=Y_k+b$$

via the orbit description. Apply (1) with $x=X_n$, $y=Y_k$:

$$4X_n(Y_k+b)\le (X_n+a+Y_k)^{2}\le2X_n^{2}+2(Y_k+b)^{2}. \tag{5}$$

Fix $n$ large with $X_n\ge y_0$. Choose $k=\lfloor (X_n-y_0)/b\rfloor$ so that

$$Y_k\le X_n < Y_k+b,\qquad 0\le X_n-Y_k<b. \tag{6}$$

Subtracting the two inequalities in (5) and rearranging gives the two
local estimates used in `gap_algebra`:

$$0\le (a-(X_n-Y_k))^{2}+4X_n(a-b),$$
$$0\le 2(b-(X_n-Y_k))^{2}-(a-(X_n-Y_k))^{2}+4X_n(b-a).$$

If $a\neq b$, `gap_algebra` (a pure real inequality with hypotheses
$0\le a$, $0<b$, $0\le X_n-Y_k<b$) yields

$$4X_n|a-b|\le (a+b)^{2}+2b^{2}=:C,$$

where $C$ is independent of $n$. But $X_n=x_0+n a\to\infty$, so for
$n$ large enough ($n> (C/(4|a-b|)-x_0)/a$) the left side exceeds $C$,
contradiction. Hence $a=b$.

Intuition: two arithmetic progressions with different steps drift apart;
(1) forces their steps to coincide, otherwise the left/right bounds in (5)
cannot both hold for nearby large points $X_n\approx Y_k$.

### 4.2 Zero vs positive cannot coexist (`admissible_zero_gap_forces_identity`)

Suppose $g(p)=0$ for some $p$ but $g(q)=c>0$ for another $q$.
By 4.1, **every** positive gap equals the same $c$ (`hgapcl`): for any
$r$, $g(r)=0$ or $g(r)=c$.

Define subsets of $(0,\infty)$:

$$U=\{t>0:g(t)=0\},\quad V=\{t>0:g(t)=c\}.$$

Then $(0,\infty)=U\cup V$, $U\cap V=\emptyset$, $U\ni p$, $V\ni q$.

From (1) with $f(p)=p$, $f(q)=q+c$ we get for $p\in U$, $q\in V$:

$$4p(q+c)\le(p+q)^{2}\;\Longrightarrow\;4pc\le(p-q)^{2}. \tag{7}$$

Thus a fixed point $p$ and a $c$-point $q$ are at distance $\ge2\sqrt{pc}$;
they cannot be arbitrarily close.

Using (7) one shows $U$ and $V$ are **open** in $(0,\infty)$:

* If $t\in U$, take $\rho=\min(t/2,2\sqrt{t c})$; any $s$ with $|s-t|<\rho$
  cannot be in $V$, otherwise (7) gives $4t c\le(s-t)^{2}<4t c$,
  contradiction. So the $\rho$-ball stays in $U$.
* If $t\in V$, take $\rho=\min(t/2,\sqrt{t c})$; similarly any $s$ with
  $|s-t|<\rho$ cannot be in $U$, using $4s c\le(s-t)^{2}$ and
  $s\ge t/2$.

Hence $(0,\infty)$, which is preconnected (`isPreconnected_Ioi`), is covered
by two nonempty disjoint open sets $U,V$, impossible. Therefore no such
$p,q$ exist: either all gaps are $0$ or all gaps are the same $c>0$.

Combined with 4.1 this gives `admissible_gap_constant`:

$$\forall x,y>0,\;g(x)=g(y)=:c\ge0,\quad f(x)=x+c.$$

## 5. Verification converse

If $f(x)=x+c$, $c\ge0$, then $(f(x)+y)^{2}=(x+y+c)^{2}$ and

$$(x+y+c)^{2}-4x(y+c)=(x-y-c)^{2}\ge0,$$
$$2x^{2}+2(y+c)^{2}-(x+y+c)^{2}=(x-y-c)^{2}\ge0,$$

which are exactly the two inequalities in (1) (hence (*) after taking
roots). The previous draft’s “equality when $c=0$’’ was wrong: equality in
(1) (and hence in (*)) holds iff $x=y+c$, i.e. $(x-y-c)^{2}=0$, not iff
$c=0$. For $c=0$ we get $f(x)=x$ and equality iff $x=y$; for $c>0$ equality
still occurs for pairs with $x=y+c$. In all cases the inequalities hold,
and the `admissible_of_affine` proof is `nlinarith [sq_nonneg (x-(y+c))]`.

## 6. Remarks

* The orbit identity (2) is the only place where both sides of (1) are used
  simultaneously to force equality; thereafter positivity of $g$ and the
  global comparison of two orbits are needed.
* The discriminant argument on (4) is invalid because (4) is not quantified
  over $g(x)$; the correct approach keeps $g(x),g(y)$ fixed and lets
  $X_n,Y_k$ vary with $n,k$.
