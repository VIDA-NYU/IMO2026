# Q2 — Informal Proof (sketch)

## Problem Statement

In the Euclidean plane, let $ABC$ be a nondegenerate triangle, $M$ the midpoint
of $AB$, $N$ the midpoint of $AC$. Points $K,L$ satisfy:

* $K$ inside triangle $BMC$, $L$ inside triangle $BNC$;
* $K$ inside angle $\angle LBA$, $L$ inside angle $\angle ACK$;
* $\angle KBA = \angle ACL$  (h1)
* $\angle LBK = \angle LNC$  (h2)
* $\angle LCK = \angle BMK$  (h3)

Let $O$ be the circumcentre of $AKL$ (equidistant from $A,K,L$).
Prove $OM = ON$.

Formally this is `main_theorem` in `IMO2026/Q2/problem.lean` with
`InsideTriangle` as strict convex combination and `InsideAngle` as positive
cone, angles as unsigned Euclidean angles.

## Overview

Unlike Q1, Q2 has no simple invariant. The proof is computational: choose
affine coordinates with origin $A$, reduce the geometric hypotheses to
polynomial equations in coordinates, and verify that the circumcentre condition
forces $O$ onto the perpendicular bisector of $MN$.

The Lean formalization does this in ~1200 lines; the informal version below
isolates the ideas and states the three algebraic consequences of (h1)–(h3)
without expanding all `ring` identities.

## 1. Coordinates

Since $\neg$Colinear $A,B,C$, $\{b:=B-A,\;c:=C-A\}$ is a basis of the plane.
Write

$$K-A = x\,b + y\,c,\qquad L-A = z\,b + w\,c \qquad (x,y,z,w\in\mathbb R).$$

From $M=A+b/2$, $N=A+c/2$ and convex combinations.

* $K\in\text{int}(BMC)$ gives $x=\alpha+\beta/2$, $y=\gamma$ with
  $\alpha,\beta,\gamma>0$, $\alpha+\beta+\gamma=1$. Hence
  $0<x<1,\;0<y<1$ and similarly for $L$: $0<z<1,\;0<w<1$.
  More precisely `coord_bounds` yields

  $$0<x,\;0<y,\;x<1,\;0<z,\;0<w,\;w<1.$$

* $K\in\text{int}\angle LBA$ means $K-B = s(L-B)+t(A-B)$ with $s,t>0$,
  i.e. $(x-1)b+y c = s((z-1)b+w c)+t(-b)$. Comparing coefficients on the basis
  gives $y=s w$ and $1-x=s(1-z)+t$. Hence

  $$E:=w(1-x)-y(1-z)=w t>0.$$

* $L\in\text{int}\angle ACK$ similarly gives $z=t'x$, $1-w=s'+t'(1-y)$ and

  $$F:=x(1-w)-z(1-y)=x s'>0.$$

So

$$E>0,\qquad F>0,\qquad xw-yz\neq0$$

(the last follows: if $xw-yz=0$ then $E=w-y$ and $F=x-z$, and $E>0,F>0$ with
$x<1,w<1$ forces a contradiction; this is `det_nonzero`).

Let

$$a=\langle b,b\rangle,\;b_0=\langle c,c\rangle,\;g=\langle b,c\rangle$$
with $a>0,b_0>0$ and $ab_0-g^2>0$ (strict Cauchy–Schwarz from linear
independence).

Norms expand as

$$\|K-A\|^2 = a x^2+2gxy+b_0y^2,\qquad \|L-A\|^2 = a z^2+2gzw+b_0w^2.$$

## 2. Circumcentre equations

$O$ satisfies $\|O-A\|=\|O-K\|=\|O-L\|$. Expanding
$\|O-K\|^2=\|(O-A)-(K-A)\|^2$ gives

$$2\langle O-A,\,K-A\rangle = \|K-A\|^2,\qquad
  2\langle O-A,\,L-A\rangle = \|L-A\|^2. \tag{C}$$

The goal $OM=ON$ is $\|O-M\|=\|O-N\|$, equivalently

$$\langle O-\tfrac{M+N}{2},\,N-M\rangle =0.$$

Since $N-M=\tfrac12(C-B)$ and $\tfrac{M+N}{2}-A=\tfrac14(b+c)$, this is

$$\langle O-A,\,C-B\rangle = \tfrac14(b_0-a). \tag{G}$$

Indeed $\|O-M\|^2-\|O-N\|^2 =2\langle O-\frac{M+N}{2},N-M\rangle$.

So it suffices to express $C-B$ as a combination of $K-A$ and $L-A$.
If $C-B = p(K-A)+q(L-A)$ and we know $p\|K-A\|^2+q\|L-A\|^2$,
then (C) gives $\langle O-A,C-B\rangle$.

Because $\begin{pmatrix}x&z\\y&w\end{pmatrix}$ is invertible
($D:=xw-yz\neq0$), we can solve $C-B = -b +c = (-1)b+1c$:

$$p=-(w+z)/D,\qquad q=(x+y)/D$$
satisfy

$$p(K-A)+q(L-A)=C-B\quad\text{as vectors},$$
i.e. $p x+q z=-1,\;p y+q w=1$ (since $C-B=(-1)b+1c$).

Then by (C),

$$\langle O-A,C-B\rangle =\tfrac12\bigl(p\|K-A\|^2+q\|L-A\|^2\bigr).$$

Thus (G) is equivalent to the polynomial identity

$$2\bigl(-(w+z)\|K-A\|^2+(x+y)\|L-A\|^2\bigr)=D\,(b_0-a). \tag{*} $$

Everything else is verifying (*) from the three angle hypotheses.

## 3. Angle hypotheses as algebraic equations

For nonzero vectors $u,v$, the angle lies in $[0,\pi]$ and $\cos\angle(u,v)=\langle u,v\rangle/(\|u\|\|v\|)$
and $\cos$ is injective on $[0,\pi]$, so equality of unsigned angles is
equivalent to equality of cosines. The proof uses $\cos$ equality, *squares*
it to eliminate the norms, and then must recover the sign. Squaring is where
the sign ambiguity is introduced; it is resolved by the positivity
$E>0,F>0$ and $y>0,z>0$ together with $\|u\|\|v\|>0$, via `cos_eq_implies`
which deduces $C_1z=C_2y$ from $C_1/n_1=C_2/n_2$ and $(C_1z)^2=(C_2y)^2$ when
$y,z,n_1,n_2>0$ and $C_1z\cdot C_2y\ge0$.

Each $h_i$ is of the form $\cos\angle(u_1,v_1)=\cos\angle(u_2,v_2)$, i.e.

$$\frac{\langle u_1,v_1\rangle}{\|u_1\|\|v_1\|}=\frac{\langle u_2,v_2\rangle}{\|u_2\|\|v_2\|}.$$

Cross-multiplying and squaring gives
$(\langle u_1,v_1\rangle\|u_2\|\|v_2\|)^2=(\langle u_2,v_2\rangle\|u_1\|\|v_1\|)^2$.
Expanding $\|u\|^2\|v\|^2-\langle u,v\rangle^2$ in the $b,c$ basis yields a
multiple of $ab_0-g^2>0$, which is cancelled by strict Cauchy–Schwarz. The
sign is then restored by the previous paragraph. Concretely
(`angle_eq_to_c1/c2/c3`):

* $h_1:\angle KBA=\angle ACL$ with $u_1=K-B,\;v_1=A-B,\;u_2=L-C,\;v_2=A-C$ gives

  $$a\,z(1-x)=b_0\,y(1-w). \tag{C1}$$

* $h_2:\angle LBK=\angle LNC$ with $u_1=K-B,\;v_1=L-B,\;u_2=L-N,\;v_2=C-N$,
  $E=w(1-x)-y(1-z)>0$, gives exactly

  $$2z\bigl(a xz-a x-a z+a+b_0wy+gwx-gw+gyz-gy\bigr)=E\,(2b_0w-b_0+2gz). \tag{C2}$$

  Left side is $2z\cdot\langle K-B,L-B\rangle$ expanded; right side is
  $E\cdot\langle C-N,L-N\rangle\cdot2$ after the $ab_0-g^2$ cancellation.
  The formal proof obtains this by showing
  $\|u_1\|^2\|v_1\|^2-\langle u_1,v_1\rangle^2=E^2(ab_0-g^2)$ and
  $\|u_2\|^2\|v_2\|^2-\langle u_2,v_2\rangle^2=(z/2)^2(ab_0-g^2)$, then
  $(\langle u_1,v_1\rangle z/2)^2=(\langle u_2,v_2\rangle E)^2$, then
  `cos_eq_implies` with $E>0,z>0$ yields the unsquared equality.

* $h_3:\angle LCK=\angle BMK$ with $u_1=L-C,\;v_1=K-C,\;u_2=B-M,\;v_2=K-M$,
  $F=x(1-w)-z(1-y)>0$, gives exactly

  $$2y\bigl(a xz+b_0wy-b_0w-b_0y+b_0+gwx-gx+gyz-gz\bigr)=F\,(2ax-a+2gy). \tag{C3}$$

  Similarly $\|u_1\|^2\|v_1\|^2-\langle u_1,v_1\rangle^2=F^2(ab_0-g^2)$ and
  $\|u_2\|^2\|v_2\|^2-\langle u_2,v_2\rangle^2=(y/2)^2(ab_0-g^2)$,
  then `cos_eq_implies` with $F>0,y>0$ gives (C3).

Each step is `ring` after expanding $\langle\cdot,\cdot\rangle$ via
$K-B=(x-1)b+yc$ etc., and dividing by the positive factor $ab_0-g^2$ from
`CS_strict`.

## 4. Concluding identity

With (C1)–(C3) the remaining goal (*) is a pure polynomial identity.
Let $\|K-A\|^2=a x^2+2gxy+b_0y^2$, $\|L-A\|^2=a z^2+2gzw+b_0w^2$, $D=xw-yz$,
$E=w(1-x)-y(1-z)$, $F=x(1-w)-z(1-y)$. The Lean lemma `algebraic_identity`
(stated for $a,b,g$ as $a,b_0,g$ here) is the exact identity, proved by
`ring`:

$$(x-1)(w-1)\bigl[2(-(w+z)\|K-A\|^2+(x+y)\|L-A\|^2)-D(b_0-a)\bigr]$$
$$=-(3wx+2wy-w+2xz-x+yz-y-z)\bigl(a z(1-x)-b_0y(1-w)\bigr)$$
$$\quad+(x+y)(w-1)\bigl[2z(axz-ax-az+a+b_0wy+gwx-gw+gyz-gy)-E(2b_0w-b_0+2gz)\bigr]$$
$$\quad-(w+z)(x-1)\bigl[2y(axz+b_0wy-b_0w-b_0y+b_0+gwx-gx+gyz-gz)-F(2ax-a+2gy)\bigr].$$

Indeed expanding both sides in $\mathbb R[x,y,z,w,a,b_0,g]$ gives identical
polynomials (about 30 monomials per side).

The three bracketed factors on the right are exactly the left-minus-right
sides of (C1), (C2), (C3): the first is (C1), the second is (C2) as
$2z(\cdots)-E(\cdots)$, the third is (C3) as $2y(\cdots)-F(\cdots)$.
By (C1)–(C3) each is $0$, so the right-hand side is $0$. The prefactor
$(x-1)(w-1)\neq0$ because $x<1,w<1$ (from `coord_bounds`), so the bracketed
left factor must be $0$, i.e.

$$2(-(w+z)\|K-A\|^2+(x+y)\|L-A\|^2)-D(b_0-a)=0,$$

which is precisely (*). Hence (G) holds, hence
$\langle O-\frac{M+N}{2},N-M\rangle=0$, hence $\|O-M\|=\|O-N\|$, i.e.
$\operatorname{dist} OM = \operatorname{dist} ON$.

Substitutions displayed: in `main_theorem` the final `have hpoly` rewrites
$\|K-A\|^2,\|L-A\|^2$ via $h_{\text{norm}K},h_{\text{norm}L}$, and
$hC_1,hC_2,hC_3$ are exactly (C1)–(C3) with $a=\langle b,b\rangle$ etc., then
`field_simp` + `nlinarith [hpoly]` closes (*) after dividing by $D\neq0$.

## 5. Remarks on the informal vs formal gap

* The filtration of positivity ($E>0,F>0,D\neq0$) is geometric: it encodes
  that $K,L$ are genuinely inside the triangles/angles, so no degenerate
  configuration allows a spurious cosine equality.

* Steps (C1)–(C3) each require expanding $\|u\|^2\|v\|^2-\langle u,v\rangle^2$
  as a multiple of $ab_0-g^2$. The factor $ab_0-g^2>0$ is essential to cancel
  and to deduce the unsigned equality without sign ambiguity; this is where
  strict Cauchy–Schwarz is used.

* The final `ring` closure is ~30 monomials — feasible by hand in principle
  but not enlightening. The formal proof leaves it to the kernel; the informal
  proof states it as a verifiable polynomial identity.

This mirrors Q1's structure (coordinates + invariant + monotone measure) but
here the "invariant" is the verified polynomial (*), checked computationally
rather than by a one-line Euclidean argument.
