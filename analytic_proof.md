# The analytic area-deficit estimate, including finite punctures

This proof accompanies AreaDeficit.density_deficit_cutoff and
AreaDeficit.positive_part_cutoff. The differential and integral steps
below have checked Lean proofs. The metric comparison that supplies
the constant M in an application is a separate input.

## Statement

Let V be open in ℂ, let F be finite, and let a,b be positive C² functions
on V∖F satisfying the curvature −1 equations

\[
\Delta\log a=a^2,\qquad \Delta\log b=b^2.
\]

Assume M≥0 and (log a−log b)₊≤M on V∖F. If χ≥0 is C² with compact
support contained in V, then

\[
\boxed{\displaystyle
\int_{\mathbb C\setminus F}\chi(a^2-b^2)_+\,dA
\le M\int_{\mathbb C}|\Delta\chi|\,dA.}
\]

The left-hand side is initially an extended nonnegative integral; the
conclusion proves it finite. Here Δ=∂²/∂x²+∂²/∂y² and dA is ordinary
Euclidean area.

We first prove this for a real C² function u on V∖F with u₊≤M, assuming

\[
u>0\Longrightarrow\Delta u\ge0,\qquad
u\le0\Longrightarrow\Delta u\le0,
\]

with (Δu)₊ replacing the density difference. The Lean version only
requires the bound on the test support, together with a local upper
bound near each puncture in that support.

## 1. A harmonic barrier

Put S=supp χ. Choose R>0 with |z|≤R on S, and define, off F,

\[
L(z)=\sum_{p\in F}\log|z-p|-C,\qquad
C=\sum_{p\in F}(R+|p|).
\]

Since log t≤t for t>0 and |z−p|≤R+|p|, we have L≤0 on S∖F.
Every summand is harmonic away from its centre, so ΔL=0 off F.
Near p∈F write L(z)=log|z−p|+H_p(z), where H_p is smooth and bounded
near p. Therefore L(z)→−∞ as z→p, z≠p. If F is empty, L=0.
These facts are proved in LogBarrier.lean.

## 2. A regularisation that vanishes near each puncture

Let q be smooth and nondecreasing, with q=0 on (−∞,0], q=1 on
[1,∞), and 0≤q≤1. We use mathlib's smoothTransition function. Set

\[
\beta(t)=\int_0^tq(s)\,ds.
\]

The fundamental theorem of calculus gives β′=q and β″=q′≥0.
Thus β is smooth, vanishes for t≤0, and 0≤β(t)≤t₊. These facts
and the derivative identities are proved in Regularisation.lean.

For n≥0 put A_n=n+1 and, off F, define

\[
w_n=A_nu+L,\qquad b_n=\frac{\beta(w_n)}{A_n},
\qquad c_n=q(w_n),\qquad s_n=c_n\Delta u.
\]

Extend b_n,c_n,s_n by zero at F. Fix n and p∈F∩S. Let B be an
upper bound for u in a punctured neighbourhood of p. Since L→−∞,
we have L≤−A_nB on a sufficiently small punctured neighbourhood.
Hence w_n≤0 there, and b_n=c_n=s_n=0. They vanish at p by definition,
so all three functions are identically zero on a neighbourhood of p.
In particular, b_n is C² and s_n is continuous there. Away from F,
these regularity statements follow from the hypotheses.

The neighbourhood may depend on n; no uniform neighbourhood is
required. This construction avoids a separate removable-singularity
theorem and avoids integration by parts on a region with small holes.
See PunctureRegularisation.lean.

## 3. Pointwise estimates

On S∖F, L≤0 gives

\[
0\le b_n\le\frac{(A_nu+L)_+}{A_n}\le u_+\le M.
\]

The same holds at F because b_n=0. If u≤0 on S∖F then w_n≤0, so
s_n=0. If u>0, then Δu≥0 and c_n≥0, so s_n≥0. Thus s_n≥0 on S.

The second-order chain rule and ΔL=0 give, off F,

\[
\Delta b_n
=q(w_n)\Delta u+\frac{q'(w_n)}{A_n}|\nabla w_n|^2
\ge s_n.
\]

At a puncture in S, b_n vanishes on a neighbourhood, so Δb_n=0=s_n.
The inequality therefore holds throughout S.
LaplacianChain.lean proves the chain rule for mathlib's actual
Euclidean Laplacian on ℂ, using Fréchet derivatives in directions 1,i.

## 4. Green's identity and a uniform integral bound

Since χ has compact support S and b_n is C² near S, integration by
parts twice in each real coordinate gives

\[
\int_{\mathbb C}\chi\Delta b_n\,dA
=\int_{\mathbb C}b_n\Delta\chi\,dA.
\]

GreenIdentity.lean derives this from mathlib's directional integration
by parts. It also derives integrability of the products involved:
they are continuous and compactly supported. The support of Δχ
is contained in S. There is no boundary term, and regularity of
b_n outside a neighbourhood of S is unnecessary.

Consequently

\[
0\le\int\chi s_n\,dA
\le\int\chi\Delta b_n\,dA
=\int b_n\Delta\chi\,dA
\le M\int|\Delta\chi|\,dA.
\]

The last bound follows pointwise from 0≤b_n≤M on S, and is independent
of n. Its right-hand side is finite since Δχ is continuous with compact
support. The theorem smooth_majorant_bound verifies this step with
all its integrability obligations.

## 5. Fatou's lemma

Fix z∈S∖F. If u(z)>0 then A_nu(z)+L(z)→+∞, so c_n(z)→1 and
s_n(z)→Δu(z)=(Δu(z))₊. If u(z)≤0, then c_n(z)=0 for every n and
Δu(z)≤0, so again s_n(z)→(Δu(z))₊. At punctures the extended
sources are zero; outside S their products with χ are zero.

Fatou's lemma for the nonnegative functions χs_n yields

\[
\int_{\mathbb C\setminus F}\chi(\Delta u)_+\,dA
\le\liminf_n\int\chi s_n\,dA
\le M\int|\Delta\chi|\,dA.
\]

The formal proof uses the extended nonnegative integral, so
integrability of the limiting density is never assumed.
This completes positive_part_cutoff.

## 6. Curvature −1 densities

Set u=log a−log b. Positivity and C² regularity of a,b give C²
regularity of u off F, and the curvature equations give Δu=a²−b².
Strict monotonicity of log and positivity of a,b show that u and
a²−b² have the same sign. The required sign conditions follow.
The bound for u₊ also provides the local upper bounds at punctures.
Applying the general result proves the displayed density estimate.
This deduction is checked in DensityDeficit.lean.

For a family of density pairs with a common M and fixed χ, the
right-hand side is uniform. Obtaining that common M from Poincaré
metric comparison is the remaining geometric task. The analytic
theorem alone does not establish the proposed dynamical conclusion.
