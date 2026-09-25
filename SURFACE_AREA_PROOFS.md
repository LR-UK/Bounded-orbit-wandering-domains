# Hyperbolic area gain on Riemann surfaces

Mathematical proof note, 24 September 2026. This note is on the research
branch. The statements below have mathematical proofs using classical
surface analysis; they are **not yet unconditional Lean theorems in this
repository**. In particular, the surface boundary and cusp lemmas used
below have not yet been ported. The stable 1.3.0 release is unchanged.

Update, 25 September: intrinsic metrics/area, component covers, comparison
in covering-disc form, finite-puncture convergence, and the compact remote
estimate in a hyperbolic ambient surface are now checked. See
`DomainRemoteArea.remote_compact_domainAreaGain` and `WORKSTREAMS.md`.
The point-removal and noncompact-cutoff parts below remain proof notes.
The user directs us to the intrinsic comparison in Lemmas 2.2–2.4 of the
paper (Mihaljević–Rempe/Minda); the alternative normal-family proof below
is retained in Lean but should not become a further convergence project.

All hyperbolic metrics have curvature -1. No simple-connectivity, genus,
finite-connectivity or finite-total-area assumption is imposed.

## 1. Intrinsic meaning of area gain

For hyperbolic Riemann surfaces Y ⊂ X, let g_Y = exp(2u) g_X on Y.
Schwarz–Pick gives u ≥ 0. For a measurable W ⊂ Y, define

    Gain(X,Y;W) = ∫_W (exp(2u) - 1) dA_X.

Equivalently, in a holomorphic coordinate this integrates
(ρ_Y² - ρ_X²) dx dy. The integrand is a nonnegative two-form, invariant
under coordinate changes. This definition never subtracts two infinite
total areas. For disconnected open sets, use the Poincaré metric on each
component, assuming those components are hyperbolic.

## 2. Puncture theorem

**Theorem.** If X is a hyperbolic Riemann surface and p ∈ X, then

    Gain(X, X \ {p}; X \ {p}) ≤ 2π.

Consequently, removal of a finite set E costs at most 2π |E|. The same bound
holds when the gain is integrated over any measurable subset of X \ E.

### Proof on a relatively compact bordered surface

First let D be a relatively compact connected domain with smooth boundary
in a Riemann surface, and let p ∈ D. Choose a smooth conformal background
metric g_0 near its closure. Write the complete metrics of D and D \ {p}
as exp(2v) g_0 and exp(2w) g_0, respectively, and put u = w - v ≥ 0.

Use the Laplacian with sign Δ = ∂_x² + ∂_y² in a flat coordinate.
The curvature equations give, away from p,

    (Δ_0 u) dA_0 = dA_(D\{p}) - dA_D.                       (1)

There are two boundary contributions in Green's formula.

At the original smooth boundary, the complete hyperbolic metrics have
the same first two terms of their boundary expansion. In terms of the
background distance t to the boundary,

    v = -log t + (κ/2)t + O(t²),
    w = -log t + (κ/2)t + O(t²).

The expansions hold with derivatives; κ is the same background boundary
curvature in both expressions. Thus u = O(t²) and its first normal
derivative is O(t). The flux over the curves t = ε tends to zero.
Only the local smooth-boundary expansion is being used for w; an interior
cusp does not change its leading boundary terms.

Near p, choose a cusp coordinate ζ with ζ(p) = 0. The punctured metric
is |dζ| / (|ζ| log(1/|ζ|)), while the original metric is smooth and positive.
Thus, with r = |ζ|,

    u = -log r - log log(1/r) - log ρ_D(ζ).

On an inner circle r = ε, the outward normal for the region being
integrated points towards the puncture. Its flux is

    -∫_0^(2π) ε ∂_r u(ε exp(iθ)) dθ
      = 2π - 2π/log(1/ε) + O(ε)  →  2π.

Normal-derivative flux is conformally invariant, so this computation is
also the flux for g_0. Green's formula applied to (1), followed by
exhaustion of D \ {p}, gives

    Gain(D, D \ {p}; D \ {p}) = 2π.                       (2)

The integrand is nonnegative, so this limiting integration does not
presuppose its integrability. The argument also works for a compact
hyperbolic X directly: there is no outer boundary contribution.

### Exhaustion of an arbitrary noncompact surface

Take a nested smooth relatively compact exhaustion D_j of X, containing p.
The Poincaré densities of D_j decrease locally uniformly to that of X;
the densities of D_j \ {p} decrease locally uniformly to that of
X \ {p}. These are standard monotone-exhaustion properties of the complete
Poincaré metric. The latter exhaustion is allowed to have the fixed cusp.

Use any smooth positive background area measure on X, and extend each
nonnegative density difference by zero outside D_j \ {p}. It converges
pointwise off p to the required intrinsic density difference. By Fatou
and (2), the limiting integral is at most 2π.

For a finite set, remove its points successively. At every surviving point
the differences telescope. Integrate on the final domain and bound each
step by its integral over the entire corresponding once-punctured domain.
This gives the asserted 2π |E| bound. Points already outside the old domain
make no contribution.

## 3. Uniform bound for remote removal

Here is a precise form with the uniformity needed for the wandering-domain
argument. Importantly, it bounds the gain, not the new total area.

**Theorem.** Let S be a fixed Riemann surface, K ⊂ S closed, and L ⊂ S
compact with L ∩ K = ∅. There is C(S,K,L) < ∞ such that, for every open
Ω ⊂ S whose components are hyperbolic,

    Gain(Ω, Ω \ K; L ∩ Ω) ≤ C(S,K,L).                    (3)

Neither K nor Ω needs finite connectivity. K need not be compact.
When K is allowed to be noncompact, closedness and separation of L alone
do not suffice. However, if K is compact, L may be merely closed and
disjoint from K, as proved in the extension below. Thus the earlier
restriction on L was stronger than necessary for compact removed sets.

### A fixed hyperbolic ambient surface

First suppose S itself is hyperbolic. Let χ ≥ 0 be a smooth compactly
supported cutoff, equal to 1 on a neighbourhood of L, with support
disjoint from K. For nonempty K and nonempty support choose δ > 0 such that

    d_S(supp χ, K) ≥ δ.

The empty cases are immediate. Put

    M = log coth(δ/2),
    C = M ∫_S |Δ_S χ| dA_S.                              (4)

This is finite and depends only on the fixed data, not on Ω.

**Uniform logarithmic comparison.** For z ∈ Ω \ K, choose a universal
cover q : D → Ω of its component, with q(0) = z. Viewed as a holomorphic
map to S, q decreases hyperbolic distance. Consequently the disc of
hyperbolic radius δ maps away from K whenever d_S(z,K) ≥ δ. Its Euclidean
radius is r = tanh(δ/2). Apply Schwarz–Pick to q restricted to rD, now
mapping into Ω \ K. Since q is a local hyperbolic isometry into Ω,

    1 ≤ ρ_(Ω\K)(z) / ρ_Ω(z) ≤ 1/r = coth(δ/2).           (5)

Thus the logarithmic ratio is between 0 and M on supp χ, uniformly in Ω.
This uses a disc upstairs; no assertion that the corresponding ball
downstairs is simply connected or embedded is needed.

**First take Ω = S \ P with P finite.** On a neighbourhood of supp χ,
outside P, the logarithmic ratio u satisfies

    (Δ_S u) dA_S = dA_(Ω\K) - dA_Ω ≥ 0.                 (6)

By (5), u is a bounded nonnegative subharmonic function there. Its finitely
many apparent singularities at P are removable as subharmonic functions.
Its distributional Laplacian is a positive measure and dominates the
ordinary density difference off P. Therefore

    Gain(Ω, Ω\K; L∩Ω)
      ≤ ∫ χ (dA_(Ω\K) - dA_Ω)
      ≤ ⟨Δ_S u, χ⟩
      = ∫ u Δ_S χ dA_S
      ≤ M ∫ |Δ_S χ| dA_S = C.                           (7)

These steps are local near supp χ. They do not require the ratio to be
bounded near K, or any smoothness of the boundary of K.

**Pass to an arbitrary Ω.** Write A = S \ Ω. Since S is second countable,
choose increasing finite sets P_j ⊂ A whose union is dense in A. On Ω,
the Poincaré densities of S \ P_j increase to the componentwise density
of Ω; on Ω \ K the densities of S \ (P_j ∪ K) increase to that of Ω \ K.

For completeness, this kernel-convergence assertion can be seen by
lifting normalised extremal discs to the fixed universal cover of S.
The lifts are maps D → D and hence form a normal family. A nonconstant
limit avoids every eventually omitted point by Hurwitz, and its open
image therefore avoids the closure A. Schwarz–Pick and the extremal
characterisation identify the limiting density. A fixed disc in the
limiting domain prevents the relevant normalised limit from being constant.
The same argument applies with the additional fixed closed set K.

Apply Fatou on L ∩ Ω to the nonnegative differences in (7). The bound C
is independent of j, so (3) follows with the explicit constant (4).

### Removing the assumption that the ambient S is hyperbolic

If K has at most two points, the finite-puncture theorem directly gives
a bound of 2π |K| for each Ω, and hence (3).

Otherwise choose three distinct points F ⊂ K. The surface S \ F is
hyperbolic. This standard consequence of uniformisation includes the
exceptional ambient surfaces (sphere, plane, punctured plane and torus).
The set K \ F is closed in S \ F, and L is still compact and disjoint
from it. Apply the hyperbolic-ambient result to Ω \ F inside S \ F.

The gain from Ω to Ω \ F is at most 6π by the puncture theorem. Add the
remote-removal bound in S \ F, using the telescoping density differences
on L ∩ Ω. This proves (3) with

    C(S,K,L) = 6π + C(S\F, K\F, L).

The auxiliary 6π is a permissible uniform constant, not a claim of
sharpness. The single-puncture constant 2π remains sharp, already on the
disc and on compact hyperbolic surfaces.

### Extension: compact K and closed, possibly noncompact L

**Theorem.** The uniform estimate (3) also holds when K is compact and L
is closed and disjoint from K. In particular, the area gain can be
integrated all the way out to the ends of the original domain.

More generally, in a hyperbolic ambient surface S the argument works if
there is a smooth function 0 ≤ χ ≤ 1 such that χ = 1 on L, χ vanishes
on a neighbourhood of K, and its differential has compact support.
The support of Δ_S χ is then compact and disjoint from K. Choose δ > 0
as a lower bound for its distance from K, and again put

    C = log coth(δ/2) ∫_S |Δ_S χ| dA_S.                 (8)

If Δ_S χ vanishes identically, the estimate below gives zero directly.
The uniform logarithmic comparison (5) is needed only on the support
of Δ_S χ, not throughout the noncompact measured region.

For compact K and closed disjoint L, choose a smooth compactly supported
ψ with 0 ≤ ψ ≤ 1, equal to one near K, and with support disjoint from L.
Then χ = 1 - ψ has exactly these properties. This reverses the location
of the cutoff: its derivatives are supported near the removed set,
while χ is one throughout the distant region.

To justify integration with this noncompactly supported χ, exhaust Ω by
relatively compact smoothly bordered open sets D_j (finite unions are
allowed). On D_j \ K let

    u_j = log(ρ_(D_j\K) / ρ_(D_j)).

Near K the cutoff is identically zero, so no regularity of K is needed.
At the other artificial boundaries, both hyperbolic metrics have the
same leading boundary expansion: u_j = O(t²), ∂_ν u_j = O(t).
Hence both terms in Green's boundary expression
χ ∂_ν u_j - u_j ∂_ν χ tend to zero. Where these boundaries meet K,
χ and its derivatives already vanish. Thus

    ∫_(D_j\K) χ (dA_(D_j\K) - dA_(D_j))
      = ∫_(D_j\K) u_j Δ_S χ dA_S
      ≤ C.

The constant is independent of j and of Ω. Metric convergence under
exhaustion and Fatou give the bound on L ∩ Ω. This argument handles the
boundary-at-infinity issue; applying compact-support Green's formula
directly to χ without this justification would not be valid.

For a nonhyperbolic ambient S, use the same auxiliary-puncture reduction
as before. Choose F ⊂ K. The cutoff χ remains zero near F, and its
differential is still compactly supported in S \ F. The general cutoff
criterion above therefore applies even though K \ F need not be compact
in S \ F. Add the at-most-6π auxiliary puncture cost. Finite K of at most
two points is handled directly by the puncture theorem.

### Extension: disjoint accumulation sets of ends

**Theorem.** Let S be a connected, Hausdorff, second-countable Riemann
surface without boundary. Let K and L be disjoint closed subsets of S.
Suppose that no Freudenthal end belongs to both the closure of K and the
closure of L in the end compactification of S. Then there is a finite
constant C(S,K,L), independent of the open set Ω, such that

    ∫_(L∩Ω) (dA_(Ω\K) - dA_Ω) ≤ C(S,K,L),

whenever the components of Ω are hyperbolic. Both K and L may be
noncompact. As throughout, this is the integral of the nonnegative
density difference, not a subtraction of infinite areas.

A concrete equivalent separation condition is that there is a compact
set B ⊂ S such that no component of S \ B meets both K and L. One may
enlarge B to a compact smoothly bordered subsurface. To see why the end
condition supplies B, use an exhaustion by compact smoothly bordered
subsurfaces with finitely many complementary components. If at every
stage a complementary component met both sets, the finite-branching
tree of these components would have a nested infinite branch. It would
define an end accumulated on by both K and L, a contradiction. Conversely,
such a compact separator gives every end a neighbourhood missing at
least one of the sets. The compact-surface case is immediate.

Assign value zero to each exterior component meeting K and value one to
each meeting L; components meeting neither can be assigned either value.
After enlarging the compact transition region, smooth interpolation
inside that region gives

    0 ≤ χ ≤ 1,  χ = 0 near K,  χ = 1 near L,
    supp(dχ) compact.

For clarity about this interpolation, there are only finitely many
exterior components. Outside a larger compact subsurface their assigned
constant values are compatible with the prescribed values on K and L.
The resulting closed zero and one sets are disjoint; smooth separation
on the intervening compact region preserves those prescribed values.

Apply the preceding compactly supported differential criterion. If S is
hyperbolic, put T = supp(Δ_S χ). For nonempty T and K choose
0 < δ ≤ dist_S(T,K). The explicit bound is

    C(S,K,L) = log coth(δ/2) ∫_S |Δ_S χ| dA_S.

Empty T or K gives zero directly. The Schwarz comparison is needed only
on T; the integration over the possibly infinite-area set L is justified
by the smoothly bordered exhaustion already given above. For a
nonhyperbolic ambient surface, the same auxiliary-puncture reduction
applies: χ is zero near the selected punctures in K, so its differential
remains compactly supported on the punctured surface. Add at most 6π.

Thus the effective hypothesis is a compact transition region, rather
than compactness of either individual set. Separation of their end
accumulation sets guarantees precisely such a region. No converse about
finiteness of area gain is asserted: sets sharing an end may still have
finite gain for other reasons.

### Closed K and closed L without compactness: counterexample

Take S = Ω = H = {x + iy : y > 0}, with

    K = {x + iy : 0 < y ≤ 1},
    L = {x + iy : y ≥ 2}.

Both sets are closed in H and their hyperbolic distance is log 2 > 0.
But Ω \ K is the translated upper half-plane {y > 1}, so its curvature
-1 density is 1/(y-1), whereas ρ_Ω = 1/y. The gain on L is

    ∫_R ∫_2^∞ ((y-1)^(-2) - y^(-2)) dy dx
      = ∫_R (1/2) dx = ∞.

Thus even positive hyperbolic separation does not replace all compactness
or localisation assumptions. A finite set of punctures has finite global
cost; an unbounded removed set can create the same positive gain along
infinitely much of the measured region.

This example does not satisfy the end-separation hypothesis: H is
homeomorphic to the plane and has a single Freudenthal end, accumulated
on by both K and L. Freudenthal ends must not be confused with individual
points on a conformal or visual boundary.

## 4. What must be formalised

These are genuine geometric obligations, not hypotheses to hide inside
an area-data structure and then call the requested theorem complete:

1. Descend the curvature -1 metric/area from the supplied disc cover, with
   chart and cover independence and the conformal curvature equation.
2. The local smooth-boundary and cusp statements, Green's formula on
   bordered surfaces, and smooth exhaustion with metric convergence.
3. The intrinsic Schwarz–Pick comparison (5), distributional cutoff
   integration on charts, and finite-puncture approximation of closed sets.

The project already has the planar analogues, its generic Fatou transfer
lemma `AreaDeficit.limiting_gain_bound`, and its generic finite-area
cancellation theorem. The current `Surfaces.DiscCover` is only the supplied
cover interface; it does not yet discharge the obligations above.

## References for the classical analytic ingredients

Rafe Mazzeo and Michael Taylor, *Curvature and Uniformization*:
https://mtaylor.web.unc.edu/wp-content/uploads/sites/16915/2018/04/unif7.pdf

- Section 3, Proposition 3.1 and Remark 3.5: smooth boundary expansion and
  its first geometrically determined coefficient.
- Section 7, Proposition 7.1 and Corollary 7.3: exhaustion and the complete
  Poincaré metric on a general surface.
- Formula (1.5): the punctured-disc cusp model.

The area-gain deductions in this note are the argument proposed here,
not a claim that the cited paper states these two area-gain theorems.

For the standard end-compactification language and separation of closed
sets of ends by a compact region, see Simone Cecchini, Daniel Räde and
Rudolf Zeidler, *Nonnegative scalar curvature on manifolds with at least
two ends*, Journal of Topology 16 (2023):
https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/topo.12303
The area estimate and its application to end-separated sets are the
deductions in this note, not results attributed to that paper.
