# Completing the paper: feasibility and resumption plan

Assessment dated **18 September 2026**. This is a plan, not additional proved
coverage. Mathematical development remains paused after Theorem 1.2. The
maintainer has requested private GitHub sharing and has deferred Palomar until
the full paper is ready. See [current proved coverage](../STATUS.md), the
[source audit](FULL_PAPER_SOURCE_AUDIT.md), and [private setup](PRIVATE_REVIEW.md).

## Assessment

Formalising the remaining main results looks achievable, but the remaining
work has several very different sizes. **Section 5 is the natural next project.**
The finite-set proof of Proposition 9.1 is elementary and avoids Bishop's
results completely. It supplies the case of Proposition 5.6 needed there.
The completed conformal geometry, Section 4 scaffolding, compact iterate
stability and entire-limit arguments substantially reduce the work.

Full logarithmic capacity is needed for Theorem 1.13, not for Section 5.
There are also two independent substantial developments: harmonic measure
for Theorem 1.11, and the positive-area boundary geometry of Theorem 1.14.
Thus postponing capacity does not make every other result a short corollary.
No insurmountable mathematical obstruction was found; no completion-time
estimate is justified for those new foundations yet.

The paper calls 7.2 a **lemma**. Its full arbitrary-two-domains statement is
not presently formalised. The explicit ray map and the straight-tail mapping
theorem needed for the completed constructions are proved. Section 5 need
not wait for the general Lemma 7.2.

## Remaining main results

| Result | Proposed route | Main outstanding work | Assessment |
| --- | --- | --- | --- |
| Finite Proposition 9.1 and finite Proposition 5.6 | Finite logarithmic sum; contraction inside the disc | Global univalence, end limits, Jordan subdomain and normalization | High confidence; bounded first milestone |
| Section 5 / Theorem 1.7 | Reuse Section 4; finite marked points at each approximation stage | Disconnected compact neighbourhoods, separation lemma, stage construction and countable scheduling | High confidence; substantial but likely less geometric work than Theorem 1.2 |
| Theorem 1.6 | Apply 1.7 to a closed disc with one escaping interior point and one bungee boundary point | Orbit-type propagation through a Fatou component | High confidence after 1.7; no harmonic measure needed for this deduction |
| Proposition 7.6(ii) | Combine continuum barriers with Section 5's alternating itinerary | Uniform interior escape while a boundary point is bungee | Plausible; the paper's sketch needs a separate stage invariant |
| Maverick definition, Lemma 8.1, finite versions of Proposition 6.1 | Spherical orbit separation and constant limit functions on wandering domains | Reusable spherical and normal-family dynamics | High confidence, subject to the general dynamics lemmas |
| Theorem 1.11 | Harmonic-measure exceptional-set estimate, then a countable cover | Rough-boundary harmonic measure; multiply connected wandering case | Major independent library development |
| Full 9.1, full 5.6, Theorem 1.13 | Evans potential and logarithmic integral; Proposition 6.1 | Standard logarithmic capacity and the full pointwise Evans theorem | Major independent library development |
| Theorem 1.14 | Singleton boundary target in Proposition 6.1 | Positive-area arc, winding boundary, collapsing conformal images, exact dimension | Major geometric development; does not require Evans |
| Proposition 7.6(i) | Existing compact-component topology plus general dynamics | Escaping Fatou-boundary implication and unbounded components of the fast escaping set | Separate foundational dynamics work |

## Finite interpolation without Bishop

After a Möbius change of coordinates, let the nonempty finite exceptional
set be `E = {p₁, …, pₙ} ⊂ ℝ`. On the upper half-plane use the principal branch:

\[
\psi(z)=\pi i-\frac1n\sum_{j=1}^{n}\log(z-p_j),\qquad
\psi'(z)=-\frac1n\sum_{j=1}^{n}\frac1{z-p_j}.
\]

Then `0 < Im ψ < π` and

\[
\operatorname{Im}\psi'(z)
=\frac1n\sum_j\frac{\operatorname{Im}z}{|z-p_j|^2}>0.
\]

A useful independent FunctionTheory lemma is that a holomorphic map on a
convex domain whose derivative has strictly positive real part is injective.
Integrate the derivative along the segment between two points. Apply this to
`−i ψ`. A nonzero derivative alone would not prove global injectivity.
The real part tends to `+∞` at every `p_j`, and to `−∞` at infinity.
Prove the required continuous spherical extension and compose with a suitable
explicit strip-to-half-strip map. Check its end normalization against the
existing log-sinh interfaces. Treat the empty exceptional set separately.

For Proposition 5.6, choose the required Jordan subdomain of the target
domain, then contract the source disc: `z ↦ φ(λz)`, with `λ < 1` close to one.
The contracted map is holomorphic past the closed disc; openness of the
prescribed target and compactness of the exceptional set retain the boundary
conditions. A finite set makes this last choice elementary. The full
proposition allows an arbitrary domain: its Jordan subdomain construction
must stay inside that domain, not fill holes through its complement.

## Section 5: what can be reused, and what must change

1. **Full compact sets may be disconnected.** The current
   [nested Jordan neighbourhoods](../EremenkosConjecture/NestedJordanNeighbourhoods.lean)
   cover continua. Complete the finite-union refinement of Lemma 2.9, with
   disjoint Jordan pieces and the appropriate nested intersections. Do not
   add a connectedness hypothesis to Theorem 1.7.
2. **Separation in Lemma 5.4 can probably avoid Koebe's quarter theorem.**
   Here is a proposed proof using the existing bounded Montel machinery.
   Normalize inverse maps `hₘ : 𝔻 → Uₘ` by `hₘ(0)=ζ`. If the images of a
   distinct marked point `ω` stay in a compact subdisc, extract convergent
   subsequences of these images and of `hₘ`. The limit sends two points to
   `ζ` and `ω`, so it is nonconstant. Nestedness puts its image in `K`; the
   open mapping theorem then puts a connected open image in `int K`,
   contradicting the prescribed separation of the two points. Thus the
   normalized images approach the unit circle. Handle eventual separation
   into different Jordan pieces separately. This proof is not yet Lean code.
3. **The available Arakelian theorem should suffice.** The paper uses a map
   continuous on a closed Jordan piece and holomorphic in its interior. For
   our neighbourhood-holomorphic interface, choose the approximation piece
   strictly inside the domain of that conformal map, while retaining a
   neighbourhood of the next compact set and all required marked points.
   Choose indices and tolerances after this shrink. The finite pieces and
   background remain separated. Verify these buffers explicitly; continuity
   on a boundary is not a neighbourhood-holomorphic hypothesis.
4. **Use compact iterate stability.**
   [UnivalentIterates](../EremenkosConjecture/UnivalentIterates.lean) does not
   require the compact source to be connected. Package the disjoint charts
   on an open union and retain disjoint images. The existing continuum stage
   should not be reused unchanged, since its chart geometry is connected.
5. **Schedule finitely many constraints per stage.** Every bungee point must
   return infinitely often, while successively larger finite sets of escaping
   points satisfy permanent escape bounds. Summable approximation errors must
   preserve old itinerary and boundary-trapping constraints. This is the
   principal application-level induction still to write.
6. **Prove the necessary Fatou-component facts explicitly.** Normality of
   these constructed interiors can use bounded reciprocals, since their
   iterates omit a fixed trapping disc. General component invariance and
   orbit-type propagation belong in ComplexDynamics. They are not supplied
   just by having definitions of Fatou and escaping sets.

For Theorem 1.6, take `K = closedUnitDisc`, `Z_I = {0}`, `Z_BU = {1}` in
Theorem 1.7. The disc is a wandering Fatou component, its interior is escaping
by orbit-type propagation, and its boundary contains a bungee point. This
proposed deduction proves the stated existence theorem without formalising
the paper's stronger mixed Lakes-of-Wada example or harmonic measure.

## Maverick points and harmonic measure

Start with the actual definition in 1.10 and prove Lemma 8.1. The sphere
already exists as `OnePoint ℂ`; a convenient chordal-distance interface still
needs checking/development. Entire functions are iterated on `ℂ`, then
included in the sphere; there is no value assigned to `f(∞)`. Constant limit
functions on wandering domains and coalescence of interior orbits need proofs.
Normality, Hurwitz and disjoint component images provide a plausible route.

Mathlib has harmonic mean-value and Poisson representation results, including
kernel bounds. The searched sources did **not** supply a verified
rough-boundary harmonic-measure theory. A disc Poisson measure alone does
not yet give the measure on the boundary of an arbitrary wandering domain.
One possible route is almost-everywhere radial limits of conformal maps and
pushforward of circle measures; another is a Perron/subharmonic construction.
Choose and validate one route before designing the public interface. Necessary
properties include measurability, basepoint-independent null sets, comparison
and holomorphic pullback. Brownian motion is not required.

Lemma 8.2 is the concrete analytic target. Its source is Osborne–Sixsmith,
[Lemma 4.1](https://arxiv.org/abs/1503.08077). Their argument compares boundary
exit sets with disjoint arcs of a fixed circle, uses Harnack bounds and
holomorphic pullback, and controls a limsup exceptional set. Preserve the
**summable measure bound**, which gives a Borel–Cantelli argument; merely
showing individual exceptional-set measures tend to zero is insufficient.
Theorem 1.11 then uses Lemma 8.1 and a countable covering argument.

The theorem includes **multiply connected wandering domains**. The paper
disposes of them using a separate general dynamics theorem. Showing only
that their interiors escape does not prove the required boundary assertion.
Record and prove the precise boundary/fast-escaping result used there, or
find a proof of the measure statement covering that case directly. A
simply-connected-only theorem must not be presented as the full Theorem 1.11.

## Capacity and Evans: a separate FunctionTheory project

For full Proposition 9.1 the finite average is replaced by a probability
measure `μ` supported on the compact exceptional set:

\[
\psi(z)=\pi i-\int\log(z-x)\,d\mu(x).
\]

Evans's theorem must supply a potential tending to `+∞` at **every** point
of the capacity-zero set. An almost-everywhere or quasi-everywhere assertion
is not sufficient for the boundary extension required here. The derivative
and univalence calculations then follow the finite case, with differentiation
under an integral on compact subsets away from the support.

Use a standard definition of logarithmic capacity (for example logarithmic
energy), and prove its connection to Evans potentials; do not define
capacity zero by the desired conclusion. Handle the extended logarithmic
kernel at the diagonal honestly: Lean's real logarithm is totalized at zero,
so it cannot by itself represent the required infinite potential. Expected
work includes probability measures on compact sets, truncated potentials,
semicontinuity/compactness arguments and changes of coordinates. Empty sets
and choosing a Möbius pole outside the exceptional set need separate checks.

The paper points to Garnett–Marshall, Appendix E, especially Theorem E.2.
This assessment checked the required statement and its use in the paper,
**not a complete reconstruction of that book's proof**. Reading and decomposing
the Evans proof is the first task before estimating this development.
Once full 5.6 and Proposition 6.1 are available, Theorem 1.13 uses concentric
discs and is a relatively small application. In its page-28 computation the
actual image is `(r/rₘ) Ξ`, tending to `Ξ`; the printed identity with `Ξ`
should be replaced by that convergence in Lean.

## Positive-area mavericks and Proposition 7.6

Theorem 1.14 uses only singleton targets `Ξⱼ={1}` in Proposition 6.1, so
Evans is unnecessary. Its independent obligations are substantial:

- Construct a Jordan arc of positive planar Lebesgue measure.
- Construct the two-sided accumulating analytic curve and prove the precise
  complementary-domain and boundary properties used on page 28.
- Prove that the conformal images of the whole positive-area arc collapse
  to one boundary point. Existing crosscut and length-area arguments are
  promising; interior kernel convergence alone does not establish this.
- Prove **equality** of the non-maverick set's Hausdorff dimension with one.
  Containment in an analytic curve gives only the upper bound. A possible
  lower-bound route uses Theorem 1.11 and harmonic measure on a regular
  boundary arc, with reflection giving local absolute continuity relative
  to arc length. This would avoid a general Makarov theorem, but remains
  a proposed argument needing verification.

For 7.6(i), the supporting
[compact-component topology](../EremenkosConjecture/CompactComponentHoles.lean)
is already present. Missing general facts concern escape from Fatou-boundary
information and the unboundedness of fast-escaping components. Construction-
specific fast-escape estimates do not establish those facts. For 7.6(ii),
combine the barriers from 1.2 with Section 5 scheduling, keeping a whole open
disc escaping and a boundary point bungee. Control the interior through a
compact exhaustion. This requires a new invariant, not just a citation of 1.7.

## What would “the full paper” cover?

Keep three coverage lists: main new theorems; numbered preliminary results;
additional assertions in remarks. Completing the first is already a valuable
milestone, but is not identical to proving every assertion in the paper.
Additional scope includes the full continuous-data Arakelian theorem (2.2),
the general unbounded forms of Lemma 2.3 and Corollary 2.7, full Lemma 7.2,
common omega-limit refinements (5.7), and unbounded-domain variants (7.3–7.4).
The infinite-order and class-B assertions in Remark 7.5 involve further
value-distribution/logarithmic-tract results, including
Denjoy–Carleman–Ahlfors. The paper's open questions are not proof targets.

## Recommended restart order and completion criteria

1. Review this assessment and the exact theorem statements with the authors.
2. In FunctionTheory, prove the finite logarithmic interpolation lemma and
   finite 5.6, with genuine global injectivity and all boundary limits.
3. In EremenkosConjecture, prove the disconnected Jordan refinement and
   separation lemma; then Section 5 with neighbourhood-holomorphic data.
   Add the required reusable Fatou-component facts to ComplexDynamics.
4. Finish Theorems 1.7 and 1.6, then 7.6(ii) and finite-target Proposition 6.1.
   Review exact coverage before choosing the next major foundation.
5. Develop harmonic measure and the required general dynamics for 1.11 and
   7.6(i). Independently assess the detailed Evans proof for 1.13 and the
   positive-area geometry for 1.14; choose their order by collaborator interest.
6. Review all remaining preliminary results and remarks against the agreed
   meaning of a full-paper submission. Only then revisit Palomar.

At every milestone require the exact advertised statement, explicit treatment
of empty/disconnected/rough-boundary cases, a clean Lean build, source scan,
and standard-axiom audit. Proposed proofs in this document must never be
imported as assumptions or recorded as completed mathematics. No new Lean
proofs were added during this assessment.
