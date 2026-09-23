# Covering-based continuation of the frozen Palomar submission

**Historical development record.** The covering and area obligations described
below have now been proved. Both final theorems compile without the classical
metric hypothesis. See [COMPLETION.md](../riemann-port/COMPLETION.md) for the
current results, proof outline and verification.

The submission of 23 September 2026 is preserved separately as
`bounded-wandering-palomar-v0.12.0-2026-09-23.zip` (SHA-256
`9021a78fe4274c1224c76ee955cc3d6335dbcc75f355231bb96556605f7f55d3`).
This directory is a separate development copy. `Challenge.lean`, `Solution.lean`
and the original submission metadata retain their frozen statements.
The new results are in `CoveringSolution.lean`.
The reported `simpa` linter warning in `HolomorphicLifting.lean` is removed
in this development copy by using `simp`; the frozen archive is untouched.

## Reduced classical input

`ClassicalDiscCoveringsAndArea` states that, for every finite P ⊂ ℂ with at
least two points, there is a holomorphic covering p: D → ℂ ∖ P whose induced
curvature −1 density has total area 2π(|P| − 1).

The covering condition uses Mathlib's `IsCoveringMapOn` for the restriction
of p to the open unit disc, together with holomorphicity, containment of the
image and surjectivity. Nonvanishing derivatives are **proved**, not assumed.
The disc is simply connected by convexity, so the covering is universal.

The density is defined by

\[
\rho_p(z)=\frac{2}{(1-|w|^2)|p'(w)|},\qquad p(w)=z,\quad w\in\mathbb D.
\]

An arbitrary preimage is selected using Mathlib's `Function.invFunOn`.
The new proofs establish independence of the choice. Values at punctures
are irrelevant to the total-area integral, because the puncture set is finite.

## Proof of all former density assumptions

1. A covering is a local homeomorphism. Restricting its open local charts
   gives open subsets of the plane on which p is injective. Tau Ceti's
   holomorphic injection theorem gives p′ ≠ 0 throughout D.

2. Given a holomorphic g: D → S and w ∈ p⁻¹(g(0)), lift g through p with
   prescribed initial point w. Mathlib's covering-lift theorem supplies the
   continuous lift; the holomorphic inverse function theorem supplies its
   complex derivative. If h is the lift, then
   h(0)=w and h′(0)=g′(0)/p′(w). Disc Schwarz–Pick therefore gives
   \[
   \frac{2}{(1-|w|^2)|p'(w)|}|g'(0)|\le 2.
   \]

3. A Möbius automorphism m of D with m(0)=w has
   |m′(0)|=1−|w|². For g=p∘m the preceding inequality is an equality.
   This proves the extremal-disc property at every fibre point.

4. For v,w in the same fibre, apply the inequality computed at v to the
   extremal disc computed at w. Its derivative is nonzero, so division gives
   ρ(v) ≤ ρ(w), where these denote the two candidate density values downstairs.
   Reverse the roles to obtain equality. This proves fibre independence.
   Positivity, Schwarz–Pick and extremal discs for the chosen density follow.

5. On a neighbourhood admitting a holomorphic inverse branch h, fibre
   independence gives
   \[
   \rho_p(z)=|h'(z)|\frac{2}{1-|h(z)|^2}.
   \]
   The existing pullback lemmas prove C² regularity and
   Δ log ρ_p = ρ_p². These are the curvature −1 conventions used throughout.
   No regularity of the globally selected preimage is required.

6. Choose one such covering for each P and use the assumed total-area
   formula. This constructs `ClassicalHyperbolicMetrics`, the complete former
   input package. The two existing dynamical theorems now apply directly.

The entire-function theorem still assumes boundedness of **one point orbit**,
not of the union of the Fatou components. It has no auxiliary assumptions of
simple connectivity or eventual injectivity. The local theorem retains its
previous local dynamical hypotheses.

## What remains for an unconditional theorem

Two statements remain unproved here:

* Existence of a holomorphic disc covering of every finitely punctured plane
  with at least two finite punctures.
* The total-area formula for the metric induced by such a covering.

More explicitly, the missing existence theorem has conclusion

```lean
∀ P : Finset ℂ, 2 ≤ P.card → ∃ p : ℂ → ℂ,
  AreaDeficit.IsHolomorphicDiscCovering p ((↑P : Set ℂ)ᶜ)
```

The missing area theorem should give, for a covering `p` of that domain,

```lean
(∫⁻ z : ℂ, ENNReal.ofReal
  ((AreaDeficit.coveringDensity p z)^2 / (2 * Real.pi))) =
  (P.card - 1 : ℕ)
```

These are written here as outstanding obligations, not introduced as axioms
or as proved Lean declarations.

The project currently proves a Green identity by ordinary integration by
parts. It does **not** contain a proof of Gauss–Bonnet. References to
Gauss–Bonnet in the earlier metric-input files describe the classical
justification of the area hypothesis, not an imported proof.

General Gauss–Bonnet is not necessary for the model area calculation.
In the upper half-plane with density 1/y, the ideal triangle with vertices
−1, 1, ∞ has the iterated area integral
\[
\int_{-1}^{1}\int_{\sqrt{1-x^2}}^{\infty}\frac{dy\,dx}{y^2}
=\int_{-1}^{1}\frac{dx}{\sqrt{1-x^2}}=\pi.
\]
`IdealTriangleIntegral.lean` proves this iterated integral directly, using
the derivative of arcsine and the improper integral of y⁻². Both the
integrability argument at x=±1 and the vertical improper integral are included.
`IdealTriangleArea.lean` now proves the two-dimensional area using Tonelli,
identifies it with Mathlib's `volume` on `UpperHalfPlane`, and applies Mathlib's
Möbius-invariance theorem. It also proves finite additivity for a given disjoint
collection of Möbius images of the model triangle, allowing a null exceptional
boundary. This does not establish the required geometric decomposition or its
identification with the covering-induced metric on a punctured sphere.
There should be 2(|P|−1) ideal triangles for the sphere punctured at P and ∞.
That decomposition has not been formalised in this development.

For covering existence, a useful accessible source is Fisher, Hubbard and
Wittner, *A proof of the uniformization theorem for arbitrary plane domains*,
Proc. AMS 104 (1988), 413–418:
https://pi.math.cornell.edu/~hubbard/FisherHubbardWittner.pdf .
It combines covering-space theory with a Koebe construction and uses the
modular covering in its reduction to bounded domains. Thus it avoids general
Riemann-surface uniformisation but does not eliminate that preliminary input.

Bargmann, *Normal families of covering maps*, J. Anal. Math. 85 (2001),
291–306, is another candidate:
https://link.springer.com/article/10.1007/BF02788084 .
Only the publisher abstract was accessible during this continuation; the
full proof has not yet been audited for formalisation dependencies.

## Further covering-existence steps

`CoveringExhaustion.lean` proves the numerical exhaustion argument. If
0 ≤ rₙ ≤ 1, dₙ ≥ c > 0, and

    dₙ₊₁ ≤ (2√rₙ / (1+rₙ)) dₙ,

then rₙ → 1. The proof shows that dₙ decreases to a limit and bounds
c(1−√rₙ)² by 2(dₙ−dₙ₊₁). This proves convergence without assuming that
the radii are monotone. Construction of maps satisfying these inequalities
is still required.

`CoveringLimitBranches.lean` proves persistence of inverse branches under
locally uniform convergence. The inverse branches map a connected open set
into the disc; a value at a moving base point converges to a point strictly
inside the disc. Montel selection and the maximum-modulus principle keep
the limiting branch inside the disc. The inverse identity passes to the
limit, so the limiting branch is holomorphic and injective. This theorem
uses the existing FunctionTheory inverse-limit lemmas.

For the square-root construction, see also Bishop's lecture notes,
*Introduction to Transcendental Dynamics*, Section 1.2:
https://www.math.stonybrook.edu/~bishop/classes/math627.S13/itd.pdf .
The numerical lemma and inverse-branch lemma above are independently written
Lean proofs using existing Mathlib and FunctionTheory results.

These are proved steps towards covering existence, not a proof of covering
existence. A complete exhausting construction and its global covering
verification are still missing. The unconditional dynamical theorem has
therefore **not** been obtained.

## Checking this development

Version 0.14.0 passed the combined build and audit on 23 September 2026.
The build completed 4041 jobs with no unexpected warnings. The audit checks
35 axiom reports, including the new metric construction,
both new dynamical corollaries, and the ideal-triangle integral. Every report
uses only `propext`, `Classical.choice`, and `Quot.sound`. The two original
Challenge/Solution theorem types and nine supporting definitions also match.
The only proof holes in project source are the two deliberate holes in the
frozen Challenge file. The reported lifting warning and the analogous
warnings in the new modules have been removed. Vendored compatibility edits
are recorded in `DEPENDENCY_COMPATIBILITY.md`. The verification script rejects
all build warnings except the two deliberate `sorry` warnings from Challenge;
it retains the informational axiom reports. The authoritative result is in
`verification/submission.json`.

Run `lake build CoveringSolution BoundedWanderingDomains` and
`lake env lean verification/CoveringAxioms.lean`.
The original submission checks remain available through
`python3 scripts/verify_submission.py`.
The packaging script writes `bounded-wandering-covering.zip`, so it does not
overwrite the original submission archive.

This development is not a Palomar submission and has not been run through
Palomar's official comparator or independent proof checker.
