> **Submission copy, 23 September 2026.** Toolchain and dependency pins have
> been updated to Lean 4.35.0-rc2 and Mathlib
> `065356127b1dc0016f66b7283ce0ce2c4055aa55` for the unconditional submission.
> The records below describe the supplied Lean 4.34 snapshot. Current checking
> covers the modules imported by the root submission targets; see the root
> VERIFICATION.md. A fresh full standalone audit of this dependency is not claimed.

# Project status

**Runge and neighbourhood-holomorphic Arakelian approximation complete — 16 September 2026.**

`ComplexApproximation.arakelian_approximation` now proves uniform entire
approximation on a closed set satisfying the explicit no-bounded-components
and bounded-exhaustion-holes conditions. Its input is holomorphic on an open
neighbourhood. The actual-domain and closed-set interfaces are in
`ArakelianLocalDomain.lean`; the public gallery includes `MainTheorems.arakelian`.
The continuous-on-the-set, interior-holomorphic version is not asserted.

The proof follows the Runge case of Rosay–Rudin (1989). New checked foundations
include the smooth compact-support Cauchy–Pompeiu formula, a smooth right inverse
for the Cauchy–Riemann defect, uniform estimates, cutoff gluing, filled-disk
topology, and limits of functions holomorphic on expanding neighbourhoods.
See `docs/ARAKELIAN_PLAN.md` and `PROOF_MAP.md`.

All requested forms of Runge's approximation theorem are proved in Lean:

| Theorem | Result |
| --- | --- |
| `Runge.rational_approximation` | Uniform polynomial-quotient approximation on an arbitrary compact set |
| `Runge.prescribed_poles_approximation` | Denominator zeros confined to an allowed set meeting every bounded complement component |
| `Runge.polynomial_approximation` | Uniform polynomial approximation when the complement is connected |

The function is analytic on an open neighbourhood of the compact set.
`Runge/Holomorphic.lean` also provides all three results directly from complex
differentiability on that neighbourhood. All error bounds are strict and
uniform for any prescribed positive tolerance.

## Wandering-dynamics approximation inputs

The complete library, original Runge statement checks and all **160 selected
axiom reports** passed on 22 September 2026. The new
[analytic-increment formulation](Runge/MeromorphicIncrement.lean) chooses
internal representatives with analytic errors on full neighbourhoods.
[Marked local-degree preservation](Runge/MarkedMeromorphicApproximation.lean)
follows by finite-jet interpolation. Only propext, Classical.choice and
Quot.sound occur in the selected reports.

The latest additions prove two-point nonseparation, filling of disjoint compact
unions, a full compact exhaustion separating an escaping family, full barrier
neighbourhoods, and polynomial approximation preserving marked local degrees.
These supply the entire escaping construction in WanderingDynamics.

## Validation

`scripts/verify.ps1` checks:

- `lake build ComplexApproximation`: the complete proof library builds.
- `lake env lean scripts/Audit.lean`: all 158 selected results, including the
  three main theorems and their holomorphic interfaces, use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- A source-integrity scan rejects proof placeholders, added axioms, and native
  decision proofs throughout both libraries.
- `lake build RungeTargets`: the original rational and polynomial statements
  and the explicit prescribed-pole statement follow from the completed proofs.

No original Runge target remains open. The former target placeholders have been replaced by
applications of the proved theorems. The proof library does not import the
target compatibility library.

Evidence: `verification/build.log`, `verification/axioms.log`, and
`verification/targets.log`.

## Pinned environment

- Lean: 4.34.0, Windows x86-64.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- The Mathlib working tree is unmodified.

The arbitrary-compact proof uses a smooth compactly supported extension and
Green's theorem, rather than the originally proposed grid-boundary construction.
The subsequent component and factorisation arguments provide prescribed poles
and the polynomial conclusion. See `docs/PROOF_PLAN.md` for the complete route.

## Machine setup

The pinned dependencies and their official compiled cache are installed locally.
Select the pinned Lean 4.34.0 toolchain through Elan, or pass its executable
to `python scripts/verify.py --lake <path-to-lake>`. The Windows entrypoint
also accepts `scripts/verify.ps1 -LeanBin <toolchain-bin-directory>`.

Additional Mathlib cache files were retrieved with system certificate validation
when the standard cache downloader encountered a Windows certificate issue.
No library source or proof axioms were changed to work around setup problems.

The initial verification was performed locally before repository upload.

## Local-domain interfaces

All three approximation theorems now also accept a function `f : U → ℂ` on
an open neighbourhood, or `f : K → ℂ` with a holomorphic neighbourhood
extension. `Runge.IsHolomorphicFunctionOn` uses local holomorphic
representatives. Values outside the stated domain are not part of these inputs.
The original ambient-function statements are preserved.

The public challenge at https://lean-lang.org/eval/problems/runge_theorem/
does explicitly use `f : ℂ → ℂ`. This is a calculus interface convention;
it does not assert that the function is holomorphic on the whole plane.

`Runge.exists_polynomial_separator` supplies a polynomial equal to one at a
specified point outside a full compact set and uniformly smaller than one
half on that set. It supports the full-neighbourhood construction in the
EremenkosConjecture project.


## Statement and navigation revision

The public statements are gathered in `ComplexApproximation/MainTheorems.lean`
with explicit types and references to their completed proofs. `MAIN_RESULTS.md`
explains the hypotheses; `PROOF_MAP.md` shows the mathematical proof routes;
`CLASSICAL_RESULTS.md` catalogues reusable auxiliaries. The generated module
index and direct-import graph are maintained by `scripts/update-map.py`.
The statement gallery is part of the library build and selected axiom audit.
This is not yet a Palomar Challenge/Comparator submission.

`Topology/Nonseparation.lean` generalises the application's continuous-logarithm
proof to disjoint closed sets. It proves the relative-complement criterion
for full compact subsets of arbitrary plane domains and preservation under
homeomorphisms `U ≃ₜ V`, without an ambient extension. The application now
imports its compact disjoint-union consequence from this library.

## Unbounded half-strip geometry (17 September 2026)

The checked additions include Arakelian invariance under plane homeomorphisms,
adjoining a set inside a uniformly separated horizontal gap, the U-shaped band
and inner half-strip model, and simultaneous entire approximation on the
three-piece configuration. The explicit map `log(sinh z)` is holomorphic and
injective on the right half-strip; derivative bounds and a positive real-part
estimate provide bi-Lipschitz ambient extensions on closed insets. These results
are used in the completed Theorem 7.1 construction in the sibling
EremenkosConjecture project.

## Conformal foundations — 17 September 2026

The 125-result audit also includes the Riemann mapping theorem, normalized
uniqueness, holomorphic inverse maps, locally bounded Montel selection, Hurwitz,
and Schwarz reflection. These proofs are reused from Tau Ceti with explicit
[source attribution](../FunctionTheory/third_party/TauCeti/README.md), and compiled against the
unchanged pinned Mathlib. `exists_riemannMap_on_domain` states Riemann mapping
using functions on their actual domains.

New project proofs establish convergence of normalized Riemann maps and their
inverses for decreasing bounded domains under the stated kernel-component
conditions. They include the Cauchy nondegeneration estimate, passage of inverse
identities to limits, and uniform separation of an omitted closed set from
compact inverse images. See [KernelConvergence.lean](ComplexApproximation/Conformal/KernelConvergence.lean).

The application to the decorated unbounded domains of Eremenko Theorem 1.2
is now complete in EremenkosConjecture, which combines these foundations with
the entire construction. See its [proof map](../EremenkosConjecture/docs/THEOREM12_PLAN.md).

## FunctionTheory extraction

The reusable conformal proofs now live in the sibling FunctionTheory project.
The former Conformal modules here preserve their imports and theorem names as
compatibility wrappers. Tau Ceti attribution and its source manifest moved with
the proofs. Approximation, including Runge and Arakelian, remains here.

`Topology/FilledContinua` proves that filling a compact continuum preserves
compactness and connectedness and makes the complement connected. Filling
remains inside an ambient set with no bounded complementary components.
These facts support the application's simple-connectivity criterion.

`FillingStraightChannels` proves that filling bounded complementary components
preserves the width of a straight channel and controls its interior at the
channel's endpoint. `FillingInterior` places the fill of a closed set inside
the interior of an ambient set with no bounded complementary components.
These three results are included in the 125-result audit.

`ArakelianElementaryGeometry` proves the condition for closed star-convex sets,
for compact decorations added to them and then filled, and for bounded
modifications that preserve the absence of bounded complementary components.
`FillingDecreasingIntersection` proves an exact intersection theorem when all
added holes stay in one bounded set. `NestedBandNonseparation` supplies the
nonseparation argument for a band and a smaller inner set.
`StraightTailComplement` proves connectedness of the complement with one
straight halfstrip end. `StraightBandArakelian` verifies the Arakelian
condition for a closed set with the corresponding band-and-inner-strip tail.
All are included in the full 125-report audit of 17 September 2026.


Local-chart transport is now checked: compact fullness invariance extends to
closed unbounded images, and the straight-tail derivative estimate supplies
Arakelian transport. The expanded full audit contains 125 selected reports.
The general Fournodavlos neighbourhood characterization remains deferred.

## Finite-jet interpolation — 20–21 September 2026

The rational, prescribed-pole and polynomial Runge theorems now retain any
chosen finite number of derivatives at finitely many marked points. Orders
may vary by point. Actual-domain versions accept f:U→C on its open
neighbourhood. All six new declarations pass the full build and standard-axiom
audit; the total is now 131 selected declarations. The original Runge targets
also pass unchanged.

See [finite interpolation](docs/FINITE_INTERPOLATION.md). The original six
interfaces have holomorphic input. The subsequent meromorphic extension is
now proved, as recorded below.

## Meromorphic interpolation — 21 September 2026

`meromorphic_prescribed_poles_approximation_with_interpolation` now preserves
all principal parts at singularities in K, interpolates finite jets at regular
marked points, and confines new denominator zeros to the allowed pole set.
It supplies an error holomorphic near all of K, with uniform norm below epsilon,
including at the former singularities of the difference. Pointwise approximation
is explicit at every regular point of K.

The `_on_domain` version accepts f:U→C with `IsMeromorphicFunctionOn U f`.
Both declarations pass the full build, original Runge target checks and
133-result audit. See [meromorphic interpolation](docs/MEROMORPHIC_INTERPOLATION.md).

## Shared cutoff refactor — 21 September 2026

The existing smooth cutoff and compact extension proofs now live in
FunctionTheory/Smooth/Cutoff.lean for reuse by the wandering-dynamics
construction. Runge/SmoothCutoff.lean preserves both original declaration
names with compatibility exports and unchanged statements. The full
ComplexApproximation build, original RungeTargets and all 133 selected
axiom reports passed after this move. Only the standard allowed axioms occur.

The expanded 160-report audit includes simultaneous meromorphic and polynomial
approximation preserving finitely many return maps, all intermediate orbit
domains, and exact marked values and centred local degrees.
