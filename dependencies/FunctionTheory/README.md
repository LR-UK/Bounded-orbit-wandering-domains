# FunctionTheory

**Start here:** [Main results](MAIN_RESULTS.md) · [Lean gallery](FunctionTheory/MainTheorems.lean) · [Proof map](PROOF_MAP.md) · [Classical results](CLASSICAL_RESULTS.md) · [Module index](docs/MODULE_INDEX.md)

[Future interpolation and potential theory](docs/POTENTIAL_THEORY_PLAN.md)
records the classical analysis needed for the remaining Eremenko paper.
This is a feasibility plan; the proposed additional results are not yet proved.

A Lean library for classical complex analysis, prepared locally for private
collaboration. It supplies reusable conformal-mapping foundations for
ComplexApproximation and EremenkosConjecture. ComplexDynamics remains the home
of dynamical definitions and results.

The current library includes Riemann mapping, normalized Riemann mapping and
uniqueness, Schwarz reflection, Montel selection, Hurwitz injectivity, and
convergence of normalized Riemann maps on decreasing bounded domains with the
specified kernel. The domains can also be unbounded when they lie in a common
horizontal halfplane. Both direct maps and their inverses converge locally uniformly.

The Riemann mapping, reflection and Carathéodory proofs are **reused from Tau Ceti**, with
their original statements and names preserved. They are compiled from Lean
source, with attribution and licensing. Our additions include an interface
for functions on their actual domains, inverse-limit estimates, and kernel
convergence. See [provenance](PROVENANCE.md) for the distinction.

## Use and verify

Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`
are pinned. With Lean/Elan and Python 3 installed:

```text
lake exe cache get
python scripts/verify.py
```

Use `import FunctionTheory`, or import individual modules. The verification
script builds the library, scans proof sources, and checks the selected
theorems' axiom dependencies. See [STATUS.md](STATUS.md) and `verification/`.

FunctionTheory depends on Mathlib and attributed Tau Ceti and Ray source
included here. To build the application projects, keep the four directories
beside each other: `FunctionTheory`, `ComplexApproximation`, `ComplexDynamics`,
`EremenkosConjecture`, and optionally `WanderingDynamics`. Existing `ComplexApproximation.Conformal.*` imports
and theorem names remain available as compatibility aliases.

This new repository has been prepared locally; no GitHub repository has been
created or uploaded automatically. Apache 2.0; see [LICENSE](LICENSE).

Further checked results include conformal reflection with positive derivative
at a boundary zero, strip-end asymptotics, and uniform bounds and continuity
on closed strip insets. Their geometric hypotheses are explicit. The completed application is
Theorem 1.2 in the sibling EremenkosConjecture project; its proof map links
these classical foundations to the full approximation construction.

The geometric strip-map theorem now constructs the boundary normalization
and both end asymptotics. The stronger `StripEndMapLocal` interface now needs
only the straight-tail geometry, with no global Jordan-boundary hypothesis.
It uses Carathéodory continuity and reflection at the straight boundary end.
See the gallery's `normalized_strip_map` for every geometric hypothesis.
The imported source has one documented measure-theory compatibility change;
see [provenance](PROVENANCE.md).


Riemann mapping is also proved for open domains on the **Riemann sphere**,
including domains containing infinity, provided the complement has at least
two points. The maps have their actual domains as types. The sphere is
`OnePoint ℂ` with an attributed Ray complex-manifold atlas. See the
[spherical statement](docs/RIEMANN_SPHERE.md).

The 22 September private-review checkpoint also includes the attributed
Zalcman rescaling proof, omitted-values Montel via Zalcman, Bloch and Little
Picard, proper-disc finite Blaschke classification, local analytic-boundary
continuation without a Jordan assumption, and finite smooth forward
corrections. All 604 selected axiom reports pass. The dependent univalent
infinite realisation remains unfinished; see [STATUS.md](STATUS.md).
