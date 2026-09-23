# FunctionTheory

Collect reusable classical complex analysis here. Approximation belongs in
ComplexApproximation; dynamical results belong in ComplexDynamics. This project
depends on Mathlib and included, attributed source from Tau Ceti and Ray.

Keep existing public theorem statements, names and proofs aligned with their
sources. Do not attribute vendored results to our automated development.
Preserve the pinned toolchain and dependencies. New actual-domain interfaces
should coexist with ambient Mathlib formulations.

The library contains only complete proofs: no sorry, admit, added axioms,
native_decide, or weakened substitutes for requested conclusions. Only
propext, Classical.choice and Quot.sound are allowed in headline axiom reports.
Run python scripts/verify.py, update the maps with python scripts/update-map.py,
and keep STATUS.md honest about compiled results and outstanding obligations.

Search public formalisations before substantial redevelopment, including other
provers and the EPFL reformalization project (initially recalled as Zurich).
Do not publish or contact other people without explicit authorization.
