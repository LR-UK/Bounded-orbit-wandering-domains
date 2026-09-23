# Foundation reuse

FunctionTheory, ComplexDynamics, ComplexApproximation and EremenkosConjecture
are the supplied 22 September 2026 source
snapshots, using the same Lean 4.34.0 and Mathlib revision as this project.
All four are contained Lake path dependencies in the source archive.

FunctionTheory includes attributed Tau Ceti conformal mapping, inverse and
normal-family results, Ray sphere foundations and Li–Luo normal-family
sources. Its third_party directories record licences and precise revisions.
Its prior audit records 608 selected results; ComplexDynamics records 44.
Current final-theorem axiom checks cover actual transitive proof dependencies.

RiemannMappingFull and UnitDiscShift adapt Yury Kudryashov's planar Riemann
mapping development at the revision in THIRD_PARTY_NOTICES.md.
They do not construct finite-puncture uniformisation.

No suitable Fatou-component definitions were found in pinned Mathlib or
the supplied Tau Ceti snapshot. The short ComplexDynamics definitions are
therefore copied into Challenge.lean and included in declaration comparison.


ComplexApproximation and EremenkosConjecture supply the planar criterion used
in TrappedSimpleConnectivity. Their Schoenflies dependency retains Álvaro
Begué's notices and pinned provenance. Final theorem axiom checks cover the
actual transitive topology dependencies as well as the analytic ones.
