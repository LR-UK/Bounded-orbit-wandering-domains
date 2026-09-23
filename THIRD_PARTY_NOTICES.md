# Third-party sources

RiemannMappingFull.lean and UnitDiscShift.lean adapt work by Yury Kudryashov,
copyright 2025–2026, licensed under Apache 2.0. The original copyright
headers are retained and the licence is included in LICENSE.

Source: https://github.com/leanprover-community/mathlib4/pull/33505
Repository: https://github.com/urkud/mathlib4
Commit: d43061d911b1aeae0788591da437a3b115098962

Original paths:

- Mathlib/Analysis/Complex/RiemannMapping.lean
- Mathlib/Analysis/Complex/UnitDisc/Shift.lean

The local adaptations remove prerequisites already present in Mathlib,
update changed API names and proofs, replace experimental imports, and
compile against the pinned Mathlib 4.34.0 revision. These files prove
ordinary planar Riemann mapping and the stated limit theorems. They do
not prove uniformisation of multiply connected plane domains.

Mathlib itself is an Apache 2.0 dependency, pinned in lakefile.toml.

The contained dependencies/FunctionTheory and dependencies/ComplexDynamics
source snapshots retain their own LICENSE and THIRD_PARTY_NOTICES.md files.
FunctionTheory includes attributed Tau Ceti, Ray and Li–Luo sources with
revision manifests and licences in its third_party directories.
ComplexDynamics records its adaptation of LR-UK/exp-chaotic normality
foundations. The short ComplexDynamics definitions reproduced in
Challenge.lean have the same provenance.
