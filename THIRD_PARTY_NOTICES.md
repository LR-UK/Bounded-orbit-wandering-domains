# Licensing and third-party attribution

The original project development is distributed under the Apache License,
Version 2.0; the complete text is in [LICENSE](LICENSE). Reused source retains
its own authorship, copyright notices and licence. Paper co-authorship and
AI assistance do not confer authorship of the reused proofs.

This inventory covers the **distributed source archive**, including source
files in dependency snapshots that are not imported by the two main theorems.
The snapshots' own notices and provenance records remain part of the package.

## Included licences and source records

| Component | Attribution | Included licence | Source and adaptation record |
| --- | --- | --- | --- |
| Riemann mapping and unit-disc shift adaptations | Yury Kudryashov, copyright 2026 and 2025 respectively | [Apache 2.0](LICENSE) | Details below; original notices in both files |
| FunctionTheory | Project development under Lasse Rempe's direction; third-party authors credited separately | [Licence](dependencies/FunctionTheory/LICENSE) | [Provenance](dependencies/FunctionTheory/PROVENANCE.md), [notices](dependencies/FunctionTheory/THIRD_PARTY_NOTICES.md) |
| ComplexDynamics | Lasse Rempe; normality foundations adapted from LR-UK/exp-chaotic | [Licence](dependencies/ComplexDynamics/LICENSE) | [Provenance](dependencies/ComplexDynamics/PROVENANCE.md), [notices](dependencies/ComplexDynamics/THIRD_PARTY_NOTICES.md) |
| ComplexApproximation | Project development under Lasse Rempe's direction | [Licence](dependencies/ComplexApproximation/LICENSE) | [Provenance](dependencies/ComplexApproximation/PROVENANCE.md), [notices](dependencies/ComplexApproximation/THIRD_PARTY_NOTICES.md) |
| EremenkosConjecture | Project development under Lasse Rempe's direction; mathematical paper authors credited below | [Licence](dependencies/EremenkosConjecture/LICENSE) | [Provenance](dependencies/EremenkosConjecture/PROVENANCE.md), [notices](dependencies/EremenkosConjecture/THIRD_PARTY_NOTICES.md) |
| Selected Tau Ceti modules | The Tau Ceti contributors; Chris Birkbeck where named in source headers; D. Cureton adaptation noted below | [Licence](dependencies/FunctionTheory/third_party/TauCeti/LICENSE) | [README](dependencies/FunctionTheory/third_party/TauCeti/README.md), [manifest](dependencies/FunctionTheory/third_party/TauCeti/UPSTREAM.json), [compatibility changes](dependencies/FunctionTheory/third_party/TauCeti/COMPATIBILITY.md) |
| Ray sphere-atlas adaptations and review copies | Geoffrey Irving | [Licence](dependencies/FunctionTheory/third_party/Ray/LICENSE) | [README](dependencies/FunctionTheory/third_party/Ray/README.md), [manifest](dependencies/FunctionTheory/third_party/Ray/UPSTREAM.json) |
| Selected NoWanderingDomains modules and finite-chart adaptation | Will (Ziang) Li; associated paper by Ziang Li and Yusheng Luo | [Licence](dependencies/FunctionTheory/third_party/NoWanderingDomains/LICENSE) | [README](dependencies/FunctionTheory/third_party/NoWanderingDomains/README.md), [manifest](dependencies/FunctionTheory/third_party/NoWanderingDomains/SOURCE.json) |
| Vendored Schoenflies modules | Álvaro Begué, copyright 2026 | [Licence](dependencies/EremenkosConjecture/vendor/schoenflies/LICENSE) | [Provenance](dependencies/EremenkosConjecture/vendor/schoenflies/PROVENANCE.md), [alignment](dependencies/EremenkosConjecture/vendor/schoenflies/ALIGNMENT.json) |

Each linked licence is the retained Apache 2.0 text for that component.
The individual source headers remain authoritative for file-level authorship.

## Yury Kudryashov: Riemann mapping and unit-disc shifts

`BoundedWanderingDomains/RiemannMappingFull.lean` and
`BoundedWanderingDomains/UnitDiscShift.lean` adapt, respectively:

- `Mathlib/Analysis/Complex/RiemannMapping.lean`;
- `Mathlib/Analysis/Complex/UnitDisc/Shift.lean`.

Source: [mathlib PR 33505](https://github.com/leanprover-community/mathlib4/pull/33505),
[urkud/mathlib4](https://github.com/urkud/mathlib4), commit
`d43061d911b1aeae0788591da437a3b115098962`.
Original copyright and author headers are retained. The adaptations narrow
imports, replace experimental prerequisites, and update proofs/API names for
Lean and Mathlib 4.34.0. The submission layout subsequently changed the local
module paths and imports. These are adapted public proofs, not independently
created proofs of Riemann mapping. They do not establish general plane-domain
uniformisation.

## Tau Ceti and its retained secondary attribution

The 138 selected modules are from
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti), commit
`f441315d5d3c9ccc377a691d7a7da00613010718`. The supplied alignment record
identifies 137 copies identical after line-ending normalisation and one
measure-theory compatibility port, `MeasureTheory/Function/Lp/LIntegralRpow.lean`.
The changes are documented in the linked compatibility record. Original
copyright and author headers are retained in all 138 files.

`TauCeti/Analysis/Complex/Conformal/Inverse/BoundaryCluster.lean` additionally
attributes its inverse-boundary-cluster development to **D. Cureton**,
[sphere-six-complex](https://github.com/deancureton/sphere-six-complex),
`SphereSixComplex/Periods/Uniformization/InverseBoundaryCluster.lean`, revision
`895c0a0`, under Apache 2.0. Its retained source note says that cusp-chart
material was omitted. This is a secondary attribution through Tau Ceti, not
an assertion that a separate copy of the entire sphere-six-complex project
is included. Source comments crediting other mathematical and formalisation
background, including Chris Birkbeck's AINTLIB work, are retained as well.

## Geoffrey Irving: Ray

The sphere-atlas source is
[Ray/Manifold/RiemannSphere.lean](https://github.com/girving/ray/blob/753f7131cf96f4651294de4398368abf136c34de/Ray/Manifold/RiemannSphere.lean),
commit `753f7131cf96f4651294de4398368abf136c34de`.
`FunctionTheory/RiemannSphere/Basic.lean` adapts its initial atlas and manifold
construction; `Coordinates.lean` adapts its finite-chart and inversion proofs.
The model abbreviation comes from `Ray/Manifold/Defs.lean`. Original review
copies, licence, retained definitions, omitted material and compatibility
changes are recorded under `third_party/Ray/`. The later sphere-domain
Riemann-mapping application is additional project work, not a result attributed
to Ray.

## Will (Ziang) Li and the Li–Luo Sullivan project

The eight selected `NoWanderingDomains` modules come from
[will1491/no-wandering-domains](https://github.com/will1491/no-wandering-domains),
commit `0a6497b0cc9ed39a6a705bf013449635894b56d0`.
Their source author and copyright holder is **Will (Ziang) Li**; the associated
paper is by **Ziang Li and Yusheng Luo**. The retained material includes sphere,
normal-family and Zalcman foundations. Per-file adaptation notes and the
manifest record explicit-import changes for the pinned Mathlib.

`FunctionTheory/NormalFamilies/FiniteChartConvergence.lean` extracts and
generalises a finite-chart convergence argument from Li's sphere-valued
Weierstrass proof. Its original copyright, author and adaptation notices are
retained. Neither these public proofs nor Zalcman's theorem are attributed
to the present paper's authors or its AI assistance.

## Álvaro Begué: Schoenflies

The 128-module selected closure of `Schoenflies.JordanSchoenflies` comes from
[alonamaloh/schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean),
commit `05a43d29cde026618777db3d4e4316204ccca237`.
All original source copyright and author headers are retained, together with
the complete licence. The initial import records identified 125
unchanged files after line-ending normalisation and compatibility edits to
`Subarc.lean`, `Endgame.lean` and `InitialPair.lean`. The supplied port updates
proof details for Lean 4.34.0 while retaining theorem statements.
The subsequent linter/deprecation update is documented in
[DEPENDENCY_COMPATIBILITY.md](DEPENDENCY_COMPATIBILITY.md); the current alignment
record retains the upstream hashes and records 63 identical files.

The application to simple connectivity of trapped components is additional
project work. The Schoenflies theorem itself remains attributed to Begué.

## ComplexDynamics and historical sources

The domain-restricted normal-sequence definition, its restriction lemma and
the sphere's one-point-compactification presentation adapt
`ExpChaotic/Normality.lean` and `ExpChaotic/Spherical.lean` from
[LR-UK/exp-chaotic](https://github.com/LR-UK/exp-chaotic), retrieved 16 September
2026, as recorded in ComplexDynamics. No commit is invented where the supplied
record gives only a retrieval date. The short definitions reproduced in
`Challenge.lean` have this same provenance.

The exp-chaotic source records generative-AI assistance and the historical
influence of John Harrison's HOL Light exponential-map formalisation. That
history is retained; no HOL Light implementation is bundled here.

## Separately fetched foundations

Mathlib and its Lake dependencies are pinned in `lake-manifest.json` and are
fetched separately. The `.lake` sources, caches and binaries are excluded from
this archive. Mathlib is an Apache 2.0 dependency at revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; its contributors retain their source
notices. The manifest also records plausible, LeanSearchClient, importGraph,
ProofWidgets4, aesop, Qq, batteries and Cli. Their own licences accompany the
separately fetched packages. Lean itself is the separately installed toolchain.

## Mathematical sources and project credit

The paper's co-authors are **Nikolai Prochorov, Lasse Rempe and James Waterman**.
The working proof's mathematical and AI-assistance attribution is recorded in
`formalization.yaml`, separately from ownership of reused source.
Mathematical references include Zihao Ye's new no-wandering-domain proof,
Helena Mihaljević-Brandt and Lasse Rempe-Gillen's hyperbolic-density comparison,
and David Minda's *Quotients of hyperbolic metrics*; full references are in the
metadata. EremenkosConjecture additionally credits David Martí-Pete, Lasse Rempe
and James Waterman's *Eremenko's conjecture, wandering Lakes of Wada, and maverick
points*, DOI `10.1090/jams/1049`. These papers are references, not redistributed
texts. No endorsement by third-party authors is asserted.

The EPFL/LARA Jordan development was inspected in the supplied projects'
source research but is not a bundled dependency of this submission.

## Archive checks

`scripts/audit_attribution.py` checks that the recorded licence, notice and
provenance files exist and that the selected vendored files retain their
copyright and licence headers. Its report is `verification/attribution.json`.
Packaging also verifies that each recorded attribution file is present in the
ZIP with the same contents. These are source-package checks, not a claim of
an independent legal review or renewed upstream-source verification.

## Uniformisation sources in the unconditional submission

Selected `RiemannDynamics/` source is adapted from Will (Ziang) Li's
[RiemannDynamics](https://github.com/will1491/RiemannDynamics), commit
`b3fa37cc0f18a23ea66b654ea3f73eb472129010`. Its complete licence is retained as
[RIEMANN_DYNAMICS_LICENSE](RIEMANN_DYNAMICS_LICENSE). The port updates Lean and
Mathlib APIs, generalises covering second-countability, and adds the
punctured-plane covering bridge and final dynamical application. Original
source headers are retained. New project proofs are identified in their files.

The included `RMT4/` source comes from Will (Ziang) Li's
[RMT4](https://github.com/will1491/RMT4), commit
`7e092cd5e347a1ee01afb165dd6ab043082e0f4d`. Its complete licence is retained as
[RMT4_LICENSE](RMT4_LICENSE); original headers are retained. The uniformisation
argument uses its winding-index and holomorphic square-root development.
The Lean 4.34 port's deprecation edits are listed in
[port-deprecation-updates.json](port-deprecation-updates.json).
Further submission-toolchain adaptations are documented in
[DEPENDENCY_COMPATIBILITY.md](DEPENDENCY_COMPATIBILITY.md).

## Verification tooling

The minimal Palomar metadata validator under `verification/palomar-contract/`
is MIT-licensed, copyright 2026 Kim Morrison. Its
[licence](verification/palomar-contract/LICENSE) and
[provenance](verification/palomar-contract/PROVENANCE.md) are included.
It is development tooling and is not part of the Lean proof's assumptions.
The Comparator runner is adapted from PalomarTemplate at the commit recorded
in its header; the template is Apache-2.0 licensed. The local adaptation limits
Mathlib cache retrieval to the submitted modules' imported dependencies.
