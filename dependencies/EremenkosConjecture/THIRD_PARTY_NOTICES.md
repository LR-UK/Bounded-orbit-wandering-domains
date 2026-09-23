# Source attribution

The mathematical source is *Eremenko's conjecture, wandering Lakes of Wada,
and maverick points*, David Martí-Pete, Lasse Rempe, and James Waterman,
[DOI 10.1090/jams/1049](https://doi.org/10.1090/jams/1049). The supplied paper
is not redistributed in this source package.

The sibling ComplexDynamics library adapts the normality and spherical
foundations of [LR-UK/exp-chaotic](https://github.com/LR-UK/exp-chaotic).
Its attribution and Apache 2.0 licence are retained in that project.

`vendor/schoenflies` contains the selected dependency closure of
[Álvaro Begué's Schoenflies project](https://github.com/alonamaloh/schoenflies-lean),
at revision `05a43d29cde026618777db3d4e4316204ccca237`, with the upstream
Apache 2.0 licence. `vendor/schoenflies/PROVENANCE.md` records the compatibility
edits and validation. Its source notices have been preserved.

`TruncatedSineCurve.lean` imports the pinned Mathlib
`Counterexamples.TopologistsSineCurve`, by Daniele Bolla and David Loeffler.
Mathlib's source and licence remain in its separately fetched dependency.
Our compact truncation, shrinking-chain construction, and dynamical use are
in the project modules.

The EPFL/LARA Jordan development was separately ported and checked during
source research, but is not a dependency of this package. It is recorded in
`docs/TOPOLOGY_SOURCES.md`.
