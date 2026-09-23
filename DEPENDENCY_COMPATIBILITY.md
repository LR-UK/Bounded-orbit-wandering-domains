# Dependency compatibility changes, 23 September 2026

This development updates deprecated Mathlib names and Lean style issues in the
included source dependencies. The original frozen submission is unchanged.
The changes replace deprecated set, conditional, graph and restriction lemmas;
use `have`/`let` where Lean requests them; remove unnecessary tactic sequencing;
and resolve ambiguous namespace openings explicitly. No linter is disabled.
The two deliberate Challenge proof holes and informational axiom reports remain.

The exact dependency paths are in `verification/linter-updated-files.json`, and
`verification/linter-compatibility.patch` records the source changes against the
frozen submission. The supporting theorem statements are preserved; renamed
restriction expressions use the current definitionally equivalent API.

Schoenflies remains the work of Álvaro Begué, under Apache 2.0. All its original
copyright, author and licence headers are retained. Modified files now also carry
a compatibility note. `vendor/schoenflies/ALIGNMENT.json` in EremenkosConjecture
retains the recorded upstream hashes and updates the local hashes and comparison
counts. The initial import had 125 identical files and three adaptations; the
current snapshot has 63 identical files after line-ending normalisation.

FunctionTheory, ComplexDynamics and EremenkosConjecture retain their own
licences, source records and third-party notices. Their compatibility changes
do not transfer authorship to this paper's authors or its AI assistance.

The verification script now fails on any build warning other than the two
intentional Challenge `sorry` warnings. No official Palomar check is claimed.

## Unconditional Palomar port to Lean 4.35.0-rc2

The unconditional submission is an isolated copy of the completed Lean 4.34
sources. The original proof trees and frozen conditional archive are preserved.
PalomarSubmission commit `e48a86d0495356b5131a92c9406aa6e27cf99e56` requires
Lean 4.35.0-rc2 or later, so this copy pins that toolchain and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Active contained dependencies and
vendored Schoenflies use the same pins and matching transitive Git revisions.
All active path dependencies resolve within the submission root.

`RiemannDynamics/` and `RMT4/` are incorporated into the same project;
no sibling uniformisation or Mathlib directory is needed. The public
Challenge/Solution statements omit the former metric hypothesis and keep the
bounded-point-orbit condition. Original source authorship and licences are
retained. The dependency STATUS notes distinguish historical full dependency
audits from the submitted proof closure's current build.

The exact toolchain-port source/configuration changes are recorded in
`verification/toolchain435-changes.json` and
`verification/toolchain435-changes.patch`, relative to the assembled,
unconditional Lean 4.34 baseline. The root VERIFICATION.md records the actual
new-toolchain checks and the local official-Comparator environment limitation.
