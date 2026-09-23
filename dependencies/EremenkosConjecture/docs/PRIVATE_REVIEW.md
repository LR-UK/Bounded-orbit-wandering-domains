# Private review: clone matching revisions

This guide accompanies the **22 September 2026** source checkpoint. Use matching
versions of all four private LR-UK repositories. Their current local changes
are prepared for the maintainer to upload; access to every dependency is needed.
The included [checkpoint record](SHARING_CHECKPOINT.json) identifies the checked
proof sources. It is not a claim that the changes have already been uploaded.

Theorem 1.2 is proved. Further proof development is paused; the
[full-paper assessment](FULL_PAPER_FEASIBILITY.md) and
[source audit](FULL_PAPER_SOURCE_AUDIT.md) record the proposed continuation.
Palomar submission is deferred until the full paper is ready.

## Clone the four repositories

In a new parent directory, with Git authenticated to an account invited to
all four repositories, run:

~~~text
git clone https://github.com/LR-UK/FunctionTheory.git
git clone https://github.com/LR-UK/ComplexApproximation.git
git clone https://github.com/LR-UK/ComplexDynamics.git
git clone https://github.com/LR-UK/EremenkosConjecture.git
~~~

Keep those exact directory names beside each other. The application uses local
sibling dependencies, so record and use matching revisions rather than mixing
unreviewed changes from different branches.

## Match the source checkpoint

Use the complete source archive or the matching upload commits supplied by the
maintainer. The sibling dependencies are local paths. Their proof-source
identifiers and successful audit times are recorded in
[SHARING_CHECKPOINT.json](SHARING_CHECKPOINT.json); each project's verification
summary contains the exact source hashes. The old 18 September dependency pins
are not the matching versions for this update. The maintainer's current upload
guide uses main throughout, without creating additional development branches.

## Read and verify

Begin with [main results](../MAIN_RESULTS.md) and the
[proof map](../PROOF_MAP.md). The exact selected statements are also in
[Challenge](../Challenge.lean), with proved counterparts in
[Solution](../Solution.lean). Challenge's four intentional holes are isolated
from the proof library and Solution.

All four projects use Lean **4.34.0** and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
With Lean/Elan and Python 3 installed, open a terminal in EremenkosConjecture:

~~~text
lake exe cache get
python scripts/verify.py
~~~

This builds the application and its dependencies, builds Challenge/Solution,
and checks the application's source and 299 selected axiom reports. For each
sibling's own audit, run its `python scripts/verify.py` from that sibling's
directory as well. Successful recorded audits comprise 604 selected reports
in FunctionTheory, 160 in ComplexApproximation and 44 in ComplexDynamics.
The source hashes still matched all recorded successful runs at preparation;
this documentation update did not change any Lean proofs.

See [GitHub verification](GITHUB_VERIFICATION.md) for optional hosted checks
and the extra private-dependency read access they require. No hosted checks
or registry submission were performed during preparation.

The original code is Apache 2.0. Attributed Tau Ceti, Ray, Schoenflies and
exp-chaotic material retains its provenance and notices. Private visibility
and licensing are separate: keep repository visibility private until the
maintainer chooses otherwise.
