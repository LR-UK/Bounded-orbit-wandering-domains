# Palomar-style package and remaining submission work

[Challenge](../Challenge.lean) · [Solution](../Solution.lean) · [Comparison configuration](../comparator.json) · [Metadata](../formalization.yaml)

**Maintainer decision, 18 September 2026: defer submission until the full
paper is ready.** Retain these files for private statement review. The
[full-paper plan](FULL_PAPER_FEASIBILITY.md) records the remaining work and
distinguishes the main theorems from the wider preliminary and remark coverage.

The prepared package selects four results: Theorem 1.2, Theorem 7.1, the
explicit singleton disproof of Eremenko's conjecture, and the strong
curve-to-infinity counterexample with fast escape. It is a completed subset,
not a full-paper submission. Its selection and metadata will need review
when mathematical coverage is expanded.

The wider library also proves the other Section 3 results, including wandering
Lakes of Wada. The current comparison does not select all of those declarations.
The metadata states both the selected scope and the wider completed coverage.
It does not advertise Section 5 or Proposition 7.6 as proved.

## Prepared locally

Challenge imports only Mathlib and displays the exact dynamics definitions.
It deliberately has four unproved statement bodies. Solution imports the
completed proof development, repeats the four theorem types and proves them.
The proof library and Solution never import Challenge. Only Challenge is
excluded from the no-hole scan; Solution is included in the scan and audit.

`python scripts/verify.py` checks both modules, the library and the selected
proof axioms. Its outcome and source hashes are recorded in `verification/`.
This local workflow does **not** run Comparator or NanoDa. The metadata
discloses substantive Codex assistance and the absence of independent expert
review. No submission, publication, visibility change or upload was performed.

## Registry requirements and updates

Palomar records an exact commit of a **public** GitHub repository. The
Challenge has restricted imports; proof dependencies must be public and
pinned. Verification includes Comparator and NanoDa. Registration additionally
requires the submission and review process. See the
[official submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).

**Updates are supported.** Later corrections or dependency updates use the
existing identifier with successive version numbers. Automated updates retain
the repository, project path and comparison-configuration path; earlier
versions remain unchanged. Each version needs fresh authorization and checks.
The policy explicitly describes corrections and dependency updates; a large
expansion of mathematical scope should be checked against the then-current
rules rather than assumed to qualify automatically. See
[section 9](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#9-updates-and-permanent-identifiers).

## Before an actual submission

Keep the current repositories private for colleague review. The present Lake
files intentionally use sibling paths, which support that workflow. After
the maintainer decides to publish, convert those dependencies to exact public
GitHub commit pins (including FunctionTheory), regenerate manifests, and
verify a fresh checkout. No such conversion or publication was made here.

Review the four statements and the metadata, retain `comparator.json` as the
stable configuration path if versioned updates are intended, then run the
official independent verification workflow for the final public commit.
The [official template](https://github.com/PalomarRegistry/PalomarTemplate)
documents that workflow. A full-paper submission can be considered later;
the current project is explicitly a completed subset of the paper.
