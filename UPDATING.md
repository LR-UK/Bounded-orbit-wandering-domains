# Updating this submission

Keep the independent Challenge statement, Solution and comparator.json in
agreement. Do not import Challenge into Solution. Preserve the two intentional
Challenge placeholders and keep proved source free of proof holes, extra axioms
and native_decide. A changed definition must be reflected in both independent
presentations and compared explicitly.

Use the pinned toolchain and Mathlib revision. For a future port, make changes
in a separate branch and retain the previous successful commit and evidence.
Run the commands in README.md, inspect the theorem signatures and axiom audit,
and complete the official Comparator check before submitting a new commit.
Record source adaptations and keep all copyright/licence notices.

The archived source SHA-256 manifest detects changed files; it is not a public
Git commit. Publish first, then select the full public commit SHA for Palomar.
Run `python3 scripts/package_submission.py` only after regenerating the checks.
