# Contributing

Begin with the main results and proof map. Discuss statement changes with the
maintainer; preserve compatibility names while downstream projects depend on
them. Prefer public Mathlib and Tau Ceti interfaces and record provenance for
reused proofs. Avoid duplicate developments.

Use the pinned Lean toolchain. Run `python scripts/verify.py` and regenerate the
module map before submitting a change. Include the exact mathematical result,
its hypotheses, and validation in the review description. Original contributions
use Apache 2.0. Future Mathlib submissions will require its usual mathematical
and code review; successful kernel checking alone is not that review.
