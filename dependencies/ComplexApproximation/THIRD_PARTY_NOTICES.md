# Attribution

The library depends on the pinned Apache 2.0 Mathlib release. The theorem
statements and source search are documented in `docs/SOURCES.md`; the proof
architecture is in `docs/PROOF_PLAN.md`. The original challenge is acknowledged
there. No HOL Light or EPFL theorem is imported as a trusted replacement for
the Runge proof. See `PROVENANCE.md` for the development process.

## Tau Ceti

Selected Apache 2.0 conformal-mapping proofs are provided by the sibling FunctionTheory project under `TauCeti/`.
See [the provenance and module manifest](../FunctionTheory/third_party/TauCeti/README.md).
They retain their upstream authorship and are checked from source using our
pinned Lean and Mathlib versions.
