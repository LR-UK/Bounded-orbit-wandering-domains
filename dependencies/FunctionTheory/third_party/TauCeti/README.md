# Selected Tau Ceti conformal-mapping proofs

These 138 modules come from [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
commit `f441315d5d3c9ccc377a691d7a7da00613010718`.
The module list is in `UPSTREAM.json`. Original copyright and authorship
headers are retained, and the Apache 2.0 licence is included here.

They supply Riemann mapping, normalized uniqueness, holomorphic inverses,
locally bounded Montel selection, Hurwitz, Schwarz reflection, and
Carathéodory continuous extension for bounded Jordan domains, with their
actual proof dependencies. They compile from source; no external theorem is
taken as an axiom. Carathéodory's statement does not claim boundary injectivity.

The [alignment record](ALIGNMENT.json) reports 137 identical modules after
line-ending normalization. One module, `MeasureTheory/Function/Lp/LIntegralRpow.lean`,
has [documented measurability compatibility changes](COMPATIBILITY.md) for
our Mathlib version. Two auxiliary statements gain measurability assumptions;
the Fatou and Hölder statements are retained. Headline conformal theorem
statements and proofs are unchanged. The original reflection comment is
also restored. Upstream used Lean 4.34.0-rc2; we use pinned Lean 4.34.0.

Public modules retain their `TauCeti/` paths. Additional interfaces and
proofs live under `FunctionTheory/Conformal/`. The reused proofs are not
attributed to this project's author or automated formalisation work.
Selected axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
