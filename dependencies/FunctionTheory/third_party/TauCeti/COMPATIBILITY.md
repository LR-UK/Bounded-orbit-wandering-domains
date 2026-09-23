# Compatibility with the pinned Mathlib

All sources come from Tau Ceti commit
`f441315d5d3c9ccc377a691d7a7da00613010718`. Of the 138 imported modules,
137 are unchanged after line-ending normalization. The Riemann mapping,
Carathéodory continuity, and Schwarz reflection declarations and proofs are
among those unchanged modules.

One module, `TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean`, has been
adapted to our pinned Mathlib revision. Here `eLpNorm f p μ` is defined to be
infinity when `f` is not almost everywhere strongly measurable. Consequently,
identities with lower Lebesgue integrals require measurability hypotheses.

| Declaration | Compatibility change |
| --- | --- |
| `eLpNorm_rpow_eq_lintegral` | Adds `AEMeasurable f μ` and supplies its strong-measurability consequence. |
| `eLpNorm_le_eLpNorm_of_lintegral_rpow_le` | Adds `AEStronglyMeasurable v μ` and `AEStronglyMeasurable w μ`. |
| `eLpNorm_le_of_ae_tendsto_ennreal` | Statement unchanged; the limit's measurability is deduced from the existing sequence hypotheses. |
| `rpow_lintegral_le_measure_univ_rpow_mul` | Statement unchanged; supplies the strong measurability already present in its proof. |

The Carathéodory dependency uses the last of these results, whose statement is
unchanged. The two strengthened auxiliary statements are not presented as
identical to their upstream versions. The modified file retains attribution
and an in-file compatibility note. No additional assumptions were added to
the boundary-continuity theorem.

The original comment in `Reflection/Principle.lean` is restored. The integrity
scanner now recognizes nested Lean comments instead of rejecting ordinary
words in mathematical prose. Executable forbidden constructs remain rejected;
strings, including interpolation bodies, are still scanned conservatively.
