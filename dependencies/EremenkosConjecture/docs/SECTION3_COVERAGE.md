# Checked correspondence with Section 3

Start with the [readable statements](../MAIN_RESULTS.md),
[checked Lean gallery](../EremenkosConjecture/MainTheorems.lean), and
[proof map](../PROOF_MAP.md).

The references are to the supplied 42-page paper, DOI
[10.1090/jams/1049](https://doi.org/10.1090/jams/1049).
All declarations below are in namespace `EremenkosConjecture`.

| Paper result | Lean declaration | File |
| --- | --- | --- |
| Theorem 3.1, arbitrary full compactum, including the empty set | `wandering_compactum` | [UniformEscape.lean](../EremenkosConjecture/UniformEscape.lean) |
| Proposition 3.2, arbitrary compact nonseparating boundary subsets | `UniformEscapeData.prescribed_boundary_itinerary` | [PrescribedBoundaryConstruction.lean](../EremenkosConjecture/PrescribedBoundaryConstruction.lean) |
| Theorem 1.4, proved in Section 3 | `fatou_components_common_boundary` | [LakesOfWada.lean](../EremenkosConjecture/LakesOfWada.lean) |
| Stronger wandering and fast-escaping Lakes of Wada statement | `wandering_lakes_of_wada` | [LakesOfWada.lean](../EremenkosConjecture/LakesOfWada.lean) |
| Proposition 3.3, fast escape, with every-radius estimates | `fast_escaping_wandering_compactum` | [FastEscape.lean](../EremenkosConjecture/FastEscape.lean) |
| Theorem 3.4 and Remark 3.5, all full continua, including singletons | `fast_escaping_path_components` | [PathComponentTheorem.lean](../EremenkosConjecture/PathComponentTheorem.lean) |
| Explicit failure of escape along curves from the prescribed continuum | `strong_eremenko_counterexamples` | [PathComponentTheorem.lean](../EremenkosConjecture/PathComponentTheorem.lean) |

The filenames in the table are relative to `EremenkosConjecture/`.
The conclusions use the Fatou set defined by local spherical normality,
actual connected components of that set, and pairwise distinct forward Fatou
components for wandering domains. Entire and transcendental entire have their
usual differentiation and nonpolynomial meanings.

Theorem 3.4 identifies **path components**. Its singleton case is not the
singleton **connected component** counterexample of Section 7. The latter is
the subject of the separate feasibility assessment.

Two nontrivial topological existence inputs are proved in this project:

- `exists_countably_many_lakes_of_wada`: an unconditional construction of
  countably many bounded connected open domains with a common compact
  connected frontier.
- `exists_full_continuum_singleton_pathComponent`: a nontrivial full continuum
  containing a prescribed boundary point as a singleton path component.

The first uses supported ambient homeomorphisms and nested disk configurations.
The second uses a shrinking chain of compact topologist's sine curves. Neither
is supplied as a hypothesis of the final dynamical existence statements.

The Section 2 support includes the compact-domain Runge theorem, compact
univalence and finite-iterate stability, entire limits, full compact
neighbourhoods, Jordan neighbourhoods for continua, and disjoint-full-union
lemmas. Full unbounded stability, Arakelyan approximation, and the finite-union
Jordan refinement for disconnected compacta are not proved here.

The complete root library passed its build and source-integrity check. All 68
selected axiom reports, including every headline theorem above, contain only
`propext`, `Classical.choice`, and `Quot.sound`. The reproducible checks are in
`scripts/verify.ps1`, and the saved evidence is in `verification/`.
