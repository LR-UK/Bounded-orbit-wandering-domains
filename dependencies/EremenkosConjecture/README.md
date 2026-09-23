# EremenkosConjecture

**Start here:** [Main results](MAIN_RESULTS.md) · [Exact Lean statements](EremenkosConjecture/MainTheorems.lean) · [Proof map](PROOF_MAP.md) · [Classical results](CLASSICAL_RESULTS.md) · [Module index](docs/MODULE_INDEX.md)

[Challenge](Challenge.lean) · [Proved solution](Solution.lean) · [Palomar readiness](docs/PALOMAR.md)

[Private review setup](docs/PRIVATE_REVIEW.md) · [Full-paper feasibility and restart plan](docs/FULL_PAPER_FEASIBILITY.md) · [Source audit](docs/FULL_PAPER_SOURCE_AUDIT.md)

The maintainer has deferred Palomar submission until the full paper is ready.
The existing Challenge/Solution files remain useful for private statement review.

Research version prepared for private review. See [PROVENANCE.md](PROVENANCE.md)
for development and review status.

Lean formalisation project for *Eremenko's conjecture, wandering Lakes of Wada,
and maverick points*, David Martí-Pete, Lasse Rempe, and James Waterman (2025),
https://doi.org/10.1090/jams/1049.

All results of Section 3 are proved, together with the Section 2 material needed
by those proofs. See `STATUS.md` for exact coverage and the stronger Section 2
versions that remain open. Section 4's strip scaffolding and initial entire
approximation are now proved in `EremenkosConjecture/Scaffolding.lean`.
The original Eremenko counterexample is now proved: a transcendental entire
function has a singleton connected component of its escaping set. The full
Theorem 7.1 is checked with its endpoint at zero in `Theorem71.lean`. See [the Section 7 map](docs/SECTION7_PROGRESS.md).
**Theorem 1.2 is proved:** every nonempty full compact continuum is exactly
a connected escaping component of a transcendental entire function.
Read [the final theorem](EremenkosConjecture/ContinuumCounterexample.lean) and
[its proof map](docs/THEOREM12_PLAN.md). Mathematical development stops here;
Proposition 7.6 and the remaining paper results are deferred.

**Main counterexample statement:** there exist a transcendental entire function
$f$ and $z\in I(f)$ such that every connected set $A\subset I(f)$ containing $z$
equals $\{z\}$. This is `MainTheorems.eremenko_conjecture_false`, displayed first
in [the statement gallery](EremenkosConjecture/MainTheorems.lean).

Theorem 3.1 is proved as `EremenkosConjecture.wandering_compactum` in
`EremenkosConjecture/UniformEscape.lean`. Proposition 3.3 is proved as
`fast_escaping_wandering_compactum` in `EremenkosConjecture/FastEscape.lean`,
with a bound at every nonnegative starting radius. Proposition 3.2 is proved
for arbitrary compact nonseparating boundary subsets. Theorem 3.4 and Remark
3.5 are proved in `PathComponentTheorem.lean`, including singleton continua
and the no-curve-to-infinity conclusion. `LakesOfWada.lean` proves Theorem 1.4,
including an unconditional construction of the required topological Lakes of
Wada. The domains may all be chosen wandering and fast escaping.

Verification builds the library, checks 299 selected theorem axiom reports, and
scans the project sources for forbidden proof constructs. The audit permits
only `propext`, `Classical.choice`, and `Quot.sound`.

Place this project beside `FunctionTheory`, `ComplexApproximation`, and `ComplexDynamics`.
Run `lake build` with Lean 4.34.0.
On Windows, `scripts/verify.ps1 -LeanBin <Lean-4.34.0-bin-directory>` runs the
full verification workflow.

`docs/SECTION3_COVERAGE.md` maps the paper's statements to the Lean declarations.
The selected Schoenflies dependency is vendored with its licence and provenance;
see `THIRD_PARTY_NOTICES.md` and `docs/TOPOLOGY_SOURCES.md`.


## Private collaboration setup

Clone **FunctionTheory**, **ComplexApproximation**, **ComplexDynamics**, and **EremenkosConjecture**
into one parent directory, keeping those exact directory names. Colleagues
need repository access to all four. `ComplexApproximation` replaces the old
`runge-approximation` directory name; the `Runge.*` imports are preserved.
The dependency arrangement is:

```text
parent/
  FunctionTheory/
  ComplexApproximation/
  ComplexDynamics/
  EremenkosConjecture/
```

From this directory run `lake exe cache get`, then `python scripts/verify.py`.
Use matching reviewed revisions of the siblings; the current Lake files use
local path dependencies, not Git commit pins for the sibling repositories.
The external Mathlib revision is pinned. See `docs/GITHUB_VERIFICATION.md`
for the optional manual GitHub check and private dependency authentication.

Apache 2.0 for the original code; third-party notices remain in force.
See `LICENSE`, `THIRD_PARTY_NOTICES.md`, `PROVENANCE.md`, and `CONTRIBUTING.md`.
