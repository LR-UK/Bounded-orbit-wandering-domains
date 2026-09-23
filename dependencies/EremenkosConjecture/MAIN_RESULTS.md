# Main results, by paper number

[Read all headline statements in Lean](EremenkosConjecture/MainTheorems.lean) · [Proof map](PROOF_MAP.md) · [Auxiliary classical results](CLASSICAL_RESULTS.md) · [All modules](docs/MODULE_INDEX.md)

This project formalises Section 3 of *Eremenko's conjecture, wandering Lakes
of Wada, and maverick points*, David Martí-Pete, Lasse Rempe and James Waterman
(2025), [DOI: 10.1090/jams/1049](https://doi.org/10.1090/jams/1049), and the
compact foundations it needs from Section 2. Section 4 and the original
Eremenko counterexample in Section 7, and Theorem 1.2 for every full continuum, are proved.

Here **full** means that the plane complement is connected; a **continuum**
is a nonempty compact connected set. $I(f),F(f),J(f),A(f)$ denote the escaping,
Fatou, Julia and fast escaping sets. $f^n$ is iteration, not a power.
Definitions are in the sibling ComplexDynamics library; the most important
conventions are explained [below](#definitions-worth-reviewing).

## The theorem directory

Every row has an explicit proved statement in the gallery, under namespace
`EremenkosConjecture.MainTheorems`. The last column goes directly to its proof.

| Paper result | Gallery declaration | Proof module and original declaration |
| --- | --- | --- |
| Theorem 1.2 | `theorem_1_2` | [ContinuumCounterexample](EremenkosConjecture/ContinuumCounterexample.lean): `theorem1_2` |
| Failure of Eremenko's conjecture, connected-subset formulation | `eremenko_conjecture_false` | [Theorem71](EremenkosConjecture/Theorem71.lean): `eremenko_conjecture_false` |
| Theorem 7.1, exact coordinates | `theorem_7_1` | [Theorem71](EremenkosConjecture/Theorem71.lean): `theorem7_1` |
| Original Eremenko counterexample | `eremenko_counterexample` | [RayCounterexample](EremenkosConjecture/RayCounterexample.lean): `eremenko_counterexample` |
| Theorem 7.1, endpoint at `7i/2` | `theorem_7_1_translated` | [RayCounterexample](EremenkosConjecture/RayCounterexample.lean): `theorem7_1_translated` |
| Theorem 3.1 | `theorem_3_1` | [UniformEscape](EremenkosConjecture/UniformEscape.lean): `wandering_compactum` |
| Proposition 3.2 | `proposition_3_2` | [PrescribedBoundaryConstruction](EremenkosConjecture/PrescribedBoundaryConstruction.lean): `UniformEscapeData.prescribed_boundary_itinerary` |
| Proposition 3.3 | `proposition_3_3` | [FastEscape](EremenkosConjecture/FastEscape.lean): `fast_escaping_wandering_compactum` |
| Theorem 3.4 and Remark 3.5 | `theorem_3_4` | [PathComponentTheorem](EremenkosConjecture/PathComponentTheorem.lean): `fast_escaping_path_components` |
| No escaping curve to infinity from the chosen continuum | `no_escaping_curve_to_infinity` | [PathComponentTheorem](EremenkosConjecture/PathComponentTheorem.lean): `strong_eremenko_counterexamples` |
| Topological Lakes of Wada | `topological_lakes_of_wada` | [LakesOfWada](EremenkosConjecture/LakesOfWada.lean): `exists_countably_many_lakes_of_wada` |
| Theorem 1.4, proved in Section 3 | `theorem_1_4` | [LakesOfWada](EremenkosConjecture/LakesOfWada.lean): `wandering_lakes_of_wada` |

## Original Eremenko counterexample

**There exist a transcendental entire function $f$ and a point $z\in I(f)$
such that every connected subset $A\subset I(f)$ containing $z$ is equal to
$\{z\}$.** This is the first statement in the Lean gallery,
`MainTheorems.eremenko_conjecture_false`.

There is a transcendental entire function with an escaping point whose
**connected component** in the escaping set is a singleton. This disproves
the original conjecture, not only its stronger path-to-infinity variant.

The stronger checked statement supplies a horizontal ray starting at `7i/2`.
The whole ray is in the Julia set; its endpoint escapes; every other point is
bungee; and the ray is a connected component of the union of the Julia,
escaping, and bungee sets. The final theorem translates the endpoint to zero, as in the paper. Theorem 1.2 for arbitrary full continua is also proved; see below.

## Theorem 3.1: wandering compacta

For **every full compact set** $K\subset\mathbb C$, there exists a
transcendental entire $f$ such that:

- The compact sets $f^n(K)$ are pairwise disjoint.
- $f^n\to\infty$ uniformly on $K$.
- $\partial K\subset J(f)$.
- Every connected component of $\operatorname{int}K$ is a wandering Fatou component.

The theorem includes disconnected compacta and the empty set. No existence
of a construction witness is left as a hypothesis in this final statement.

## Proposition 3.2: prescribed boundary itineraries

This is the construction theorem. Its input `UniformEscapeData` in
[ConstructionData.lean](EremenkosConjecture/ConstructionData.lean) consists of:

- Full compact sets $K_n$ with $K_{n+1}\subset\operatorname{int}K_n$ and
  $K_0\subset D(0,1)$.
- Compact full sets $P_n\subset\partial K_n$. They need not be finite.

The output is a transcendental entire $f$ such that $f^n$ is injective on
$K_n$ and sends it into $D(3n,1)$, while $f^{n+1}(P_n)\subset D(-3,1)$.
Also $f(\overline D(-3,1))\subset D(-3,1)$, providing a trapping region.
The exact disk constants are defined in [DiscGeometry.lean](EremenkosConjecture/DiscGeometry.lean).
The eventual-empty case is included. This is the normalised construction
form; scaling in the main existence theorems removes the initial location
restriction on the compact set.

## Proposition 3.3: fast escape

The function in Theorem 3.1 can be chosen with $K\subset A(f)$. The formal
conclusion is stronger: for every $r\ge0$ and every $z\in K$ there is
$\ell$ such that $M_f^n(r)\le |f^{n+\ell}(z)|$ for all $n$.

## Theorem 3.4 and Remark 3.5: path components

For every full continuum $K$, including a singleton, there is a
transcendental entire $f$ with $K\subset A(f)$ and

$$\operatorname{pc}_{I(f)}(x)=\operatorname{pc}_{K}(x)\quad(x\in K),$$
$$\operatorname{pc}_{J(f)}(x)=\operatorname{pc}_{\partial K}(x)\quad(x\in\partial K).$$

Consequently no continuous curve $\gamma:[0,\infty)\to I(f)$ starting in
$K$ tends to infinity. This refutes the **strong curve-to-infinity version**
of Eremenko's conjecture. It is not the connected-component counterexample
to the original conjecture in the later sections of the paper.

## Theorem 1.4: wandering Lakes of Wada

There are a transcendental entire $f$, a compact connected set $X\subset J(f)$,
and countably infinitely many pairwise disjoint wandering Fatou domains $U_i$
with

$$\partial U_i=X,\qquad \overline{U_i}\subset A(f),$$

and uniform escape on each $\overline{U_i}$. The topological existence of
the required Lakes of Wada is proved within this project, then combined
with Proposition 3.3. It is not an assumed input.

## Definitions worth reviewing

`IsFatouComponent` means a connected component of the Fatou set defined
using local normality of sphere-valued iterates. `IsWanderingDomain` asserts
that the components containing successive images are pairwise distinct.
`fastEscapingSetAtRadius` includes escape and the maximum-modulus inequality;
`fastEscapingSet` quantifies over positive radii whose disk meets the Julia
set. The construction proves the inequality at every nonnegative radius.
See the sibling [ComplexDynamics guide](../ComplexDynamics/MAIN_RESULTS.md)
when reading the projects in their supplied sibling layout.

The Lean curve statement uses a function on $\mathbb R$ with continuity
and image restrictions only on $[0,\infty)$; its values at negative times
have no role. The approximation library also offers functions with their
actual compact or open domains.

## What is not yet claimed

Proposition 7.6, Section 5 and other remaining paper results, the full unbounded versions of Section 2's general univalence estimates,
and the disconnected finite-union Jordan refinement remain outside the
proved coverage. See [STATUS.md](STATUS.md),
[Section 3 coverage](docs/SECTION3_COVERAGE.md), and
[counterexample feasibility](docs/COUNTEREXAMPLE_FEASIBILITY.md).

## Section 4: horizontal strip scaffolding

[Scaffolding.lean](EremenkosConjecture/Scaffolding.lean) contains the exact
statement of `lemma4_1`. A holomorphic function uniformly close to $5z$ on
the paper's source strips has expanding real parts and conformal inverse
domains $V_j\subset S_0$ for its iterates onto $T_j$. The domains are connected,
their real parts are unbounded above and below, and the derivative bounds
$2\le |f'|\le8$ hold along the intermediate images.

`exists_scaffolding_function` constructs the initial entire function of (4.3),
with the disk trapping property of (4.4). The proof verifies the Arakelian
hypotheses for the actual unbounded approximation set. The required
neighbourhood-holomorphic Arakelian theorem and Cauchy–Pompeiu foundation are
proved in the sibling ComplexApproximation project.

## Theorem 1.2: prescribed connected escaping components

For **every nonempty full compact connected** set $X\subset\mathbb C$ there
exists a transcendental entire function $f$ for which $X$ is exactly a connected
component of $I(f)$. The statement includes a singleton and assumes no local
connectedness or boundary regularity.

The final proof is [ContinuumCounterexample.lean](EremenkosConjecture/ContinuumCounterexample.lean),
`EremenkosConjecture.theorem1_2`; the gallery names it `theorem_1_2`.
The [detailed proof map](docs/THEOREM12_PLAN.md) explains how the geometric
construction and approximation lemmas supply the entire function and identify
its exact escaping component.

## Reviewing the selected counterexamples

[Challenge.lean](Challenge.lean) displays four selected statements and all
their definitions using Mathlib imports only. [Solution.lean](Solution.lean)
gives their proved counterparts. These cover the explicit failure of Eremenko's
conjecture, Theorems 1.2 and 7.1, and the strong curve-to-infinity counterexample
with fast escape. The broader proved gallery above includes the Section 3
and Lakes of Wada results. This is a scoped package, not a full-paper claim.
See [Palomar readiness](docs/PALOMAR.md) for checks and remaining submission steps.
