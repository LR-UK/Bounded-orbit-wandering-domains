# Attributed normal-family and Zalcman foundations

Source: [Li and Luo's Sullivan project](https://github.com/will1491/no-wandering-domains),
commit `0a6497b0cc9ed39a6a705bf013449635894b56d0`. Copyright and authorship
notices are retained in every file; the [licence](LICENSE) is Apache 2.0.
The accompanying paper is [arXiv:2609.16027](https://arxiv.org/abs/2609.16027).

The selected public statements and proofs retain their `NoWanderingDomains`
names. Imports are narrowed to the sphere, normal-family and inversion-isometry
foundations; no modular lambda or rational-dynamics implementation is included.
The [manifest](SOURCE.json) records the source and adaptations for each file.
These are reused public proofs, not original results of this project.

The spherical metric induces the existing one-point-compactification topology.
The source's normality predicate is a family predicate; applications using
ComplexDynamics' sequence predicate require an explicit compatibility proof.
Zalcman's theorem alone does not assert omitted-values Montel or the paper's
nowhere-analytic-boundary theorem.


### Derived local convergence lemma

`FunctionTheory/NormalFamilies/FiniteChartConvergence.lean` extracts and
generalises the finite-chart core of the public sphere-valued Weierstrass
proof. It is explicitly credited to Will (Ziang) Li. The new spherical
Hurwitz and Zalcman–Montel assembly uses this lemma, the preserved public
Zalcman theorem, Tau Ceti Hurwitz, and the project's Bloch-based Little
Picard theorem. This assembly has passed the full546-report audit.
