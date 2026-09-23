# Development roadmap

The project is intended to grow into a collaborative library of complex
dynamics, with reusable contributions to Mathlib where suitable.

Current checked foundations: entire/transcendental entire maps, escaping and
bounded-orbit sets, spherical normality, Fatou and Julia sets and components,
wandering criteria, uniform and fast escape, trapping, and path components.
See `STATUS.md` for precise coverage and the 44 selected axiom reports.

The [remaining Eremenko-paper dependencies](docs/EREMENKO_FUTURE.md) provide
a concrete application-driven plan. Proof development is currently paused
after the completed Theorem 1.2 application; this roadmap is not a completion
claim or an instruction to resume automatically.

Early collaboration work: review definitions and interoperability with
Mathlib; organise foundational lemmas into small modules; improve public
documentation and examples; separate application hypotheses from general
dynamics facts; develop general conjugacy and fast-escape radius independence.

Further mathematics can include bungee sets, stronger iteration and univalence
interfaces, and normal-family theory as applications demand. Establish scope
through issues before starting a large development. A general Montel theorem
is not required by the completed Section 3 application.

Prefer small, independently useful upstream contributions. This research
library is not yet a submission-ready Mathlib patch.
