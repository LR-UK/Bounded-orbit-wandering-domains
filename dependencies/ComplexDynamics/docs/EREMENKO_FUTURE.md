# Reusable dynamics needed for the remaining paper

Planning record, 18 September 2026. Current proved coverage and its 44 selected
axiom reports remain unchanged. No new mathematical work is authorized by
this record alone. See the sibling EremenkosConjecture repository's
`docs/FULL_PAPER_FEASIBILITY.md` for the complete assessment.

The first application to resume is Section 5 / Theorem 1.7. Supply the precise
Fatou-component invariance and orbit-type propagation facts its proof needs.
For constructed domains, normality can use bounded reciprocals when all
iterates omit a fixed trapping disc. Review the existing interfaces before
adding broader normal-family infrastructure.

Next, define maverick points as in Definition 1.10 and prove Lemma 8.1's
equivalence with persistent spherical separation from interior orbits. The
required constant-limit and interior-coalescence facts on wandering domains
are new proof obligations. The existing one-point sphere supplies topology
and uniformity; a convenient explicit chordal-distance interface may be
added. Iterate entire functions only on the plane, then include their values
in the sphere; do not assign a value to a transcendental entire function at
infinity.

For Theorem 1.11, a theorem restricted to simply connected wandering domains
is only a partial result. The paper also uses general dynamics for multiply
connected wandering domains and their boundaries. Interior escape alone does
not justify the boundary conclusion. FunctionTheory should own harmonic
measure; this project should own those dynamical reductions.

Proposition 7.6(i) requires general fast-escape results, including the
unboundedness of fast-escaping components and their interaction with Julia
neighbourhoods, together with the appropriate escape-from-boundary theorem
for Fatou components. The current construction-specific maximum-modulus
bounds do not supply these general results. Check radius conventions and
their independence before identifying an interface with the standard `A(f)`.

For Theorem 1.6, a simpler deduction after 1.7 uses a closed disc, one escaping
interior point and one bungee boundary point. Orbit-type propagation makes
the entire disc escaping. Harmonic measure is unnecessary for that existence
statement. The mixed Lakes-of-Wada construction is a stronger separate target.

Keep these general facts independent of the application's stage invariants.
Every advertised result needs a complete proof and the usual source and
axiom audits; none of the proposals here changes current proved coverage.
