# Definitions and main results

[Exact Lean statements](ComplexDynamics/MainTheorems.lean) · [Proof map](PROOF_MAP.md) · [Classical lemmas](CLASSICAL_RESULTS.md) · [All modules](docs/MODULE_INDEX.md)

This is a reusable foundations library. Its current results supply the
dynamical conclusions of the approximation constructions in EremenkosConjecture.

## The mathematical objects

| Object | Meaning | Definition |
| --- | --- | --- |
| Transcendental entire function | An everywhere holomorphic $f:\mathbb C\to\mathbb C$ which is not a polynomial function. | `IsTranscendentalEntire`, [Basic](ComplexDynamics/Basic.lean) |
| Escaping set $I(f)$ | The points $z$ for which $\lvert f^n(z)\rvert\to\infty$. | `escapingSet`, [Basic](ComplexDynamics/Basic.lean) |
| Fatou set $F(f)$ | Points with an open neighbourhood on which the sphere-valued iterates form a normal sequence. | `fatouSet`, [Basic](ComplexDynamics/Basic.lean) |
| Julia set $J(f)$ | $\mathbb C\setminus F(f)$. | `juliaSet`, [Basic](ComplexDynamics/Basic.lean) |
| Fatou component | An actual connected component of $F(f)$. | `IsFatouComponent`, [Basic](ComplexDynamics/Basic.lean) |
| Wandering domain | A Fatou component whose forward images lie in pairwise distinct Fatou components, expressed through the components containing iterated points. | `IsWanderingDomain`, [Basic](ComplexDynamics/Basic.lean) |
| Uniform escape on $K$ | For every real $R$, eventually $\lvert f^n(z)\rvert>R$ simultaneously for every $z\in K$. | `EscapesUniformlyOn`, [Basic](ComplexDynamics/Basic.lean) |
| Trapped set for $B$ | Points whose orbits eventually remain in $B$. | `trappedSet`, [Trapping](ComplexDynamics/Trapping.lean) |

Normality means: **every strictly increasing subsequence has a further
subsequence converging locally uniformly in the sphere**. The limit is a
function on the actual neighbourhood. The sphere is the one-point
compactification of the plane; an entire function is not assigned a value
at infinity. See [Normality.lean](ComplexDynamics/Normality.lean).

## Four statements to start with

The namespace of the checked gallery is `ComplexDynamics.MainTheorems`.

1. **`uniform_escape_gives_fatou_interior`.** Uniform escape on $K$ implies
   $\operatorname{int}K\subset F(f)$. This follows directly from convergence
   to infinity in the sphere.
2. **`escape_and_trapping_give_julia`.** If $f$ is continuous, $B$ is compact,
   $z\in I(f)$, and $z$ is accumulated by points eventually trapped in $B$,
   then $z\in J(f)$. The proof directly contradicts local normality.
3. **`wandering_criterion`.** Let $f$ be continuous and $K,B$ compact.
   Assume uniform escape on $K$, accumulation of $\partial K$ by orbits
   trapped in $B$, pairwise disjoint forward images of $K$, and that each
   iterate on $K$ agrees with a plane homeomorphism. Then every component
   of $\operatorname{int}K$ is an actual wandering Fatou component.
   The current criterion's chart hypothesis is explicit; it is stronger
   than needed just for preservation of fullness.
4. **`maximum_modulus_on_circle`.** For entire $f$ and $r\ge0$, the maximum
   over the closed disk equals the supremum on its boundary circle.

Several of these criteria need only continuity. The application supplies
transcendental entire maps. Neither the uniform-escape argument nor the
trapped-boundary argument assumes Montel's theorem.

## Fast escape: inspect the definition

[FastEscape.lean](ComplexDynamics/FastEscape.lean) defines $M_f(r)$ first on
the closed disk. A point is in `fastEscapingSetAtRadius f r` if it escapes
and there exists $\ell\in\mathbb N$ such that

$$M_f^n(r)\le |f^{n+\ell}(z)|\qquad(n\ge0).$$

`fastEscapingSet f` quantifies over positive $r$ whose open disk meets the
Julia set. The general equivalence between all customary radius conventions
has not been proved here. The application supplies the displayed inequality
at **every nonnegative starting radius**, avoiding dependence on that
unproved equivalence.

For bounded-family normality, scaling, transcendental perturbations of
polynomials, and path-component criteria, see the [classical-results catalogue](CLASSICAL_RESULTS.md).
For future development, see [ROADMAP.md](ROADMAP.md).
