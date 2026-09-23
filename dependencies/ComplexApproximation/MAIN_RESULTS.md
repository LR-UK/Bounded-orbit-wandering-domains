# Main results

[Exact Lean statements](ComplexApproximation/MainTheorems.lean) · [Proof map](PROOF_MAP.md) · [Classical lemmas](CLASSICAL_RESULTS.md) · [All modules](docs/MODULE_INDEX.md)

A compact plane set is **full** when its complement in the plane is connected.
The set need not itself be connected, and the approximation results include
the empty compact set.

## Runge's theorem

Let $K\subset\mathbb C$ be compact. Let $f:K\to\mathbb C$ extend
holomorphically to an open neighbourhood of $K$. Given $\varepsilon>0$:

| Form | Additional hypothesis | Conclusion | Statement in the gallery |
| --- | --- | --- | --- |
| Rational | None | There are polynomials $p,q$, with $q$ nonzero on $K$, such that $\lvert f(z)-p(z)/q(z)\rvert<\varepsilon$ for every $z\in K$. | `rational_runge` |
| Prescribed poles | $P$ meets every bounded component of $\mathbb C\setminus K$. | The approximation can be chosen with a nonzero denominator polynomial whose every zero lies in $P$, and no zero on $K$. | `prescribed_poles_runge` |
| Polynomial | $K$ is full. | There is a polynomial $p$ such that $\lvert f(z)-p(z)\rvert<\varepsilon$ for every $z\in K$. | `polynomial_runge` |

The gallery uses the namespace `ComplexApproximation.MainTheorems`.
It also displays `polynomial_runge_on_domain`, with an explicit open
neighbourhood $U$ and a function **whose domain is $U$**. All three forms have
both interfaces in [Runge/LocalDomain.lean](Runge/LocalDomain.lean).

### The hypotheses to inspect

- `Runge.HasHolomorphicExtension K f`: there are an open $U\supset K$ and
  a holomorphic $g:U\to\mathbb C$ agreeing with $f$ on $K$.
- `Runge.IsHolomorphicFunctionOn U g`: each point has a local
  complex-differentiable representative of $g$. No values outside $U$ are inputs.
- `Runge.MeetsBoundedComplementComponents K P`: every bounded connected
  component of $K^c$ contains an allowed pole. See
  [Runge/PrescribedPoles.lean](Runge/PrescribedPoles.lean).

The older `Runge.rational_approximation`, `prescribed_poles_approximation`,
and `polynomial_approximation` declarations and imports continue to work.
[RungeTargets/Statements.lean](RungeTargets/Statements.lean) checks the
original target interfaces against the completed proofs.

## Fullness is preserved by domain homeomorphisms

Let $U,V$ be open connected nonempty subsets of the plane, let
$h:U\to V$ be a homeomorphism, and let $K\subset U$ be compact and full.
Then $h(K)$ is full. **No simple-connectivity assumption is needed.**

Read `fullness_under_domain_homeomorphism` in the gallery. Its proof uses
the equivalence

$$\mathbb C\setminus K\text{ is connected}\quad\Longleftrightarrow\quad U\setminus K\text{ is connected}.$$

The map in the Lean statement has type `U ≃ₜ V`; it is defined only on its
domain. A conformal isomorphism is a special case. The proof and discussion
of the earlier ambient-chart argument are in [docs/FULLNESS.md](docs/FULLNESS.md).

## Scope

These are neighbourhood-holomorphic Runge results. They do not assert
Mergelyan approximation for arbitrary functions continuous on $K$ and
holomorphic only on its interior.

## Arakelian approximation on a closed set

Let $E$ be closed. Assume that every complementary component is unbounded,
and that, for every closed disk $D$, the union of the bounded complementary
components of $E\cup D$ is bounded. If $f$ is holomorphic on an open
neighbourhood of $E$, then for every $\varepsilon>0$ there is an entire $g$
such that $|g(z)-f(z)|<\varepsilon$ for every $z\in E$.

Read `arakelian` in the [statement gallery](ComplexApproximation/MainTheorems.lean).
Its input function has domain $E$, with an explicit holomorphic-neighbourhood
extension hypothesis. An interface with domain $U$ is also provided.
`IsArakelian` states the three geometric conditions above. Equivalence with the
sphere-complement formulation is not part of this result.

This is the neighbourhood-holomorphic case of Rosay–Rudin's Monthly proof.
The proof of the more general continuous/interior-holomorphic case is deferred.

## Cauchy–Pompeiu

For a smooth compactly supported $g:\mathbb C\to\mathbb C$, the new development
proves the area-integral representation at every point, including points
inside the support. It also proves a smooth solution operator for the
inhomogeneous Cauchy–Riemann equation with a uniform bound. The gallery's
`cauchy_pompeiu_compact` exposes the representation; the exact normalization
and analytic identities are in [CauchyPompeiu](ComplexApproximation/CauchyPompeiu.lean).

See [STATUS.md](STATUS.md) and [ROADMAP.md](ROADMAP.md).

## Conformal maps and kernel convergence

For an open simply connected proper plane domain, a homeomorphism onto the unit
disk exists and is holomorphic in both directions. Its functions have exactly
those domains: [exists_riemannMap_on_domain](ComplexApproximation/Conformal/RiemannMapping.lean).
The underlying Riemann mapping, normalized uniqueness and Schwarz reflection
proofs are attributed upstream work; see [Tau Ceti provenance](../FunctionTheory/third_party/TauCeti/README.md).

For decreasing bounded domains, normalized Riemann maps and their inverse maps
converge locally uniformly to the normalized map of the kernel. The exact
kernel hypotheses are explicit in
[normalized_riemannMaps_tendsto_on_bounded_kernel](ComplexApproximation/Conformal/KernelConvergence.lean):
the candidate domain lies in every source domain and contains the base-point
component of the interior of the intersection of their closures. The latter
condition keeps the relevant component when a neck pinches off.

The conformal-mapping development is now maintained in
[FunctionTheory](../FunctionTheory/README.md); the corresponding modules in
this repository are compatibility wrappers. Consult its theorem gallery for
the current statements and extensions.

## Prescribed values and derivatives

All three Runge forms also preserve finite jets at finitely many marked
points in K. Choose a natural number m(a) at each point a; derivatives of
orders k<m(a) are matched exactly while the same uniform approximation bound
holds. Thus m(a)=M+1 preserves orders 0 through M.

The [exact statements](Runge/Interpolation.lean) include
`rational_approximation_with_interpolation`,
`prescribed_poles_approximation_with_interpolation`, and
`polynomial_approximation_with_interpolation`.
[Actual-domain statements](Runge/InterpolationLocalDomain.lean) are available
for functions defined only on U. See [proof and scope](docs/FINITE_INTERPOLATION.md).

## Meromorphic input with unchanged principal parts

[Meromorphic interpolation](Runge/MeromorphicInterpolation.lean) extends the
finite-jet theorem to meromorphic input. The error extends holomorphically
across every pole in K and is uniformly smaller than epsilon there; finite
derivatives are interpolated at regular marked points. New poles are confined
to the prescribed allowed set. There is also an
[actual-domain interface](Runge/MeromorphicInterpolationLocalDomain.lean).
See [the mathematical statement and proof](docs/MEROMORPHIC_INTERPOLATION.md).
