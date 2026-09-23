# Kernel convergence and normalization at the right end

The geometric input used here is a common straight right tail inside the
standard horizontal strip. This is a sufficient condition for the current
Eremenko construction, rather than a general theorem about arbitrary accesses
to infinity.

## Mathematical references

Lasse Rempe pointed out these references during the formalisation:

- [Arc-like continua, Julia sets of entire functions, and Eremenko's Conjecture,
  arXiv:1610.06278v5, Section 13, Proposition 13.3](https://arxiv.org/html/1610.06278v5#S13),
  4 March 2026. Kernel convergence first gives a correcting halfplane
  automorphism. A separating quadrilateral of large modulus controls the
  end and forces this correction to approach the identity.
- [Benitez and Rempe, A bouquet of pseudo-arcs, arXiv:2105.10391v1,
  Proposition 8.2, pp. 19–20](https://arxiv.org/pdf/2105.10391v1#page=19).
  The proof reduces the change of normalization to convergence of the circle
  points corresponding to infinity, using harmonic measure and control of
  crosscuts. Remark 8.3 explains why kernel convergence alone is insufficient.
  Version 1 is the currently posted arXiv version checked on 17 September 2026;
  the author mentioned a pending update.

## Formal proof and its scope

The Lean proof uses the local straight tail to get uniform small caps in the
disk from the length-area crosscut argument already available in the library.
The cap radius is chosen before the domain and disk map. Interior convergence
at one nearby point then gives convergence of the endpoint values by a triangle
inequality. Dividing by these unit-circle values converts derivative
normalization into end normalization.

The proof uses the same change-of-normalization principle as the references.
It does not claim a formalisation of their more general tract hypotheses,
the Teichmüller modulus theorem, or harmonic measure.

| Step | Lean file |
| --- | --- |
| Uniform small caps at a common straight boundary | [UniformStraightBoundary](../FunctionTheory/Conformal/UniformStraightBoundary.lean) |
| Boundary values converge from interior convergence | [StraightBoundaryConvergence](../FunctionTheory/Conformal/StraightBoundaryConvergence.lean) |
| Transfer by the exponential coordinate and rotate | [StripBoundaryConvergence](../FunctionTheory/Conformal/StripBoundaryConvergence.lean) |
| End estimates for the same prescribed disk map | [PrescribedStripEndMap](../FunctionTheory/Conformal/PrescribedStripEndMap.lean) |
| Kernel convergence with the end fixed | [RightEndKernel](../FunctionTheory/Conformal/RightEndKernel.lean) |
| End normalization: existence, uniqueness, asymptotics | [RightEndNormalization](../FunctionTheory/Conformal/RightEndNormalization.lean) |

The unchanged public Tau Ceti Riemann mapping and uniqueness results supply
the interior disk maps. No boundary convergence is assumed in the uniform-cap
argument, and no regularity of the remote boundary is needed.
