# Proposition 3.3: implementation route

**Implemented and audited.** The modules VariableDiscs through FastEscape
complete this construction. The final result additionally gives fast escape
at every nonnegative starting radius, avoiding reliance on radius independence.
This document records the construction decisions.

Theorem 3.1 is fully proved and audited. Preserve its proof when generalising
the construction. ComplexDynamics/FastEscape.lean proves maximum-modulus
bounds, the equivalence of closed-disk and circle definitions for entire
functions, uniform-error control, and a radius-sequence fast-escape criterion.

The new control radii must depend on the current polynomial. A fixed rapidly
growing sequence chosen in advance does not supply the needed bound.

Keep control disks centred at -3 with radii rho_n and rho_0 = 1. Target disks
have radius 1 and centres a_0 = 0, a_n = rho_n for n > 0. Choose rho_(n+1)
after p_n so that rho_(n+1) > rho_n + 5, rho_(n+1) > 4, and, for n >= 1,
rho_(n+1) - 3 > M(rho_n - 3, p_n) + 2. The next reference translation is
z -> z + (a_(n+1) - a_n). The current target and control disk are separated
by a vertical line, and all earlier targets lie inside the current control.

Use a finite-stage record containing p_n, the radius prefix through n,
geometric inequalities, StageProperty, and a positive tolerance <= 1/4.
Extending it changes only radius n+1 and preserves the earlier prefix.
Tolerances halve. Existing gluing, ambient conformal chart, finite-target
stability, Runge approximation, and entire-limit proofs supply the analytic
steps. Generalise their geometric inputs without weakening the conclusions.

For n >= 1 put r_n = rho_n - 3. The closed disk about 0 of radius r_n lies
in the control disk. The tail error is below 1, so
M(r_n, f) <= M(r_n, p_n) + 1 < r_(n+1).
Points in target n have norm > rho_n - 1 > r_n. Monotonicity of M gives
fast escape from radius r_1 with orbit offset 1. Since r_1 > 1, this disk
contains a Julia boundary point of any nonempty normalized compactum.

For arbitrary compacta, scaling additionally requires
M(c f(c^-1 z), |c| r) = |c| M(f,r). Scaling.lean already proves the iterate,
transcendence, uniform-escape, and trapping statements. Radius independence
of the fast-escape definition remains a separate reusable dynamics result.

The other Section 3 obligations have subsequently been completed: general
nonseparating boundary subsets in Proposition 3.2, the Lakes of Wada existence
used by Theorem 1.4, and the access-gate/path-component construction in
Theorem 3.4 and Remark 3.5, including the singleton case.

Transcendence for variable disks: keep the stronger one-step bound at
Q_n = p_n^n(P_n), namely |p_(n+1)(q)+3| < tolerance_n for q in Q_n.
Q_n lies in target n, hence in the next control disk. Future tail error is
at most 2*tolerance_(n+1) <= tolerance_n. With tolerances <= 1/4, the limit
maps each Q_n into the fixed disk about -3 of radius 1. For nonempty K,
each finite boundary net P_n is nonempty, so choose q_n in Q_n. Its norm
tends to infinity, while f(q_n) stays bounded. Together with an escaping
orbit this rules out both nonconstant and constant polynomials. The reusable
criterion is ComplexDynamics.isTranscendentalEntire_of_escape_and_bounded_values.
