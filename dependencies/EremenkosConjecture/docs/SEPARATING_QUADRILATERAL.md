# The separating quadrilateral for equation (7.3)

The author clarified that a quadrilateral of large modulus separates the
whole continuum X (including its rightmost point zeta) from zeta + 1. The
formal analytic estimate now uses the length-area version of this argument.
It does not require a theorem about convergence on the whole closed strip.

## Geometry and order of choices

Write a = zeta + epsilon for the finite left tip of the fixed straight
halfstrip L. Work in disk coordinates, with the interior base point mapped
to 0, the right end to 1, and the left tip of the limiting straight halfstrip
to -1. For sufficiently small R, the right half-disk about a lies in L.

1. Choose a cap radius delta less than 1. The desired strip real-part bound
   follows by making log(delta) sufficiently negative.
2. The fixed limiting map tends to -1 along a + t as t decreases to zero.
   Choose an outer radius R so this radial segment is close to -1.
3. The uniform length-area estimate chooses r in (0,R), before the decorated
   domain or its disk map is chosen. All the disk images have area at most pi.
   A sufficiently large log(R/r) ensures that some semicircle with radius
   rho in (r,R) has image length less than delta/2. The half-annulus is the
   separating quadrilateral.
4. Choose the attachment narrow enough that its intersection with Re(z)=Re(a)
   lies in the disk of radius r about a. Interior kernel convergence gives
   simultaneous control on the compact segment a + [r,R]. Thus the selected
   semicircle's image lies in the cap of radius delta about -1.
5. The real-valued continuous barrier

       q(z) = min(Re(z-a), |z-a|-rho)

   is positive at the base point and negative everywhere to the left of a,
   including the whole of X. Within the domain, its zero set lies on the
   right semicircle: the shrinking-gate condition rules out zeros on the
   vertical line outside the small attachment.
6. The unit disk outside the closed cap is connected. If a point with q <= 0
   mapped outside the cap, the intermediate value theorem, applied through
   the inverse map, would force a zero of q outside that cap. This contradicts
   the crosscut estimate. Hence the entire attached side maps into the cap.
7. The explicit disk-to-strip coordinate is

       w -> -log((1-w)/(1+w)).

   For |w+1| <= delta <= 1, its real part is at most log(delta). This estimate
   is uniform even for images approaching the horizontal strip boundary.
   Positive rescaling and translation preserve uniform leftward escape.
8. `ContinuumReturnEscape` applies the already checked return-branch estimates
   to this uniform bound, yielding |Re(psi(z))| > j simultaneously for z in X,
   and the large-real-part estimates throughout the return block.

## Checked statements

- FunctionTheory: `exists_uniform_annulus_of_bounded_image`.
- FunctionTheory: `nonpositive_side_subset_boundary_cap`.
- FunctionTheory: `exists_gate_size_for_uniform_leftward_bound`.
- FunctionTheory: `uniform_left_escape_of_shrinking_attachment`.
- EremenkosConjecture.Scaffolding: `eventually_return_map_real_part_gt`.

The new FunctionTheory modules are listed in its main-results page and proof
map. All displayed geometric conditions, inverse identities, and convergence
hypotheses are explicit in the Lean statements. There are no proof holes.

## What this does not yet establish

The decorated domains still have to be constructed with these conditions,
their kernel and normalization identified, and the general-continuum stage
induction assembled. Thus this is the completed analytic estimate for the
proposed geometry, not yet an unconditional proof of Theorem 1.2. Theorem 7.1
and the explicit counterexample to Eremenko's conjecture remain proved.
