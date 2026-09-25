/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphereCompactRemoval
import BoundedWanderingDomains.SphereFiniteRemoval
import BoundedWanderingDomains.SphereCombinedRemoval
import BoundedWanderingDomains.PlaneUniformFiniteRemoval
import BoundedWanderingDomains.LocallyUniformSingularLimits
import BoundedWanderingDomains.LocalUniformSingularLimits

/-!
# Sphere area and derived singular limits

The following proved declarations are the public entry points:

* `AreaDeficit.uniform_compact_gain_sphere`: uniform compact-deletion gain.
* `AreaDeficit.sphere_finite_puncture_gain_le_two_pi_mul_card`: at most
  `2π * E.card` for any finite sphere set, including infinity.
* `BoundedWanderingDomains.wandering_orbit_locallyUniform_spherical_singular_derivedSet`:
  a locally uniform subsequence on every transcendental entire wandering
  component converges to a derived point of the spherical singular set.

The third statement has no simple-connectivity hypothesis. Its pointwise form
and the class-B no-escaping-wandering-orbit corollary are also imported here.
Area uses curvature −1 without dividing by 2π.
-/

#print axioms AreaDeficit.uniform_compact_gain_sphere
#print axioms AreaDeficit.sphere_finite_puncture_gain_le_two_pi_mul_card
#print axioms AreaDeficit.uniform_compact_finite_gain_plane
#print axioms AreaDeficit.uniform_compact_finite_gain_sphere_le
#print axioms BoundedWanderingDomains.wandering_orbit_locallyUniform_spherical_singular_derivedSet
#print axioms BoundedWanderingDomains.no_escaping_wandering_orbit_of_classB

#print axioms BoundedWanderingDomains.local_wandering_orbit_locallyUniform_singular_derivedSet
