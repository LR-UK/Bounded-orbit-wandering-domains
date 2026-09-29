module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.SphereHyperbolicArea
public import BoundedWanderingDomains.UnnormalisedPointRemoval

@[expose] public section

/-!
# Area cost of puncturing a sphere domain

Deleting one point from a hyperbolic sphere domain increases its total
curvature −1 hyperbolic area by at most `2π`.
-/

open Set Function OnePoint MeasureTheory
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

private theorem poleChart_preimage_union_singleton
    {A : Set (OnePoint ℂ)} {p w : OnePoint ℂ} (hw : w ≠ p) :
    (spherePoleChart p) ⁻¹' (A ∪ {w}) =
      (spherePoleChart p) ⁻¹' A ∪ {(spherePoleChart p).symm w} := by
  have hwt : w ∈ (spherePoleChart p).target := by
    rw [spherePoleChart_target]
    exact hw
  ext z
  constructor
  · intro hz
    rcases hz with hzA | hzw
    · exact Or.inl hzA
    · apply Or.inr
      have he : spherePoleChart p z = w := by simpa only [mem_singleton_iff] using hzw
      change z = (spherePoleChart p).symm w
      calc
        z = (spherePoleChart p).symm (spherePoleChart p z) :=
          ((spherePoleChart p).left_inv (by simp)).symm
        _ = (spherePoleChart p).symm w := congrArg (spherePoleChart p).symm he
  · rintro (hzA | hz)
    · exact Or.inl hzA
    · apply Or.inr
      have he : z = (spherePoleChart p).symm w := by
        simpa only [mem_singleton_iff] using hz
      subst z
      simpa only [mem_singleton_iff] using (spherePoleChart p).right_inv hwt

/-- Removing one point costs at most `2π` in the unique complete metric of
curvature −1.  The area gain is the integral of the density difference, so
no finiteness assumption on the old total area is required. -/
theorem sphere_point_removal_gain_le_two_pi
    {A : Set (OnePoint ℂ)} (hA : IsClosed A)
    (D : SphereHyperbolicMetricData A) {w : OnePoint ℂ} (hw : w ∉ A) :
    sphereHyperbolicAreaGain A hA (A ∪ {w})
      (hA.union isClosed_singleton) subset_union_left D Set.univ ≤
        ENNReal.ofReal (2 * Real.pi) := by
  have hwp : w ≠ D.pole := fun he => hw (he ▸ D.pole_mem)
  let wc : ℂ := (spherePoleChart D.pole).symm w
  have hpre : (spherePoleChart D.pole) ⁻¹' (A ∪ {w}) =
      (spherePoleChart D.pole) ⁻¹' A ∪ {wc} := by
    exact poleChart_preimage_union_singleton hwp
  have hplane := point_removal_gain_le_two_pi
    ((spherePoleChart D.pole) ⁻¹' A)
    (closed_sphere_set_in_pole_chart hA D.pole)
    D.anchor_ne D.anchorOne_mem D.anchorTwo_mem (w := wc)
  unfold sphereHyperbolicAreaGain
  simp only [univ_inter]
  simpa only [preimage_compl, hpre] using hplane

end AreaDeficit
