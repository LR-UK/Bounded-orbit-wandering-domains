/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphereChartTransition
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Intrinsic hyperbolic area of sphere domains

A hyperbolic sphere domain is represented by its closed complement together
with a pole in that complement and two further omitted chart coordinates.
The resulting curvature −1 area is independent of all these choices.
-/

open Set Function OnePoint MeasureTheory
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

noncomputable instance sphereMeasurableSpace : MeasurableSpace (OnePoint ℂ) :=
  borel (OnePoint ℂ)

instance sphereBorelSpace : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

/-- Coordinate data witnessing that the complement of `A` is hyperbolic. -/
structure SphereHyperbolicMetricData (A : Set (OnePoint ℂ)) where
  pole : OnePoint ℂ
  pole_mem : pole ∈ A
  anchorOne : ℂ
  anchorTwo : ℂ
  anchor_ne : anchorOne ≠ anchorTwo
  anchorOne_mem : anchorOne ∈ (spherePoleChart pole) ⁻¹' A
  anchorTwo_mem : anchorTwo ∈ (spherePoleChart pole) ⁻¹' A

/-- The same coordinate witnesses remain valid after enlarging the closed
complement. -/
def SphereHyperbolicMetricData.mono
    {A B : Set (OnePoint ℂ)} (D : SphereHyperbolicMetricData A)
    (hAB : A ⊆ B) : SphereHyperbolicMetricData B where
  pole := D.pole
  pole_mem := hAB D.pole_mem
  anchorOne := D.anchorOne
  anchorTwo := D.anchorTwo
  anchor_ne := D.anchor_ne
  anchorOne_mem := hAB D.anchorOne_mem
  anchorTwo_mem := hAB D.anchorTwo_mem

private noncomputable def metricDataWithPoleOfTwoPoints
    {A : Set (OnePoint ℂ)} (p s t : OnePoint ℂ)
    (hp : p ∈ A) (hs : s ∈ A) (ht : t ∈ A)
    (hst : s ≠ t) (hsp : s ≠ p) (htp : t ≠ p) :
    SphereHyperbolicMetricData A where
  pole := p
  pole_mem := hp
  anchorOne := (spherePoleChart p).symm s
  anchorTwo := (spherePoleChart p).symm t
  anchor_ne := by
    intro he
    have hsTarget : s ∈ (spherePoleChart p).target := by
      rw [spherePoleChart_target]
      exact hsp
    have htTarget : t ∈ (spherePoleChart p).target := by
      rw [spherePoleChart_target]
      exact htp
    apply hst
    rw [← (spherePoleChart p).right_inv hsTarget,
      ← (spherePoleChart p).right_inv htTarget, he]
  anchorOne_mem := by
    change spherePoleChart p ((spherePoleChart p).symm s) ∈ A
    rw [(spherePoleChart p).right_inv (by
      rw [spherePoleChart_target]
      exact hsp)]
    exact hs
  anchorTwo_mem := by
    change spherePoleChart p ((spherePoleChart p).symm t) ∈ A
    rw [(spherePoleChart p).right_inv (by
      rw [spherePoleChart_target]
      exact htp)]
    exact ht

/-- Inserting any point into the complement supplies metric data whose pole
is that inserted point. -/
noncomputable def SphereHyperbolicMetricData.insertAt
    {A : Set (OnePoint ℂ)} (D : SphereHyperbolicMetricData A)
    (p : OnePoint ℂ) : SphereHyperbolicMetricData (A ∪ {p}) := by
  let x := spherePoleChart D.pole D.anchorOne
  let y := spherePoleChart D.pole D.anchorTwo
  have hxr : x ≠ D.pole := by
    rw [← mem_compl_singleton_iff, ← spherePoleChart_target]
    exact (spherePoleChart D.pole).map_source (by simp)
  have hyr : y ≠ D.pole := by
    rw [← mem_compl_singleton_iff, ← spherePoleChart_target]
    exact (spherePoleChart D.pole).map_source (by simp)
  have hxy : x ≠ y := by
    intro he
    apply D.anchor_ne
    exact (spherePoleChart D.pole).injOn (by simp) (by simp) he
  have hxA : x ∈ A := D.anchorOne_mem
  have hyA : y ∈ A := D.anchorTwo_mem
  classical
  by_cases hpr : p = D.pole
  · exact metricDataWithPoleOfTwoPoints p x y (Or.inr rfl)
      (Or.inl hxA) (Or.inl hyA) hxy (hpr ▸ hxr) (hpr ▸ hyr)
  · by_cases hpx : p = x
    · exact metricDataWithPoleOfTwoPoints p D.pole y (Or.inr rfl)
        (Or.inl D.pole_mem) (Or.inl hyA) hyr.symm (fun h => hpr h.symm)
        (hpx ▸ hxy.symm)
    · exact metricDataWithPoleOfTwoPoints p D.pole x (Or.inr rfl)
        (Or.inl D.pole_mem) (Or.inl hxA) hxr.symm (fun h => hpr h.symm)
        (fun h => hpx h.symm)

@[simp] theorem SphereHyperbolicMetricData.insertAt_pole
    {A : Set (OnePoint ℂ)} (D : SphereHyperbolicMetricData A)
    (p : OnePoint ℂ) : (D.insertAt p).pole = p := by
  unfold SphereHyperbolicMetricData.insertAt
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- Curvature −1 hyperbolic area, computed in one pole chart. -/
noncomputable def sphereHyperbolicArea
    (A : Set (OnePoint ℂ)) (hA : IsClosed A)
    (D : SphereHyperbolicMetricData A) (W : Set (OnePoint ℂ)) : ℝ≥0∞ :=
  ∫⁻ z in (spherePoleChart D.pole) ⁻¹' (W ∩ Aᶜ),
    hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
      (closed_sphere_set_in_pole_chart hA D.pole)
      D.anchor_ne D.anchorOne_mem D.anchorTwo_mem z

/-- Gain of curvature −1 area after enlarging the closed complement from
`A` to `B`.  It is defined by integrating the nonnegative density difference
on the new domain, so it remains meaningful when either total area is
infinite. -/
noncomputable def sphereHyperbolicAreaGain
    (A : Set (OnePoint ℂ)) (hA : IsClosed A)
    (B : Set (OnePoint ℂ)) (hB : IsClosed B) (hAB : A ⊆ B)
    (D : SphereHyperbolicMetricData A) (W : Set (OnePoint ℂ)) : ℝ≥0∞ :=
  ∫⁻ z in (spherePoleChart D.pole) ⁻¹' (W ∩ Bᶜ),
    hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' B)
        (closed_sphere_set_in_pole_chart hB D.pole) D.anchor_ne
        (show D.anchorOne ∈ (spherePoleChart D.pole) ⁻¹' B from hAB D.anchorOne_mem)
        (show D.anchorTwo ∈ (spherePoleChart D.pole) ⁻¹' B from hAB D.anchorTwo_mem) z -
      hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
        (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
        D.anchorOne_mem D.anchorTwo_mem z

private theorem measurable_spherePoleChart (p : OnePoint ℂ) :
    Measurable (spherePoleChart p) := by
  apply Continuous.measurable
  exact continuousOn_univ.mp (by simpa using (spherePoleChart p).continuousOn)

private theorem transition_image_chart_preimage
    {A W : Set (OnePoint ℂ)}
    {p q : OnePoint ℂ} (hp : p ∈ A) (hq : q ∈ A) :
    sphereChartTransition p q ''
        ((spherePoleChart q) ⁻¹' (W ∩ Aᶜ)) =
      (spherePoleChart p) ⁻¹' (W ∩ Aᶜ) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzA : spherePoleChart q z ∉ A := hz.2
    have hzp : spherePoleChart q z ≠ p := fun he => hzA (he ▸ hp)
    change spherePoleChart p (sphereChartTransition p q z) ∈ W ∩ Aᶜ
    rw [spherePoleChart_transition hzp]
    exact hz
  · intro hy
    let z := sphereChartTransition q p y
    have hyA : spherePoleChart p y ∉ A := hy.2
    have hye : spherePoleChart p y ≠ q := fun he => hyA (he ▸ hq)
    have hzchart : spherePoleChart q z = spherePoleChart p y := by
      exact spherePoleChart_transition hye
    have hz : z ∈ (spherePoleChart q) ⁻¹' (W ∩ Aᶜ) := by
      change spherePoleChart q z ∈ W ∩ Aᶜ
      rw [hzchart]
      exact hy
    refine ⟨z, hz, ?_⟩
    exact sphereChartTransition_inverse hye

/-- The sphere hyperbolic area does not depend on the pole chart or the two
anchors used to construct its universal-covering density. -/
theorem sphereHyperbolicArea_independent
    {A W : Set (OnePoint ℂ)} (hA : IsClosed A) (hW : MeasurableSet W)
    (D E : SphereHyperbolicMetricData A) :
    sphereHyperbolicArea A hA D W = sphereHyperbolicArea A hA E W := by
  let WE : Set ℂ := (spherePoleChart E.pole) ⁻¹' (W ∩ Aᶜ)
  have hWE : MeasurableSet WE :=
    (hW.inter hA.measurableSet.compl).preimage (measurable_spherePoleChart E.pole)
  have hWEA : WE ⊆ ((spherePoleChart E.pole) ⁻¹' A)ᶜ := by
    intro z hz hzA
    exact hz.2 hzA
  have harea := sphere_chart_hyperbolic_area_image hA
    D.pole_mem E.pole_mem
    E.anchor_ne E.anchorOne_mem E.anchorTwo_mem
    D.anchor_ne D.anchorOne_mem D.anchorTwo_mem hWE hWEA
  rw [transition_image_chart_preimage D.pole_mem E.pole_mem] at harea
  simpa only [sphereHyperbolicArea, WE] using harea

/-- The area gain is intrinsic: it is independent of the pole chart and of
the anchor coordinates used to construct both densities. -/
theorem sphereHyperbolicAreaGain_independent
    {A B W : Set (OnePoint ℂ)} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ⊆ B) (hW : MeasurableSet W)
    (D E : SphereHyperbolicMetricData A) :
    sphereHyperbolicAreaGain A hA B hB hAB D W =
      sphereHyperbolicAreaGain A hA B hB hAB E W := by
  let WE : Set ℂ := (spherePoleChart E.pole) ⁻¹' (W ∩ Bᶜ)
  have hWE : MeasurableSet WE :=
    (hW.inter hB.measurableSet.compl).preimage (measurable_spherePoleChart E.pole)
  have hWEB : WE ⊆ ((spherePoleChart E.pole) ⁻¹' B)ᶜ := by
    intro z hz hzB
    exact hz.2 hzB
  have hgain := sphere_chart_hyperbolic_gain_image hA hB hAB
    D.pole_mem E.pole_mem
    E.anchor_ne E.anchorOne_mem E.anchorTwo_mem
    D.anchor_ne D.anchorOne_mem D.anchorTwo_mem hWE hWEB
  rw [transition_image_chart_preimage (hAB D.pole_mem) (hAB E.pole_mem)] at hgain
  simpa only [sphereHyperbolicAreaGain, WE] using hgain

end AreaDeficit

#print axioms AreaDeficit.sphereHyperbolicArea_independent
#print axioms AreaDeficit.sphereHyperbolicAreaGain_independent
