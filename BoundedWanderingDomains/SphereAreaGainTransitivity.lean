/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphereHyperbolicArea
import BoundedWanderingDomains.AreaGainSubadditivity

/-!
# Subadditivity of intrinsic sphere area gain

Area gain along two successive enlargements of the closed obstacle is
subadditive.  The statement remains valid when any of the total areas is
infinite because every term integrates a nonnegative density difference.
-/

open Set Function OnePoint MeasureTheory
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

theorem sphereHyperbolicAreaGain_trans
    {A B C W : Set (OnePoint ℂ)}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (hAB : A ⊆ B) (hBC : B ⊆ C)
    (D : SphereHyperbolicMetricData A) :
    sphereHyperbolicAreaGain A hA C hC (hAB.trans hBC) D W ≤
      sphereHyperbolicAreaGain A hA B hB hAB D W +
        sphereHyperbolicAreaGain B hB C hC hBC (D.mono hAB) W := by
  let S : Set ℂ := (spherePoleChart D.pole) ⁻¹' (W ∩ Cᶜ)
  let T : Set ℂ := (spherePoleChart D.pole) ⁻¹' (W ∩ Bᶜ)
  let ρA := hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' A)
    (closed_sphere_set_in_pole_chart hA D.pole) D.anchor_ne
    D.anchorOne_mem D.anchorTwo_mem
  let ρB := hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' B)
    (closed_sphere_set_in_pole_chart hB D.pole) D.anchor_ne
    (hAB D.anchorOne_mem) (hAB D.anchorTwo_mem)
  let ρC := hyperbolicAreaWeight ((spherePoleChart D.pole) ⁻¹' C)
    (closed_sphere_set_in_pole_chart hC D.pole) D.anchor_ne
    (hBC (hAB D.anchorOne_mem)) (hBC (hAB D.anchorTwo_mem))
  have hST : S ⊆ T := by
    intro z hz
    exact ⟨hz.1, fun hzB => hz.2 (hBC hzB)⟩
  have hmeas : AEMeasurable (fun z => ρC z - ρB z)
      (volume.restrict S) := by
    exact ((((measurable_closedComplementDensity
      ((spherePoleChart D.pole) ⁻¹' C)
      (closed_sphere_set_in_pole_chart hC D.pole) D.anchor_ne
      (hBC (hAB D.anchorOne_mem))
      (hBC (hAB D.anchorTwo_mem))).pow_const 2).ennreal_ofReal).sub
      (((measurable_closedComplementDensity
        ((spherePoleChart D.pole) ⁻¹' B)
        (closed_sphere_set_in_pole_chart hB D.pole) D.anchor_ne
        (hAB D.anchorOne_mem) (hAB D.anchorTwo_mem)).pow_const 2).ennreal_ofReal)).aemeasurable
  have hsplit : (∫⁻ z in S, ρC z - ρA z) ≤
      (∫⁻ z in S, ρC z - ρB z) + (∫⁻ z in S, ρB z - ρA z) :=
    lintegral_gain_le_gain_add_gain ρC ρC ρB ρA
      (Filter.Eventually.of_forall fun _ => le_rfl) hmeas
  have hmono : (∫⁻ z in S, ρB z - ρA z) ≤
      ∫⁻ z in T, ρB z - ρA z := by
    exact lintegral_mono_set hST
  unfold sphereHyperbolicAreaGain
  dsimp only [SphereHyperbolicMetricData.mono]
  change (∫⁻ z in S, ρC z - ρA z) ≤
    (∫⁻ z in T, ρB z - ρA z) + (∫⁻ z in S, ρC z - ρB z)
  exact hsplit.trans (add_le_add le_rfl hmono) |>.trans_eq (add_comm _ _)

end AreaDeficit

#print axioms AreaDeficit.sphereHyperbolicAreaGain_trans
