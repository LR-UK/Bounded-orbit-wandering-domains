/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralDomainMetric
import BoundedWanderingDomains.HolomorphicLifting
import BoundedWanderingDomains.UnnormalisedPointRemoval
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Pullback of the intrinsic density under a holomorphic covering

A holomorphic covering is a local isometry for the complete curvature `-1`
metrics.  The proof uses the extremal-disc characterisation in both
directions.  For the direction that needs a disc in the source, an extremal
disc downstairs is lifted through the covering.
-/

open Set Function Filter Metric Topology MeasureTheory
open scoped Topology

namespace AreaDeficit

private theorem deriv_ne_zero_of_covering
    {f : ℂ → ℂ} {B : Set ℂ}
    (hf : Differentiable ℂ f) (hcov : IsCoveringMapOn f Bᶜ)
    {z : ℂ} (hz : f z ∉ B) :
    deriv f z ≠ 0 := by
  obtain ⟨e, hze, he⟩ := hcov.isLocalHomeomorphOn z hz
  have hinj : InjOn f e.source := by
    intro x hx y hy hxy
    apply e.injOn hx hy
    rw [← he]
    exact hxy
  exact TauCeti.deriv_ne_zero_of_injOn hf.differentiableOn e.open_source hinj hze

/-- The intrinsic curvature `-1` density pulls back exactly under a
holomorphic covering.  The equality `A = f ⁻¹' B` records the full source
of the restricted covering. -/
theorem closedComplementDensity_covering_pullback
    {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    {a₁ a₂ b₁ b₂ : ℂ}
    (ha : a₁ ≠ a₂) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb : b₁ ≠ b₂) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hcov : IsCoveringMapOn f Bᶜ) (hpre : A = f ⁻¹' B)
    {z : ℂ} (hz : z ∉ A) :
    closedComplementDensity B hB hb hb₁ hb₂ (f z) * ‖deriv f z‖ =
      closedComplementDensity A hA ha ha₁ ha₂ z := by
  have hfz : f z ∉ B := by
    intro h
    exact hz (hpre.symm ▸ h)
  have hreg : ∀ w : ℂ, f w ∉ B → deriv f w ≠ 0 :=
    fun w hw => deriv_ne_zero_of_covering hf hcov hw
  obtain ⟨p, hp⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hA hz ha ha₁ ha₂
  obtain ⟨q, hq⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hB hfz hb hb₁ hb₂
  rw [closedComplementDensity_eq_cover A hA ha ha₁ ha₂ hz hp,
    closedComplementDensity_eq_cover B hB hb hb₁ hb₂ hfz hq]
  apply le_antisymm
  · obtain ⟨g, hg, hgmap, hg0, hgext⟩ :=
      hp.density_extremal (mem_connectedComponentIn hz)
    have hfg : DifferentiableOn ℂ (f ∘ g) (ball 0 1) :=
      hf.differentiableOn.comp hg (fun _ _ => mem_univ _)
    have hfgmap : MapsTo (f ∘ g) (ball 0 1)
        (connectedComponentIn Bᶜ (f z)) := by
      have hmapsB : MapsTo (f ∘ g) (ball 0 1) Bᶜ := by
        intro w hw hwB
        have hgwA : g w ∉ A := connectedComponentIn_subset _ _ (hgmap hw)
        exact hgwA (hpre.symm ▸ hwB)
      rw [mapsTo_iff_image_subset]
      exact ((convex_ball (0 : ℂ) 1).isPreconnected.image (f ∘ g)
        hfg.continuousOn).subset_connectedComponentIn
          ⟨0, by simp, by simp only [Function.comp_apply, hg0]⟩
          (mapsTo_iff_image_subset.mp hmapsB)
    have hs := hq.density_schwarz hfg hfgmap
    have hgd : DifferentiableAt ℂ g 0 :=
      hg.differentiableAt (isOpen_ball.mem_nhds (by simp))
    have hder : deriv (f ∘ g) 0 = deriv f z * deriv g 0 := by
      simpa only [hg0] using deriv_comp 0 (hf (g 0)) hgd
    simp only [Function.comp_apply, hg0, hder, norm_mul, ← mul_assoc] at hs
    have hgpos : 0 < ‖deriv g 0‖ := by
      by_contra hn
      have hzero : ‖deriv g 0‖ = 0 :=
        le_antisymm (le_of_not_gt hn) (norm_nonneg _)
      rw [hzero, mul_zero] at hgext
      norm_num at hgext
    apply (mul_le_mul_iff_right₀ hgpos).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (hs.trans_eq hgext.symm)
  · obtain ⟨g, hg, hgmap, hg0, hgext⟩ :=
      hq.density_extremal (mem_connectedComponentIn hfz)
    have hcovU : IsCoveringMapOn
        (fun x : (Set.univ : Set ℂ) => f x) Bᶜ := by
      have hc := hcov.comp_homeomorph (Homeomorph.Set.univ ℂ)
      convert hc using 1
      funext x
      rfl
    obtain ⟨t, ht0, _htmap, hfac, ht, htder⟩ :=
      exists_holomorphic_covering_lift
        (U := ball (0 : ℂ) 1) (K := (Set.univ : Set ℂ)) (S := Bᶜ)
        (x := 0) (y := z) isOpen_ball unitBall_isSimplyConnected
        (by simp) (by simp) hg0.symm hcovU
        (hf.differentiableOn.analyticOnNhd isOpen_univ) hg
        (hgmap.mono_right (connectedComponentIn_subset _ _))
        (fun w _ hw => hreg w hw)
    have htA : MapsTo t (ball 0 1) Aᶜ := by
      intro w hw hwA
      have hBmem : t w ∈ f ⁻¹' B := by
        rw [← hpre]
        exact hwA
      have hfactor := hfac hw
      exact (connectedComponentIn_subset Bᶜ (f z) (hgmap hw))
        (hfactor ▸ hBmem)
    have htcomp : MapsTo t (ball 0 1) (connectedComponentIn Aᶜ z) := by
      rw [mapsTo_iff_image_subset]
      exact ((convex_ball (0 : ℂ) 1).isPreconnected.image t ht.continuousOn)
        |>.subset_connectedComponentIn ⟨0, by simp, ht0⟩
          (mapsTo_iff_image_subset.mp htA)
    have hs := hp.density_schwarz ht htcomp
    have htd0 := (htder 0 (by simp)).deriv
    have htd : deriv t 0 = deriv g 0 / deriv f z := by
      rw [ht0] at htd0
      exact htd0
    have hfpos : 0 < ‖deriv f z‖ := norm_pos_iff.mpr (hreg z hfz)
    have hgpos : 0 < ‖deriv g 0‖ := by
      by_contra hn
      have hzero : ‖deriv g 0‖ = 0 :=
        le_antisymm (le_of_not_gt hn) (norm_nonneg _)
      rw [hzero, mul_zero] at hgext
      norm_num at hgext
    rw [ht0, htd, norm_div] at hs
    have heq : coveringDensity p z * (‖deriv g 0‖ / ‖deriv f z‖) =
        (coveringDensity p z * ‖deriv g 0‖) / ‖deriv f z‖ := by ring
    rw [heq] at hs
    have hs' : coveringDensity p z * ‖deriv g 0‖ ≤
        2 * ‖deriv f z‖ := (div_le_iff₀ hfpos).mp hs
    have htarget : coveringDensity p z * ‖deriv g 0‖ ≤
        (coveringDensity q (f z) * ‖deriv f z‖) * ‖deriv g 0‖ := by
      calc
        coveringDensity p z * ‖deriv g 0‖ ≤
            2 * ‖deriv f z‖ := hs'
        _ = (coveringDensity q (f z) * ‖deriv f z‖) *
            ‖deriv g 0‖ := by rw [← hgext]; ring
    apply (mul_le_mul_iff_right₀ hgpos).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using htarget

/-- If `A` is an obstacle whose points map into the target obstacle `B`,
then the pullback of the `B`-metric dominates the `A`-metric.  This is the
form used with finite forward-invariant puncture sets. -/
theorem closedComplementDensity_le_covering_pullback
    {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hcov : IsCoveringMapOn f Bᶜ) (hforward : A ⊆ f ⁻¹' B)
    {z : ℂ} (hz : f z ∉ B) :
    closedComplementDensity A hA hab ha hb z ≤
      closedComplementDensity B hB hab (hAB ha) (hAB hb) (f z) *
        ‖deriv f z‖ := by
  let Z : Set ℂ := f ⁻¹' B
  have hZ : IsClosed Z := hB.preimage hf.continuous
  have hzZ : z ∉ Z := hz
  have hmono := closedComplementDensity_mono A Z hA hZ hforward
    hab ha hb hzZ
  have hpull := closedComplementDensity_covering_pullback hZ hB
    hab (hforward ha) (hforward hb) hab (hAB ha) (hAB hb)
    hf hcov rfl hzZ
  exact hmono.trans_eq hpull.symm

/-- Area transport on an injective measurable set, using the covering
pullback inequality and the holomorphic change-of-variables theorem. -/
theorem hyperbolicArea_le_image_of_covering
    {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hcov : IsCoveringMapOn f Bᶜ) (hforward : A ⊆ f ⁻¹' B)
    {W : Set ℂ} (hW : MeasurableSet W) (hinj : InjOn f W)
    (havoid : ∀ z ∈ W, f z ∉ B) :
    (∫⁻ z in W, hyperbolicAreaWeight A hA hab ha hb z) ≤
      ∫⁻ z in f '' W,
        hyperbolicAreaWeight B hB hab (hAB ha) (hAB hb) z := by
  rw [holomorphic_change_of_variables hW
    (fun z _ => (hf z).hasDerivAt) hinj]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hW] with z hz
  have hden := closedComplementDensity_le_covering_pullback
    hA hB hAB hab ha hb hf hcov hforward (havoid z hz)
  have hzA : z ∉ A := by
    intro hzmem
    exact (havoid z hz) (hforward hzmem)
  have hnew : 0 ≤ closedComplementDensity B hB hab (hAB ha) (hAB hb) (f z) :=
    le_of_lt (closedComplementDensity_pos B hB hab (hAB ha) (hAB hb)
      (havoid z hz))
  have hold : 0 ≤ closedComplementDensity A hA hab ha hb z :=
    le_of_lt (closedComplementDensity_pos A hA hab ha hb hzA)
  unfold hyperbolicAreaWeight
  rw [← ENNReal.ofReal_mul (sq_nonneg ‖deriv f z‖)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_nonneg (deriv f z)]

end AreaDeficit
