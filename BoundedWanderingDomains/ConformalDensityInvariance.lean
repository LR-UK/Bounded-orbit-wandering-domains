/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralDomainMetric

/-!
# Conformal invariance of the hyperbolic density

The componentwise density constructed by uniformisation transforms as a
length density under a biholomorphism between complements of closed sets.
This is the analytic input needed to compare the pole charts of the sphere.
-/

open Set Function Metric Filter Topology

namespace AreaDeficit

private theorem mapsTo_component_of_mapsTo_compl
    {A B : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Aᶜ) (hf : DifferentiableOn ℂ f Aᶜ)
    (hmap : MapsTo f Aᶜ Bᶜ) :
    MapsTo f (connectedComponentIn Aᶜ z)
      (connectedComponentIn Bᶜ (f z)) := by
  rw [mapsTo_iff_image_subset]
  exact (hf.continuousOn.image_connectedComponentIn_subset hz).trans
    (connectedComponentIn_mono (f z) (image_subset_iff.mpr hmap))

/-- The curvature −1 density transforms by the absolute derivative under a
conformal equivalence of plane domains. -/
theorem closedComplementDensity_conformal_equiv
    {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    {a₁ a₂ b₁ b₂ : ℂ}
    (ha : a₁ ≠ a₂) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb : b₁ ≠ b₂) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Aᶜ) (hg : DifferentiableOn ℂ g Bᶜ)
    (hfmap : MapsTo f Aᶜ Bᶜ) (hgmap : MapsTo g Bᶜ Aᶜ)
    (hgf : ∀ z ∈ Aᶜ, g (f z) = z)
    {z : ℂ} (hz : z ∉ A) :
    closedComplementDensity B hB hb hb₁ hb₂ (f z) * ‖deriv f z‖ =
      closedComplementDensity A hA ha ha₁ ha₂ z := by
  have hzA : z ∈ Aᶜ := hz
  have hfzB : f z ∈ Bᶜ := hfmap hzA
  obtain ⟨p, hp⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hA hz ha ha₁ ha₂
  obtain ⟨q, hq⟩ :=
    RiemannDynamics.exists_disc_covering_complement_component hB hfzB hb hb₁ hb₂
  rw [closedComplementDensity_eq_cover A hA ha ha₁ ha₂ hz hp,
    closedComplementDensity_eq_cover B hB hb hb₁ hb₂ hfzB hq]
  have hpmap := mapsTo_component_of_mapsTo_compl hzA hf hfmap
  have hqmap : MapsTo g (connectedComponentIn Bᶜ (f z))
      (connectedComponentIn Aᶜ z) := by
    simpa only [hgf z hzA] using
      (mapsTo_component_of_mapsTo_compl hfzB hg hgmap)
  have hfAt : DifferentiableAt ℂ f z :=
    hf.differentiableAt (hA.isOpen_compl.mem_nhds hzA)
  have hgAt : DifferentiableAt ℂ g (f z) :=
    hg.differentiableAt (hB.isOpen_compl.mem_nhds hfzB)
  have hderiv_inv : deriv g (f z) * deriv f z = 1 := by
    have hcomp := (hgAt.hasDerivAt.comp z hfAt.hasDerivAt).deriv
    have hevent : g ∘ f =ᶠ[𝓝 z] id := by
      filter_upwards [hA.isOpen_compl.mem_nhds hzA] with w hw
      exact hgf w hw
    have hid : deriv (g ∘ f) z = 1 := by
      rw [Filter.EventuallyEq.deriv_eq hevent]
      simp
    exact hcomp ▸ hid
  have hnorm_inv : ‖deriv g (f z)‖ * ‖deriv f z‖ = 1 := by
    rw [← norm_mul, hderiv_inv, norm_one]
  have hle_forward :
      coveringDensity q (f z) * ‖deriv f z‖ ≤ coveringDensity p z := by
    obtain ⟨t, ht, htmap, ht0, htext⟩ :=
      hp.density_extremal (mem_connectedComponentIn hz)
    have hft : DifferentiableOn ℂ (f ∘ t) (ball 0 1) :=
      hf.comp ht (htmap.mono_right (connectedComponentIn_subset _ _))
    have hftmap : MapsTo (f ∘ t) (ball 0 1)
        (connectedComponentIn Bᶜ (f z)) := by
      simpa only [MapsTo, Function.comp_apply, ht0] using hpmap.comp htmap
    have hs := hq.density_schwarz hft hftmap
    have htAt : DifferentiableAt ℂ t 0 :=
      ht.differentiableAt (isOpen_ball.mem_nhds (by simp))
    have hfAtT : DifferentiableAt ℂ f (t 0) := ht0 ▸ hfAt
    have hd : deriv (f ∘ t) 0 = deriv f z * deriv t 0 := by
      simpa only [ht0] using deriv_comp 0 hfAtT htAt
    simp only [Function.comp_apply, ht0, hd, norm_mul, ← mul_assoc] at hs
    have htpos : 0 < ‖deriv t 0‖ := by
      by_contra hn
      have hzder : ‖deriv t 0‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
      rw [hzder, mul_zero] at htext
      norm_num at htext
    apply (mul_le_mul_iff_right₀ htpos).mp
    simpa only [mul_comm] using (hs.trans_eq htext.symm)
  have hle_reverse :
      coveringDensity p z * ‖deriv g (f z)‖ ≤ coveringDensity q (f z) := by
    obtain ⟨t, ht, htmap, ht0, htext⟩ :=
      hq.density_extremal (mem_connectedComponentIn hfzB)
    have hgt : DifferentiableOn ℂ (g ∘ t) (ball 0 1) :=
      hg.comp ht (htmap.mono_right (connectedComponentIn_subset _ _))
    have hgtmap : MapsTo (g ∘ t) (ball 0 1)
        (connectedComponentIn Aᶜ z) := by
      have hm := hqmap.comp htmap
      intro w hw
      have := hm hw
      simpa only [Function.comp_apply, ht0, hgf z hzA] using this
    have hs := hp.density_schwarz hgt hgtmap
    have htAt : DifferentiableAt ℂ t 0 :=
      ht.differentiableAt (isOpen_ball.mem_nhds (by simp))
    have hgAtT : DifferentiableAt ℂ g (t 0) := ht0 ▸ hgAt
    have hd : deriv (g ∘ t) 0 = deriv g (f z) * deriv t 0 := by
      simpa only [ht0] using deriv_comp 0 hgAtT htAt
    simp only [Function.comp_apply, ht0, hgf z hzA, hd, norm_mul, ← mul_assoc] at hs
    have htpos : 0 < ‖deriv t 0‖ := by
      by_contra hn
      have hzder : ‖deriv t 0‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
      rw [hzder, mul_zero] at htext
      norm_num at htext
    apply (mul_le_mul_iff_right₀ htpos).mp
    simpa only [mul_comm] using (hs.trans_eq htext.symm)
  apply le_antisymm hle_forward
  calc
    coveringDensity p z = coveringDensity p z * 1 := by rw [mul_one]
    _ = (coveringDensity p z * ‖deriv g (f z)‖) * ‖deriv f z‖ := by
      rw [mul_assoc, hnorm_inv, mul_one]
    _ ≤ coveringDensity q (f z) * ‖deriv f z‖ :=
      mul_le_mul_of_nonneg_right hle_reverse (norm_nonneg _)

end AreaDeficit
