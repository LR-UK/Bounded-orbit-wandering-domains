/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.FiniteModelCancellation
import BoundedWanderingDomains.LocalSingularValues

/-! # Area transport for a covering with an open, local source domain -/

open Set Function Filter Metric Topology MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit

theorem deriv_ne_zero_of_local_covering {f : ℂ → ℂ} {V S : Set ℂ}
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hc : IsCoveringMapOn (fun x : V => f x) S)
    {z : ℂ} (hz : z ∈ V) (hfs : f z ∈ S) : deriv f z ≠ 0 := by
  obtain ⟨e, hze, he⟩ := hc.isLocalHomeomorphOn ⟨z, hz⟩ hfs
  have hWo : IsOpen (Subtype.val '' e.source) := hV.isOpenMap_subtype_val _ e.open_source
  have hWV : Subtype.val '' e.source ⊆ V := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hi : InjOn f (Subtype.val '' e.source) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    apply congrArg Subtype.val (e.injOn hx hy ?_)
    rw [← he]
    exact hxy
  exact TauCeti.deriv_ne_zero_of_injOn (hf.differentiableOn.mono hWV) hWo hi ⟨⟨z, hz⟩, hze, rfl⟩

/-- Lift an extremal disc through the restriction to V. Forward invariance
is needed only for obstacle points lying in V. -/
theorem closedComplementDensity_le_local_covering_pullback
    {A B V : Set ℂ} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    {f : ℂ → ℂ} (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hcov : IsCoveringMapOn (fun x : V => f x) Bᶜ)
    (hforward : ∀ x ∈ V, x ∈ A → f x ∈ B)
    {z : ℂ} (hzV : z ∈ V) (hz : f z ∉ B) :
    closedComplementDensity A hA hab ha hb z ≤
      closedComplementDensity B hB hab (hAB ha) (hAB hb) (f z) * ‖deriv f z‖ := by
  have hzA : z ∉ A := fun h => hz (hforward z hzV h)
  have hreg : ∀ w ∈ V, f w ∈ Bᶜ → deriv f w ≠ 0 :=
    fun w hw hfw => deriv_ne_zero_of_local_covering hV hf hcov hw hfw
  obtain ⟨p, hp⟩ := RiemannDynamics.exists_disc_covering_complement_component hA hzA hab ha hb
  obtain ⟨q, hq⟩ := RiemannDynamics.exists_disc_covering_complement_component hB hz hab (hAB ha) (hAB hb)
  rw [closedComplementDensity_eq_cover A hA hab ha hb hzA hp,
    closedComplementDensity_eq_cover B hB hab (hAB ha) (hAB hb) hz hq]
  obtain ⟨g, hg, hgmap, hg0, hgext⟩ := hq.density_extremal (mem_connectedComponentIn hz)
  obtain ⟨t, ht0, htmap, hfac, ht, htder⟩ := exists_holomorphic_covering_lift
    (U := ball (0 : ℂ) 1) (K := V) (S := Bᶜ) (x := 0) (y := z)
    isOpen_ball unitBall_isSimplyConnected (by simp) hzV hg0.symm hcov hf hg
    (hgmap.mono_right (connectedComponentIn_subset _ _)) hreg
  have htA : MapsTo t (ball 0 1) Aᶜ := by
    intro w hw hwA
    have hBmem := hforward (t w) (htmap hw) hwA
    exact (connectedComponentIn_subset Bᶜ (f z) (hgmap hw)) ((hfac hw) ▸ hBmem)
  have htcomp : MapsTo t (ball 0 1) (connectedComponentIn Aᶜ z) := by
    rw [mapsTo_iff_image_subset]
    exact ((convex_ball (0 : ℂ) 1).isPreconnected.image t ht.continuousOn)
      |>.subset_connectedComponentIn ⟨0, by simp, ht0⟩ htA.image_subset
  have hs := hp.density_schwarz ht htcomp
  have htd : deriv t 0 = deriv g 0 / deriv f z := by
    simpa only [ht0] using (htder 0 (by simp)).deriv
  have hfpos : 0 < ‖deriv f z‖ := norm_pos_iff.mpr (hreg z hzV hz)
  have hgpos : 0 < ‖deriv g 0‖ := by
    by_contra hn
    have hzero : ‖deriv g 0‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [hzero, mul_zero] at hgext
    norm_num at hgext
  rw [ht0, htd, norm_div] at hs
  have heq : coveringDensity p z * (‖deriv g 0‖ / ‖deriv f z‖) =
      (coveringDensity p z * ‖deriv g 0‖) / ‖deriv f z‖ := by ring
  rw [heq] at hs
  have hs' := (div_le_iff₀ hfpos).mp hs
  apply (mul_le_mul_iff_right₀ hgpos).mp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using (show
      coveringDensity p z * ‖deriv g 0‖ ≤
        (coveringDensity q (f z) * ‖deriv f z‖) * ‖deriv g 0‖ from by
    calc
      coveringDensity p z * ‖deriv g 0‖ ≤ 2 * ‖deriv f z‖ := hs'
      _ = (coveringDensity q (f z) * ‖deriv f z‖) * ‖deriv g 0‖ := by rw [← hgext]; ring)

theorem hyperbolicArea_le_image_of_local_covering
    {A B V : Set ℂ} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A)
    {f : ℂ → ℂ} (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hcov : IsCoveringMapOn (fun x : V => f x) Bᶜ)
    (hforward : ∀ x ∈ V, x ∈ A → f x ∈ B)
    {W : Set ℂ} (hWV : W ⊆ V) (hW : MeasurableSet W) (hinj : InjOn f W)
    (havoid : ∀ z ∈ W, f z ∉ B) :
    (∫⁻ z in W, hyperbolicAreaWeight A hA hab ha hb z) ≤
      ∫⁻ z in f '' W, hyperbolicAreaWeight B hB hab (hAB ha) (hAB hb) z := by
  rw [holomorphic_change_of_variables hW
    (fun z hz => (hf z (hWV hz)).differentiableAt.hasDerivAt) hinj]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hW] with z hz
  have hden := closedComplementDensity_le_local_covering_pullback
    hA hB hAB hab ha hb hV hf hcov hforward (hWV hz) (havoid z hz)
  have hzA : z ∉ A := fun h => havoid z hz (hforward z (hWV hz) h)
  have hnew := le_of_lt (closedComplementDensity_pos B hB hab (hAB ha) (hAB hb) (havoid z hz))
  have hold := le_of_lt (closedComplementDensity_pos A hA hab ha hb hzA)
  unfold hyperbolicAreaWeight
  rw [← ENNReal.ofReal_mul (sq_nonneg ‖deriv f z‖)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_nonneg (deriv f z)]

theorem finite_model_area_bound_local
    (P : Finset ℂ) {A : Set ℂ} (hA : IsClosed A) (hPA : (↑P : Set ℂ) ⊆ A)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P)
    {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hcov : IsCoveringMapOn (fun x : V => f x) Aᶜ)
    (hforward : ∀ x ∈ V, x ∈ P → f x ∈ A)
    {B W : Set ℂ} (hWV : W ⊆ V) (hB : MeasurableSet B) (hW : MeasurableSet W)
    (hBW : B ⊆ W) (hinj : InjOn f W) (himage : f '' W ⊆ W \ B)
    (havoid : ∀ z ∈ W, f z ∉ A) {C : ℝ≥0∞}
    (hgain : (∫⁻ z in f '' W,
      hyperbolicAreaWeight A hA hab (hPA ha) (hPA hb) z -
        hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z) ≤ C) :
    (∫⁻ z in B,
      hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb z) ≤ C := by
  let p := hyperbolicAreaWeight (↑P : Set ℂ) P.finite_toSet.isClosed hab ha hb
  let q := hyperbolicAreaWeight A hA hab (hPA ha) (hPA hb)
  let μ := volume.withDensity p
  let ν := volume.withDensity q
  have hp : Measurable p := measurable_hyperbolicAreaWeight _ _ hab ha hb
  have hi : MeasurableSet (f '' W) :=
    hW.image_of_continuousOn_injOn (hf.continuousOn.mono hWV) hinj
  have hfinite : μ W ≠ ∞ := by
    rw [withDensity_apply _ hW]
    exact ne_top_of_le_ne_top
      (finite_puncture_hyperbolicArea_ne_top P
        (Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩) hab ha hb)
      (setLIntegral_le_lintegral _ _)
  have hadvance : μ W ≤ ν (f '' W) + 0 := by
    rw [add_zero, withDensity_apply _ hW, withDensity_apply _ hi]
    exact hyperbolicArea_le_image_of_local_covering P.finite_toSet.isClosed hA hPA
      hab ha hb hV hf hcov hforward hWV hW hinj havoid
  have hcost : ν (f '' W) ≤ μ (f '' W) + C := by
    rw [withDensity_apply _ hi, withDensity_apply _ hi]
    calc
      (∫⁻ z in f '' W, q z) ≤ ∫⁻ z in f '' W, p z + (q z - p z) :=
        lintegral_mono (fun _ => le_add_tsub)
      _ = (∫⁻ z in f '' W, p z) + ∫⁻ z in f '' W, q z - p z :=
        lintegral_add_left hp _
      _ ≤ (∫⁻ z in f '' W, p z) + C := add_le_add le_rfl hgain
  have h := finite_area_cancellation hB hBW hfinite himage hadvance hcost
  simpa only [add_zero, μ, withDensity_apply _ hB] using h

end AreaDeficit
