/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.GeneralDomainCovering
import BoundedWanderingDomains.TrappedComponentCovering
import BoundedWanderingDomains.ShrinkingImages

/-! # Pointed universal covering discs -/

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- A disc covering may be centred at any marked target point. -/
theorem IsHolomorphicDiscCovering.exists_centred {q : ℂ → ℂ} {U : Set ℂ}
    (hq : IsHolomorphicDiscCovering q U) {z : ℂ} (hz : z ∈ U) :
    ∃ p : ℂ → ℂ, IsHolomorphicDiscCovering p U ∧ p 0 = z := by
  obtain ⟨w, hw, hwz⟩ := hq.surj hz
  let m : ℂ → ℂ := fun v => (v - -w) / (1 - (starRingEnd ℂ) (-w) * v)
  let t : ℂ → ℂ := fun v => (v - w) / (1 - (starRingEnd ℂ) w * v)
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hmn : ‖-w‖ < 1 := by simpa using hwn
  have hm : DifferentiableOn ℂ m (ball 0 1) :=
    TauCeti.differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hmn
  have hmD : MapsTo m (ball 0 1) (ball 0 1) :=
    TauCeti.mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hmn
  have htD : MapsTo t (ball 0 1) (ball 0 1) :=
    TauCeti.mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hwn
  have htm : LeftInvOn t m (ball 0 1) := by
    simpa only [neg_neg] using TauCeti.leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hmn
  have hmt : LeftInvOn m t (ball 0 1) :=
    TauCeti.leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hwn
  have hmb : BijOn m (ball 0 1) (ball 0 1) :=
    ⟨hmD, htm.injOn, fun v hv => ⟨t v, htD hv, hmt hv⟩⟩
  let e := DifferentiableOn.toHomeomorphOfBijOn hm isOpen_ball hmb
  refine ⟨q ∘ m, ⟨hq.holo.comp hm hmD, hq.maps.comp hmD,
    hq.surj.comp hmb.surjOn, ?_⟩, ?_⟩
  · simpa only [Function.comp_def, e, DifferentiableOn.toHomeomorphOfBijOn_apply] using
      hq.covering.comp_homeomorph e
  · simpa only [Function.comp_apply, m, zero_sub, neg_neg, mul_zero, sub_zero, div_one] using hwz

/-- Covering maps send open subsets of the disc to plane-open sets. -/
theorem IsHolomorphicDiscCovering.image_isOpen {p : ℂ → ℂ} {U D : Set ℂ}
    (hp : IsHolomorphicDiscCovering p U) (hD : IsOpen D) (hDB : D ⊆ ball 0 1) :
    IsOpen (p '' D) := by
  apply analytic_locally_open (hp.holo.analyticOnNhd isOpen_ball) ?_ D hDB hD
  intro w hw hc
  obtain ⟨c, he⟩ := eventuallyConst_iff_exists_eventuallyEq.mp hc
  apply hp.deriv_ne_zero hw
  rw [he.deriv_eq]
  simp

/-- Schwarz lifting gives forward inclusion of equal-radius covering discs. -/
theorem mapsTo_covering_disc {p q f : ℂ → ℂ} {U V : Set ℂ}
    (hp : IsHolomorphicDiscCovering p U) (hq : IsHolomorphicDiscCovering q V)
    (hf : DifferentiableOn ℂ f U) (hfm : MapsTo f U V) (h0 : q 0 = f (p 0))
    {r : ℝ} (hr1 : r < 1) :
    MapsTo f (p '' ball 0 r) (q '' ball 0 r) := by
  obtain ⟨h, hzero, hm, hfac, hh, _⟩ := exists_holomorphic_covering_lift
    isOpen_ball unitBall_isSimplyConnected (by simp : (0 : ℂ) ∈ ball 0 1)
    (by simp : (0 : ℂ) ∈ ball 0 1) h0 hq.covering
    (hq.holo.analyticOnNhd isOpen_ball) (hf.comp hp.holo hp.maps) (hfm.comp hp.maps)
    (fun w hw _ => hq.deriv_ne_zero hw)
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : w ∈ ball (0 : ℂ) 1 := ball_subset_ball hr1.le hw
  have hs := Complex.norm_le_norm_of_mapsTo_ball hh (hm.mono_right ball_subset_closedBall)
    hzero (mem_ball_zero_iff.mp hw1)
  refine ⟨h w, mem_ball_zero_iff.mpr (hs.trans_lt (mem_ball_zero_iff.mp hw)), ?_⟩
  exact hfac hw1

/-- The analogous inclusion for closed covering discs. -/
theorem mapsTo_closed_covering_disc {p q f : ℂ → ℂ} {U V : Set ℂ}
    (hp : IsHolomorphicDiscCovering p U) (hq : IsHolomorphicDiscCovering q V)
    (hf : DifferentiableOn ℂ f U) (hfm : MapsTo f U V) (h0 : q 0 = f (p 0))
    {r : ℝ} (hr1 : r < 1) :
    MapsTo f (p '' closedBall 0 r) (q '' closedBall 0 r) := by
  obtain ⟨h, hzero, hm, hfac, hh, _⟩ := exists_holomorphic_covering_lift
    isOpen_ball unitBall_isSimplyConnected (by simp : (0 : ℂ) ∈ ball 0 1)
    (by simp : (0 : ℂ) ∈ ball 0 1) h0 hq.covering
    (hq.holo.analyticOnNhd isOpen_ball) (hf.comp hp.holo hp.maps) (hfm.comp hp.maps)
    (fun w hw _ => hq.deriv_ne_zero hw)
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : w ∈ ball (0 : ℂ) 1 := closedBall_subset_ball hr1 hw
  have hs := Complex.norm_le_norm_of_mapsTo_ball hh (hm.mono_right ball_subset_closedBall)
    hzero (mem_ball_zero_iff.mp hw1)
  exact ⟨h w, mem_closedBall_zero_iff.mpr (hs.trans (mem_closedBall_zero_iff.mp hw)), hfac hw1⟩

/-- Disjoint bounded target domains force covering discs to shrink even when
the covering maps are not globally injective. -/
theorem covering_discs_shrink {p : ℕ → ℂ → ℂ} {U : ℕ → Set ℂ} {M : ℝ}
    (hp : ∀ n, IsHolomorphicDiscCovering (p n) (U n))
    (hb : ∀ n z, z ∈ U n → ‖z‖ ≤ M)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {r ε : ℝ} (_hr : 0 ≤ r) (hr1 : r < 1) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z ∈ p n '' closedBall 0 r, dist z (p n 0) < ε := by
  have hsh := disjoint_bounded_images_shrink isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected (by simp : (0 : ℂ) ∈ ball 0 1)
    (isCompact_closedBall (0 : ℂ) r) (closedBall_subset_ball hr1)
    (fun n => (hp n).holo) (fun n w hw => hb n _ ((hp n).maps hw))
    (fun n m hnm => (hdis hnm).mono (hp n).maps.image_subset (hp m).maps.image_subset)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hsh ε hε] with n hn z hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa only [dist_eq_norm, zero_sub, norm_neg] using hn w hw

end AreaDeficit
