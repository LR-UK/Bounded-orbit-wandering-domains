module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Conformal
public import ComplexApproximation.Topology.LocalHomeomorphNonseparation
public import ComplexApproximation.Topology.FilledContinua
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

@[expose] public section

/-! # Compact fillings in simply connected plane domains -/

open Set Metric Bornology

namespace AreaDeficit

/-- A compact set in a simply connected plane domain can be filled without
leaving the domain. The proof uses a Riemann chart and fullness invariance. -/
theorem fill_subset_of_isSimplyConnected {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hsc : IsSimplyConnected U)
    (hKU : K ⊆ U) : ComplexApproximation.fill K ⊆ U := by
  classical
  by_cases hUne : U = univ
  · simp [hUne]
  obtain ⟨e, hs, ht, _, _, _, _⟩ :=
    TauCeti.riemannMapping_openPartialHomeomorph hU hsc hUne
  have hKe : K ⊆ e.source := hs ▸ hKU
  have hC : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKe)
  have hCB : e '' K ⊆ ball 0 1 := by
    rw [← ht]
    exact (image_mono hKe).trans e.mapsTo.image_subset
  obtain ⟨r, ⟨hr, hr1⟩, hCr⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1)
    hC.isClosed hCB
  let L : Set ℂ := e.symm '' closedBall 0 r
  have hBe : closedBall (0 : ℂ) r ⊆ e.symm.source := by
    rw [e.symm_source, ht]
    exact closedBall_subset_ball hr1
  have hL : IsCompact L := (isCompact_closedBall 0 r).image_of_continuousOn
    (e.symm.continuousOn.mono hBe)
  have hLc : IsConnected Lᶜ :=
    ComplexApproximation.isConnected_compl_image_openPartialHomeomorph e.symm
      (by rw [e.symm_source, ht]; exact (convex_ball (0 : ℂ) 1).isConnected ⟨0, by simp⟩)
      (isCompact_closedBall 0 r) hBe
      (by convert ComplexApproximation.isConnected_exterior r hr using 1
          ext z
          simp [mem_closedBall, dist_zero_right])
  have hLU : L ⊆ U := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hs]
    exact e.symm.map_source (hBe hw)
  have hKL : K ⊆ L := by
    intro z hz
    refine ⟨e z, ball_subset_closedBall (hCr (mem_image_of_mem e hz)), ?_⟩
    exact e.left_inv (hKe hz)
  have hLu : ¬ IsBounded Lᶜ := by
    intro hb
    have hall : IsBounded (univ : Set ℂ) := by
      simpa only [union_compl_self] using hL.isBounded.union hb
    exact ComplexApproximation.not_isBounded_exterior 1 (hall.subset (subset_univ _))
  exact (ComplexApproximation.fill_subset_of_unbounded_preconnected_complement
    hKL hLc.isPreconnected hLu).trans hLU

end AreaDeficit
