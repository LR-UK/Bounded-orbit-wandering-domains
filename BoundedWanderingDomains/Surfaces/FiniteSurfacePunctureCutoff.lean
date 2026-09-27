/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SurfaceLogCutoff

/-! # A cutoff around finitely many surface punctures -/

open Set Function Filter Metric
open scoped Manifold Topology ContDiff BigOperators

namespace AreaDeficit.Surfaces

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M]

/-- Pairwise disjoint coordinate discs centred at a finite set of points. -/
structure FinitePunctureDiscs (F : Finset M) where
  disc : ↥F → RiemannDynamics.CoordDisk M
  center : ∀ i, (disc i).center = (i : M)
  pairwise : (Set.univ : Set ↥F).PairwiseDisjoint
    (fun i => (disc i).closedCarrier)

theorem exists_finitePunctureDiscs (F : Finset M) :
    Nonempty (FinitePunctureDiscs F) := by
  classical
  obtain ⟨U, hU, hUdisj⟩ := F.finite_toSet.t2_separation
  let D : ↥F → RiemannDynamics.CoordDisk M := fun i =>
    Classical.choose
      (SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset
        (hU (i : M)).2 (hU (i : M)).1)
  have hD : ∀ i : ↥F,
      (D i).center = (i : M) ∧ (D i).closedCarrier ⊆ U i := by
    intro i
    exact Classical.choose_spec
      (SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset
        (hU (i : M)).2 (hU (i : M)).1)
  refine ⟨⟨D, fun i => (hD i).1, ?_⟩⟩
  intro i _ j _ hij
  exact (hUdisj i.property j.property (by
    intro h
    apply hij
    exact Subtype.ext h)).mono (hD i).2 (hD j).2

namespace FinitePunctureDiscs

/-- One minus the sum of shrinking logarithmic cutoffs at the punctures. -/
noncomputable def cutoff {F : Finset M} (D : FinitePunctureDiscs F)
    (t : ℝ) (x : M) : ℝ :=
  1 - ∑ i : ↥F, surfaceLogCutoff (D.disc i) t x

def Admissible {F : Finset M} (D : FinitePunctureDiscs F) (t : ℝ) : Prop :=
  0 < t ∧ ∀ i : ↥F, -Real.log (D.disc i).radius ≤ t

theorem eventually_admissible {F : Finset M}
    (D : FinitePunctureDiscs F) :
    ∀ᶠ t : ℝ in atTop, D.Admissible t := by
  have hr : ∀ᶠ t : ℝ in atTop,
      ∀ i : ↥F, -Real.log (D.disc i).radius ≤ t := by
    exact ((Filter.eventually_all_finite Set.finite_univ).2 fun i _ =>
      eventually_ge_atTop (-Real.log (D.disc i).radius)).mono
        (fun _ h i => h i (mem_univ i))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hr] with t ht hrt
  exact ⟨ht, hrt⟩

theorem cutoff_contMDiff {F : Finset M} (D : FinitePunctureDiscs F)
    {t : ℝ} (ht : D.Admissible t) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (D.cutoff t) := by
  exact contMDiff_const.sub (ContMDiff.sum fun i _ =>
    surfaceLogCutoff_contMDiff (D.disc i) ht.1 (ht.2 i))

theorem cutoff_hasCompactSupport [CompactSpace M]
    {F : Finset M} (D : FinitePunctureDiscs F) (t : ℝ) :
    HasCompactSupport (D.cutoff t) :=
  isCompact_univ.of_isClosed_subset (isClosed_tsupport (D.cutoff t))
    (subset_univ _)

private theorem cutoff_sum_eq_single {F : Finset M}
    (D : FinitePunctureDiscs F) {t : ℝ} (ht : D.Admissible t)
    {x : M} {i : ↥F} (hi : surfaceLogCutoff (D.disc i) t x ≠ 0) :
    (∑ j : ↥F, surfaceLogCutoff (D.disc j) t x) =
      surfaceLogCutoff (D.disc i) t x := by
  apply Finset.sum_eq_single i
  · intro j _ hji
    by_contra hj
    have hxi : x ∈ (D.disc i).closedCarrier :=
      surfaceLogCutoff_tsupport_subset_closedCarrier
        (D.disc i) ht.1 (ht.2 i) (subset_closure hi)
    have hxj : x ∈ (D.disc j).closedCarrier :=
      surfaceLogCutoff_tsupport_subset_closedCarrier
        (D.disc j) ht.1 (ht.2 j) (subset_closure hj)
    exact Set.disjoint_left.mp
      (D.pairwise (mem_univ i) (mem_univ j) hji.symm) hxi hxj
  · simp

theorem cutoff_bounds {F : Finset M} (D : FinitePunctureDiscs F)
    {t : ℝ} (ht : D.Admissible t) (x : M) :
    0 ≤ D.cutoff t x ∧ D.cutoff t x ≤ 1 := by
  classical
  by_cases h : ∃ i : ↥F, surfaceLogCutoff (D.disc i) t x ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [cutoff, D.cutoff_sum_eq_single ht hi]
    have hb := surfaceLogCutoff_bounds (D.disc i) t x
    constructor <;> linarith
  · have hz : (∑ i : ↥F, surfaceLogCutoff (D.disc i) t x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
    rw [cutoff, hz]
    constructor <;> norm_num

theorem cutoff_eq_zero_at_puncture {F : Finset M}
    (D : FinitePunctureDiscs F) {t : ℝ} (ht : D.Admissible t)
    (i : ↥F) : D.cutoff t i = 0 := by
  have hi : surfaceLogCutoff (D.disc i) t (i : M) = 1 := by
    rw [← D.center i]
    exact surfaceLogCutoff_center (D.disc i) ht.1
  have hine : surfaceLogCutoff (D.disc i) t (i : M) ≠ 0 := by linarith
  rw [cutoff, D.cutoff_sum_eq_single ht hine, hi]
  ring

theorem cutoff_tsupport_avoids {F : Finset M}
    (D : FinitePunctureDiscs F) {t : ℝ} (ht : D.Admissible t) :
    tsupport (D.cutoff t) ⊆ (↑F : Set M)ᶜ := by
  intro x hx hxF
  let i : ↥F := ⟨x, hxF⟩
  have hzero : D.cutoff t =ᶠ[𝓝 x] 0 := by
    have hxsource : x ∈ (chartAt ℂ (D.disc i).center).source := by
      rw [D.center i]
      exact mem_chart_source ℂ x
    have hball : ball (chartAt ℂ (D.disc i).center x)
        (Real.exp (-2 * t)) ∈ 𝓝 (chartAt ℂ (D.disc i).center x) :=
      ball_mem_nhds _ (Real.exp_pos _)
    have hpre : (chartAt ℂ (D.disc i).center) ⁻¹'
        ball (chartAt ℂ (D.disc i).center x) (Real.exp (-2 * t)) ∈ 𝓝 x :=
      (chartAt ℂ (D.disc i).center).continuousAt hxsource hball
    filter_upwards [
      (chartAt ℂ (D.disc i).center).open_source.mem_nhds hxsource,
      hpre] with y hys hyb
    have hcenter : (D.disc i).center = x := D.center i
    change dist (chartAt ℂ (D.disc i).center y)
      (chartAt ℂ (D.disc i).center x) < Real.exp (-2 * t) at hyb
    have hone : surfaceLogCutoff (D.disc i) t y = 1 :=
      surfaceLogCutoff_eq_one (D.disc i) ht.1 hys (by
        rw [hcenter]
        simpa only [dist_eq_norm] using
          (show dist (chartAt ℂ x y) (chartAt ℂ x x) < _ by
            simpa only [hcenter] using hyb).le)
    have hine : surfaceLogCutoff (D.disc i) t y ≠ 0 := by linarith
    rw [cutoff, D.cutoff_sum_eq_single ht hine, hone]
    simp
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hx

theorem cutoff_eventually_one {F : Finset M}
    (D : FinitePunctureDiscs F) {x : M} (hx : x ∉ F) :
    ∀ᶠ t : ℝ in atTop, D.cutoff t x = 1 := by
  have hzero : ∀ᶠ t : ℝ in atTop,
      ∀ i : ↥F, surfaceLogCutoff (D.disc i) t x = 0 := by
    refine ((Filter.eventually_all_finite Set.finite_univ).2 fun i _ =>
      surfaceLogCutoff_eventually_zero (D.disc i) ?_).mono
        (fun _ h i => h i (mem_univ i))
    intro hxi
    apply hx
    have : x = (i : M) := hxi.trans (D.center i)
    exact this ▸ i.property
  filter_upwards [hzero] with t ht
  simp [cutoff, ht]

end FinitePunctureDiscs
end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.exists_finitePunctureDiscs
#print axioms AreaDeficit.Surfaces.FinitePunctureDiscs.cutoff_tsupport_avoids
