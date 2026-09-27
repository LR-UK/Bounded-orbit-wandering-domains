/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactDiscImages
import BoundedWanderingDomains.ShrinkingImages

/-! # Shrinking disjoint holomorphic discs on a covered surface

Lift the discs with centres in one compact set of the universal disc cover.
Their lifted images remain disjoint, so ordinary bounded Montel and Hurwitz
give the existing planar shrinking theorem. This transfers shrinking to any
open cover of the compact set of marked points on the surface.
-/

open Set Function Filter Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces.DiscCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

theorem disjoint_disc_images_eventually_in_cover
    (p : DiscCover X) {K : Set X} (hK : IsCompact K)
    (F : ℕ → unitDisc → X)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    {ι : Sort*} (V : ι → Set X) (hV : ∀ i, IsOpen (V i))
    (hcover : K ⊆ ⋃ i, V i) {r : ℝ} (hr1 : r < 1) :
    ∀ᶠ n in atTop, ∃ i, ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → F n z ∈ V i := by
  obtain ⟨B, hB, hKB⟩ := p.compact_lift_set hK
  let C := B ∩ p.projection ⁻¹' K
  have hC : IsCompact C := hB.inter_right (hK.isClosed.preimage p.continuous)
  choose b hbB hbp using fun n => hKB (hcentre n)
  have hbC : ∀ n, b n ∈ C := fun n => ⟨hbB n, by
    change p.projection (b n) ∈ K
    rw [hbp]; exact hcentre n⟩
  letI : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  letI : LocallyPathConnectedSpace unitDisc :=
    ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  choose H hH0 hfac hH using fun n =>
    exists_holomorphic_lift p.holomorphic p.covering (hF n)
      discZero (b n) (hbp n)
  have hfac' : ∀ n z, p.projection (H n z) = F n z :=
    fun n z => congrFun (hfac n) z
  let G : ℕ → ℂ → ℂ := fun n => planeExtension (fun z => (H n z : ℂ))
  have hG : ∀ n, DifferentiableOn ℂ (G n) (ball 0 1) := fun n =>
    planeExtension_differentiableOn ((mdifferentiable_subtype_val unitDisc).comp (hH n))
  have hbound : ∀ n z, z ∈ ball (0 : ℂ) 1 → ‖G n z‖ ≤ 1 := by
    intro n z hz
    rw [show G n z = (H n ⟨z, hz⟩ : ℂ) from planeExtension_coe _ ⟨z, hz⟩]
    exact (mem_ball_zero_iff.mp (H n ⟨z, hz⟩).property).le
  have hGdis : Pairwise (fun n m =>
      Disjoint (G n '' ball 0 1) (G m '' ball 0 1)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hwy⟩
    have hval : (H n ⟨z, hz⟩ : ℂ) = (H m ⟨w, hw⟩ : ℂ) := by
      exact (planeExtension_coe _ (⟨z, hz⟩ : unitDisc)).symm.trans
        ((hzy.trans hwy.symm).trans (planeExtension_coe _ (⟨w, hw⟩ : unitDisc)))
    have hproj := congrArg p.projection (Subtype.ext hval)
    rw [hfac', hfac'] at hproj
    exact Set.disjoint_left.mp (hdis hnm)
      (show F n ⟨z, hz⟩ ∈ range (F n) from mem_range_self _)
      (hproj.symm ▸ (show F m ⟨w, hw⟩ ∈ range (F m) from mem_range_self _))
  have hshrink := AreaDeficit.disjoint_bounded_images_shrink isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected (by simp : (0 : ℂ) ∈ ball 0 1)
    (isCompact_closedBall (0 : ℂ) r) (closedBall_subset_ball hr1)
    hG hbound hGdis
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric hC
    (fun i => (hV i).preimage p.continuous) (by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx.2)
      exact mem_iUnion.mpr ⟨i, hi⟩)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hshrink δ hδ] with n hn
  obtain ⟨i, hi⟩ := hδcover (b n) (hbC n)
  refine ⟨i, ?_⟩
  intro z hz
  have hdist : dist (H n z) (b n) < δ := by
    change dist (H n z : ℂ) (b n : ℂ) < δ
    have hh := hn (z : ℂ) (mem_closedBall_zero_iff.mpr hz)
    have hzero : G n 0 = (b n : ℂ) := by
      change planeExtension (fun z => (H n z : ℂ)) (discZero : ℂ) = _
      rw [planeExtension_coe, hH0]
    rw [hzero] at hh
    simpa only [G, planeExtension_coe, dist_eq_norm,
      zero_sub, norm_neg] using hh
  have hh := hi hdist
  change p.projection (H n z) ∈ V i at hh
  simpa only [hfac'] using hh

end AreaDeficit.Surfaces.DiscCover
