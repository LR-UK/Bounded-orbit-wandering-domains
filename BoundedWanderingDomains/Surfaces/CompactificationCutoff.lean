/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FiniteSurfacePunctureCutoff

/-! # Restricting compact-surface puncture cutoffs to an open subsurface -/

open Set Function Filter Metric
open scoped Manifold Topology ContDiff

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

namespace FinitePunctureDiscs

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- Restricting an ambient function whose support stays in the open subtype
preserves compact support when the ambient space is compact. -/
theorem hasCompactSupport_restrict_of_tsupport_subset [CompactSpace X]
    (O : TopologicalSpace.Opens X) {g : X → ℝ}
    (hgO : tsupport g ⊆ O) :
    HasCompactSupport (g ∘ (Subtype.val : O → X)) := by
  let K : Set O := (Subtype.val : O → X) ⁻¹' tsupport g
  have hK : IsCompact K := by
    have hgrange : tsupport g ⊆
        Set.range (Subtype.val : O → X) := by
      intro x hx
      exact ⟨⟨x, hgO hx⟩, rfl⟩
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
      image_preimage_eq_of_subset hgrange]
    exact (isClosed_tsupport g).isCompact
  apply HasCompactSupport.of_support_subset_isCompact hK
  exact subset_closure.trans
    (tsupport_comp_subset_preimage g continuous_subtype_val)

/-- Restriction to an open subsurface of the finite cutoff constructed on a
compactifying surface. -/
noncomputable def restrictedCutoff {F : Finset X}
    (D : FinitePunctureDiscs F) (O : TopologicalSpace.Opens X)
    (t : ℝ) : O → ℝ :=
  D.cutoff t ∘ (Subtype.val : O → X)

/-- Restriction of one logarithmic end cutoff to an open subsurface. -/
noncomputable def restrictedSurfaceLogCutoff
    (D : RiemannDynamics.CoordDisk X) (O : TopologicalSpace.Opens X)
    (t : ℝ) : O → ℝ :=
  surfaceLogCutoff D t ∘ (Subtype.val : O → X)

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] [T2Space X] in
theorem restrictedCutoff_apply {F : Finset X}
    (D : FinitePunctureDiscs F) (O : TopologicalSpace.Opens X)
    (t : ℝ) (x : O) :
    D.restrictedCutoff O t x = D.cutoff t (x : X) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] [T2Space X] in
theorem restrictedSurfaceLogCutoff_apply
    (D : RiemannDynamics.CoordDisk X) (O : TopologicalSpace.Opens X)
    (t : ℝ) (x : O) :
    restrictedSurfaceLogCutoff D O t x = surfaceLogCutoff D t (x : X) := rfl

theorem restrictedCutoff_contMDiff {F : Finset X}
    (D : FinitePunctureDiscs F) (O : TopologicalSpace.Opens X)
    {t : ℝ} (ht : D.Admissible t) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (D.restrictedCutoff O t) := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ X := isManifold_real_of_complex
  let : IsManifold 𝓘(ℝ, ℂ) ∞ O := isManifold_real_of_complex
  exact (D.cutoff_contMDiff ht).comp
    (contMDiff_subtype_val (I := 𝓘(ℝ, ℂ)) (n := 2))

theorem restrictedSurfaceLogCutoff_contMDiff
    (D : RiemannDynamics.CoordDisk X) (O : TopologicalSpace.Opens X)
    {t : ℝ} (ht : 0 < t) (hr : -Real.log D.radius ≤ t) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2
      (restrictedSurfaceLogCutoff D O t) := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ X := isManifold_real_of_complex
  let : IsManifold 𝓘(ℝ, ℂ) ∞ O := isManifold_real_of_complex
  exact (surfaceLogCutoff_contMDiff D ht hr).comp
    (contMDiff_subtype_val (I := 𝓘(ℝ, ℂ)) (n := 2))

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- If the ambient cutoff support stays in the open subsurface, its
restriction has compact support there. -/
theorem restrictedCutoff_hasCompactSupport [CompactSpace X]
    {F : Finset X} (D : FinitePunctureDiscs F)
    (O : TopologicalSpace.Opens X) (t : ℝ)
    (hDO : tsupport (D.cutoff t) ⊆ O) :
    HasCompactSupport (D.restrictedCutoff O t) :=
  hasCompactSupport_restrict_of_tsupport_subset O hDO

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- The restricted cutoff can only be supported over points which are not
among the ambient punctures. -/
theorem restrictedCutoff_tsupport_avoids {F : Finset X}
    (D : FinitePunctureDiscs F) (O : TopologicalSpace.Opens X)
    {t : ℝ} (ht : D.Admissible t) :
    tsupport (D.restrictedCutoff O t) ⊆
      (Subtype.val : O → X) ⁻¹' ((↑F : Set X)ᶜ) := by
  exact (tsupport_comp_subset_preimage (D.cutoff t)
    continuous_subtype_val).trans (preimage_mono (D.cutoff_tsupport_avoids ht))

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- On a compactification, including every missing point among the cutoff
centres makes the restricted cutoff compactly supported. -/
theorem restrictedCutoff_hasCompactSupport_of_compl_finset [CompactSpace X]
    {F : Finset X} (D : FinitePunctureDiscs F)
    (O : TopologicalSpace.Opens X) (E : Finset X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E) (hEF : E ⊆ F)
    {t : ℝ} (ht : D.Admissible t) :
    HasCompactSupport (D.restrictedCutoff O t) := by
  apply D.restrictedCutoff_hasCompactSupport O t
  intro x hx
  exact (hO x).mpr (fun hxE =>
    D.cutoff_tsupport_avoids ht hx (hEF hxE))

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
theorem restrictedCutoff_bounds {F : Finset X}
    (D : FinitePunctureDiscs F) (O : TopologicalSpace.Opens X)
    {t : ℝ} (ht : D.Admissible t) (x : O) :
    0 ≤ D.restrictedCutoff O t x ∧ D.restrictedCutoff O t x ≤ 1 :=
  D.cutoff_bounds ht (x : X)

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] [T2Space X] in
theorem restrictedCutoff_eventually_one {F : Finset X}
    (D : FinitePunctureDiscs F) (O : TopologicalSpace.Opens X)
    {x : O} (hx : (x : X) ∉ F) :
    ∀ᶠ t : ℝ in atTop, D.restrictedCutoff O t x = 1 :=
  D.cutoff_eventually_one hx

/-- Difference of two readings of one end cutoff.  The subtraction removes
the constant value at the missing end and therefore has compact support on
the punctured compactification. -/
noncomputable def restrictedSurfaceLogCutoffDiff
    (D : RiemannDynamics.CoordDisk X) (O : TopologicalSpace.Opens X)
    (t s : ℝ) : O → ℝ :=
  (surfaceLogCutoff D t - surfaceLogCutoff D s) ∘
    (Subtype.val : O → X)

theorem restrictedSurfaceLogCutoffDiff_contMDiff
    (D : RiemannDynamics.CoordDisk X) (O : TopologicalSpace.Opens X)
    {t s : ℝ} (ht : 0 < t) (hrt : -Real.log D.radius ≤ t)
    (hs : 0 < s) (hrs : -Real.log D.radius ≤ s) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2
      (restrictedSurfaceLogCutoffDiff D O t s) := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ X := isManifold_real_of_complex
  let : IsManifold 𝓘(ℝ, ℂ) ∞ O := isManifold_real_of_complex
  exact ((surfaceLogCutoff_contMDiff D ht hrt).sub
    (surfaceLogCutoff_contMDiff D hs hrs)).comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, ℂ)) (n := 2))

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- The difference of two logarithmic cutoffs at one member of a disjoint
finite family avoids every centre of that family. -/
theorem tsupport_surfaceLogCutoff_sub_subset_compl
    {F : Finset X} (D : FinitePunctureDiscs F) (i : ↑F)
    {t s : ℝ} (ht : D.Admissible t) (hs : D.Admissible s) :
    tsupport (surfaceLogCutoff (D.disc i) t -
      surfaceLogCutoff (D.disc i) s) ⊆ ((↑F : Set X)ᶜ) := by
  intro x hx hxF
  let j : ↑F := ⟨x, hxF⟩
  have hzero : (surfaceLogCutoff (D.disc i) t -
      surfaceLogCutoff (D.disc i) s) =ᶠ[𝓝 x] 0 := by
    by_cases hji : j = i
    · have hxi : x = (i : X) := congrArg Subtype.val hji
      subst x
      have htone := surfaceLogCutoff_eventuallyEq_one_center
        (D.disc i) ht.1
      have hsone := surfaceLogCutoff_eventuallyEq_one_center
        (D.disc i) hs.1
      have htone' : surfaceLogCutoff (D.disc i) t =ᶠ[𝓝 (i : X)]
          (fun _ => (1 : ℝ)) := by simpa only [D.center i] using htone
      have hsone' : surfaceLogCutoff (D.disc i) s =ᶠ[𝓝 (i : X)]
          (fun _ => (1 : ℝ)) := by simpa only [D.center i] using hsone
      filter_upwards [htone', hsone'] with y hyt hys
      simp [hyt, hys]
    · have hxj : x ∈ (D.disc j).closedCarrier := by
        rw [show x = (j : X) from rfl, ← D.center j]
        refine ⟨chartAt ℂ (D.disc j).center (D.disc j).center, ?_, ?_⟩
        · simpa only [mem_closedBall, dist_self] using (D.disc j).radius_pos.le
        · exact (chartAt ℂ (D.disc j).center).left_inv
            (mem_chart_source ℂ (D.disc j).center)
      have hxi : x ∉ (D.disc i).closedCarrier := by
        intro hxi
        exact Set.disjoint_left.mp
          (D.pairwise (mem_univ j) (mem_univ i) hji) hxj hxi
      have hnt : x ∉ tsupport (surfaceLogCutoff (D.disc i) t) :=
        fun h => hxi (surfaceLogCutoff_tsupport_subset_closedCarrier
          (D.disc i) ht.1 (ht.2 i) h)
      have hns : x ∉ tsupport (surfaceLogCutoff (D.disc i) s) :=
        fun h => hxi (surfaceLogCutoff_tsupport_subset_closedCarrier
          (D.disc i) hs.1 (hs.2 i) h)
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnt,
        notMem_tsupport_iff_eventuallyEq.mp hns] with y hyt hys
      simp at hyt hys
      simp [hyt, hys]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hx

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
theorem restrictedSurfaceLogCutoffDiff_hasCompactSupport [CompactSpace X]
    {F : Finset X} (D : FinitePunctureDiscs F) (i : ↑F)
    (O : TopologicalSpace.Opens X) (E : Finset X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E) (hEF : E ⊆ F)
    {t s : ℝ} (ht : D.Admissible t) (hs : D.Admissible s) :
    HasCompactSupport
      (restrictedSurfaceLogCutoffDiff (D.disc i) O t s) := by
  apply hasCompactSupport_restrict_of_tsupport_subset O
  intro x hx
  exact (hO x).mpr (fun hxE =>
    D.tsupport_surfaceLogCutoff_sub_subset_compl i ht hs hx (hEF hxE))

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- Restricting a normalized end cutoff difference preserves avoidance of
every centre in the ambient finite family. -/
theorem restrictedSurfaceLogCutoffDiff_tsupport_avoids
    {F : Finset X} (D : FinitePunctureDiscs F) (i : ↑F)
    (O : TopologicalSpace.Opens X) {t s : ℝ}
    (ht : D.Admissible t) (hs : D.Admissible s) :
    tsupport (restrictedSurfaceLogCutoffDiff (D.disc i) O t s) ⊆
      (Subtype.val : O → X) ⁻¹' ((↑F : Set X)ᶜ) := by
  exact (tsupport_comp_subset_preimage
    (surfaceLogCutoff (D.disc i) t - surfaceLogCutoff (D.disc i) s)
      continuous_subtype_val).trans
    (preimage_mono (D.tsupport_surfaceLogCutoff_sub_subset_compl i ht hs))

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X] in
/-- Reading a restricted ambient function in the restricted chart gives the
same zero extension as reading the ambient function, provided its support
does not meet the deleted part of the surface. -/
theorem chartZeroExtensionIn_subtypeRestr
    (O : TopologicalSpace.Opens X) (hON : Nonempty O)
    {g : X → ℝ} (hgO : tsupport g ⊆ O)
    (c : OpenPartialHomeomorph X ℂ) :
    chartZeroExtensionIn (c.subtypeRestr hON)
        (g ∘ (Subtype.val : O → X)) =
      chartZeroExtensionIn c g := by
  funext z
  by_cases hzO : z ∈ (c.subtypeRestr hON).target
  · have hzc : z ∈ c.target := c.subtypeRestr_target_subset hON hzO
    rw [chartZeroExtensionIn_eq hzO, chartZeroExtensionIn_eq hzc]
    exact congrArg g (by
      simpa only [Function.comp_apply] using c.subtypeRestr_symm_apply hON hzO)
  · rw [show chartZeroExtensionIn (c.subtypeRestr hON)
        (g ∘ (Subtype.val : O → X)) z = 0 by
      simp [chartZeroExtensionIn, hzO]]
    by_cases hzc : z ∈ c.target
    · rw [chartZeroExtensionIn_eq hzc]
      have hgzero : g (c.symm z) = 0 := by
        by_contra hne
        have hxO : c.symm z ∈ O := hgO (subset_closure hne)
        let x : O := ⟨c.symm z, hxO⟩
        have hxs : x ∈ (c.subtypeRestr hON).source := by
          simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
            using c.map_target hzc
        have hmap := (c.subtypeRestr hON).map_source hxs
        have heq : c x = z := c.right_inv hzc
        exact hzO (heq ▸ hmap)
      exact hgzero.symm
    · simp [chartZeroExtensionIn, hzc]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) 1 X] [T2Space X] in
/-- Zero extension through a chart is linear under subtraction. -/
theorem chartZeroExtensionIn_sub (c : OpenPartialHomeomorph X ℂ)
    (f g : X → ℝ) :
    chartZeroExtensionIn c (f - g) =
      chartZeroExtensionIn c f - chartZeroExtensionIn c g := by
  funext z
  by_cases hz : z ∈ c.target <;>
    simp [chartZeroExtensionIn, hz, Pi.sub_apply]

omit [IsManifold 𝓘(ℂ, ℂ) 1 X] in
/-- A compactly supported difference of two end cutoffs reads in the
restricted coordinate exactly as the corresponding planar difference. -/
theorem chartZeroExtensionIn_restrictedSurfaceLogCutoffDiff
    {F : Finset X} (D : FinitePunctureDiscs F) (i : ↑F)
    (O : TopologicalSpace.Opens X) (hON : Nonempty O) (E : Finset X)
    (hO : ∀ x : X, x ∈ O ↔ x ∉ E) (hEF : E ⊆ F)
    {t s : ℝ} (ht : D.Admissible t) (hs : D.Admissible s) :
    chartZeroExtensionIn
        ((chartAt ℂ (D.disc i).center).subtypeRestr hON)
        (restrictedSurfaceLogCutoffDiff (D.disc i) O t s) =
      AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * t) (-t) -
        AreaDeficit.logCutoff
          (chartAt ℂ (D.disc i).center (D.disc i).center)
          (-2 * s) (-s) := by
  let c := chartAt ℂ (D.disc i).center
  let g := surfaceLogCutoff (D.disc i) t -
    surfaceLogCutoff (D.disc i) s
  have hgO : tsupport g ⊆ O := by
    intro x hx
    exact (hO x).mpr (fun hxE =>
      D.tsupport_surfaceLogCutoff_sub_subset_compl i ht hs hx (hEF hxE))
  change chartZeroExtensionIn (c.subtypeRestr hON)
      (g ∘ (Subtype.val : O → X)) = _
  rw [chartZeroExtensionIn_subtypeRestr O hON hgO c,
    chartZeroExtensionIn_sub c,
    chartZeroExtensionIn_surfaceLogCutoff (D.disc i) ht.1 (ht.2 i),
    chartZeroExtensionIn_surfaceLogCutoff (D.disc i) hs.1 (hs.2 i)]

end FinitePunctureDiscs
end AreaDeficit.Surfaces
