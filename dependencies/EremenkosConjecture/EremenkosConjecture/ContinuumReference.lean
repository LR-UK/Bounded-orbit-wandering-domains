import EremenkosConjecture.ContinuumReturnChannel
import EremenkosConjecture.ContinuumRegionGeometry
import EremenkosConjecture.LocalReferenceOrbits
import EremenkosConjecture.FilledRayBandArakelian
import ComplexApproximation.Topology.StripArakelian

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding ComplexApproximation

theorem ContinuumStage.affine_le {X : Set ℂ}
    {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ} (S : ContinuumStage D j) :
    ∀ z ∈ sourceStrips, ‖S.f z - 5 * z‖ ≤ 1 / 100 := by
  intro z hz
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  have h := S.affine z (mem_iUnion.mpr ⟨k, sourceStrip_subset_closed k hk⟩)
  linarith [S.reserve_pos]

theorem ContinuumStage.mapsTo_region_target {X : Set ℂ}
    {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ} (S : ContinuumStage D j) :
    MapsTo (S.f^[returnTime j]) (D.region S.depth) (targetStrip j) := by
  obtain ⟨d, hd, hbound⟩ := S.targetMargin
  intro z hz
  obtain ⟨hl, hu⟩ := hbound z hz
  constructor <;> linarith

def ContinuumNeighbourhoods.band {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (i : ℕ) : Set ℂ :=
  D.region i \ D.openRegion (i + 2)

theorem ContinuumNeighbourhoods.band_union_inner_isArakelian {X : Set ℂ} {ζ : ℂ} {r : ℝ}
    (D : ContinuumNeighbourhoods X ζ r) (hζ : ζ ∈ X) {i n : ℕ} (hin : i + 2 < n) :
    IsArakelian (D.band i ∪ D.region n) :=
  isArakelian_filledRayBand_union_inner (D.decoration i).compact
    (D.decoration (i + 2)).compact (D.decoration n).compact (D.decoration n).connected
    (interior_subset ((D.decoration n).contains hζ))
    (D.decoration_subset_interior (by omega)) (D.decoration_subset_interior hin)
    (D.positive n) (D.decreasing hin) (D.decreasing (by omega))
    (D.positive n) (D.decreasing hin) (D.decreasing (by omega))

/-- The glued holomorphic function on the old background, the surrounding
band, and the image of the new inner neighbourhood. -/
structure ContinuumReference {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)}
    {j : ℕ} (S : ContinuumStage D j)
    (R : ContinuumReturnChannel D S.f j (S.depth + 3)) where
  oldChart : LocalIterateChart S.f (returnTime j) (D.region S.depth)
  reference : LocalReference S.f R.ψ oldChart.chart j (D.band S.depth) (D.region R.depth)

variable {X : Set ℂ} {D : ContinuumNeighbourhoods X rayBase (1 / 16)} {j : ℕ}
  {S : ContinuumStage D j} {R : ContinuumReturnChannel D S.f j (S.depth + 3)}

def ContinuumReference.controlSet (P : ContinuumReference S R) : Set ℂ :=
  (background j ∪ P.oldChart.chart '' D.band S.depth) ∪
    P.oldChart.chart '' D.region R.depth

theorem exists_continuumReference (hζ : rayBase ∈ X)
    (S : ContinuumStage D j) (R : ContinuumReturnChannel D S.f j (S.depth + 3)) :
    Nonempty (ContinuumReference S R) := by
  obtain ⟨e⟩ := S.charts (returnTime j) le_rfl
  have hinner : D.region R.depth ⊆ D.region S.depth :=
    D.region_antitone (by have := R.later; omega)
  have hwhole : D.band S.depth ∪ D.region R.depth ⊆ D.region S.depth :=
    union_subset sdiff_subset hinner
  have hBC : Disjoint (D.band S.depth) (D.region R.depth) := by
    apply disjoint_left.mpr
    intro z hz hw
    exact hz.2 (D.region_subset_openRegion hζ (by have := R.later; omega) hw)
  obtain ⟨P⟩ := exists_localReference S.entire e.chart e.inverse_holomorphic
    R.open_domain (R.holomorphic 0 (by omega))
    ((D.geometry S.depth).1.isClosed.sdiff (D.openRegion_properties (S.depth + 2)).1)
    (D.geometry R.depth).1.isClosed hBC (hwhole.trans e.contains) R.region_subset
    (e.tail.mono hwhole) (by
      intro z hz
      rw [e.agrees]
      exact S.mapsTo_region_target (hwhole hz))
  exact ⟨⟨e, P⟩⟩

theorem ContinuumReference.isArakelian_controlSet (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) : IsArakelian P.controlSet := by
  have hwhole : D.band S.depth ∪ D.region R.depth ⊆ D.region S.depth :=
    union_subset sdiff_subset (D.region_antitone (by have := R.later; omega))
  have hsource := hwhole.trans P.oldChart.contains
  have hband := D.band_union_inner_isArakelian (i := S.depth) (n := R.depth)
    hζ (by have := R.later; omega)
  have himage := hband.image_openPartialHomeomorph_of_homeomorphic_tail
    P.oldChart.chart P.oldChart.connected_source hsource (P.oldChart.tail.mono hwhole)
  obtain ⟨d, hd, hmargin⟩ := S.targetMargin
  have hbound : P.oldChart.chart '' (D.band S.depth ∪ D.region R.depth) ⊆
      {z | (height j + 7) / 4 + d ≤ z.im ∧ z.im ≤ (height j + 11) / 4 - d} := by
    rintro _ ⟨z, hz, rfl⟩
    rw [P.oldChart.agrees]
    exact hmargin z (hwhole hz)
  have hgap : Disjoint (horizontalLift (backgroundLevels j))
      (openHorizontalStrip ((height j + 7) / 4) ((height j + 11) / 4)) := by
    rw [← background_eq_horizontalLift, ← targetStrip_eq_openHorizontalStrip]
    exact disjoint_background_targetStrip j
  have h := himage.union_horizontal_background (isClosed_backgroundLevels j)
    (show (height j + 7) / 4 < (height j + 7) / 4 + d by linarith)
    (show (height j + 11) / 4 - d < (height j + 11) / 4 by linarith) hbound hgap
  simpa only [ContinuumReference.controlSet, image_union, union_assoc,
    ← background_eq_horizontalLift] using h

theorem ContinuumReference.controlSet_subset_background (P : ContinuumReference S R) :
    P.controlSet ⊆ background (j + 1) := by
  have himage : P.oldChart.chart '' D.region S.depth ⊆ background (j + 1) := by
    rintro _ ⟨z, hz, rfl⟩
    apply ball_target_subset_next_background (j := j) (z := P.oldChart.chart z) _
      (mem_ball_self (by norm_num))
    rw [P.oldChart.agrees]
    exact S.mapsTo_region_target hz
  rintro z ((hz | hz) | hz)
  · exact background_monotone (Nat.le_succ j) hz
  · exact himage (image_mono sdiff_subset hz)
  · exact himage (image_mono (D.region_antitone (by have := R.later; omega)) hz)

theorem ContinuumReference.exists_entire_approximation (P : ContinuumReference S R)
    (hζ : rayBase ∈ X) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ z ∈ P.controlSet, dist (F z) (P.reference.g z) < ε :=
  P.reference.exists_entire_approximation (P.isArakelian_controlSet hζ) hε

end EremenkosConjecture
