import EremenkosConjecture.ScaffoldingBackground
import EremenkosConjecture.ScaffoldingApproximation
import EremenkosConjecture.UnboundedIterateStability
import EremenkosConjecture.RayGeometry

/-! # Quantitative stages for the Section 7 construction

This file records the invariant and proves its initial instance. The successor
construction is a separate theorem, not an assumed field of the invariant.
-/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding

noncomputable def rayBase : ℂ := (7 / 2 : ℝ) * Complex.I

def HasQuantitativeExtensionOn (f : ℂ → ℂ) (A : Set ℂ) : Prop :=
  ∃ H : ℂ ≃ₜ ℂ, EqOn f H A ∧ ∃ L L' : ℝ≥0,
    LipschitzWith L H ∧ LipschitzWith L' H.symm

def HasUniformTube (A U : Set ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ z ∈ A, ball z r ⊆ U

structure RayStage (j : ℕ) where
  f : ℂ → ℂ
  entire : Differentiable ℂ f
  a : ℝ
  b : ℝ
  reserve : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  a_small : a ≤ 1 / 16
  b_small : b ≤ 1 / 16
  reserve_pos : 0 < reserve
  affine : ∀ z ∈ closedSourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100 - reserve
  trapping : ∀ z ∈ trappingDisk, ‖f z‖ ≤ 1 / 4 - reserve
  extensions : ∀ k ≤ returnTime j,
    HasQuantitativeExtensionOn (f^[k]) (closedHalfStrip rayBase (2 * a) (2 * b))
  orbitTubes : ∀ k < returnTime j,
    HasUniformTube ((f^[k]) '' closedHalfStrip rayBase (2 * a) (2 * b)) (background j)
  targetMargin : ∃ d : ℝ, 0 < d ∧ ∀ z ∈ closedHalfStrip rayBase (2 * a) (2 * b),
    (height j + 7) / 4 + d ≤ ((f^[returnTime j]) z).im ∧
      ((f^[returnTime j]) z).im ≤ (height j + 11) / 4 - d

namespace RayStage

def core {j : ℕ} (S : RayStage j) : Set ℂ := closedHalfStrip rayBase S.a S.b
def region {j : ℕ} (S : RayStage j) : Set ℂ := closedHalfStrip rayBase (2 * S.a) (2 * S.b)

theorem affine_le {j : ℕ} (S : RayStage j) :
    ∀ z ∈ sourceStrips, ‖S.f z - 5 * z‖ ≤ 1 / 100 := by
  intro z hz
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  have h := S.affine z (mem_iUnion.mpr ⟨k, sourceStrip_subset_closed k hk⟩)
  linarith [S.reserve_pos]

theorem mapsTo_region_target {j : ℕ} (S : RayStage j) :
    MapsTo (S.f^[returnTime j]) S.region (targetStrip j) := by
  obtain ⟨d, hd, hbound⟩ := S.targetMargin
  intro z hz
  obtain ⟨hl, hu⟩ := hbound z hz
  constructor <;> linarith

theorem ray_subset_core {j : ℕ} (S : RayStage j) : horizontalRay rayBase ⊆ S.core := by
  intro z hz
  exact ⟨by linarith [hz.1, S.a_pos], by simpa only [hz.2, sub_self, abs_zero] using S.b_pos.le⟩

end RayStage

theorem exists_initial_rayStage : Nonempty (RayStage 0) := by
  obtain ⟨f, hf, hsource, hdisk⟩ := exists_initial_entire (1 / 400) (by norm_num)
  refine ⟨{
    f := f
    entire := hf
    a := 1 / 16
    b := 1 / 16
    reserve := 1 / 400
    a_pos := by norm_num
    b_pos := by norm_num
    a_small := le_rfl
    b_small := le_rfl
    reserve_pos := by norm_num
    affine := ?_
    trapping := ?_
    extensions := ?_
    orbitTubes := ?_
    targetMargin := ?_ }⟩
  · intro z hz
    have h := hsource z hz
    linarith
  · intro z hz
    have h := hdisk z hz
    linarith
  · intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact ⟨Homeomorph.refl ℂ, fun _ _ => rfl, 1, 1, LipschitzWith.id, LipschitzWith.id⟩
  · intro k hk
    simp at hk
  · refine ⟨1 / 4, by norm_num, ?_⟩
    intro z hz
    have h := abs_le.mp hz.2
    norm_num [rayBase, height] at h ⊢
    constructor <;> linarith [h.1, h.2]

end EremenkosConjecture
