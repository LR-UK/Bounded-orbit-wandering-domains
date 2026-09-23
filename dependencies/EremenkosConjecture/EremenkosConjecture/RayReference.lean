import EremenkosConjecture.RayReturnChannel
import EremenkosConjecture.RayApproximationGeometry

/-! # The holomorphic reference function at a ray-construction stage -/

open Set Metric Function
open scoped NNReal

namespace EremenkosConjecture

open Scaffolding ComplexApproximation

namespace RayReturnChannel

def inner {f : ℂ → ℂ} {j : ℕ} {a b : ℝ} (R : RayReturnChannel f j a b) : Set ℂ :=
  closedHalfStrip rayBase (R.η / 2) (b / 4)

def domain {f : ℂ → ℂ} {j : ℕ} {a b : ℝ} (R : RayReturnChannel f j a b) : Set ℂ :=
  openHalfStrip rayBase R.η (Real.pi / 2)

theorem inner_subset_domain {f : ℂ → ℂ} {j : ℕ} {a b : ℝ}
    (R : RayReturnChannel f j a b) (hb : b ≤ 1 / 16) : R.inner ⊆ R.domain := by
  intro z hz
  exact ⟨by linarith [hz.1, R.η_pos], hz.2.trans_lt (by linarith [Real.two_le_pi])⟩

theorem ray_subset_inner {f : ℂ → ℂ} {j : ℕ} {a b : ℝ}
    (R : RayReturnChannel f j a b) (hb : 0 ≤ b) : horizontalRay rayBase ⊆ R.inner := by
  intro z hz
  exact ⟨by linarith [hz.1, R.η_pos], by simpa only [hz.2, sub_self, abs_zero] using
    (show 0 ≤ b / 4 by positivity)⟩

end RayReturnChannel

structure RayReference {j : ℕ} (S : RayStage j) (R : RayReturnChannel S.f j S.a S.b) where
  H : ℂ ≃ₜ ℂ
  extension : EqOn (S.f^[returnTime j]) H S.region
  quantitative : ∃ L L' : ℝ≥0, LipschitzWith L H ∧ LipschitzWith L' H.symm
  g : ℂ → ℂ
  D : Set ℂ
  open_domain : IsOpen D
  subset_domain : (background j ∪ H '' rayBand S.a S.b) ∪ H '' R.inner ⊆ D
  holomorphic : DifferentiableOn ℂ g D
  background_eq : EqOn g S.f (background j)
  barrier_eq : ∀ z ∈ H '' rayBand S.a S.b, g z = 0
  return_eq : ∀ z ∈ R.inner, g (H z) = R.ψ z

namespace RayReference

def controlSet {j : ℕ} {S : RayStage j} {R : RayReturnChannel S.f j S.a S.b}
    (P : RayReference S R) : Set ℂ :=
  (background j ∪ P.H '' rayBand S.a S.b) ∪ P.H '' R.inner

theorem isArakelian_controlSet {j : ℕ} {S : RayStage j} {R : RayReturnChannel S.f j S.a S.b}
    (P : RayReference S R) : IsArakelian P.controlSet :=
  S.isArakelian_configuration P.H P.extension R.η_pos R.η_small

theorem controlSet_subset_background {j : ℕ} {S : RayStage j}
    {R : RayReturnChannel S.f j S.a S.b} (P : RayReference S R) :
    P.controlSet ⊆ background (j + 1) :=
  S.configuration_subset_next_background P.H P.extension R.η_small

theorem exists_entire_approximation {j : ℕ} {S : RayStage j}
    {R : RayReturnChannel S.f j S.a S.b} (P : RayReference S R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ z ∈ P.controlSet, dist (f z) (P.g z) < ε := by
  obtain ⟨f, hf, he⟩ := arakelian_approximation_of_holomorphic P.controlSet
    P.isArakelian_controlSet P.D P.open_domain P.subset_domain P.g P.holomorphic ε hε
  exact ⟨f, hf, fun z hz => by simpa only [dist_eq_norm] using he z hz⟩

end RayReference

theorem exists_rayReference {j : ℕ} (S : RayStage j) (R : RayReturnChannel S.f j S.a S.b) :
    Nonempty (RayReference S R) := by
  obtain ⟨H, heH, L, L', hL, hL'⟩ := S.extensions (returnTime j) le_rfl
  have heHi : EqOn (S.f^[returnTime j]) H (interior S.region) := heH.mono interior_subset
  have hinv : DifferentiableOn ℂ H.symm (H '' interior S.region) :=
    differentiableOn_symm_of_holomorphic_extension isOpen_interior
      (S.entire.iterate _).differentiableOn H heHi hL'
  let W := H.symm ⁻¹' (R.domain ∩ interior S.region)
  have hW : IsOpen W := ((isOpen_openHalfStrip _ _ _).inter isOpen_interior).preimage H.symm.continuous
  have hinner : R.inner ⊆ interior S.region :=
    (hasUniformTube_halfStrip (ζ := rayBase)
      (show R.η / 2 < 2 * S.a by linarith [R.η_small, S.a_pos])
      (show S.b / 4 < 2 * S.b by linarith [S.b_pos])).interior_right.subset
  have hHW : H '' R.inner ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    change H.symm (H z) ∈ R.domain ∩ interior S.region
    rw [H.symm_apply_apply]
    exact ⟨R.inner_subset_domain S.b_small hz, hinner hz⟩
  have hψ : DifferentiableOn ℂ R.ψ R.domain := R.holomorphic 0 (by omega)
  have hh : DifferentiableOn ℂ (R.ψ ∘ H.symm) W := by
    apply hψ.comp (hinv.mono ?_) (fun _ hz => hz.1)
    intro z hz
    exact ⟨H.symm z, hz.2, H.apply_symm_apply z⟩
  have himageT : H '' S.region ⊆ targetStrip j := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← heH hz]
    exact S.mapsTo_region_target hz
  have hbgB : Disjoint (background j) (H '' rayBand S.a S.b) :=
    (disjoint_background_targetStrip j).mono_right
      ((image_mono (rayBand_subset_halfStrip S.a_pos.le S.b_pos.le)).trans himageT)
  have hbgC : Disjoint (background j) (H '' R.inner) :=
    (disjoint_background_targetStrip j).mono_right
      ((image_mono (S.inner_subset_region R.η_small)).trans himageT)
  have hBC : Disjoint (H '' rayBand S.a S.b) (H '' R.inner) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact disjoint_left.mp (disjoint_rayBand_inner R.η_small S.b_pos) hx ((H.injective hxy) ▸ hy)
  obtain ⟨D, g, hD, hsubset, hg, hbg, hbar, hret⟩ := exists_holomorphic_gluing_three_closed
    (background j) (H '' rayBand S.a S.b) (H '' R.inner) univ univ W
    (isArakelian_background j).isClosed (H.isClosedMap _ (isClosed_rayBand _ _))
    (H.isClosedMap _ (isClosed_closedHalfStrip _ _ _)) hbgB hbgC hBC
    isOpen_univ isOpen_univ hW (subset_univ _) (subset_univ _) hHW
    S.f (fun _ => 0) (R.ψ ∘ H.symm) S.entire.differentiableOn (differentiableOn_const 0) hh
  refine ⟨{
    H := H
    extension := heH
    quantitative := ⟨L, L', hL, hL'⟩
    g := g
    D := D
    open_domain := hD
    subset_domain := hsubset
    holomorphic := hg
    background_eq := fun z hz => (hbg z hz).eq_of_nhds
    barrier_eq := fun z hz => (hbar z hz).eq_of_nhds
    return_eq := ?_ }⟩
  intro z hz
  simpa only [Function.comp_apply, H.symm_apply_apply] using
    (hret (H z) (mem_image_of_mem H hz)).eq_of_nhds

end EremenkosConjecture
