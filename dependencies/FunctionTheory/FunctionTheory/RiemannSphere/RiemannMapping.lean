import FunctionTheory.RiemannSphere.Coordinates
import FunctionTheory.Conformal.RiemannMapping
import Mathlib.Geometry.Manifold.ContMDiff.Basic

open Set Metric OneDimension RiemannSphere
open scoped Topology OnePoint RiemannSphere

namespace FunctionTheory

/-- The unit disk with its inherited complex-manifold structure. -/
def unitDiskDomain : TopologicalSpace.Opens ℂ := ⟨ball 0 1, isOpen_ball⟩

/-- Riemann mapping for a spherical domain with a specified finite omitted point.
Both directions are defined only on their actual domains. Complex smoothness
is holomorphy, and is expressed using Mathlib's manifold calculus. -/
theorem exists_riemannMap_on_sphere_domain_of_omitted_point
    (U : TopologicalSpace.Opens 𝕊) (hUc : IsSimplyConnected (U : Set 𝕊))
    (a : ℂ) (ha : (a : 𝕊) ∉ U) (q : 𝕊) (hq : q ∉ U) (hqa : q ≠ (a : 𝕊)) :
    ∃ e : U ≃ₜ unitDiskDomain,
      ContMDiff I I (↑(⊤ : ℕ∞)) e ∧ ContMDiff I I (↑(⊤ : ℕ∞)) e.symm := by
  let φ := omittedPointParam a
  have hφs : φ.source = univ := omittedPointParam_source a
  have hφe := φ.isOpenEmbedding hφs
  let V : TopologicalSpace.Opens ℂ := ⟨φ ⁻¹' (U : Set 𝕊), U.isOpen.preimage hφe.continuous⟩
  have hUt : (U : Set 𝕊) ⊆ φ.target := by
    intro z hz
    rw [omittedPointParam_target]
    exact fun h => ha (h ▸ hz)
  have himg : φ '' (V : Set ℂ) = (U : Set 𝕊) := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    refine ⟨φ.symm z, ?_, φ.right_inv (hUt hz)⟩
    change φ (φ.symm z) ∈ U
    rwa [φ.right_inv (hUt hz)]
  have hVc : IsSimplyConnected (V : Set ℂ) := by
    rw [← hφe.isEmbedding.isSimplyConnected_image, himg]
    exact hUc
  have hVproper : (V : Set ℂ) ≠ univ := by
    intro hV
    have hqt : q ∈ φ.target := by simpa [φ] using hqa
    have hmem : φ.symm q ∈ V := by change φ.symm q ∈ (V : Set ℂ); rw [hV]; trivial
    apply hq
    change φ (φ.symm q) ∈ U at hmem
    rwa [φ.right_inv hqt] at hmem
  obtain ⟨f, hbij, hf, hg, -, -⟩ :=
    TauCeti.exists_bijOn_ball_differentiableOn_invFunOn V.isOpen hVc hVproper
  let c : V ≃ₜ U := φ.homeomorphOfImageSubsetSource (by rw [hφs]; exact subset_univ _) himg
  let d : V ≃ₜ unitDiskDomain := hf.toHomeomorphOfBijOn V.isOpen hbij
  refine ⟨c.symm.trans d, ?_, ?_⟩
  · apply (ContMDiff.subtypeVal_comp_iff unitDiskDomain _).mp
    intro z
    change ContMDiffAt I I (↑(⊤ : ℕ∞)) (fun z : U => f (φ.symm z)) z
    apply (contMDiffAt_subtype_iff (U := U) (f := fun w : 𝕊 => f (φ.symm w))).mpr
    have hmem : φ.symm (z : 𝕊) ∈ V := by
      change φ (φ.symm (z : 𝕊)) ∈ U
      rw [φ.right_inv (hUt z.property)]
      exact z.property
    exact ((hf.contDiffOn V.isOpen).contDiffAt (V.isOpen.mem_nhds hmem)).contMDiffAt.comp _
      ((mAnalyticAt_omittedPointParam_symm a (fun h => ha (h ▸ z.property))).of_le le_top)
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    intro z
    change ContMDiffAt I I (↑(⊤ : ℕ∞)) (fun z : unitDiskDomain => φ (Function.invFunOn f V z)) z
    apply (contMDiffAt_subtype_iff (U := unitDiskDomain)
      (f := fun w : ℂ => φ (Function.invFunOn f V w))).mpr
    exact ((mAnalytic_omittedPointParam a).of_le le_top).contMDiffAt.comp _
      (((hg.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds z.property)).contMDiffAt)

/-- Every simply connected open spherical domain omitting at least two points
is biholomorphic to the unit disk. The domain may contain infinity. -/
theorem exists_riemannMap_on_sphere_domain
    (U : TopologicalSpace.Opens 𝕊) (hUc : IsSimplyConnected (U : Set 𝕊))
    (hU : ∃ p q : 𝕊, p ∉ U ∧ q ∉ U ∧ p ≠ q) :
    ∃ e : U ≃ₜ unitDiskDomain,
      ContMDiff I I (↑(⊤ : ℕ∞)) e ∧ ContMDiff I I (↑(⊤ : ℕ∞)) e.symm := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hU
  induction p using OnePoint.rec with
  | coe a => exact exists_riemannMap_on_sphere_domain_of_omitted_point U hUc a hp q hq hpq.symm
  | infty =>
    induction q using OnePoint.rec with
    | infty => exact (hpq rfl).elim
    | coe a => exact exists_riemannMap_on_sphere_domain_of_omitted_point U hUc a hq ∞ hp hpq

end FunctionTheory
