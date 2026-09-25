/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.MeromorphicSurfaceModel
import ComplexDynamics.Basic

/-! # Normality of meromorphic iterates in the sphere model -/

open Set Function Filter OnePoint Topology
open scoped Topology Manifold

namespace MeromorphicDynamics

noncomputable local instance sphereCompactificationUniformSpace :
    UniformSpace (OnePoint (OnePoint ℂ)) := uniformSpaceOfCompactR1

noncomputable def finiteImage (W : Set ℂ) : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' W

theorem finiteImage_subset_finiteSphereOpens (W : Set ℂ) :
    finiteImage W ⊆ finiteSphereOpens := by
  rintro _ ⟨z, _, rfl⟩
  exact coe_mem_finiteSphereOpens z

/-- The inverse finite chart maps the embedded copy of a plane set back to
that set. -/
noncomputable def finiteImageToSet (W : Set ℂ) : finiteImage W → W := fun z => by
  refine ⟨RiemannDynamics.sphereChartFinite (z : OnePoint ℂ), ?_⟩
  obtain ⟨w, hw, heq⟩ := z.property
  simpa only [← heq, RiemannDynamics.sphereChartFinite_coe] using hw

theorem continuous_finiteImageToSet (W : Set ℂ) :
    Continuous (finiteImageToSet W) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro z
  have hzfin : (z : OnePoint ℂ) ∈ finiteSphereOpens :=
    finiteImage_subset_finiteSphereOpens W z.property
  have hzsrc : (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source := by
    change (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source at hzfin
    exact hzfin
  exact (RiemannDynamics.sphereChartFinite.continuousAt hzsrc).comp
    continuous_subtype_val.continuousAt

@[simp] theorem coe_finiteImageToSet (W : Set ℂ) (z : finiteImage W) :
    ((finiteImageToSet W z : ℂ) : OnePoint ℂ) = (z : OnePoint ℂ) := by
  have hzfin : (z : OnePoint ℂ) ∈ finiteSphereOpens :=
    finiteImage_subset_finiteSphereOpens W z.property
  have hzsrc : (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source := by
    change (z : OnePoint ℂ) ∈ RiemannDynamics.sphereChartFinite.source at hzfin
    exact hzfin
  simpa only [finiteImageToSet, RiemannDynamics.sphereChartFinite_symm_apply] using
    RiemannDynamics.sphereChartFinite.left_inv hzsrc

/-- Normality of ordinary meromorphic iterates on a pole-avoiding plane set
is exactly the normality needed by the local sphere model on its embedded
copy. -/
theorem surfaceModel_isNormalOn_of_normalSequence
    {f : ℂ → ℂ} {W : Set ℂ} (hW : W ⊆ poleAvoidingSet f)
    (hN : ComplexDynamics.IsNormalSequenceOn
      (ComplexDynamics.sphericalIterate f) W) :
    (surfaceModel f).IsNormalOn (finiteImage W) := by
  intro φ hφ
  obtain ⟨ψ, hψ, g, hg⟩ := hN φ hφ
  let j := finiteImageToSet W
  let G : finiteImage W → OnePoint (OnePoint ℂ) := fun z => (g (j z) : OnePoint (OnePoint ℂ))
  refine ⟨ψ, hψ, G, ?_⟩
  have hj : Continuous j := continuous_finiteImageToSet W
  have hpre := hg.comp j hj
  have hcoe : UniformContinuous ((↑) : OnePoint ℂ → OnePoint (OnePoint ℂ)) :=
    CompactSpace.uniformContinuous_of_continuous OnePoint.continuous_coe
  have hconv := hcoe.comp_tendstoLocallyUniformly hpre
  have hseq := hconv.congr (fun n z => by
    have hzW : (j z : ℂ) ∈ W := (j z).property
    have hzpole : (j z : ℂ) ∈ poleAvoidingSet f := hW hzW
    have hzcoe : ((j z : ℂ) : OnePoint ℂ) = (z : OnePoint ℂ) :=
      coe_finiteImageToSet W z
    change ((((f^[φ (ψ n)]) (j z : ℂ) : ℂ) : OnePoint ℂ) : OnePoint (OnePoint ℂ)) =
      (surfaceModel f).compactifiedIterate (φ (ψ n)) (z : OnePoint ℂ)
    rw [← hzcoe]
    exact (surfaceModel_compactifiedIterate_coe_of_poleAvoiding
      f (φ (ψ n)) hzpole).symm)
  exact hseq.congr_right (fun z => rfl)

end MeromorphicDynamics

#print axioms MeromorphicDynamics.surfaceModel_isNormalOn_of_normalSequence
