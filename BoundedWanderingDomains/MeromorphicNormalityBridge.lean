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

noncomputable def setToFiniteImage (W : Set ℂ) : W → finiteImage W := fun z =>
  ⟨((z : ℂ) : OnePoint ℂ), ⟨z, z.property, rfl⟩⟩

theorem continuous_setToFiniteImage (W : Set ℂ) :
    Continuous (setToFiniteImage W) :=
  (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _

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

/-- Collapse the extra point introduced by compactifying the already compact
Riemann sphere onto its ordinary point at infinity. -/
noncomputable def compactificationFlatten :
    OnePoint (OnePoint ℂ) → OnePoint ℂ := fun z => z.rec ∞ id

@[simp] theorem compactificationFlatten_coe (z : OnePoint ℂ) :
    compactificationFlatten (z : OnePoint (OnePoint ℂ)) = z := rfl

@[simp] theorem compactificationFlatten_infty :
    compactificationFlatten (∞ : OnePoint (OnePoint ℂ)) = ∞ := rfl

theorem continuous_compactificationFlatten :
    Continuous compactificationFlatten := by
  rw [OnePoint.continuous_iff]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact, Filter.cocompact_eq_bot]
    exact bot_le
  · exact continuous_id

/-- Local-map normality on the embedded finite chart gives the usual
meromorphic normal-family statement. -/
theorem normalSequence_of_surfaceModel_isNormalOn
    {f : ℂ → ℂ} {W : Set ℂ} (hW : W ⊆ poleAvoidingSet f)
    (hN : (surfaceModel f).IsNormalOn (finiteImage W)) :
    ComplexDynamics.IsNormalSequenceOn
      (ComplexDynamics.sphericalIterate f) W := by
  intro φ hφ
  obtain ⟨ψ, hψ, g, hg⟩ := hN φ hφ
  let k := setToFiniteImage W
  let G : W → OnePoint ℂ := fun z => compactificationFlatten (g (k z))
  refine ⟨ψ, hψ, G, ?_⟩
  have hk : Continuous k := continuous_setToFiniteImage W
  have hpre := hg.comp k hk
  have hflat : UniformContinuous compactificationFlatten :=
    CompactSpace.uniformContinuous_of_continuous continuous_compactificationFlatten
  have hconv := hflat.comp_tendstoLocallyUniformly hpre
  have hseq := hconv.congr (fun n z => by
    have hzpole : (z : ℂ) ∈ poleAvoidingSet f := hW z.property
    change compactificationFlatten
        ((surfaceModel f).compactifiedIterate (φ (ψ n)) ((z : ℂ) : OnePoint ℂ)) =
      (((f^[φ (ψ n)]) (z : ℂ) : ℂ) : OnePoint ℂ)
    rw [surfaceModel_compactifiedIterate_coe_of_poleAvoiding f _ hzpole]
    rfl)
  exact hseq.congr_right (fun z => rfl)

/-- Meromorphic Fatou points have a genuine pole-avoiding neighbourhood on
which the ordinary iterates form a normal sphere-valued family. -/
def fatouSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ W ⊆ poleAvoidingSet f ∧
    ComplexDynamics.IsNormalSequenceOn
      (ComplexDynamics.sphericalIterate f) W}

/-- A meromorphic Fatou neighbourhood embeds into the normality locus of the
local sphere model. -/
theorem mapsTo_fatouSet_surfaceModel_omega (f : ℂ → ℂ) :
    MapsTo ((↑) : ℂ → OnePoint ℂ) (fatouSet f) (surfaceModel f).omega := by
  rintro z ⟨W, hWo, hzW, hWp, hWN⟩
  refine ⟨finiteImage W, ?_, ⟨z, hzW, rfl⟩, ?_,
    surfaceModel_isNormalOn_of_normalSequence hWp hWN⟩
  · exact OnePoint.isOpenEmbedding_coe.isOpenMap W hWo
  · rintro _ ⟨w, hw, rfl⟩
    exact poleAvoiding_mem_surfaceModel_trapped (hWp hw)

/-- Taking the inverse image under the finite inclusion and then embedding
again recovers any subset of the finite sphere chart. -/
theorem finiteImage_preimage_coe_eq {V : Set (OnePoint ℂ)}
    (hV : V ⊆ finiteSphereOpens) :
    finiteImage (((↑) : ℂ → OnePoint ℂ) ⁻¹' V) = V := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hz
  · intro y hy
    let z : ℂ := RiemannDynamics.sphereChartFinite y
    have hysrc : y ∈ RiemannDynamics.sphereChartFinite.source := by
      have hyfin := hV hy
      change y ∈ RiemannDynamics.sphereChartFinite.source at hyfin
      exact hyfin
    have hzy : (z : OnePoint ℂ) = y := by
      simpa only [z, RiemannDynamics.sphereChartFinite_symm_apply] using
        RiemannDynamics.sphereChartFinite.left_inv hysrc
    refine ⟨z, ?_, hzy⟩
    change (z : OnePoint ℂ) ∈ V
    rw [hzy]
    exact hy

/-- Every finite point of the sphere-model normality locus is a meromorphic
Fatou point in the ordinary plane formulation. -/
theorem mem_fatouSet_of_coe_mem_surfaceModel_omega
    {f : ℂ → ℂ} {z : ℂ} (hz : (z : OnePoint ℂ) ∈ (surfaceModel f).omega) :
    z ∈ fatouSet f := by
  obtain ⟨V, hVo, hzV, hVt, hVN⟩ := hz
  let W : Set ℂ := ((↑) : ℂ → OnePoint ℂ) ⁻¹' V
  have hWo : IsOpen W := hVo.preimage OnePoint.continuous_coe
  have hzW : z ∈ W := hzV
  have hWp : W ⊆ poleAvoidingSet f := by
    intro w hw
    exact poleAvoiding_of_mem_surfaceModel_trapped (hVt hw)
  refine ⟨W, hWo, hzW, hWp,
    normalSequence_of_surfaceModel_isNormalOn hWp ?_⟩
  have hVsource : V ⊆ finiteSphereOpens := by
    exact hVt.trans (surfaceModel f).trapped_subset_source
  rw [finiteImage_preimage_coe_eq hVsource]
  exact hVN

/-- The ordinary meromorphic Fatou set is precisely the finite part of the
normality locus of the sphere local model. -/
theorem mem_fatouSet_iff_coe_mem_surfaceModel_omega (f : ℂ → ℂ) (z : ℂ) :
    z ∈ fatouSet f ↔ (z : OnePoint ℂ) ∈ (surfaceModel f).omega := by
  constructor
  · intro hz
    exact mapsTo_fatouSet_surfaceModel_omega f hz
  · exact mem_fatouSet_of_coe_mem_surfaceModel_omega

end MeromorphicDynamics

#print axioms MeromorphicDynamics.surfaceModel_isNormalOn_of_normalSequence
#print axioms MeromorphicDynamics.normalSequence_of_surfaceModel_isNormalOn
#print axioms MeromorphicDynamics.mapsTo_fatouSet_surfaceModel_omega
#print axioms MeromorphicDynamics.mem_fatouSet_iff_coe_mem_surfaceModel_omega
