import ComplexDynamics.Basic

open Function Filter Set Metric
open scoped Topology Uniformity OnePoint

namespace ComplexDynamics

theorem tendsto_coe_sphere_cobounded :
    Tendsto (fun z : ℂ => (z : RiemannSphere)) (Bornology.cobounded ℂ)
      (𝓝 (∞ : RiemannSphere)) := by
  simpa only [Metric.cobounded_eq_cocompact, coclosedCompact_eq_cocompact] using
    (OnePoint.tendsto_coe_infty (X := ℂ))

theorem tendsto_sphericalIterate_of_mem_escapingSet {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ escapingSet f) :
    Tendsto (fun n => sphericalIterate f n z) atTop (𝓝 (∞ : RiemannSphere)) :=
  tendsto_coe_sphere_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hz)

theorem EscapesUniformlyOn.tendstoUniformlyOn_sphericalIterate
    {f : ℂ → ℂ} {K : Set ℂ} (h : EscapesUniformlyOn f K) :
    TendstoUniformlyOn (sphericalIterate f) (fun _ => (∞ : RiemannSphere)) atTop K := by
  intro V hV
  have hpair := tendsto_left_nhds_uniformity.comp tendsto_coe_sphere_cobounded
  have hpre : {z : ℂ | ((∞ : RiemannSphere), (z : RiemannSphere)) ∈ V} ∈
      Bornology.cobounded ℂ := hpair hV
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hpre
  exact (h R).mono fun n hn z hz => hR (hn z hz).le

theorem EscapesUniformlyOn.isNormalSequenceOn {f : ℂ → ℂ} {K : Set ℂ}
    (h : EscapesUniformlyOn f K) : IsNormalSequenceOn (sphericalIterate f) K :=
  isNormalSequenceOn_of_tendstoLocallyUniformly
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp
      h.tendstoUniformlyOn_sphericalIterate).tendstoLocallyUniformly

/-- Uniform escape directly implies normality on the interior. -/
theorem EscapesUniformlyOn.interior_subset_fatouSet {f : ℂ → ℂ} {K : Set ℂ}
    (h : EscapesUniformlyOn f K) : interior K ⊆ fatouSet f := by
  intro z hz
  exact ⟨interior K, isOpen_interior, hz, h.isNormalSequenceOn.mono interior_subset⟩

end ComplexDynamics
