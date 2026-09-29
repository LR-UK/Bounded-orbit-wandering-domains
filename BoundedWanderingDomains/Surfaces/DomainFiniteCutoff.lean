module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainRemoteBound
public import BoundedWanderingDomains.Surfaces.FinitePunctureChartTarget

@[expose] public section

/-! # Uniform cutoff estimates for componentwise finite-puncture metrics -/
open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem domain_chart_gain_cutoff_finite_exceptions (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (F : Finset ℂ) {D : Set ℂ} (hD : IsOpen D)
    (hDV : ∀ z ∈ D, z ∉ F → z ∈ domainChartSet V c)
    {chi : ℂ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hchi : ContDiff ℝ 2 chi) (hcomp : HasCompactSupport chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hsupp : tsupport chi ⊆ D)
    (hbound : ∀ z ∈ D, z ∉ F → Real.log (p.domainChartDensity V c z) -
      Real.log (p.domainChartDensity U c z) ≤ B) :
    (∫⁻ z, ENNReal.ofReal (chi z * (if z ∈ F then 0 else
      (p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2))) ≤
      ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  have hDU : ∀ z ∈ D, z ∉ F → z ∈ domainChartSet U c :=
    fun z hz hf => ⟨(hDV z hz hf).1, hVU (hDV z hz hf).2⟩
  have hmain := AreaDeficit.density_deficit_cutoff F hD hB hchi hcomp hchi0 hsupp
    (a := p.domainChartDensity V c) (b := p.domainChartDensity U c)
    (fun z hz hf => ⟨p.domainChartDensity_pos V hc (hDV z hz hf),
      p.domainChartDensity_contDiffAt V hc (hDV z hz hf)⟩)
    (fun z hz hf => ⟨p.domainChartDensity_pos U hc (hDU z hz hf),
      p.domainChartDensity_contDiffAt U hc (hDU z hz hf)⟩)
    (fun z hz hf => p.domainChartDensity_curvature V hc (hDV z hz hf))
    (fun z hz hf => p.domainChartDensity_curvature U hc (hDU z hz hf))
    (fun z hz hf => max_le (hbound z hz hf) hB)
  convert hmain using 1
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ tsupport chi
  · by_cases hf : z ∈ F
    · simp [hf]
    · have hm := p.domainChartDensity_mono hVU hc (hDV z (hsupp hz) hf)
      have hp := p.domainChartDensity_pos U hc (hDU z (hsupp hz) hf)
      have hn : 0 ≤ (p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2 := by
        nlinarith
      simp only [hf,ite_false,max_eq_left hn]
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- One fixed chart cutoff bounds every pair of finite-puncture models.
The old punctures may vary arbitrarily; the additional punctures need
only lie in the fixed closed remote set. All complements may be disconnected. -/
theorem remote_finite_models_chart_cutoff [DecidableEq M] (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {D : Set ℂ} (hD : IsOpen D) (hDc : D ⊆ c.target)
    (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (P Q : Finset M), (↑Q : Set M) ⊆ K →
      ∀ chi : ℂ → ℝ, ContDiff ℝ 2 chi → HasCompactSupport chi →
      (∀ z, 0 ≤ chi z) → tsupport chi ⊆ D →
      (∫⁻ z, ENNReal.ofReal (chi z *
        ((p.domainChartDensity (finitePunctureDomain (P ∪ Q)) c z)^2 -
          (p.domainChartDensity (finitePunctureDomain P) c z)^2))) ≤
        ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  classical
  obtain ⟨B,hB,hbound⟩ := p.remote_domainChart_log_bound hK hC hCK
  refine ⟨B,hB,?_⟩
  intro P Q hQ chi hchi hcomp hchi0 hsupp
  let U := finitePunctureDomain P
  let V := finitePunctureDomain (P ∪ Q)
  have hVU : V ≤ U := finitePunctureDomain_antitone Finset.subset_union_left
  have hUVK : ∀ y ∈ U, y ∉ K → y ∈ V := by
    intro y hy hyK hyPQ
    rcases Finset.mem_union.mp hyPQ with hyP | hyQ
    · exact hy hyP
    · exact hyK (hQ hyQ)
  let F := chartPunctures c P
  have hDV : ∀ z ∈ D, z ∉ F → z ∈ domainChartSet V c := by
    intro z hz hzF
    have hzP : c.symm z ∉ P :=
      fun hp => hzF ((mem_chartPunctures_iff c P (hDc hz)).mpr hp)
    refine ⟨hDc hz, hUVK _ hzP ?_⟩
    exact fun hk => disjoint_left.mp hCK (hDC z hz) hk
  have hmain := p.domain_chart_gain_cutoff_finite_exceptions hVU hc F hD hDV hB
    hchi hcomp hchi0 hsupp (fun z hz hf =>
      hbound U V hVU hUVK c hc z (hDV z hz hf) (hDC z hz))
  convert hmain using 1
  apply lintegral_congr
  intro z
  change ENNReal.ofReal (chi z *
    ((p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2)) = _
  by_cases hz : z ∈ tsupport chi
  · by_cases hf : z ∈ F
    · have hzP : c.symm z ∈ P := (mem_chartPunctures_iff c P (hDc (hsupp hz))).mp hf
      have hzU : z ∉ domainChartSet U c := fun h => h.2 hzP
      have hzV : z ∉ domainChartSet V c := fun h => h.2 (Finset.mem_union_left Q hzP)
      simp only [hf,ite_true,domainChartDensity,dite_eq_right hzU,dite_eq_right hzV]
      simp
    · simp only [hf,ite_false]
  · simp [image_eq_zero_of_notMem_tsupport hz]

end AreaDeficit.Surfaces.DiscCover
