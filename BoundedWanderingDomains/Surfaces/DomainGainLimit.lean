module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainFiniteCutoff
public import BoundedWanderingDomains.Surfaces.DomainChartKernel
public import BoundedWanderingDomains.Surfaces.GainFatou

@[expose] public section

/-! # Passing the uniform remote area estimate to arbitrary subdomains

Finite approximations of the old complement and the newly removed closed
set give one uniform bound. Density convergence and Fatou pass that bound
to the actual domains. No connectedness or area-finiteness assumption occurs.
-/
open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem remote_domain_chart_cutoff (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {D : Set ℂ} (hD : IsOpen D) (hDc : D ⊆ c.target)
    (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (A : Set M) (hA : IsClosed A),
      ∀ chi : ℂ → ℝ, ContDiff ℝ 2 chi → HasCompactSupport chi →
      (∀ z, 0 ≤ chi z) → tsupport chi ⊆ D →
      (∫⁻ z in domainChartSet ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩ c,
        ENNReal.ofReal (chi z *
          ((p.domainChartDensity ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩ c z)^2 -
            (p.domainChartDensity ⟨Aᶜ,hA.isOpen_compl⟩ c z)^2))) ≤
          ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  classical
  obtain ⟨B,hB,hfinite⟩ := p.remote_finite_models_chart_cutoff hK hC hCK hc hD hDc hDC
  refine ⟨B,hB,?_⟩
  intro A hA chi hchi hcomp hchi0 hsupp
  obtain ⟨P,hP,hPA,hclP⟩ := closed_set_dense_finite_exhaustion hA
  obtain ⟨Q,hQ,hQK,hclQ⟩ := closed_set_dense_finite_exhaustion hK
  let R : ℕ → Finset M := fun n => P n ∪ Q n
  have hR : Monotone R := fun i j hij => Finset.union_subset_union (hP hij) (hQ hij)
  have hRA : ∀ n, (↑(R n) : Set M) ⊆ A ∪ K := by
    intro n x hx
    rcases Finset.mem_union.mp hx with hp | hq
    · exact Or.inl (hPA n hp)
    · exact Or.inr (hQK n hq)
  have hclR : closure (⋃ n, (↑(R n) : Set M)) = A ∪ K := by
    have he : (⋃ n, (↑(R n) : Set M)) =
        (⋃ n, (↑(P n) : Set M)) ∪ (⋃ n, (↑(Q n) : Set M)) := by
      simp only [R, Finset.coe_union, iUnion_union_distrib]
    rw [he,closure_union,hclP,hclQ]
  let U : TopologicalSpace.Opens M := ⟨Aᶜ,hA.isOpen_compl⟩
  let V : TopologicalSpace.Opens M := ⟨(A ∪ K)ᶜ,(hA.union hK).isOpen_compl⟩
  let g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (chi z *
    ((p.domainChartDensity V c z)^2 - (p.domainChartDensity U c z)^2))
  let gn : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (chi z *
    ((p.domainChartDensity (finitePunctureDomain (R n)) c z)^2 -
      (p.domainChartDensity (finitePunctureDomain (P n)) c z)^2))
  apply chart_gain_bound_of_pointwise_limit (isOpen_domainChartSet V c).measurableSet g gn
  · intro n
    exact (hchi.continuous.measurable.mul
      (((p.domainChartDensity_measurable _ hc).pow_const 2).sub
        ((p.domainChartDensity_measurable _ hc).pow_const 2))).ennreal_ofReal
  · intro z hz
    have hzU : z ∈ domainChartSet U c := ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
    have hu := p.domainChartDensity_tendsto_finite_punctures hA P hP hPA hclP hc hzU
    have hv := p.domainChartDensity_tendsto_finite_punctures
      (hA.union hK) R hR hRA hclR hc hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((hv.pow 2).sub (hu.pow 2)))
  · intro n
    exact (setLIntegral_le_lintegral _ _).trans
      (hfinite (P n) (Q n) (hQK n) chi hchi hcomp hchi0 hsupp)

end AreaDeficit.Surfaces.DiscCover
