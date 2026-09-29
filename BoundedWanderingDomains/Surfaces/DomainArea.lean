module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DomainGainOrder

@[expose] public section

/-! # Intrinsic area of arbitrary open subdomains, extended by zero -/
open Set Function Filter MeasureTheory
open scoped Manifold Topology ENNReal
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem domainDensity_top (p : DiscCover M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : M} (hx : x ∈ c.source) :
    p.domainDensity ⊤ c ⟨x,mem_univ x⟩ = p.density c x := by
  apply le_antisymm
  · obtain ⟨g,hg,hg0,he⟩ := p.density_extremal_disc hc hx
    have hs := p.domainDensity_schwarz_disc ⊤ hg (fun _ => mem_univ _) hc (hg0.symm ▸ hx)
    have hpt : (⟨g discZero,mem_univ _⟩ : (⊤ : TopologicalSpace.Opens M)) =
        ⟨x,mem_univ x⟩ := Subtype.ext hg0
    rw [hpt] at hs
    have hn : 0 < ‖deriv (planeExtension (c ∘ g)) 0‖ := by
      have hnn := norm_nonneg (deriv (planeExtension (c ∘ g)) 0)
      by_contra hn
      have he0 := le_antisymm (le_of_not_gt hn) hnn
      rw [he0,mul_zero] at he
      norm_num at he
    exact (mul_le_mul_iff_left₀ hn).mp (hs.trans_eq he.symm)
  · exact p.density_subdomain_le (p.componentCover ⊤ ⟨x,mem_univ x⟩)
      ⟨componentPoint ⊤ ⟨x,mem_univ x⟩⟩ hc (x := componentPoint ⊤ ⟨x,mem_univ x⟩) hx

@[simp] theorem domainDensityRatio_top (p : DiscCover M) (x : M) :
    p.domainDensityRatio ⊤ x = 1 := by
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ)) x).1
  have hx := mem_chart_source ℂ x
  rw [p.domainDensityRatio_eq ⊤ hc (mem_univ x) hx,p.domainDensity_top hc hx]
  exact div_self (ne_of_gt (p.density_pos hc hx))

variable [MeasurableSpace M] [BorelSpace M]

noncomputable def domainArea (p : DiscCover M) (U : TopologicalSpace.Opens M) : Measure M :=
  p.hyperbolicArea.withDensity (fun x => ENNReal.ofReal ((p.domainDensityRatio U x)^2))

/-- Shrinking the hyperbolic model increases its intrinsic area on sets that
remain inside the smaller domain. -/
theorem domainArea_mono_on (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {A : Set M} (hA : MeasurableSet A) (hAV : A ⊆ V) :
    p.domainArea U A ≤ p.domainArea V A := by
  simp only [domainArea, withDensity_apply _ hA]
  apply setLIntegral_mono' hA
  intro x hx
  have hr := p.domainDensityRatio_mono hVU (hAV hx)
  exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀
    (p.domainDensityRatio_nonneg U x) (p.domainDensityRatio_nonneg V x)).2 hr)

theorem domainArea_independent (p q : DiscCover M) (U : TopologicalSpace.Opens M) :
    p.domainArea U = q.domainArea U := by
  unfold domainArea
  rw [p.hyperbolicArea_independent q]
  congr 1
  funext x
  rw [p.domainDensityRatio_independent q U x]

@[simp] theorem domainArea_top (p : DiscCover M) : p.domainArea ⊤ = p.hyperbolicArea := by
  simp only [domainArea,p.domainDensityRatio_top,one_pow,ENNReal.ofReal_one]
  exact withDensity_one

theorem domainArea_le_add_gain (p : DiscCover M) (U V : TopologicalSpace.Opens M)
    {E : Set M} (hE : MeasurableSet E) :
    p.domainArea V E ≤ p.domainArea U E + p.domainAreaGain U V E := by
  have hm : Measurable (fun x => ENNReal.ofReal ((p.domainDensityRatio U x)^2)) :=
    ((p.domainDensityRatio_measurable U).pow_const 2).ennreal_ofReal
  simp only [domainArea,domainAreaGain,withDensity_apply _ hE]
  rw [← lintegral_add_left hm]
  apply lintegral_mono
  intro x
  calc
    ENNReal.ofReal ((p.domainDensityRatio V x)^2) =
        ENNReal.ofReal ((p.domainDensityRatio U x)^2 +
          ((p.domainDensityRatio V x)^2 - (p.domainDensityRatio U x)^2)) := by congr 1; ring
    _ ≤ _ := ENNReal.ofReal_add_le

/-- On a measurable set contained in the smaller domain, area is exactly
the old area plus the nonnegative intrinsic gain.  This is the finite-area
identity needed to convert a Gauss--Bonnet total-area increment into a gain
bound without any `∞ - ∞` subtraction. -/
theorem domainArea_eq_add_gain_on (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {E : Set M} (hE : MeasurableSet E) (hEV : E ⊆ V) :
    p.domainArea V E = p.domainArea U E + p.domainAreaGain U V E := by
  have hm : Measurable (fun x => ENNReal.ofReal
      ((p.domainDensityRatio U x)^2)) :=
    ((p.domainDensityRatio_measurable U).pow_const 2).ennreal_ofReal
  simp only [domainArea, domainAreaGain, withDensity_apply _ hE]
  rw [← lintegral_add_left hm]
  apply setLIntegral_congr_fun hE
  intro x hx
  have hr := p.domainDensityRatio_mono hVU (hEV hx)
  have hU0 := p.domainDensityRatio_nonneg U x
  have hV0 := p.domainDensityRatio_nonneg V x
  have hsq : (p.domainDensityRatio U x)^2 ≤
      (p.domainDensityRatio V x)^2 := (sq_le_sq₀ hU0 hV0).2 hr
  dsimp only
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sub_nonneg.mpr hsq)]
  congr 1
  ring

theorem domainArea_coordinate_formula (p : DiscCover M)
    (U : TopologicalSpace.Opens M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A : Set M} (hA : MeasurableSet A) (hAc : A ⊆ c.source) :
    p.domainArea U A = ∫⁻ z in c '' A, ENNReal.ofReal ((p.domainChartDensity U c z)^2) := by
  have hm := ((p.domainDensityRatio_measurable U).pow_const 2).ennreal_ofReal
  rw [domainArea,withDensity_apply _ hA,p.hyperbolicArea_setLIntegral hc hA hAc hm]
  apply setLIntegral_congr_fun (chart_image_measurable c (p.projection discZero) hA hAc)
  rintro z ⟨x,hx,rfl⟩
  dsimp only
  rw [c.left_inv (hAc hx),p.domainDensityRatio_chart U hc (hAc hx),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hn := ne_of_gt (p.chartDensity_pos hc (c.map_source (hAc hx)))
  field_simp

end AreaDeficit.Surfaces.DiscCover
