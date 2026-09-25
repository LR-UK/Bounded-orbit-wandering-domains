/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FinitePunctureRemoteChart
import BoundedWanderingDomains.CompactCutoff
import BoundedWanderingDomains.Surfaces.ChartPunctures

/-! # Ambient charts restricted through finite point removals -/

open Set Function
open scoped Manifold
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M]

/-- An ambient chart point away from a finite set and a closed obstacle is
in the chart obtained by restricting first to the punctured old domain and
then to the new domain. -/
theorem finite_puncture_restricted_chart_target
    (P : Finset M) (U : TopologicalSpace.Opens M)
    (hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
    {K C : Set M} (hCK : Disjoint C K)
    (W : TopologicalSpace.Opens U)
    (hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (hWN : Nonempty W)
    (c : OpenPartialHomeomorph M ℂ) {z : ℂ}
    (hz : z ∈ c.target) (hzF : z ∉ chartPunctures c P)
    (hzC : c.symm z ∈ C) :
    z ∈ ((c.subtypeRestr hUN).subtypeRestr hWN).target := by
  have hxP : c.symm z ∉ (↑P : Set M) :=
    fun hp => hzF ((mem_chartPunctures_iff c P hz).mpr hp)
  let x : U := ⟨c.symm z,(hU _).mpr hxP⟩
  let d := c.subtypeRestr hUN
  have hxsource : x ∈ d.source := by
    simpa only [d,OpenPartialHomeomorph.subtypeRestr_source,mem_preimage]
      using c.map_target hz
  have hxW : x ∈ W := (hW x).mpr (fun hxK => disjoint_left.mp hCK hzC hxK)
  let y : W := ⟨x,hxW⟩
  have hdy : d y ∈ (d.subtypeRestr hWN).target :=
    d.map_subtype_source hWN hxsource
  have hdz : d y = z := by
    change c (c.symm z) = z
    exact c.right_inv hz
  exact hdz ▸ hdy

end AreaDeficit.Surfaces

open Set Function Filter Metric MeasureTheory Laplacian
open scoped Manifold Topology ENNReal ContDiff
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- A fixed ambient chart cutoff controls the gain for every finite puncture
set. Its support and upper bound are independent of that set. -/
theorem ambient_chart_gain_finite_punctures (p : DiscCover M) {K C : Set M}
    (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K)
    (c : OpenPartialHomeomorph M ℂ)
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {D : Set ℂ} (hD : IsOpen D) (hDc : D ⊆ c.target)
    (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (P : Finset M) (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (hWN : Nonempty W)
      (s : DiscCover W) (chi : ℂ → ℝ),
      ContDiff ℝ 2 chi → HasCompactSupport chi →
      (∀ z, 0 ≤ chi z) → tsupport chi ⊆ D →
      (∫⁻ z, ENNReal.ofReal (chi z *
        (if z ∈ AreaDeficit.Surfaces.chartPunctures c P then 0 else
          (s.chartDensity ((c.subtypeRestr hUN).subtypeRestr hWN) z)^2 -
            (r.chartDensity (c.subtypeRestr hUN) z)^2))) ≤
        ENNReal.ofReal (B * ∫ z, |Δ chi z|) := by
  obtain ⟨B, hB, hbound⟩ := p.remote_chart_gain_finite_punctures hK hC hCK
  refine ⟨B, hB, ?_⟩
  intro P U hU hUN r W hW hWN s chi hchi hcomp hchi0 hsupp
  apply hbound U r W s hW hWN (c.subtypeRestr hUN)
    (mdifferentiableOn_subtypeRestr hUN hc)
    (AreaDeficit.Surfaces.chartPunctures c P) D hD
  · intro z hz hzF
    exact AreaDeficit.Surfaces.finite_puncture_restricted_chart_target
      P U hU hUN hCK W hW hWN c (hDc hz) hzF (hDC z hz)
  · intro z hz hzF
    have ht := AreaDeficit.Surfaces.finite_puncture_restricted_chart_target
      P U hU hUN hCK W hW hWN c (hDc hz) hzF (hDC z hz)
    have htU := (c.subtypeRestr hUN).subtypeRestr_symm_apply hWN ht
    have htM := c.subtypeRestr_symm_apply hUN
      ((c.subtypeRestr hUN).subtypeRestr_target_subset hWN ht)
    have heq : (((c.subtypeRestr hUN).subtypeRestr hWN).symm z : M) =
        c.symm z := by
      calc
        _ = ((c.subtypeRestr hUN).symm z : M) := by
          exact congrArg Subtype.val (by simpa only [Function.comp_apply] using htU)
        _ = c.symm z := by simpa only [Function.comp_apply] using htM
    rw [heq]
    exact hDC z hz
  · exact hchi
  · exact hcomp
  · exact hchi0
  · exact hsupp

/-- The compact-set estimate retains one constant for all finite puncture
models, because its cutoff lives in the fixed ambient chart. -/
theorem ambient_chart_compact_gain_finite_punctures (p : DiscCover M)
    {K C : Set M} (hK : IsClosed K) (hC : IsCompact C)
    (hCK : Disjoint C K) (c : OpenPartialHomeomorph M ℂ)
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {A D : Set ℂ} (hA : IsCompact A) (hD : IsOpen D)
    (hAD : A ⊆ D) (hDc : D ⊆ c.target)
    (hDC : ∀ z ∈ D, c.symm z ∈ C) :
    ∃ R : ℝ, ∀ (P : Finset M) (U : TopologicalSpace.Opens M)
      (_hU : ∀ x : M, x ∈ U ↔ x ∉ (↑P : Set M)) (hUN : Nonempty U)
      (r : DiscCover U) (W : TopologicalSpace.Opens U)
      (_hW : ∀ x : U, x ∈ W ↔ (x : M) ∉ K) (hWN : Nonempty W)
      (s : DiscCover W),
      (∫⁻ z in A, ENNReal.ofReal
        (if z ∈ AreaDeficit.Surfaces.chartPunctures c P then 0 else
          (s.chartDensity ((c.subtypeRestr hUN).subtypeRestr hWN) z)^2 -
            (r.chartDensity (c.subtypeRestr hUN) z)^2)) ≤ ENNReal.ofReal R := by
  obtain ⟨B, _hB, hbound⟩ := p.ambient_chart_gain_finite_punctures
    hK hC hCK c hc hD hDc hDC
  obtain ⟨chi, hchi, hcomp, hsupp, hchi0, hchiA⟩ :=
    AreaDeficit.exists_compact_cutoff hA hD hAD
  refine ⟨B * ∫ z, |Δ chi z|, ?_⟩
  intro P U hU hUN r W hW hWN s
  let d := c.subtypeRestr hUN
  let e := d.subtypeRestr hWN
  let F := AreaDeficit.Surfaces.chartPunctures c P
  calc
    (∫⁻ z in A, ENNReal.ofReal
      (if z ∈ F then 0 else (s.chartDensity e z)^2 -
        (r.chartDensity d z)^2)) ≤
      ∫⁻ z in A, ENNReal.ofReal (chi z *
        (if z ∈ F then 0 else (s.chartDensity e z)^2 -
          (r.chartDensity d z)^2)) := by
            apply setLIntegral_mono' hA.measurableSet
            intro z hz
            by_cases hf : z ∈ F
            · simp [hf]
            · have ht := AreaDeficit.Surfaces.finite_puncture_restricted_chart_target
                P U hU hUN hCK W hW hWN c (hDc (hAD hz)) hf
                  (hDC z (hAD hz))
              have hpos : 0 ≤ (s.chartDensity e z)^2 -
                  (r.chartDensity d z)^2 := by
                rw [← r.chartLogRatio_laplacian s hWN
                  (mdifferentiableOn_subtypeRestr hUN hc) ht]
                exact r.chartLogRatio_laplacian_nonneg s hWN
                  (mdifferentiableOn_subtypeRestr hUN hc) ht
              simp only [hf, ite_false]
              exact ENNReal.ofReal_le_ofReal (by nlinarith [hchiA z hz])
    _ ≤ ∫⁻ z, ENNReal.ofReal (chi z *
      (if z ∈ F then 0 else (s.chartDensity e z)^2 -
        (r.chartDensity d z)^2)) := setLIntegral_le_lintegral A _
    _ ≤ ENNReal.ofReal (B * ∫ z, |Δ chi z|) :=
      hbound P U hU hUN r W hW hWN s chi hchi hcomp hchi0 hsupp

end AreaDeficit.Surfaces.DiscCover
