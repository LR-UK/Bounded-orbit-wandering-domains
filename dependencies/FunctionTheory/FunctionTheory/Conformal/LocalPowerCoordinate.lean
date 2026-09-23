import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- The classical local power coordinate at a point of finite positive local
degree. The root branch is supplied by Tau Ceti's holomorphic root theorem. -/
theorem exists_local_power_coordinate_of_order
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) {n : ℕ} (hn : n ≠ 0)
    (horder : analyticOrderAt (fun z => f z - f a) a = n) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ a ∧ ψ a = 0 ∧ deriv ψ a ≠ 0 ∧
      ∀ᶠ z in 𝓝 a, f z = f a + ψ z ^ n := by
  have hF : AnalyticAt ℂ (fun z => f z - f a) a := hf.sub analyticAt_const
  obtain ⟨g, hg, hg0, hgeq⟩ :=
    hF.analyticOrderAt_eq_natCast.mp horder
  have hgorder : analyticOrderAt g a = 0 := hg.analyticOrderAt_eq_zero.mpr hg0
  obtain ⟨h, hh, hheq⟩ := (TauCeti.exists_eventuallyEq_pow_iff_dvd hg hn).mpr
    (by rw [hgorder]; exact dvd_zero _)
  have hh0 : h a ≠ 0 := by
    intro heq
    apply hg0
    simpa [heq, zero_pow hn] using hheq.self_of_nhds
  let ψ : ℂ → ℂ := fun z => (z - a) * h z
  have hderiv : HasDerivAt ψ (h a) a := by
    simpa [ψ] using ((hasDerivAt_id a).sub_const a).fun_mul hh.differentiableAt.hasDerivAt
  refine ⟨ψ, (analyticAt_id.sub analyticAt_const).mul hh, by simp [ψ],
    hderiv.deriv ▸ hh0, ?_⟩
  filter_upwards [hgeq, hheq] with z hz hz'
  have heq : f z - f a = ψ z ^ n := by
    simpa only [ψ, mul_pow, hz', smul_eq_mul] using hz
  linear_combination heq

/-- Every locally nonconstant holomorphic germ has a conformal power coordinate. -/
theorem exists_local_power_coordinate
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hnc : ¬ ∀ᶠ z in 𝓝 a, f z = f a) :
    ∃ n : ℕ, 0 < n ∧ ∃ ψ : ℂ → ℂ,
      AnalyticAt ℂ ψ a ∧ ψ a = 0 ∧ deriv ψ a ≠ 0 ∧
      ∀ᶠ z in 𝓝 a, f z = f a + ψ z ^ n := by
  have hfinite : analyticOrderAt (fun z => f z - f a) a ≠ ⊤ := by
    intro htop
    apply hnc
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    exact sub_eq_zero.mp hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hn0 : n ≠ 0 := by
    intro heq
    have hF : AnalyticAt ℂ (fun z => f z - f a) a := hf.sub analyticAt_const
    have hzero := hF.analyticOrderAt_ne_zero.mpr (sub_self (f a))
    exact hzero (by simpa [heq] using hn.symm)
  exact ⟨n, Nat.pos_of_ne_zero hn0, exists_local_power_coordinate_of_order hf hn0 hn.symm⟩

/-- Holomorphic germs of the same finite local degree and with the same value
are related by a conformal change of source coordinate fixing the base point.
This local assertion does not yet choose the branch compatible with a specified
correction on an annulus. -/
theorem exists_local_conformal_correction_of_equal_order
    {f g : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hvalue : g a = f a) {n : ℕ} (hn : n ≠ 0)
    (hfOrder : analyticOrderAt (fun z => f z - f a) a = n)
    (hgOrder : analyticOrderAt (fun z => g z - g a) a = n) :
    ∃ θ : ℂ → ℂ, AnalyticAt ℂ θ a ∧ θ a = a ∧ deriv θ a ≠ 0 ∧
      ∀ᶠ z in 𝓝 a, g (θ z) = f z := by
  obtain ⟨α, hα, hα0, hαd, hfα⟩ := exists_local_power_coordinate_of_order hf hn hfOrder
  obtain ⟨β, hβ, hβ0, hβd, hgβ⟩ := exists_local_power_coordinate_of_order hg hn hgOrder
  let βinv := hβ.hasStrictDerivAt.localInverse β (deriv β a) a hβd
  have hleft : (βinv ∘ β) =ᶠ[𝓝 a] id := hβ.hasStrictDerivAt.eventually_left_inverse hβd
  have hright : ∀ᶠ w in 𝓝 (β a), β (βinv w) = w :=
    hβ.hasStrictDerivAt.eventually_right_inverse hβd
  have hβinv0 : βinv 0 = a := by simpa only [Function.comp_apply, hβ0, id_eq] using hleft.eq_of_nhds
  have hβinv : AnalyticAt ℂ βinv 0 := by
    have hc : AnalyticAt ℂ (βinv ∘ β) a := analyticAt_id.congr hleft.symm
    simpa only [hβ0] using (analyticAt_comp_iff_of_deriv_ne_zero hβ hβd).mp hc
  have hβinvD : HasDerivAt βinv (deriv β a)⁻¹ 0 := by
    simpa only [hβ0] using (hβ.hasStrictDerivAt.to_localInverse hβd).hasDerivAt
  let θ := βinv ∘ α
  have hθ : AnalyticAt ℂ θ a :=
    (show AnalyticAt ℂ βinv (α a) by simpa only [hα0] using hβinv).comp hα
  have hθa : θ a = a := by simp only [θ, Function.comp_apply, hα0, hβinv0]
  have hθD : HasDerivAt θ ((deriv β a)⁻¹ * deriv α a) a :=
    (show HasDerivAt βinv (deriv β a)⁻¹ (α a) by
      simpa only [hα0] using hβinvD).comp a hα.differentiableAt.hasDerivAt
  refine ⟨θ, hθ, hθa, hθD.deriv ▸ mul_ne_zero (inv_ne_zero hβd) hαd, ?_⟩
  have hgθ : ∀ᶠ z in 𝓝 a, g (θ z) = g a + β (θ z) ^ n :=
    (show Tendsto θ (𝓝 a) (𝓝 a) by simpa only [hθa] using hθ.continuousAt.tendsto).eventually hgβ
  have hαright : ∀ᶠ z in 𝓝 a, β (βinv (α z)) = α z :=
    (show Tendsto α (𝓝 a) (𝓝 (β a)) by
      simpa only [hα0, hβ0] using hα.continuousAt.tendsto).eventually hright
  filter_upwards [hgθ, hαright, hfα] with z hz hr hfz
  simpa only [θ, Function.comp_apply, hr, hvalue, hfz] using hz

end FunctionTheory
