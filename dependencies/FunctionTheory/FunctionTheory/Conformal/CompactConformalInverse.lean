import TauCeti.Analysis.Complex.Conformal.Biholomorph
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.Topology.Separation.Hausdorff

open Set Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A holomorphic map injective and unramified on a compact set has a
single conformal inverse on a neighbourhood of its whole image. The
neighbourhood need not be a Jordan domain. -/
theorem exists_conformal_neighbourhood_of_compact_injective
    {K : Set ℂ} (hK : IsCompact K) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hi : InjOn f K)
    (hd : ∀ z ∈ K, deriv f z≠0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      K ⊆ e.source ∧ (e : ℂ → ℂ)=f ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target := by
  obtain ⟨V,hV,hKV,hVi⟩ := hi.exists_isOpen_superset hK
    (fun z hz => (hf z hz).continuousAt)
    (fun z hz => (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero (hf z hz)).mpr (hd z hz))
  let W := V ∩ {z | AnalyticAt ℂ f z}
  have hW : IsOpen W := hV.inter (isOpen_analyticAt ℂ f)
  have hKW : K ⊆ W := fun z hz => ⟨hKV hz,hf z hz⟩
  have hWi : InjOn f W := hVi.mono inter_subset_left
  have hWa : AnalyticOnNhd ℂ f W := fun z hz => hz.2
  let e := hWa.differentiableOn.toOpenPartialHomeomorph hW hWi
  refine ⟨e,hKW,by rfl,hWa,?_⟩
  exact (hWa.differentiableOn.differentiableOn_toOpenPartialHomeomorph_symm hW hWi).analyticOnNhd
    e.open_target

end FunctionTheory
