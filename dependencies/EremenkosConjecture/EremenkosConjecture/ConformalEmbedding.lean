import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Conformal charts on open domains, without an ambient extension -/

open Set Function Filter Topology
open scoped Topology

namespace EremenkosConjecture

theorem isOpenMap_domRestrict_of_deriv_ne_zero {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hd : ∀ z ∈ U, deriv f z ≠ 0) : IsOpenMap (U.domRestrict f) := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  have hopen := (hf.analyticOnNhd hU x x.property).eventually_constant_or_nhds_le_map_nhds
  have hlocal : 𝓝 (f x) ≤ map f (𝓝 (x : ℂ)) := by
    apply hopen.resolve_left
    intro he
    have heq : f =ᶠ[𝓝 (x : ℂ)] (fun _ => f x) := he
    exact hd x x.property (by simpa only [deriv_const] using heq.deriv_eq)
  change 𝓝 (f x) ≤ map (f ∘ Subtype.val) (𝓝 x)
  rw [← map_map, hU.isOpenEmbedding_subtypeVal.map_nhds_eq]
  exact hlocal

/-- An injective holomorphic map with nonzero derivative on an open set
gives a conformal chart whose target is its image. -/
theorem exists_conformal_chart_of_injOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hd : ∀ z ∈ U, deriv f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = U ∧ e.target = f '' U ∧
      (∀ z, e z = f z) ∧ DifferentiableOn ℂ e.symm e.target := by
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U)
    hf.continuousOn (isOpenMap_domRestrict_of_deriv_ne_zero hU hf hd) hU
  refine ⟨e, rfl, rfl, (fun _ => rfl), ?_⟩
  intro w hw
  have hz : e.symm w ∈ U := e.map_target hw
  have hfz : HasDerivAt e (deriv f (e.symm w)) (e.symm w) :=
    (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hcont : ContinuousAt e.symm w := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hw)
  exact (HasDerivAt.of_local_left_inverse hcont hfz (hd _ hz)
    (e.eventually_right_inverse hw)).differentiableAt.differentiableWithinAt

end EremenkosConjecture
