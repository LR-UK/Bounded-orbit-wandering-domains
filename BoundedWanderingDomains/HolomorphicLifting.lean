import BoundedWanderingDomains.LocalCovering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Calculus.Deriv.Inverse

open Set Function Filter Topology
open scoped Topology

namespace AreaDeficit

/-- A continuous lift through a regular holomorphic map is holomorphic,
with the derivative dictated by the chain rule. -/
theorem holomorphic_lift_derivative {f h p : ℂ → ℂ} {U K S : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f K)
    (hp : DifferentiableOn ℂ p U) (hh : ContinuousOn h U)
    (hmap : MapsTo h U K) (hpS : MapsTo p U S)
    (hreg : ∀ z ∈ K, f z ∈ S → deriv f z ≠ 0)
    (hfactor : EqOn (f ∘ h) p U) :
    ∀ z ∈ U, HasDerivAt h (deriv p z / deriv f (h z)) z := by
  intro z hz
  apply HasDerivAt.of_comp_left (hh.continuousAt (hU.mem_nhds hz))
    (hf (h z) (hmap hz)).differentiableAt.hasDerivAt
    (hp.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  · apply hreg (h z) (hmap hz)
    simpa only [← hfactor hz, Function.comp_apply] using hpS hz
  · exact hfactor.eventuallyEq_of_mem (hU.mem_nhds hz)

/-- The actual lift exists, is holomorphic and has the specified base
point. Its source may be any simply connected open plane domain.
The target covering is the restriction to K, which may be compact. -/
theorem exists_holomorphic_covering_lift {f p : ℂ → ℂ} {U K S : Set ℂ}
    {x y : ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hx : x ∈ U) (hy : y ∈ K) (hxy : f y = p x)
    (hcov : IsCoveringMapOn (fun z : K => f z) S)
    (hf : AnalyticOnNhd ℂ f K) (hp : DifferentiableOn ℂ p U)
    (hpS : MapsTo p U S)
    (hreg : ∀ z ∈ K, f z ∈ S → deriv f z ≠ 0) :
    ∃ h : ℂ → ℂ, h x = y ∧ MapsTo h U K ∧
      EqOn (f ∘ h) p U ∧ DifferentiableOn ℂ h U ∧
      ∀ z ∈ U, HasDerivAt h (deriv p z / deriv f (h z)) z := by
  classical
  have := hUc.simplyConnectedSpace
  have := hU.locallyPathConnectedSpace
  obtain ⟨H, ⟨hH0, hH⟩, _⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨U.domRestrict p, hp.continuousOn.domRestrict⟩ : C(U, ℂ))
    (a₀ := ⟨x, hx⟩) (e₀ := ⟨y, hy⟩) hxy (fun z => hpS z.2)
  let h : ℂ → ℂ := fun z => if hz : z ∈ U then H ⟨z, hz⟩ else y
  have he (z : U) : h z = (H z : ℂ) := by simp [h]
  have hh : ContinuousOn h U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hh' : U.domRestrict h = fun z => (H z : ℂ) := funext he
    rw [hh']
    exact continuous_subtype_val.comp H.continuous
  have hm : MapsTo h U K := fun z hz => by simp [h, hz]
  have hfac : EqOn (f ∘ h) p U := by
    intro z hz
    have heq := congrFun hH ⟨z, hz⟩
    simpa [h, hz, Function.comp_def, Set.domRestrict, ContinuousMap.coe_mk] using heq
  have hder := holomorphic_lift_derivative hU hf hp hh hm hpS hreg hfac
  refine ⟨h, ?_, hm, hfac, fun z hz => (hder z hz).differentiableAt.differentiableWithinAt, hder⟩
  simpa [h, hx] using congrArg Subtype.val hH0

end AreaDeficit
