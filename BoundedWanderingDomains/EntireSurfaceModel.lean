module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.MeromorphicNormalityBridge
public import BoundedWanderingDomains.MeromorphicSingularValues

@[expose] public section

/-! # The entire-function specialization of the meromorphic sphere model -/

open Set Function OnePoint
open scoped Topology Manifold

namespace MeromorphicDynamics

theorem surfaceModel_isOpenHolomorphic_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnonconst : ¬ ∃ c, ∀ z, f z = c) :
    SurfaceDynamics.IsOpenHolomorphic (surfaceModel f) := by
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hopen : IsOpenMap f := ha.is_constant_or_isOpenMap.resolve_left hnonconst
  refine ⟨?_, surfaceModel_mdifferentiable ha.meromorphicNFOn⟩
  change IsOpenMap (FunctionTheory.meromorphicSphereValue f ∘ finiteSphereHomeomorph.symm)
  rw [meromorphicSphereValue_eq_coe_of_entire hf]
  exact OnePoint.isOpenEmbedding_coe.isOpenMap.comp
    (hopen.comp finiteSphereHomeomorph.symm.isOpenMap)

/-- For an entire function the pole-avoidance condition is automatic, so
the ordinary and meromorphic Fatou sets are identical. -/
theorem fatouSet_eq_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    fatouSet f = ComplexDynamics.fatouSet f := by
  ext z
  constructor
  · rintro ⟨W, hWo, hzW, _, hWN⟩
    exact ⟨W, hWo, hzW, hWN⟩
  · rintro ⟨W, hWo, hzW, hWN⟩
    exact ⟨W, hWo, hzW, fun _ _ _ => hf.analyticAt _, hWN⟩

theorem isFatouComponent_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : Set ℂ} (hU : ComplexDynamics.IsFatouComponent f U) :
    IsFatouComponent f U := by
  simpa only [IsFatouComponent, fatouSet_eq_of_entire hf,
    ComplexDynamics.IsFatouComponent] using hU

end MeromorphicDynamics
