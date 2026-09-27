/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.RegularCoveringArea

open Set Function MeasureTheory
open AreaDeficit.Surfaces
open scoped Manifold Topology ENNReal

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

/-- Exact area advance with a finite set covering singular values and the
failure of forward invariance of the puncture model. -/
theorem finite_defect_domainArea_advance (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (p : DiscCover X) (P E : Finset X) (hS : f.singularValues ⊆ E)
    (hforward : ∀ x : f.source, (x : X) ∈ P → f.map x ∈ (P ∪ E : Finset X))
    {W : Set X} (hW : MeasurableSet W) (hWs : W ⊆ f.source)
    (hinj : InjOn f.totalize W) (havoid : ∀ x ∈ W, f.totalize x ∉ (P ∪ E : Finset X)) :
    p.domainArea (finitePunctureDomain P) W ≤
      p.domainArea (finitePunctureDomain (P ∪ E)) (f.totalize '' W) := by
  let Y := finitePunctureDomain (P ∪ E)
  let T := f.regularCoverDomain Y hf.2.continuous
  have hY : (Y : Set X) ⊆ f.singularValuesᶜ := by
    intro x hx hs
    exact hx (Finset.mem_union.mpr (Or.inr (hS hs)))
  obtain ⟨F, hF, hcov, hFeq⟩ := f.exists_regular_domain_cover hf Y hY
  have hTU : T ≤ finitePunctureDomain P := by
    rintro x ⟨w, hw, rfl⟩ hx
    exact hw (hforward w hx)
  have hWT : W ⊆ T := by
    intro x hx
    refine ⟨⟨x, hWs hx⟩, ?_, rfl⟩
    change f.map ⟨x, hWs hx⟩ ∉ (P ∪ E : Finset X)
    rw [← f.totalize_eq (hWs hx)]
    exact havoid x hx
  calc
    p.domainArea (finitePunctureDomain P) W ≤ p.domainArea T W :=
      p.domainArea_mono_on hTU hW hWT
    _ = p.domainArea Y (f.totalize '' W) :=
      p.domainArea_eq_image_of_openDomain_covering T Y F hF hcov hFeq
        (f.measurable_totalize hf.2.continuous) hW hWT hinj

end SurfaceDynamics.LocalMap
