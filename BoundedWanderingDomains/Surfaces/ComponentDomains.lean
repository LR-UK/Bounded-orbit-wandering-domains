module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DiscCover
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-! # Open components and finite-puncture kernel domains -/
open Set Function TopologicalSpace
open scoped Manifold
namespace AreaDeficit.Surfaces
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The component of an open set containing a given point, as an open
submanifold. It is empty if the point is outside the open set. -/
def componentDomain (U : Opens M) (x : M) : Opens M := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  exact ⟨connectedComponentIn U x, U.isOpen.connectedComponentIn⟩

@[simp] theorem componentDomain_coe (U : Opens M) (x : M) :
    (componentDomain U x : Set M) = connectedComponentIn U x := rfl

theorem componentDomain_le (U : Opens M) (x : M) :
    componentDomain U x ≤ U := connectedComponentIn_subset _ _

theorem mem_componentDomain {U : Opens M} {x : M} (hx : x ∈ U) :
    x ∈ componentDomain U x := mem_connectedComponentIn hx

theorem componentDomain_connected {U : Opens M} {x : M} (hx : x ∈ U) :
    ConnectedSpace (componentDomain U x) :=
  isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hx)

theorem componentDomain_mono {U V : Opens M} (hUV : U ≤ V) (x : M) :
    componentDomain U x ≤ componentDomain V x := connectedComponentIn_mono x hUV

theorem componentDomain_eq_of_mem {U : Opens M} {x y : M}
    (hy : y ∈ componentDomain U x) : componentDomain U y = componentDomain U x := by
  apply Opens.ext
  exact (connectedComponentIn_eq hy).symm

variable [T1Space M]

def finitePunctureDomain (P : Finset M) : Opens M :=
  ⟨(↑P : Set M)ᶜ, P.finite_toSet.isClosed.isOpen_compl⟩

omit [ChartedSpace ℂ M] in
@[simp] theorem mem_finitePunctureDomain (P : Finset M) (x : M) :
    x ∈ finitePunctureDomain P ↔ x ∉ P := Iff.rfl

omit [ChartedSpace ℂ M] in
theorem finitePunctureDomain_antitone : Antitone (finitePunctureDomain (M := M)) := by
  intro P Q hPQ x hx hPx
  exact hx (hPQ hPx)

theorem component_finite_punctures_antitone
    (P : ℕ → Finset M) (hP : Monotone P) (x : M) :
    Antitone (fun n => componentDomain (finitePunctureDomain (P n)) x) := by
  intro i j hij
  exact componentDomain_mono (finitePunctureDomain_antitone (hP hij)) x

theorem component_complement_le_finite_punctures
    {A : Set M} (hA : IsClosed A) (P : Finset M)
    (hP : (↑P : Set M) ⊆ A) (x : M) :
    componentDomain ⟨Aᶜ,hA.isOpen_compl⟩ x ≤
      componentDomain (finitePunctureDomain P) x := by
  apply componentDomain_mono (U := ⟨Aᶜ,hA.isOpen_compl⟩) (V := finitePunctureDomain P) _ x
  intro y hy hPy
  exact hy (hP hPy)

end AreaDeficit.Surfaces
