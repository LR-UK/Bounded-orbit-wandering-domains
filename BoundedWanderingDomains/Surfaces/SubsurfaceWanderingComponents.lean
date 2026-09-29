module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SubsurfaceCompactNormal
public import BoundedWanderingDomains.Surfaces.SaturationDynamics

@[expose] public section

open Set Function Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

theorem components_restrictAmbient_restrictSource_of_compact_orbit
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O V : TopologicalSpace.Opens X) [LocallyCompactSpace O] (p : DiscCover O)
    (hVs : (V : Set X) ⊆ f.source) (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (S : ℕ → Set X) (hS : ∀ n, f.IsComponent (S n))
    (hSC : ∀ n, IsSimplyConnected (S n)) (hSV : ∀ n, S n ⊆ V)
    (hforward : ∀ n, MapsTo f.totalize (S n) (S (n + 1)))
    (z : ((f.restrictSource V hVs).restrictAmbient O hVO hm).trapped)
    (hzS : ∀ n, (((f.restrictSource V hVs).restrictAmbient O hVO hm).orbit n z : X) ∈ S n)
    {K : Set O} (hK : IsCompact K)
    (hzK : ∀ n, ((f.restrictSource V hVs).restrictAmbient O hVO hm).orbit n z ∈ K) :
    ∀ n, ((f.restrictSource V hVs).restrictAmbient O hVO hm).IsComponent
      (Subtype.val ⁻¹' S n) ∧ IsSimplyConnected (Subtype.val ⁻¹' S n : Set O) := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let : LocallyPathConnectedSpace O := ChartedSpace.locallyPathConnectedSpace ℂ O
  let r := f.restrictSource V hVs
  let g := r.restrictAmbient O hVO hm
  have hr := f.isOpenHolomorphic_restrictSource hf V hVs
  have hg := r.isOpenHolomorphic_restrictAmbient hr O hVO hm
  have hSomega : ∀ n, S n ⊆ f.omega := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hS n
    rw [hSx]
    exact connectedComponentIn_subset _ _
  have hSo : ∀ n, IsOpen (S n) := by
    intro n
    obtain ⟨x, hx, hSx⟩ := hS n
    rw [hSx]
    exact f.isOpen_omega.connectedComponentIn
  have hStrap : ∀ n, S n ⊆ f.trapped := fun n =>
    (hSomega n).trans (f.omega_subset_trapped_interior.trans interior_subset)
  have hstay : ∀ n y, y ∈ S n → ∀ m, f.totalize^[m] y ∈ S (n + m) := by
    intro n y hy m
    induction m with
    | zero => simpa using hy
    | succ m ih =>
      rw [iterate_succ_apply']
      exact hforward (n + m) ih
  let R : ℕ → TopologicalSpace.Opens O := fun n =>
    ⟨Subtype.val ⁻¹' S n, (hSo n).preimage continuous_subtype_val⟩
  have hRimage : ∀ n, Subtype.val '' (R n : Set O) = S n := by
    intro n
    change Subtype.val '' (Subtype.val ⁻¹' S n : Set O) = S n
    rw [image_preimage_eq_inter_range]
    exact inter_eq_left.mpr (fun x hx => ⟨⟨x, hVO (hSV n hx)⟩, rfl⟩)
  have hRsc : ∀ n, IsSimplyConnected (R n : Set O) := by
    intro n
    apply IsEmbedding.subtypeVal.isSimplyConnected_image.mp
    rw [hRimage]
    exact hSC n
  have hRtrap : ∀ n, (R n : Set O) ⊆ g.trapped := by
    intro n y hy
    apply (r.mem_restrictAmbient_trapped_iff O hVO hm y).mpr
    apply f.restrictSource_mem_trapped_of_orbit_mem V hVs (hStrap n hy)
    intro m
    rw [← f.totalize_iterate_orbit m ⟨(y : X), hStrap n hy⟩]
    exact hSV (n + m) (hstay n y hy m)
  have hshiftK : ∀ n m, g.orbit m (g.trappedMap^[n] z) ∈ K := by
    intro n m
    change ((g.trappedMap^[m]) ((g.trappedMap^[n]) z) : O) ∈ K
    rw [← iterate_add_apply]
    exact hzK (m + n)
  have hRomega : ∀ n, (R n : Set O) ⊆ g.omega := by
    intro n
    let : SimplyConnectedSpace (R n) := hRsc n
    exact g.connected_trapped_open_subset_omega_of_compact_orbit hg p (R n) (hRtrap n)
      ⟨g.orbit n z, hzS n⟩ hK (hshiftK n)
  intro n
  let C := componentDomain ⟨g.omega, g.isOpen_omega⟩ (g.orbit n z)
  have hzn : g.orbit n z ∈ g.omega := hRomega n (hzS n)
  let : ConnectedSpace C := componentDomain_connected hzn
  have hCtrap : (C : Set O) ⊆ g.trapped :=
    (connectedComponentIn_subset _ _).trans (g.omega_subset_trapped_interior.trans interior_subset)
  have hComega : Subtype.val '' (C : Set O) ⊆ f.omega :=
    (r.image_connected_trapped_open_subset_omega_of_compact_orbit hr O p hVO hm C hCtrap
      ⟨g.orbit n z, mem_componentDomain hzn⟩ hK (hshiftK n)).trans
      (f.restrictSource_omega_subset V hVs)
  have hCsub : (C : Set O) ⊆ R n := by
    have hc : IsPreconnected (Subtype.val '' (C : Set O) : Set X) :=
      isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
    obtain ⟨x, hx, hSx⟩ := hS n
    have hsub := hc.subset_connectedComponentIn
      (show (g.orbit n z : X) ∈ Subtype.val '' (C : Set O) from
        ⟨g.orbit n z, mem_componentDomain hzn, rfl⟩) hComega
    have he : connectedComponentIn f.omega (g.orbit n z : X) = S n :=
      (connectedComponentIn_eq (hSx ▸ hzS n)).symm.trans hSx.symm
    intro y hy
    change (y : X) ∈ S n
    exact he ▸ hsub ⟨y, hy, rfl⟩
  have hRsub : (R n : Set O) ⊆ C := by
    have hc : IsPreconnected (R n : Set O) :=
      (hRsc n).isPathConnected.isConnected.isPreconnected
    exact hc.subset_connectedComponentIn (hzS n) (hRomega n)
  refine ⟨⟨g.orbit n z, hzn, ?_⟩, hRsc n⟩
  exact Subset.antisymm hRsub hCsub

end SurfaceDynamics.LocalMap
