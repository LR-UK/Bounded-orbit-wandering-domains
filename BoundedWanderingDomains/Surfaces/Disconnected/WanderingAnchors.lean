module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.OpenComponentCovers
public import BoundedWanderingDomains.Surfaces.Disconnected.CoordDiskRestriction
public import BoundedWanderingDomains.Surfaces.CoordinateDiscParam
public import BoundedWanderingDomains.Surfaces.WanderingAnchorDisk
public import BoundedWanderingDomains.Surfaces.OmegaDynamics

@[expose] public section

/-! # Finitely many wandering-domain anchors, one in each visited ambient component -/

open Set Function Topology TopologicalSpace
open scoped Manifold ContDiff
open AreaDeficit.Surfaces

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [Finite (ConnectedComponents X)]

theorem exists_componentwise_anchor_restriction
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (S : ℕ → Set X) (hS : ∀ n, f.IsComponent (S n))
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m)))
    (hforward : ∀ n, MapsTo f.totalize (S n) (S (n + 1)))
    (z : f.trapped) (hzS : ∀ n, f.orbit n z ∈ S n)
    {K : Set X} (hK : IsCompact K) (hzK : ∀ n, f.orbit n z ∈ K)
    (hvisited : ∀ c : ConnectedComponents X, ∃ n, ConnectedComponents.mk (f.orbit n z) = c) :
    ∃ (N : ℕ) (O : Opens X) (_p : ComponentwiseDiscCover O),
      NoncompactComponents O ∧
      (∀ n, S (n + N) ⊆ O) ∧
      ∃ C : Set X, IsCompact C ∧ C ⊆ O ∧ (∀ n, f.orbit (n + N) z ∈ C) ∧
      ∃ B : Set X, IsCompact B ∧
        (∀ u : f.source, (u : X) ∉ O → f.map u ∈ B) ∧
        Disjoint B (closure (range (fun n => f.orbit (n + N + 1) z))) := by
  classical
  let : Fintype (ConnectedComponents X) := Fintype.ofFinite _
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  let : IsManifold 𝓘(ℂ) ω X := isManifold_analytic_of_complex
  have hSo : ∀ n, IsOpen (S n) := by
    intro n
    obtain ⟨a, _, ha⟩ := hS n
    rw [ha]
    exact f.isOpen_omega.connectedComponentIn
  have hSs : ∀ n, S n ⊆ f.source := by
    intro n
    obtain ⟨a, _, ha⟩ := hS n
    rw [ha]
    exact (connectedComponentIn_subset _ _).trans f.omega_subset_source
  choose t ht using hvisited
  choose D hDc hD using fun c =>
    exists_coordDisk_center_closedCarrier_subset (hSo (t c)) (hzS (t c))
  have hDcenter : ∀ c, (D c).center ∈ ambientComponent c := by
    intro c
    change ConnectedComponents.mk (D c).center = c
    rw [hDc c]
    exact ht c
  have hDcomponent : ∀ c, (D c).closedCarrier ⊆ ambientComponent c := by
    intro c
    simpa only [show ConnectedComponents.mk (D c).center = c from hDcenter c] using
      (D c).closedCarrier_subset_ambientComponent
  let H := ⋃ c, (D c).closedCarrier
  have hH : IsCompact H := isCompact_iUnion (fun c => (D c).isCompact_closedCarrier)
  let O : Opens X := ⟨Hᶜ, hH.isClosed.isOpen_compl⟩
  let R : ∀ c, RiemannDynamics.CoordDisk (ambientComponent c) :=
    fun c => (D c).restrict (ambientComponent c) (hDcenter c) (hDcomponent c)
  let P : ∀ c, Opens (ambientComponent c) := fun c => (R c).compl
  have hOP : ∀ c, (Subtype.val : ambientComponent c → X) ⁻¹' (O : Set X) ⊆ P c := by
    intro c x hx hxR
    apply hx
    apply mem_iUnion.mpr
    refine ⟨c, ?_⟩
    rw [← (D c).image_closedCarrier_restrict (ambientComponent c) (hDcenter c) (hDcomponent c)]
    exact ⟨x, hxR, rfl⟩
  obtain ⟨p⟩ := nonempty_componentwiseDiscCover_of_component_pieces O P hOP (fun c _ =>
    nonempty_discCover_coordDisk_compl (R c))
  have hNC : NoncompactComponents O := noncompactComponents_of_omitted_points O (by
    intro x
    let c := ConnectedComponents.mk (x : X)
    refine ⟨(D c).center, ?_, ?_⟩
    · rw [← ambientComponent_mk]
      exact hDcenter c
    · intro hx
      apply hx
      refine mem_iUnion.mpr ⟨c, ?_⟩
      rw [← (D c).param_zero]
      exact (D c).param_mem_closedCarrier discZero)
  let N := Finset.univ.sup t + 1
  have htN : ∀ c, t c < N := fun c => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ c))
  let J := ⋃ c, S (t c)
  have hJo : IsOpen J := isOpen_iUnion (fun c => hSo (t c))
  have hHJ : H ⊆ J := iUnion_mono hD
  have htail : ∀ n, Disjoint (S (n + N)) J := by
    intro n
    apply disjoint_iUnion_right.mpr
    intro c
    exact hdis (by have := htN c; omega)
  have hSO : ∀ n, S (n + N) ⊆ O := fun n x hx hxh =>
    disjoint_left.mp (htail n) hx (hHJ hxh)
  let C := K \ J
  have hC : IsCompact C := hK.diff hJo
  have hCO : C ⊆ O := fun _ hx hh => hx.2 (hHJ hh)
  have htailC : ∀ n, f.orbit (n + N) z ∈ C := fun n =>
    ⟨hzK _, fun hj => disjoint_left.mp (htail n) (hzS _) hj⟩
  have hHs : H ⊆ f.source := by
    intro x hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    exact hSs (t c) (hD c hc)
  let B := f.totalize '' H
  have hB : IsCompact B := hH.image_of_continuousOn ((f.continuousOn_totalize hf.2.continuous).mono hHs)
  let J' := ⋃ c, S (t c + 1)
  have hJ'o : IsOpen J' := isOpen_iUnion (fun c => hSo (t c + 1))
  have hBJ : B ⊆ J' := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨c, hforward (t c) (hD c hc)⟩
  have havoid : closure (range (fun n => f.orbit (n + N + 1) z)) ⊆ J'ᶜ := by
    apply closure_minimal _ hJ'o.isClosed_compl
    rintro _ ⟨n, rfl⟩ hj
    obtain ⟨c, hc⟩ := mem_iUnion.mp hj
    exact disjoint_left.mp (hdis (by have := htN c; omega)) (hzS _) hc
  refine ⟨N, O, p, hNC, hSO, C, hC, hCO, htailC, B, hB, ?_, ?_⟩
  · intro u hu
    exact ⟨u, not_not.mp hu, f.totalize_eq u.property⟩
  · exact disjoint_left.mpr (fun _ hb hc => havoid hc (hBJ hb))

end SurfaceDynamics.LocalMap
