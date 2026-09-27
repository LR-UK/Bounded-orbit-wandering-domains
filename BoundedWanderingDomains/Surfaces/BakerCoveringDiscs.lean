/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
import BoundedWanderingDomains.Surfaces.SurfaceFilling
import BoundedWanderingDomains.Surfaces.WanderingDiscShrink
import BoundedWanderingDomains.Surfaces.CoordinateDiscParam

/-! # Baker's filling argument on a noncompact covered surface -/

open Set Function Filter Metric Topology
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [ConnectedSpace X] [NoncompactSpace X]

/-- Compact-centred disjoint covering discs eventually embed in their
trapped components. The components themselves need not be simply connected. -/
theorem eventually_covering_disc_embedded
    (q : DiscCover X) {f : X → X} {V K : Set X}
    (hV : IsOpen V) (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f V)
    (hfo : ∀ D : Set X, D ⊆ V → IsOpen D → IsOpen (f '' D))
    (hK : IsCompact K) (hKV : K ⊆ V)
    (U : ℕ → TopologicalSpace.Opens X) (p : ∀ n, DiscCover (U n))
    (hcentre : ∀ n, ((p n).projection discZero : X) ∈ K)
    (hU : ∀ n, (U n : Set X) = connectedComponentIn
      (interior {x : X | ∀ k : ℕ, (f^[k]) x ∈ V}) ((p n).projection discZero).val)
    (hfm : ∀ n, MapsTo f (U n) (U (n + 1)))
    (hnext : ∀ n, f ((p n).projection discZero) = (p (n + 1)).projection discZero)
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop,
      InjOn (fun z => ((p n).projection z : X)) {z : unitDisc | ‖(z : ℂ)‖ < r} ∧
      IsSimplyConnected ((fun z => ((p n).projection z : X)) ''
        {z : unitDisc | ‖(z : ℂ)‖ < r}) := by
  classical
  letI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  letI : LocallyPathConnectedSpace unitDisc := unitDisc.isOpen.locallyPathConnectedSpace
  let F : ℕ → unitDisc → X := fun n z => (p n).projection z
  let C : ℕ → Set X := fun n => F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}
  let T := {x : X | ∀ k : ℕ, (f^[k]) x ∈ V}
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := fun n =>
    (mdifferentiable_subtype_val (U n)).comp (p n).holomorphic
  have hC : ∀ n, IsCompact (C n) := fun n =>
    (unitDisc_closed_radius_compact hr1).image (hF n).continuous
  have hCc : ∀ n, IsConnected (C n) := fun n =>
    (unitDisc_closed_radius_connected hr.le hr1).image _ (hF n).continuous.continuousOn
  have hCU : ∀ n, C n ⊆ U n := by
    rintro n x ⟨z, hz, rfl⟩
    exact ((p n).projection z).property
  have hzC : ∀ n, F n discZero ∈ C n := fun n =>
    ⟨discZero, by change ‖(0 : ℂ)‖ ≤ r; simpa only [norm_zero] using hr.le, rfl⟩
  have hUV : ∀ n, (U n : Set X) ⊆ V := by
    intro n x hx
    have hxi : x ∈ interior T := by
      exact connectedComponentIn_subset _ _ (hU n ▸ hx)
    exact interior_subset hxi 0
  have hCnext : ∀ n, MapsTo f (C n) (C (n + 1)) := by
    intro n
    let g : U n → U (n + 1) := fun x => ⟨f x, hfm n x.property⟩
    have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
      apply (mdifferentiable_subtypeVal_comp_iff (U (n + 1)) g).mp
      intro x
      exact ((hf x (hUV n x.property)).mdifferentiableAt
        (hV.mem_nhds (hUV n x.property))).comp x (mdifferentiable_subtype_val (U n) x)
    have hg0 : (p (n + 1)).projection discZero = g ((p n).projection discZero) :=
      Subtype.ext (hnext n).symm
    have hm := (p n).mapsTo_closed_radius (p (n + 1)) hg hg0 r
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwe⟩ := hm (mem_image_of_mem _ hz)
    exact ⟨w, hw, congrArg Subtype.val hwe⟩
  have hD : ∀ x : K, ∃ D : RiemannDynamics.CoordDisk X,
      D.center = x ∧ D.closedCarrier ⊆ V := fun x =>
    SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset hV (hKV x.property)
  choose D hDc hDV using hD
  have hcover : K ⊆ ⋃ x : K, range (D x).param := by
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨⟨x, hx⟩, discZero, (D ⟨x, hx⟩).param_zero.trans (hDc ⟨x, hx⟩)⟩
  have hdisF : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))) := by
    intro n m hnm
    apply (hdis hnm).mono
    · rintro x ⟨z, rfl⟩
      exact ((p n).projection z).property
    · rintro x ⟨z, rfl⟩
      exact ((p m).projection z).property
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (q.disjoint_disc_images_eventually_in_cover hK F hF hcentre hdisF
      (fun x : K => range (D x).param)
      (fun x => (D x).isOpenEmbedding_param.isOpen_range) hcover hr1)
  have hCD : ∀ n ≥ N, ∃ x : K, C n ⊆ (D x).closedCarrier := by
    intro n hn
    obtain ⟨x, hx⟩ := hN n hn
    refine ⟨x, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := hx z hz
    exact hw ▸ (D x).param_mem_closedCarrier w
  have hFV : ∀ n ≥ N, compactFill (C n) ⊆ V := by
    intro n hn
    obtain ⟨x, hx⟩ := hCD n hn
    exact (compactFill_subset_coordDisk (D x) hx).trans (hDV x)
  have hFT := compactFill_iterates_mem_of_forward hf.continuousOn hfo
    (K := fun j => C (N + j)) (fun j => (hC (N + j)).isClosed)
    (fun j => hFV (N + j) (by omega))
    (fun j => by simpa only [Nat.add_assoc] using hCnext (N + j))
  have hFU : ∀ n ≥ N, compactFill (C n) ⊆ U n := by
    intro n hn
    have hFC : compactFill (C n) ⊆ T := by
      simpa only [Nat.add_sub_of_le hn, T, Set.subset_def, Set.mem_setOf_eq] using hFT (n - N)
    have hCI : C n ⊆ interior T := by
      intro x hx
      exact connectedComponentIn_subset _ _ (hU n ▸ hCU n hx)
    have hFI := compactFill_subset_interior_of_subset (hC n).isClosed hCI hFC
    rw [hU n]
    exact (isConnected_compactFill (hC n).isClosed (hCc n)).isPreconnected
      |>.subset_connectedComponentIn (subset_compactFill _ (hzC n)) hFI
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨x, hx⟩ := hCD n hn
  obtain ⟨W, hWo, hWsc, hCW, hWU⟩ :=
    exists_simplyConnected_neighborhood_of_compactFill_subset (hC n) (hCc n)
      (U n).isOpen (D x) hx (hFU n hn)
  have hcov : IsCoveringMapOn (F n) W := by
    intro y hy
    have hh := IsEvenlyCovered.subtypeVal_comp (U n : Set X) (U n).isOpen
      (f := (p n).projection) ((p n).covering ⟨y, hWU hy⟩)
    exact hh.to_isEvenlyCovered_preimage
  have hR : IsOpen {z : unitDisc | ‖(z : ℂ)‖ < r} :=
    isOpen_lt continuous_subtype_val.norm continuous_const
  have hsc := unitDisc_open_radius_simplyConnected hr hr1
  have hi : InjOn (F n) {z : unitDisc | ‖(z : ℂ)‖ < r} :=
    covering_injOn_simplyConnected hR hsc hWo hWsc
      (a := discZero) (by change ‖(0 : ℂ)‖ < r; simpa only [norm_zero] using hr)
      (hF n).continuous.continuousOn
      (fun z hz => hCW ⟨z, show ‖(z : ℂ)‖ ≤ r from le_of_lt hz, rfl⟩) hcov
  refine ⟨hi, ?_⟩
  have hFo : IsOpenMap (F n) := (U n).isOpen.isOpenMap_subtype_val.comp (p n).isOpenMap
  have he : Topology.IsOpenEmbedding ({z : unitDisc | ‖(z : ℂ)‖ < r}.domRestrict (F n)) := by
    rw [isOpenEmbedding_iff_continuous_injective_isOpenMap]
    exact ⟨(hF n).continuous.comp continuous_subtype_val, hi.injective, hFo.domRestrict hR⟩
  have hsci : IsSimplyConnected (univ : Set {z : unitDisc | ‖(z : ℂ)‖ < r}) := by
    let := hsc.simplyConnectedSpace
    exact (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace
  have hh := he.isEmbedding.isSimplyConnected_image.mpr hsci
  simpa only [image_univ, range_domRestrict] using hh

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.eventually_covering_disc_embedded
