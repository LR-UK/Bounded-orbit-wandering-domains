module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.CompactOrbitRestriction
public import BoundedWanderingDomains.Surfaces.InvariantSubsurface

@[expose] public section

/-! # Restricting compact orbits inside a prescribed covered subsurface -/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

theorem exists_invariant_neighborhood_in_subsurface
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (O : TopologicalSpace.Opens X)
    {C : Set X} (hC : IsCompact C) (hCs : C ⊆ f.source) (hCO : C ⊆ O)
    (hforward : MapsTo f.totalize C C) :
    ∃ (V : TopologicalSpace.Opens X) (hVs : closure (V : Set X) ⊆ f.source),
      C ⊆ V ∧ closure (V : Set X) ⊆ O ∧ IsCompact (closure (V : Set X)) ∧
      (∀ x : (f.restrictSource V (subset_closure.trans hVs)).source,
        (f.restrictSource V (subset_closure.trans hVs)).map x ∈ O) := by
  let T : Set X := (f.source : Set X) ∩ (O : Set X) ∩ f.totalize ⁻¹' (O : Set X)
  have hTo : IsOpen T := by
    have hp := (f.continuousOn_totalize hf.2.continuous).isOpen_inter_preimage
      f.source.isOpen O.isOpen
    convert (f.source.isOpen.inter O.isOpen).inter hp using 1
    ext x
    simp only [T, mem_inter_iff, mem_preimage]
    tauto
  obtain ⟨V, hVo, hCV, hVT, hVc⟩ := exists_open_between_and_isCompact_closure hC hTo
    (fun x hx => ⟨⟨hCs hx, hCO hx⟩, hCO (hforward hx)⟩)
  refine ⟨⟨V, hVo⟩, (fun x hx => (hVT hx).1.1), hCV,
    (fun x hx => (hVT hx).1.2), hVc, ?_⟩
  intro x
  have hh := (hVT (subset_closure x.property)).2
  change f.totalize (x : X) ∈ O at hh
  rwa [f.totalize_eq ((hVT (subset_closure x.property)).1.1)] at hh

omit [T2Space X] [LocallyCompactSpace X] in
theorem mem_interior_trapped_restrict_of_subsurface_orbit
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O : TopologicalSpace.Opens X) (p : DiscCover O)
    (W : TopologicalSpace.Opens X) (hW : (W : Set X) ⊆ f.trapped)
    (hWO : ∀ n (w : W), f.orbit n ⟨w, hW w.property⟩ ∈ O)
    (V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    {x : X} (hx : x ∈ W) {K : Set X}
    (hK : IsCompact K) (hKO : K ⊆ O) (hKV : K ⊆ V)
    (horbitK : ∀ n, f.orbit n ⟨x, hW hx⟩ ∈ K) :
    x ∈ interior (f.restrictSource V hVs).trapped := by
  obtain ⟨D, hDcenter, hDsub⟩ :=
    SurfaceDynamics.exists_coordDisk_center_closedCarrier_subset W.isOpen hx
  let d : unitDisc → W := fun z => ⟨D.param z, hDsub (D.param_mem_closedCarrier z)⟩
  have hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) d := by
    apply (mdifferentiable_subtypeVal_comp_iff W d).mp
    exact D.mdifferentiable_param
  let F : ℕ → unitDisc → O := fun n z =>
    ⟨f.orbitOn W hW n (d z), hWO n (d z)⟩
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := by
    intro n
    apply (mdifferentiable_subtypeVal_comp_iff O (F n)).mp
    exact (f.mdifferentiable_orbitOn hf W hW n).comp hd
  let KO : Set O := Subtype.val ⁻¹' K
  have hKOc : IsCompact KO := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    rw [image_preimage_eq_inter_range]
    convert hK using 1
    exact inter_eq_left.mpr (fun y hy => ⟨⟨y, hKO hy⟩, rfl⟩)
  have hF0 : ∀ n, F n discZero ∈ KO := by
    intro n
    simpa only [F, KO, mem_preimage, comp_apply, d, orbitOn,
      D.param_zero, hDcenter] using horbitK n
  obtain ⟨r, hr, -, havoid⟩ := p.compact_uniform_disc_avoidance
    (V.isOpen.preimage (continuous_subtype_val : Continuous (Subtype.val : O → X))).isClosed_compl
    hKOc (disjoint_left.mpr (fun y hy hn => hn (hKV hy)))
  let R := {z : unitDisc | ‖(z : ℂ)‖ < r}
  have hRo : IsOpen R := isOpen_lt continuous_subtype_val.norm continuous_const
  have hximage : x ∈ D.param '' R :=
    ⟨discZero, by change ‖(0 : ℂ)‖ < r; simpa using hr,
      D.param_zero.trans hDcenter⟩
  have himage : D.param '' R ⊆ (f.restrictSource V hVs).trapped := by
    rintro y ⟨z, hz, rfl⟩
    apply f.restrictSource_mem_trapped_of_orbit_mem V hVs (hW (d z).property)
    intro n
    exact not_not.mp (havoid (F n) (hF n) (hF0 n) z hz)
  exact ((D.isOpenEmbedding_param.isOpenMap _ hRo).subset_interior_iff.mpr himage) hximage

end SurfaceDynamics.LocalMap
