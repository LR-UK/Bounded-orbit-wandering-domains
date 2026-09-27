/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactDiscImages
import BoundedWanderingDomains.Surfaces.HolomorphicLifting
import Mathlib.Analysis.Complex.Schwarz

/-! # Pointed covering discs on surfaces -/

open Set Function Metric
open scoped Manifold Topology

namespace AreaDeficit.Surfaces

/-- Uniqueness of covering lifts gives injectivity on a simply connected
domain whose image fits in a simply connected part of the target. -/
theorem covering_injOn_simplyConnected
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace B]
    {p : A → B} {D : Set A} {T : Set B} {a : A}
    (hD : IsOpen D) (hDc : IsSimplyConnected D)
    (hT : IsOpen T) (hTc : IsSimplyConnected T)
    (ha : a ∈ D) (hp : ContinuousOn p D) (hm : MapsTo p D T)
    (hcov : IsCoveringMapOn p T) : InjOn p D := by
  let := hDc.simplyConnectedSpace
  let := hTc.simplyConnectedSpace
  let := hD.locallyPathConnectedSpace
  let := hT.locallyPathConnectedSpace
  obtain ⟨H, ⟨hH0, hH⟩, _⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨Subtype.val, continuous_subtype_val⟩ : C(T, B))
    (a₀ := ⟨p a, hm ha⟩) (e₀ := a) rfl (fun x => x.2)
  let F : C(D, A) := H.comp ⟨fun x => ⟨p x, hm x.2⟩,
    hp.domRestrict.subtype_mk _⟩
  let I : C(D, A) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨L, _, huniq⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨D.domRestrict p, hp.domRestrict⟩ : C(D, B))
    (a₀ := ⟨a, ha⟩) (e₀ := a) rfl (fun x => hm x.2)
  have hF : F = L := huniq F ⟨hH0, by
    funext x
    exact congrFun hH ⟨p x, hm x.2⟩⟩
  have hI : I = L := huniq I ⟨rfl, rfl⟩
  have hFI := hF.trans hI.symm
  intro x hx y hy hxy
  have hFx : H ⟨p x, hm hx⟩ = x :=
    congrArg (fun M : C(D, A) => M ⟨x, hx⟩) hFI
  have hFy : H ⟨p y, hm hy⟩ = y :=
    congrArg (fun M : C(D, A) => M ⟨y, hy⟩) hFI
  exact hFx.symm.trans ((congrArg H (Subtype.ext hxy)).trans hFy)

theorem unitDisc_norm_le_of_zero {h : unitDisc → unitDisc}
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (h0 : h discZero = discZero)
    (z : unitDisc) : ‖(h z : ℂ)‖ ≤ ‖(z : ℂ)‖ := by
  let g := planeExtension (fun w => (h w : ℂ))
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    planeExtension_differentiableOn ((mdifferentiable_subtype_val unitDisc).comp hh)
  have hgm : MapsTo g (ball 0 1) (closedBall 0 1) := by
    intro w hw
    change planeExtension (fun v => (h v : ℂ)) (⟨w, hw⟩ : unitDisc) ∈ _
    rw [planeExtension_coe]
    exact ball_subset_closedBall (h ⟨w, hw⟩).property
  have hg0 : g 0 = 0 := by
    change planeExtension (fun v => (h v : ℂ)) (discZero : ℂ) = 0
    rw [planeExtension_coe, h0]
    rfl
  simpa only [g, planeExtension_coe] using
    Complex.norm_le_norm_of_mapsTo_ball hg hgm hg0 (mem_ball_zero_iff.mp z.property)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N]

/-- Schwarz's lemma applied to the pointed covering lift. -/
theorem DiscCover.mapsTo_closed_radius
    (p : DiscCover M) (q : DiscCover N) {f : M → N}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (h0 : q.projection discZero = f (p.projection discZero)) (r : ℝ) :
    MapsTo f (p.projection '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})
      (q.projection '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) := by
  let := unitDisc_simplyConnected
  let := unitDisc.isOpen.locallyPathConnectedSpace
  obtain ⟨h, hh0, hfac, hh⟩ := exists_holomorphic_lift q.holomorphic q.covering
    (hf.comp p.holomorphic) discZero discZero h0
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨h z, (unitDisc_norm_le_of_zero hh hh0 z).trans hz, congrFun hfac z⟩

theorem DiscCover.mapsTo_open_radius
    (p : DiscCover M) (q : DiscCover N) {f : M → N}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (h0 : q.projection discZero = f (p.projection discZero)) (r : ℝ) :
    MapsTo f (p.projection '' {z : unitDisc | ‖(z : ℂ)‖ < r})
      (q.projection '' {z : unitDisc | ‖(z : ℂ)‖ < r}) := by
  let := unitDisc_simplyConnected
  let := unitDisc.isOpen.locallyPathConnectedSpace
  obtain ⟨h, hh0, hfac, hh⟩ := exists_holomorphic_lift q.holomorphic q.covering
    (hf.comp p.holomorphic) discZero discZero h0
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨h z, (unitDisc_norm_le_of_zero hh hh0 z).trans_lt hz, congrFun hfac z⟩

theorem unitDisc_open_radius_simplyConnected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IsSimplyConnected {z : unitDisc | ‖(z : ℂ)‖ < r} := by
  apply (Topology.IsEmbedding.subtypeVal (p := fun z : ℂ => z ∈ unitDisc)).isSimplyConnected_image.mp
  have heq : Subtype.val '' {z : unitDisc | ‖(z : ℂ)‖ < r} = ball (0 : ℂ) r := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact mem_ball_zero_iff.mpr hw
    · intro hz
      exact ⟨⟨z, ball_subset_ball hr1.le hz⟩, mem_ball_zero_iff.mp hz, rfl⟩
  rw [heq]
  let : ContractibleSpace (ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace (nonempty_ball.mpr hr)
  change SimplyConnectedSpace (ball (0 : ℂ) r)
  infer_instance

theorem unitDisc_closed_radius_connected {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    IsConnected {z : unitDisc | ‖(z : ℂ)‖ ≤ r} := by
  refine ⟨⟨discZero, by change ‖(0 : ℂ)‖ ≤ r; simpa only [norm_zero] using hr⟩, ?_⟩
  apply (Topology.IsInducing.subtypeVal (t := (unitDisc : Set ℂ))).isPreconnected_image.mp
  change IsPreconnected ((Subtype.val : unitDisc → ℂ) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})
  have heq : Subtype.val '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r} = closedBall (0 : ℂ) r := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact mem_closedBall_zero_iff.mpr hw
    · intro hz
      exact ⟨⟨z, closedBall_subset_ball hr1 hz⟩, mem_closedBall_zero_iff.mp hz, rfl⟩
  exact heq.symm ▸ (convex_closedBall (0 : ℂ) r).isPreconnected

end AreaDeficit.Surfaces
