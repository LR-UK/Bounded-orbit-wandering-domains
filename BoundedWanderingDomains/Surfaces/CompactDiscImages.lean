module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.UniformDiscAvoidance
public import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic
public import RiemannDynamics.Hyperbolic.DiskModel.SchwarzPick

@[expose] public section

/-! # Compact control of holomorphic discs with compact centres

This is the covering-disc form of proper hyperbolic-distance control.
It is used to make remote metric comparison tend to one at infinity.
-/
open Set Function Filter Metric RiemannDynamics
open scoped Manifold Topology
namespace AreaDeficit.Surfaces

noncomputable def discMobiusFromZero (w z : unitDisc) : unitDisc :=
  ⟨mobiusDisk (-(w : ℂ)) z, mobiusDisk_mapsTo z.property (by
    simpa only [unitDisc,TopologicalSpace.Opens.mem_mk,mem_ball_zero_iff,norm_neg] using w.property)⟩

theorem discMobiusFromZero_continuous :
    Continuous (fun v : unitDisc × unitDisc => discMobiusFromZero v.1 v.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun v : unitDisc × unitDisc =>
    ((v.2 : ℂ) - -(v.1 : ℂ)) / (1 - (starRingEnd ℂ) (-(v.1 : ℂ)) * (v.2 : ℂ)))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro v
    exact mobiusDisk_denom_ne_zero v.2.property (by
      simpa only [unitDisc,TopologicalSpace.Opens.mem_mk,mem_ball_zero_iff,norm_neg] using v.1.property)

theorem discMobiusFromZero_holomorphic (w : unitDisc) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (discMobiusFromZero w) := by
  apply (mdifferentiable_subtypeVal_comp_iff unitDisc _).mp
  intro z
  change MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v : unitDisc => mobiusDisk (-(w : ℂ)) v) z
  apply mdifferentiableAt_subtype_iff.mpr
  have hw : -(w : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [unitDisc,TopologicalSpace.Opens.mem_mk,mem_ball_zero_iff,norm_neg] using w.property
  exact ((mobiusDisk_differentiableOn hw).differentiableAt
    (isOpen_ball.mem_nhds z.property)).mdifferentiableAt

theorem discMobiusFromZero_zero (w : unitDisc) : discMobiusFromZero w discZero = w :=
  Subtype.ext (mobiusDisk_neg_apply_zero w)

theorem unitDisc_closed_radius_compact {r : ℝ} (hr : r < 1) :
    IsCompact {z : unitDisc | ‖(z : ℂ)‖ ≤ r} := by
  apply Subtype.isCompact_iff.mpr
  have he : (Subtype.val '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) = closedBall (0 : ℂ) r := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact mem_closedBall_zero_iff.mpr hw
    · intro hz
      have hn := mem_closedBall_zero_iff.mp hz
      exact ⟨⟨z,mem_ball_zero_iff.mpr (hn.trans_lt hr)⟩,hn,rfl⟩
  rw [he]
  exact isCompact_closedBall _ _

theorem unitDisc_closed_ball_compact {r : ℝ} (hr : r < 1) :
    IsCompact {z : unitDisc | ‖(z : ℂ)‖ ≤ r} := by
  exact unitDisc_closed_radius_compact hr

theorem unitDisc_maps_compact_radius {B : Set unitDisc} (hB : IsCompact B)
    {r : ℝ} (hr : r < 1) :
    ∃ C : Set unitDisc, IsCompact C ∧
      ∀ h : unitDisc → unitDisc, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
        h discZero ∈ B → ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → h z ∈ C := by
  let T := {z : unitDisc | ‖(z : ℂ)‖ ≤ r}
  let F := fun v : unitDisc × unitDisc => discMobiusFromZero v.1 v.2
  refine ⟨F '' (B ×ˢ T), (hB.prod (unitDisc_closed_radius_compact hr)).image
    discMobiusFromZero_continuous, ?_⟩
  intro h hh hh0 z hz
  let g := planeExtension (fun v => (h v : ℂ))
  have hd : DifferentiableOn ℂ g (ball 0 1) :=
    planeExtension_differentiableOn ((mdifferentiable_subtype_val unitDisc).comp hh)
  have hm : MapsTo g (ball 0 1) (ball 0 1) := by
    intro w hw
    have he : g w = (h (⟨w,hw⟩ : unitDisc) : ℂ) := planeExtension_coe _ (⟨w,hw⟩ : unitDisc)
    rw [he]
    exact (h ⟨w,hw⟩).property
  have hsp := schwarzPick_pseudo hd hm z.property discZero.property
  have hg0 : g 0 = (h discZero : ℂ) := planeExtension_coe _ discZero
  have hgz : g z = (h z : ℂ) := planeExtension_coe _ z
  have hm0 : mobiusDisk 0 (z : ℂ) = z := by simp [mobiusDisk]
  change ‖mobiusDisk (g 0) (g z)‖ ≤ ‖mobiusDisk 0 z‖ at hsp
  rw [hg0,hgz,hm0] at hsp
  let v : unitDisc := ⟨mobiusDisk (h discZero : ℂ) (h z),
    mobiusDisk_mapsTo (h z).property (h discZero).property⟩
  refine ⟨(h discZero,v), ⟨hh0,hsp.trans hz⟩, ?_⟩
  apply Subtype.ext
  exact mobiusDisk_neg_mobiusDisk (h z).property (h discZero).property

/-- The compact-centre control also holds simultaneously on a closed
Euclidean subdisc. -/
theorem unitDisc_maps_compact_closed_ball {B : Set unitDisc} (hB : IsCompact B)
    {r : ℝ} (hr : r < 1) :
    ∃ C : Set unitDisc, IsCompact C ∧
      ∀ h : unitDisc → unitDisc, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
        h discZero ∈ B → ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → h z ∈ C := by
  exact unitDisc_maps_compact_radius hB hr

namespace DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem compact_lift_set (p : DiscCover M) {K : Set M} (hK : IsCompact K) :
    ∃ B : Set unitDisc, IsCompact B ∧ K ⊆ p.projection '' B := by
  classical
  let : LocallyCompactSpace unitDisc := unitDisc.isOpen.locallyCompactSpace
  have hlocal : ∀ x : K, ∃ B : Set unitDisc, IsCompact B ∧
      (x : M) ∈ p.projection '' interior B := by
    intro x
    obtain ⟨w,hw⟩ := p.surjective (x : M)
    obtain ⟨B,hB,hwB⟩ := exists_compact_mem_nhds w
    exact ⟨B,hB,w,mem_interior_iff_mem_nhds.mpr hwB,hw⟩
  choose B hB hxB using hlocal
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun x => p.projection '' interior (B x))
    (fun _ => p.isOpenMap _ isOpen_interior) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxB ⟨x,hx⟩⟩)
  refine ⟨⋃ x ∈ I, B x, ?_, ?_⟩
  · exact I.isCompact_biUnion (fun x _ => hB x)
  · intro x hx
    obtain ⟨i,hi,w,hw,hwx⟩ := mem_iUnion₂.mp (hI hx)
    exact ⟨w,mem_iUnion₂.mpr ⟨i,hi,interior_subset hw⟩,hwx⟩

theorem compact_disc_images (p : DiscCover M) {K : Set M} (hK : IsCompact K)
    {r : ℝ} (hr : r < 1) :
    ∃ C : Set M, IsCompact C ∧
      ∀ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
        g discZero ∈ K → ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → g z ∈ C := by
  obtain ⟨B,hB,hKB⟩ := p.compact_lift_set hK
  obtain ⟨T,hT,hcontrol⟩ := unitDisc_maps_compact_radius hB hr
  refine ⟨p.projection '' T, hT.image p.continuous, ?_⟩
  intro g hg hgK z hz
  obtain ⟨w,hw,hwg⟩ := hKB hgK
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  let : LocallyPathConnectedSpace unitDisc := ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  obtain ⟨h,hh0,hfac,hh⟩ := exists_holomorphic_lift p.holomorphic p.covering hg discZero w hwg
  refine ⟨h z,hcontrol h hh (hh0.symm ▸ hw) z hz,?_⟩
  exact congrFun hfac z

end DiscCover
end AreaDeficit.Surfaces
