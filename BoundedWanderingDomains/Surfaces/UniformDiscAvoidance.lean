module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.Surfaces.PlaneReading
public import Mathlib.Analysis.Complex.Schwarz

@[expose] public section

/-! # Uniform avoidance by small holomorphic discs on a covered surface

The small radius is uniform over all holomorphic discs centred in a fixed
neighbourhood. It follows from lifting to the disc and the Schwarz lemma.
No simple connectivity of the surface itself is required.
-/
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces

noncomputable def discZero : unitDisc := ⟨0,by simp [unitDisc]⟩

theorem unitDisc_displacement {h : unitDisc → unitDisc}
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (z : unitDisc) :
    dist (h z) (h discZero) ≤ 2 * ‖(z : ℂ)‖ := by
  let g := planeExtension (fun w => (h w : ℂ))
  have hd : DifferentiableOn ℂ g (ball 0 1) :=
    planeExtension_differentiableOn ((mdifferentiable_subtype_val unitDisc).comp hh)
  have h0 : g 0 = (h discZero : ℂ) := planeExtension_coe _ discZero
  have hm : MapsTo g (ball 0 1) (closedBall (g 0) 2) := by
    intro w hw
    change dist (g w) (g 0) ≤ 2
    have hwv : g w = (h ⟨w,hw⟩ : ℂ) := planeExtension_coe _ ⟨w,hw⟩
    rw [hwv,h0]
    have hn1 : ‖(h ⟨w,hw⟩ : ℂ)‖ < 1 := mem_ball_zero_iff.mp (h ⟨w,hw⟩).2
    have hn0 : ‖(h discZero : ℂ)‖ < 1 := mem_ball_zero_iff.mp (h discZero).2
    rw [dist_eq_norm_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm z.2
  change dist (h z : ℂ) (h discZero : ℂ) ≤ _
  have hz : g z = (h z : ℂ) := planeExtension_coe _ z
  simpa only [hz,h0,div_one,dist_zero_right] using hs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

theorem DiscCover.uniform_disc_avoidance (p : DiscCover M) {K : Set M}
    (hK : IsClosed K) {x : M} (hx : x ∉ K) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → g discZero ∈ V →
        ∀ z : unitDisc, ‖(z : ℂ)‖ < r → g z ∉ K := by
  obtain ⟨w,rfl⟩ := p.surjective x
  have hO : IsOpen (p.projection ⁻¹' Kᶜ) := hK.isOpen_compl.preimage p.continuous
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO w hx
  let V := p.projection '' ball w (ε / 2)
  refine ⟨V,p.isOpenMap _ isOpen_ball,⟨w,mem_ball_self (by positivity),rfl⟩,
    min (ε / 4) (1 / 2),lt_min (by positivity) (by norm_num),
    (min_le_right _ _).trans (by norm_num),?_⟩
  intro g hg hgV z hz
  obtain ⟨v,hv,hvg⟩ := hgV
  let : LocallyPathConnectedSpace unitDisc := ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  obtain ⟨h,h0,hfac,hh⟩ := exists_holomorphic_lift p.holomorphic p.covering hg discZero v hvg
  have hdis := unitDisc_displacement hh z
  rw [h0] at hdis
  have hzε : ‖(z : ℂ)‖ < ε / 4 := hz.trans_le (min_le_left _ _)
  have hvε : dist v w < ε / 2 := hv
  have hwball : h z ∈ ball w ε := by
    apply lt_of_le_of_lt (dist_triangle (h z) v w)
    linarith
  have havoid := hball hwball
  have hgz : p.projection (h z) = g z := congrFun hfac z
  simpa only [mem_preimage,mem_compl_iff,hgz] using havoid

/-- The avoidance radius can be chosen uniformly on a compact set of centres. -/
theorem DiscCover.compact_uniform_disc_avoidance (p : DiscCover M) {K C : Set M}
    (hK : IsClosed K) (hC : IsCompact C) (hCK : Disjoint C K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → g discZero ∈ C →
        ∀ z : unitDisc, ‖(z : ℂ)‖ < r → g z ∉ K := by
  classical
  have hloc (x : C) := p.uniform_disc_avoidance hK
    (show (x : M) ∉ K from fun hx => disjoint_left.mp hCK x.2 hx)
  choose V hVo hxV r hr hr1 hav using hloc
  obtain ⟨t,ht⟩ := hC.elim_finite_subcover V hVo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have hfinite (s : Finset C) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i ∈ s, δ ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,le_rfl,by simp⟩
    | @insert a s _ ih =>
      obtain ⟨δ,hδ,hδ1,hs⟩ := ih
      refine ⟨min δ (r a),lt_min hδ (hr a),(min_le_left _ _).trans hδ1,?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs i hi)
  obtain ⟨δ,hδ,hδ1,hδr⟩ := hfinite t
  refine ⟨δ,hδ,hδ1,?_⟩
  intro g hg hgC z hz
  obtain ⟨i,hi,hgi⟩ := mem_iUnion₂.mp (ht hgC)
  exact hav i g hg hgi z (hz.trans_le (hδr i hi))

end AreaDeficit.Surfaces
