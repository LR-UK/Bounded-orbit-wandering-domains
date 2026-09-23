/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.Pieces

/-!
# Bipolar Green: Harnack chains and normal families

Symmetry-free infrastructure for the dipole limit: connectivity of the
complement of two disjoint closed coordinate disks, the Harnack chain
constant of a connected open set, and the locally bounded normal-families
limit for sequences of harmonic functions.

## Main statements

* `isConnected_two_coordDisk_compl` — removing two disjoint closed
  coordinate disks keeps the surface connected;
* `exists_harnack_chain_const` — the Harnack chain bound;
* `exists_mharmonicOn_limit_of_locally_bounded` — the harmonic
  normal-families brick.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

/-!
### Symmetry-free Harnack and normal-families infrastructure

The two bricks below are themselves symmetry-free: the Harnack chain constant and
the normal-families limit are obtained without any cross-symmetry input. The dipole
limit is normalized at a third base point, so only the weakest consequence of the
classical cross-symmetry of the piece Green's functions is needed — see
`exists_pieceGreen_drift_bound_core`, where it cancels the cross terms — and the rest of
the shrink-uniform control comes from the Harnack chain bound.
-/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- The complement of two disjoint closed coordinate disks in a connected
surface is connected. -/
theorem isConnected_two_coordDisk_compl
    (D₁ D₂ : CoordDisk M)
    (hdisj : Disjoint D₁.closedCarrier D₂.closedCarrier) :
    IsConnected ((D₁.closedCarrier ∪ D₂.closedCarrier)ᶜ : Set M) := by
  classical
  -- ## Generic plane bricks
  -- The open chart annulus is connected, via polar coordinates.
  have hann : ∀ (c : ℂ) (r R : ℝ), 0 < r → r < R →
      IsConnected (ball c R \ closedBall c r) := by
    intro c r R hr hrR
    have hcont : Continuous fun p : ℝ × ℝ ↦
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ ↦ c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo r R ×ˢ (Set.univ : Set ℝ)) = ball c R \ closedBall c r := by
      apply Set.Subset.antisymm
      · rintro w ⟨⟨t, θ⟩, ⟨⟨hrt, htR⟩, -⟩, hw⟩
        rw [← hw]
        change c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball c R \ closedBall c r
        have hd : dist (c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) c = t := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg (hr.le.trans hrt.le)]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, hd]; exact htR
        · intro hmem
          rw [mem_closedBall, hd] at hmem
          exact absurd hmem (not_le.2 hrt)
      · rintro w ⟨hwb, hwc⟩
        have hrt : r < ‖w - c‖ := by
          rw [← dist_eq_norm]
          exact not_le.1 fun h ↦ hwc (mem_closedBall.2 h)
        have htR : ‖w - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hwb
        refine ⟨(‖w - c‖, (w - c).arg), ⟨⟨hrt, htR⟩, Set.mem_univ _⟩, ?_⟩
        change c + (‖w - c‖ : ℂ) * Complex.exp (((w - c).arg : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    have hmid : (r + R) / 2 ∈ Set.Ioo r R := ⟨by linarith, by linarith⟩
    rw [← himg]
    exact ⟨Set.Nonempty.image _ ⟨((r + R) / 2, 0), hmid, Set.mem_univ _⟩,
      (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn⟩
  -- ## Per-disk collar data
  -- For a disk `D` and an open superset `T` of its closed chart ball inside the
  -- chart target, produce a collar radius `R` with the chart-ball neighborhood
  -- `N` of the closed carrier, the compact `K ⊇ N`, and the connected annulus
  -- `A = N ∖ closedCarrier`, all of whose points read back through the chart.
  have collar : ∀ (D : CoordDisk M) (S : Set M), IsClosed S →
      Disjoint D.closedCarrier S →
      ∃ N K A : Set M, IsOpen N ∧ IsCompact K ∧ N ⊆ K ∧ K ∩ S = ∅ ∧
        D.closedCarrier ⊆ N ∧ IsConnected A ∧ A = N \ D.closedCarrier ∧
        A ∩ D.closedCarrier = ∅ := by
    intro D S hScl hDS
    set e : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center
    set c : ℂ := e D.center
    set r : ℝ := D.radius
    have hr : 0 < r := D.radius_pos
    have hsub : closedBall c r ⊆ e.target := D.closedBall_subset
    have hcarrier : D.closedCarrier = e.symm '' closedBall c r := rfl
    -- The open target region avoiding `S`.
    set T : Set ℂ := e.target ∩ e.symm ⁻¹' Sᶜ with hTdef
    have hTopen : IsOpen T := e.isOpen_inter_preimage_symm hScl.isOpen_compl
    have hTsub : closedBall c r ⊆ T := by
      intro w hw
      refine ⟨hsub hw, ?_⟩
      rw [Set.mem_preimage]
      have hmem : e.symm w ∈ D.closedCarrier := by
        rw [hcarrier]
        exact ⟨w, hw, rfl⟩
      exact fun hS ↦ Set.disjoint_left.1 hDS hmem hS
    obtain ⟨δ, hδ0, hδsub⟩ :=
      (isCompact_closedBall c r).exists_thickening_subset_open hTopen hTsub
    set R : ℝ := δ + r with hRdef
    have hrR : r < R := lt_add_of_pos_left r hδ0
    have hballR : ball c R ⊆ T := by
      rw [hRdef, ← thickening_closedBall hδ0 hr.le c]
      exact hδsub
    have hballtgt : ball c R ⊆ e.target := fun w hw ↦ (hballR hw).1
    -- The half-collar radius.
    set Rh : ℝ := (r + R) / 2 with hRhdef
    have hrRh : r < Rh := by rw [hRhdef]; linarith
    have hRhR : Rh < R := by rw [hRhdef]; linarith
    have hcbRh : closedBall c Rh ⊆ ball c R := closedBall_subset_ball hRhR
    -- The chart-ball neighborhood, its compact closure disk, and the annulus.
    set N : Set M := e.source ∩ e ⁻¹' ball c Rh with hNdef
    set K : Set M := e.symm '' closedBall c Rh with hKdef
    set A : Set M := e.symm '' (ball c Rh \ closedBall c r) with hAdef
    have hNopen : IsOpen N := e.isOpen_inter_preimage isOpen_ball
    have hKcomp : IsCompact K :=
      (isCompact_closedBall c Rh).image_of_continuousOn
        (e.continuousOn_symm.mono (hcbRh.trans hballtgt))
    have hNK : N ⊆ K := by
      rintro y ⟨hys, hyb⟩
      exact ⟨e y, ball_subset_closedBall hyb, e.left_inv hys⟩
    have hKS : K ∩ S = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨⟨w, hw, rfl⟩, hyS⟩
      have h1 := (hballR (hcbRh hw)).2
      rw [Set.mem_preimage] at h1
      exact h1 hyS
    have hcN : D.closedCarrier ⊆ N := by
      intro x hx
      rw [hcarrier] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [Set.mem_preimage, e.right_inv hwt]
      exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hw) hrRh)
    have hAconn : IsConnected A := by
      rw [hAdef]
      exact (hann c r Rh hr hrRh).image _
        (e.continuousOn_symm.mono fun w hw ↦ (hcbRh.trans hballtgt)
          (ball_subset_closedBall hw.1))
    have hAeq : A = N \ D.closedCarrier := by
      rw [hAdef, hNdef, hcarrier]
      apply Set.Subset.antisymm
      · rintro x ⟨w, ⟨hwb, hwc⟩, rfl⟩
        have hwt : w ∈ e.target := (hcbRh.trans hballtgt) (ball_subset_closedBall hwb)
        refine ⟨⟨e.map_target hwt, ?_⟩, ?_⟩
        · rw [Set.mem_preimage, e.right_inv hwt]; exact hwb
        · rintro ⟨w', hw', hw'e⟩
          have hw't : w' ∈ e.target := hsub hw'
          have h2 : e (e.symm w') = e (e.symm w) := by rw [hw'e]
          rw [e.right_inv hw't, e.right_inv hwt] at h2
          exact hwc (h2 ▸ hw')
      · rintro x ⟨⟨hxsrc, hxb⟩, hxc⟩
        rw [Set.mem_preimage] at hxb
        refine ⟨e x, ⟨hxb, fun hmem ↦ hxc ?_⟩, e.left_inv hxsrc⟩
        exact ⟨e x, hmem, e.left_inv hxsrc⟩
    have hAC : A ∩ D.closedCarrier = ∅ := by
      rw [hAeq, Set.eq_empty_iff_forall_notMem]
      rintro y ⟨⟨-, h2⟩, h3⟩
      exact h2 h3
    exact ⟨N, K, A, hNopen, hKcomp, hNK, hKS, hcN, hAconn, hAeq, hAC⟩
  -- ## The two collars, the second avoiding the first
  obtain ⟨N₁, K₁, A₁, hN₁o, hK₁c, hN₁K₁, hK₁C₂, hC₁N₁, hA₁conn, hA₁eq,
      hA₁C₁⟩ :=
    collar D₁ D₂.closedCarrier D₂.isCompact_closedCarrier.isClosed hdisj
  have hdisj₂ : Disjoint D₂.closedCarrier (D₁.closedCarrier ∪ K₁) := by
    rw [Set.disjoint_union_right]
    constructor
    · exact hdisj.symm
    · rw [Set.disjoint_left]
      intro y hy₂ hyK₁
      have : y ∈ K₁ ∩ D₂.closedCarrier := ⟨hyK₁, hy₂⟩
      rw [hK₁C₂] at this
      exact this
  obtain ⟨N₂, K₂, A₂, hN₂o, hK₂c, hN₂K₂, hK₂C₁K₁, hC₂N₂, hA₂conn,
      hA₂eq, hA₂C₂⟩ :=
    collar D₂ (D₁.closedCarrier ∪ K₁)
      (D₁.isCompact_closedCarrier.isClosed.union hK₁c.isClosed) hdisj₂
  -- Consequences of the avoidance choices.
  have hN₁C₂ : N₁ ∩ D₂.closedCarrier = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyN, hyC⟩
    have : y ∈ K₁ ∩ D₂.closedCarrier := ⟨hN₁K₁ hyN, hyC⟩
    rw [hK₁C₂] at this
    exact this
  have hN₂C₁ : N₂ ∩ D₁.closedCarrier = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyN, hyC⟩
    have : y ∈ K₂ ∩ (D₁.closedCarrier ∪ K₁) := ⟨hN₂K₂ hyN, Or.inl hyC⟩
    rw [hK₂C₁K₁] at this
    exact this
  have hN₁N₂ : N₁ ∩ N₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy₁, hy₂⟩
    have : y ∈ K₂ ∩ (D₁.closedCarrier ∪ K₁) := ⟨hN₂K₂ hy₂, Or.inr (hN₁K₁
        hy₁)⟩
    rw [hK₂C₁K₁] at this
    exact this
  -- ## Assembly
  set C : Set M := D₁.closedCarrier ∪ D₂.closedCarrier with hCdef
  have hCcl : IsClosed C :=
    (D₁.isCompact_closedCarrier.union D₂.isCompact_closedCarrier).isClosed
  have hΩo : IsOpen (Cᶜ : Set M) := hCcl.isOpen_compl
  -- The annuli sit inside the complement.
  have hA₁Ω : A₁ ⊆ (Cᶜ : Set M) := by
    intro y hy
    rintro (h | h)
    · rw [Set.eq_empty_iff_forall_notMem] at hA₁C₁
      exact hA₁C₁ y ⟨hy, h⟩
    · rw [Set.eq_empty_iff_forall_notMem] at hN₁C₂
      rw [hA₁eq] at hy
      exact hN₁C₂ y ⟨hy.1, h⟩
  have hA₂Ω : A₂ ⊆ (Cᶜ : Set M) := by
    intro y hy
    rintro (h | h)
    · rw [Set.eq_empty_iff_forall_notMem] at hN₂C₁
      rw [hA₂eq] at hy
      exact hN₂C₁ y ⟨hy.1, h⟩
    · rw [Set.eq_empty_iff_forall_notMem] at hA₂C₂
      exact hA₂C₂ y ⟨hy, h⟩
  -- The collar neighborhoods meet the complement only in the annuli.
  have hN₁Ω : N₁ ∩ (Cᶜ : Set M) ⊆ A₁ := by
    rintro y ⟨hyN, hyΩ⟩
    rw [hA₁eq]
    exact ⟨hyN, fun h ↦ hyΩ (Or.inl h)⟩
  have hN₂Ω : N₂ ∩ (Cᶜ : Set M) ⊆ A₂ := by
    rintro y ⟨hyN, hyΩ⟩
    rw [hA₂eq]
    exact ⟨hyN, fun h ↦ hyΩ (Or.inr h)⟩
  -- Nonemptiness of the complement.
  have hne : ((Cᶜ : Set M)).Nonempty := by
    obtain ⟨z, hz⟩ := hA₁conn.nonempty
    exact ⟨z, hA₁Ω hz⟩
  refine ⟨hne, ?_⟩
  intro u v hu hv huv hsu hsv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  -- Restrict the separation to the open complement.
  set u' : Set M := u ∩ Cᶜ with hu'def
  set v' : Set M := v ∩ Cᶜ with hv'def
  have hu'o : IsOpen u' := hu.inter hΩo
  have hv'o : IsOpen v' := hv.inter hΩo
  have hu'Ω : u' ⊆ (Cᶜ : Set M) := Set.inter_subset_right
  have hv'Ω : v' ⊆ (Cᶜ : Set M) := Set.inter_subset_right
  have hcov : (Cᶜ : Set M) ⊆ u' ∪ v' := by
    intro z hz
    rcases huv hz with h | h
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨h, hz⟩
  have hu'v' : u' ∩ v' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨hzu, hzΩ⟩, hzv, -⟩
    have : z ∈ Cᶜ ∩ (u ∩ v) := ⟨hzΩ, hzu, hzv⟩
    rw [hcon] at this
    exact this
  have hu'ne : u'.Nonempty := by
    obtain ⟨z, hz₁, hz₂⟩ := hsu
    exact ⟨z, hz₂, hz₁⟩
  have hv'ne : v'.Nonempty := by
    obtain ⟨z, hz₁, hz₂⟩ := hsv
    exact ⟨z, hz₂, hz₁⟩
  -- Each connected annulus lies entirely on one side.
  have hside : ∀ A : Set M, IsConnected A → A ⊆ Cᶜ → A ⊆ u' ∨ A ⊆ v' := by
    intro A hAconn hAΩ
    rcases Set.eq_empty_or_nonempty (A ∩ v') with hv0 | hv1
    · left
      intro z hz
      rcases hcov (hAΩ hz) with h | h
      · exact h
      · exact absurd hv0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
    · rcases Set.eq_empty_or_nonempty (A ∩ u') with hu0 | hu1
      · right
        intro z hz
        rcases hcov (hAΩ hz) with h | h
        · exact absurd hu0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
        · exact h
      · exfalso
        obtain ⟨z, -, hzu, hzv⟩ := hAconn.2 u' v' hu'o hv'o
          (fun z hz ↦ hcov (hAΩ hz)) hu1 hv1
        have : z ∈ u' ∩ v' := ⟨hzu, hzv⟩
        rw [hu'v'] at this
        exact this
  -- The centers of the disks lie in the carriers, hence in the collars.
  have hcen₁ : D₁.center ∈ N₁ := by
    apply hC₁N₁
    exact ⟨chartAt ℂ D₁.center D₁.center, mem_closedBall_self D₁.radius_pos.le,
      (chartAt ℂ D₁.center).left_inv (mem_chart_source ℂ D₁.center)⟩
  have hcen₂ : D₂.center ∈ N₂ := by
    apply hC₂N₂
    exact ⟨chartAt ℂ D₂.center D₂.center, mem_closedBall_self D₂.radius_pos.le,
      (chartAt ℂ D₂.center).left_inv (mem_chart_source ℂ D₂.center)⟩
  -- A two-open-set separation of the connected surface `M` is impossible.
  have hsep : ∀ P Q : Set M, IsOpen P → IsOpen Q → Set.univ ⊆ P ∪ Q →
      P ∩ Q = ∅ → P.Nonempty → Q.Nonempty → False := by
    intro P Q hP hQ hPQ hdis hPne hQne
    obtain ⟨zp, hzp⟩ := hPne
    obtain ⟨zq, hzq⟩ := hQne
    obtain ⟨z, -, hz⟩ := isPreconnected_univ P Q hP hQ hPQ
      ⟨zp, Set.mem_univ zp, hzp⟩ ⟨zq, Set.mem_univ zq, hzq⟩
    rw [hdis] at hz
    exact hz
  -- Case split on the sides of the two annuli.
  rcases hside A₁ hA₁conn hA₁Ω with h₁u | h₁v <;>
    rcases hside A₂ hA₂conn hA₂Ω with h₂u | h₂v
  · -- both annuli on the `u'` side: `v'` separates from `u' ∪ N₁ ∪ N₂`
    refine hsep (u' ∪ (N₁ ∪ N₂)) v' (hu'o.union (hN₁o.union hN₂o)) hv'o ?_ ?_ ?_ hv'ne
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inl (Or.inr (Or.inl (hC₁N₁ h)))
        · exact Or.inl (Or.inr (Or.inr (hC₂N₂ h)))
      · rcases hcov hzC with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨(hzu | hzN | hzN), hzv⟩
      · have : z ∈ u' ∩ v' := ⟨hzu, hzv⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₁ := hN₁Ω ⟨hzN, hv'Ω hzv⟩
        have : z ∈ u' ∩ v' := ⟨h₁u hzA, hzv⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₂ := hN₂Ω ⟨hzN, hv'Ω hzv⟩
        have : z ∈ u' ∩ v' := ⟨h₂u hzA, hzv⟩
        rw [hu'v'] at this
        exact this
    · exact ⟨D₁.center, Or.inr (Or.inl hcen₁)⟩
  · -- mixed: `u' ∪ N₁` against `v' ∪ N₂`
    refine hsep (u' ∪ N₁) (v' ∪ N₂) (hu'o.union hN₁o) (hv'o.union hN₂o) ?_ ?_
      ⟨D₁.center, Or.inr hcen₁⟩ ⟨D₂.center, Or.inr hcen₂⟩
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inl (Or.inr (hC₁N₁ h))
        · exact Or.inr (Or.inr (hC₂N₂ h))
      · rcases hcov hzC with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzP, hzQ⟩
      have hzu' : z ∈ u' := by
        rcases hzP with h | h
        · exact h
        · rcases hzQ with h' | h'
          · exact h₁u (hN₁Ω ⟨h, hv'Ω h'⟩)
          · have : z ∈ N₁ ∩ N₂ := ⟨h, h'⟩
            rw [hN₁N₂] at this
            exact absurd this (Set.notMem_empty z)
      have hzv' : z ∈ v' := by
        rcases hzQ with h | h
        · exact h
        · exact h₂v (hN₂Ω ⟨h, hu'Ω hzu'⟩)
      have : z ∈ u' ∩ v' := ⟨hzu', hzv'⟩
      rw [hu'v'] at this
      exact this
  · -- mixed: `u' ∪ N₂` against `v' ∪ N₁`
    refine hsep (u' ∪ N₂) (v' ∪ N₁) (hu'o.union hN₂o) (hv'o.union hN₁o) ?_ ?_
      ⟨D₂.center, Or.inr hcen₂⟩ ⟨D₁.center, Or.inr hcen₁⟩
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inr (Or.inr (hC₁N₁ h))
        · exact Or.inl (Or.inr (hC₂N₂ h))
      · rcases hcov hzC with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzP, hzQ⟩
      have hzu' : z ∈ u' := by
        rcases hzP with h | h
        · exact h
        · rcases hzQ with h' | h'
          · exact h₂u (hN₂Ω ⟨h, hv'Ω h'⟩)
          · have : z ∈ N₁ ∩ N₂ := ⟨h', h⟩
            rw [hN₁N₂] at this
            exact absurd this (Set.notMem_empty z)
      have hzv' : z ∈ v' := by
        rcases hzQ with h | h
        · exact h
        · exact h₁v (hN₁Ω ⟨h, hu'Ω hzu'⟩)
      have : z ∈ u' ∩ v' := ⟨hzu', hzv'⟩
      rw [hu'v'] at this
      exact this
  · -- both annuli on the `v'` side: `u'` separates from `v' ∪ N₁ ∪ N₂`
    refine hsep u' (v' ∪ (N₁ ∪ N₂)) hu'o (hv'o.union (hN₁o.union hN₂o)) ?_ ?_
      hu'ne ⟨D₁.center, Or.inr (Or.inl hcen₁)⟩
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inr (Or.inr (Or.inl (hC₁N₁ h)))
        · exact Or.inr (Or.inr (Or.inr (hC₂N₂ h)))
      · rcases hcov hzC with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzu, (hzv | hzN | hzN)⟩
      · have : z ∈ u' ∩ v' := ⟨hzu, hzv⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₁ := hN₁Ω ⟨hzN, hu'Ω hzu⟩
        have : z ∈ u' ∩ v' := ⟨hzu, h₁v hzA⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₂ := hN₂Ω ⟨hzN, hu'Ω hzu⟩
        have : z ∈ u' ∩ v' := ⟨hzu, h₂v hzA⟩
        rw [hu'v'] at this
        exact this

omit [T2Space M] [ConnectedSpace M] in
/-- **The Harnack chain bound**: on a connected open set, positive harmonic
functions have uniformly comparable values on any compact subset, with a
constant depending only on the compact and the domain. -/
theorem exists_harnack_chain_const {Ω : Set M} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {K : Set M} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C > 0, ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ x ∈ Ω, 0 ≤ u x) →
      ∀ x ∈ K, ∀ y ∈ K, u x ≤ C * u y := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | ⟨k₀, hk₀⟩
  · refine ⟨1, one_pos, fun u _ _ x hx ↦ ?_⟩
    rw [hKe] at hx
    exact absurd hx (Set.notMem_empty x)
  have hk₀Ω : k₀ ∈ Ω := hKΩ hk₀
  -- Step 1: every point of `Ω` has an open Harnack neighbourhood inside `Ω` on
  -- which all admissible functions are `9`-comparable, via the chart reading
  -- and the plane Harnack inequality on a concentric chart ball.
  have key : ∀ x : M, ∃ N : Set M, IsOpen N ∧ (x ∈ Ω → x ∈ N) ∧ N ⊆ Ω ∧
      ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ z ∈ Ω, 0 ≤ u z) →
        ∀ a ∈ N, ∀ b ∈ N, u a ≤ 9 * u b := by
    intro x
    by_cases hx : x ∈ Ω
    · set e := chartAt ℂ x with he
      have hxsrc : x ∈ e.source := mem_chart_source ℂ x
      have hopen : IsOpen (e.target ∩ e.symm ⁻¹' Ω) := e.isOpen_inter_preimage_symm hΩ
      have hmem : e x ∈ e.target ∩ e.symm ⁻¹' Ω := by
        refine ⟨e.map_source hxsrc, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxsrc]
        exact hx
      obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.1 hopen _ hmem
      have hr0 : 0 < ρ / 2 := by linarith
      have h2r : ball (e x) (2 * (ρ / 2)) ⊆ e.target ∩ e.symm ⁻¹' Ω := by
        rw [show 2 * (ρ / 2) = ρ by ring]
        exact hρsub
      -- The chart reading of any admissible function is harmonic on the ball.
      have htrans : ∀ u : M → ℝ, MHarmonicOn u Ω →
          ∀ w ∈ ball (e x) (2 * (ρ / 2)), HarmonicAt (u ∘ e.symm) w := by
        intro u hu w hw
        have hwt : w ∈ e.target := (h2r hw).1
        have hws : e.symm w ∈ Ω := (h2r hw).2
        have hsrc : e.symm w ∈ e.source := e.map_target hwt
        have h1 := (mharmonicAt_iff_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x) hsrc).1 (hu _ hws)
        rwa [e.right_inv hwt] at h1
      refine ⟨e.source ∩ e ⁻¹' ball (e x) (ρ / 2),
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball,
        fun _ ↦ ⟨hxsrc, Set.mem_preimage.2 (mem_ball_self hr0)⟩, ?_, ?_⟩
      · rintro a ⟨has, hab⟩
        have h1 : e a ∈ ball (e x) (2 * (ρ / 2)) :=
          ball_subset_ball (by linarith) (Set.mem_preimage.1 hab)
        have h2 : e.symm (e a) ∈ Ω := (h2r h1).2
        rwa [e.left_inv has] at h2
      · intro u hu hupos a ha b hb
        have hh : HarmonicOnNhd (u ∘ e.symm) (ball (e x) (2 * (ρ / 2))) :=
          fun w hw ↦ htrans u hu w hw
        have hpos : ∀ z ∈ ball (e x) (2 * (ρ / 2)), 0 ≤ (u ∘ e.symm) z :=
          fun z hz ↦ hupos _ (h2r hz).2
        obtain ⟨-, hup_a⟩ :=
          harnack_inequality_ball hr0 hh hpos (e a) (Set.mem_preimage.1 ha.2)
        obtain ⟨hlow_b, -⟩ :=
          harnack_inequality_ball hr0 hh hpos (e b) (Set.mem_preimage.1 hb.2)
        have hca : e.symm (e a) = a := e.left_inv ha.1
        have hcb : e.symm (e b) = b := e.left_inv hb.1
        have hcx : e.symm (e x) = x := e.left_inv hxsrc
        simp only [Function.comp_apply, hca, hcb, hcx] at hup_a hlow_b
        linarith
    · exact ⟨∅, isOpen_empty, fun h ↦ absurd h hx, Set.empty_subset _,
        fun u _ _ a ha ↦ absurd ha (Set.notMem_empty a)⟩
  choose N hNopen hNmem hNsub hNkey using key
  -- Step 2: two-sided comparability with the base point propagates between any
  -- two points of a Harnack neighbourhood.
  have prop : ∀ y ∈ Ω, ∀ p ∈ N y, ∀ q ∈ N y,
      (∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ z ∈ Ω, 0 ≤ u z) →
        u q ≤ C * u k₀ ∧ u k₀ ≤ C * u q) →
      ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ z ∈ Ω, 0 ≤ u z) →
        u p ≤ C * u k₀ ∧ u k₀ ≤ C * u p := by
    intro y hy p hp q hq hgq
    obtain ⟨C, hC, hCb⟩ := hgq
    refine ⟨9 * C, by linarith, fun u hu hup ↦ ?_⟩
    obtain ⟨h1, h2⟩ := hCb u hu hup
    have h3 := hNkey y u hu hup p hp q hq
    have h4 := hNkey y u hu hup q hq p hp
    have h5 : C * u q ≤ C * (9 * u p) := mul_le_mul_of_nonneg_left h4 hC.le
    exact ⟨by linarith, by linarith⟩
  -- Step 3 (clopen argument): every point of the preconnected set `Ω` is
  -- two-sidedly comparable to the base point.
  have main : ∀ y ∈ Ω, ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
      (∀ z ∈ Ω, 0 ≤ u z) → u y ≤ C * u k₀ ∧ u k₀ ≤ C * u y := by
    set S₁ : Set M := {z | z ∈ Ω ∧ ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
      (∀ w ∈ Ω, 0 ≤ u w) → u z ≤ C * u k₀ ∧ u k₀ ≤ C * u z} with hS₁def
    set S₂ : Set M := {z | z ∈ Ω ∧ ¬∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
      (∀ w ∈ Ω, 0 ≤ u w) → u z ≤ C * u k₀ ∧ u k₀ ≤ C * u z} with hS₂def
    have hU₁o : IsOpen (⋃ y ∈ S₁, N y) := isOpen_biUnion fun y _ ↦ hNopen y
    have hU₂o : IsOpen (⋃ y ∈ S₂, N y) := isOpen_biUnion fun y _ ↦ hNopen y
    have hdisj : Disjoint (⋃ y ∈ S₁, N y) (⋃ y ∈ S₂, N y) := by
      rw [Set.disjoint_left]
      intro z hz₁ hz₂
      obtain ⟨y₁, hy₁, hzy₁⟩ := Set.mem_iUnion₂.1 hz₁
      obtain ⟨y₂, hy₂, hzy₂⟩ := Set.mem_iUnion₂.1 hz₂
      obtain ⟨hy₁Ω, hy₁g⟩ := hy₁
      obtain ⟨hy₂Ω, hy₂g⟩ := hy₂
      have hzg := prop y₁ hy₁Ω z hzy₁ y₁ (hNmem y₁ hy₁Ω) hy₁g
      exact hy₂g (prop y₂ hy₂Ω y₂ (hNmem y₂ hy₂Ω) z hzy₂ hzg)
    have hcover : Ω ⊆ (⋃ y ∈ S₁, N y) ∪ ⋃ y ∈ S₂, N y := by
      intro y hy
      by_cases hgy : ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
          (∀ w ∈ Ω, 0 ≤ u w) → u y ≤ C * u k₀ ∧ u k₀ ≤ C * u y
      · exact Or.inl (Set.mem_biUnion ⟨hy, hgy⟩ (hNmem y hy))
      · exact Or.inr (Set.mem_biUnion ⟨hy, hgy⟩ (hNmem y hy))
    have hne : (Ω ∩ ⋃ y ∈ S₁, N y).Nonempty := by
      refine ⟨k₀, hk₀Ω, ?_⟩
      have hk₀S : k₀ ∈ S₁ :=
        ⟨hk₀Ω, 1, one_pos, fun u _ _ ↦
          ⟨le_of_eq (one_mul (u k₀)).symm, le_of_eq (one_mul (u k₀)).symm⟩⟩
      exact Set.mem_biUnion hk₀S (hNmem k₀ hk₀Ω)
    have hΩU₁ : Ω ⊆ ⋃ y ∈ S₁, N y :=
      hΩc.subset_left_of_subset_union hU₁o hU₂o hdisj hcover hne
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := Set.mem_iUnion₂.1 (hΩU₁ hy)
    obtain ⟨hy'Ω, hy'g⟩ := hy'
    exact prop y' hy'Ω y hyy' y' (hNmem y' hy'Ω) hy'g
  -- Step 4: extract a uniform constant on the compact `K` from a finite
  -- subcover by Harnack neighbourhoods.
  choose! Cc hCpos hCbd using main
  have hcov : K ⊆ ⋃ i : K, N (i : M) := fun z hz ↦
    Set.mem_iUnion.2 ⟨⟨z, hz⟩, hNmem z (hKΩ hz)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K ↦ N (i : M))
    (fun _ ↦ hNopen _) hcov
  have htne : t.Nonempty := by
    obtain ⟨i, hit, -⟩ := Set.mem_iUnion₂.1 (ht hk₀)
    exact ⟨i, hit⟩
  set B : ℝ := t.sup' htne (fun i ↦ Cc (i : M)) with hBdef
  have hBle : ∀ i ∈ t, Cc (i : M) ≤ B :=
    fun i hi ↦ Finset.le_sup' (fun i : K ↦ Cc (i : M)) hi
  have hBpos : 0 < B := by
    obtain ⟨i₀, hi₀⟩ := htne
    exact lt_of_lt_of_le (hCpos _ (hKΩ i₀.2)) (hBle i₀ hi₀)
  refine ⟨81 * B * B, mul_pos (mul_pos (by norm_num) hBpos) hBpos,
    fun u hu hup x hx y hy ↦ ?_⟩
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
  obtain ⟨j, hjt, hyj⟩ := Set.mem_iUnion₂.1 (ht hy)
  have hiΩ : (i : M) ∈ Ω := hKΩ i.2
  have hjΩ : (j : M) ∈ Ω := hKΩ j.2
  have h1 : u x ≤ 9 * u (i : M) := hNkey (i : M) u hu hup x hxi (i : M) (hNmem _ hiΩ)
  have h2 : u (i : M) ≤ Cc (i : M) * u k₀ := (hCbd _ hiΩ u hu hup).1
  have h3 : u k₀ ≤ Cc (j : M) * u (j : M) := (hCbd _ hjΩ u hu hup).2
  have h4 : u (j : M) ≤ 9 * u y := hNkey (j : M) u hu hup (j : M) (hNmem _ hjΩ) y hyj
  have hCi : 0 < Cc (i : M) := hCpos _ hiΩ
  have hCj : 0 < Cc (j : M) := hCpos _ hjΩ
  have hy0 : 0 ≤ u y := hup y (hKΩ hy)
  have h5 : Cc (j : M) * u (j : M) ≤ Cc (j : M) * (9 * u y) :=
    mul_le_mul_of_nonneg_left h4 hCj.le
  have h6 : u k₀ ≤ 9 * Cc (j : M) * u y := by linarith
  have h7 : Cc (i : M) * u k₀ ≤ Cc (i : M) * (9 * Cc (j : M) * u y) :=
    mul_le_mul_of_nonneg_left h6 hCi.le
  have h8 : Cc (i : M) * Cc (j : M) ≤ B * B :=
    mul_le_mul (hBle i hit) (hBle j hjt) hCj.le hBpos.le
  have h9 : Cc (i : M) * Cc (j : M) * u y ≤ B * B * u y :=
    mul_le_mul_of_nonneg_right h8 hy0
  nlinarith [h1, h2, h7, h9]

set_option maxHeartbeats 400000 in
-- The heartbeat limit is raised because four analytic bricks (chart transfer,
-- Poisson-kernel Lipschitz bounds, diagonal extraction, limit harmonicity)
-- elaborate within a single declaration; each individual step is fast.
omit [T2Space M] [ConnectedSpace M] in
/-- **Normal families for harmonic functions**: a locally uniformly bounded
sequence of harmonic functions on an open set of a second-countable surface
has a subsequence converging locally uniformly to a harmonic function. -/
theorem exists_mharmonicOn_limit_of_locally_bounded [SecondCountableTopology M]
    {Ω : Set M} (hΩ : IsOpen Ω) {u : ℕ → M → ℝ}
    (hu : ∀ n : ℕ, MHarmonicOn (u n) Ω)
    (hb : ∀ K : Set M, IsCompact K → K ⊆ Ω → ∃ B : ℝ, ∀ n : ℕ, ∀ x ∈ K, |u n x| ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : M → ℝ, MHarmonicOn G Ω ∧
      ∀ K : Set M, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn (fun n ↦ u (φ n)) G Filter.atTop K := by
  classical
  -- ### Brick 0: chart transfer.  The reading in the chart at `x` of any function
  -- harmonic on `Ω` is harmonic at every plane point of the chart image of `Ω`.
  have htransfer : ∀ (x : M) (v : M → ℝ), MHarmonicOn v Ω →
      ∀ w ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω,
        HarmonicAt (v ∘ (chartAt ℂ x).symm) w := by
    intro x v hv w hw
    obtain ⟨hwt, hwΩ⟩ := hw
    have hwΩ' : (chartAt ℂ x).symm w ∈ Ω := hwΩ
    have hyy : (chartAt ℂ x).symm w ∈ (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
      mem_chart_source ℂ ((chartAt ℂ x).symm w)
    have htrans : AnalyticAt ℂ (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ
        x).symm) w := by
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hwt
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ ((chartAt ℂ x).symm w)))
          ((chartAt ℂ x).symm w) :=
        contMDiffAt_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas ((chartAt ℂ x).symm w)) hyy
      exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
    have hmh : HarmonicAt (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        ((⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w) := hv _ hwΩ'
    have hcomp := harmonicAt_comp_analyticAt hmh htrans
    have hev : (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 w]
        v ∘ ⇑(chartAt ℂ x).symm := by
      have hS : IsOpen ((chartAt ℂ x).target ∩
          ⇑(chartAt ℂ x).symm ⁻¹' (chartAt ℂ ((chartAt ℂ x).symm w)).source) :=
        (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ x).open_target
          (chartAt ℂ ((chartAt ℂ x).symm w)).open_source
      filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with ζ hζ
      simp only [Function.comp_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hζ.2]
    exact (harmonicAt_congr_nhds hev).mp hcomp
  -- ### Brick 1: the Poisson kernel is continuous on the circle, for interior points.
  have hKcont : ∀ (c z : ℂ) (ρ : ℝ), z ∈ ball c ρ →
      ContinuousOn (poissonKernel c z) (sphere c ρ) := by
    intro c z ρ hz
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    apply Complex.continuous_re.comp_continuousOn
    rw [herglotzRieszKernel_fun_def]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro w hw
    have hwn : ‖w - c‖ = ρ := by rw [← dist_eq_norm]; simpa using (mem_sphere.1 hw)
    have hzlt : ‖z - c‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hz
    intro hcontra
    have hwz : w - c = z - c := by linear_combination (norm := ring_nf) hcontra
    rw [hwz] at hwn
    linarith
  -- ### Brick 2: circle averages of uniformly close functions are close.
  have havg_diff : ∀ (F g : ℂ → ℝ) (c : ℂ) (ρ A : ℝ), 0 < ρ →
      ContinuousOn F (sphere c ρ) → ContinuousOn g (sphere c ρ) →
      (∀ ζ ∈ sphere c ρ, |F ζ - g ζ| ≤ A) →
      |Real.circleAverage F c ρ - Real.circleAverage g c ρ| ≤ A := by
    intro F g c ρ A hρ hF hg hbd
    have hFi : CircleIntegrable F c ρ := hF.circleIntegrable hρ.le
    have hgi : CircleIntegrable g c ρ := hg.circleIntegrable hρ.le
    have habsci : CircleIntegrable (fun ζ ↦ |F ζ - g ζ|) c ρ :=
      ((hF.sub hg).abs).circleIntegrable hρ.le
    rw [← Real.circleAverage_fun_sub hFi hgi]
    calc |Real.circleAverage (fun ζ ↦ F ζ - g ζ) c ρ|
        ≤ Real.circleAverage |fun ζ ↦ F ζ - g ζ| c ρ :=
          Real.abs_circleAverage_le_circleAverage_abs
      _ ≤ A := by
          apply Real.circleAverage_mono_on_of_le_circle habsci
          intro ζ hζ
          rw [abs_of_pos hρ] at hζ
          exact hbd ζ hζ
  -- ### Brick 3: interior Lipschitz bound for bounded harmonic functions on a disk,
  -- from the Poisson representation and the kernel-difference estimate.
  have hplaneLip : ∀ (c : ℂ) (ρ B : ℝ), 0 < ρ → 0 ≤ B → ∀ h : ℂ → ℝ,
      HarmonicOnNhd h (closedBall c ρ) → (∀ ζ ∈ closedBall c ρ, |h ζ| ≤ B) →
      ∀ z ∈ ball c (ρ / 2), ∀ w ∈ ball c (ρ / 2),
        |h z - h w| ≤ 52 * B / ρ * ‖z - w‖ := by
    intro c ρ B hρ hB h hh hbd z hz w hw
    have hzball : z ∈ ball c ρ := ball_subset_ball (by linarith) hz
    have hwball : w ∈ ball c ρ := ball_subset_ball (by linarith) hw
    -- Poisson representations at the two points.
    have hrz := hh.circleAverage_poissonKernel_smul hzball
    have hrw := hh.circleAverage_poissonKernel_smul hwball
    have hrz' : Real.circleAverage (fun ζ ↦ poissonKernel c z ζ * h ζ) c ρ = h z := by
      rw [← hrz]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    have hrw' : Real.circleAverage (fun ζ ↦ poissonKernel c w ζ * h ζ) c ρ = h w := by
      rw [← hrw]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    -- The kernel-difference bound on the circle.
    have hker : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c z ζ - poissonKernel c w ζ| ≤ 52 / ρ * ‖z - w‖ := by
      intro ζ hζ
      have hζρ : ‖ζ - c‖ = ρ := by rw [← dist_eq_norm]; exact mem_sphere.1 hζ
      have haz : ‖z - c‖ < ρ / 2 := by rw [← dist_eq_norm]; exact mem_ball.1 hz
      have haw : ‖w - c‖ < ρ / 2 := by rw [← dist_eq_norm]; exact mem_ball.1 hw
      have haz0 : 0 ≤ ‖z - c‖ := norm_nonneg _
      have haw0 : 0 ≤ ‖w - c‖ := norm_nonneg _
      have hd0 : 0 ≤ ‖z - w‖ := norm_nonneg _
      -- distance bounds from the sphere to the interior points
      have hDz_low : ρ / 2 ≤ ‖ζ - z‖ := by
        have h1 : ‖ζ - c‖ - ‖z - c‖ ≤ ‖ζ - c - (z - c)‖ := norm_sub_norm_le _ _
        have h2 : ζ - c - (z - c) = ζ - z := by ring
        rw [h2] at h1
        linarith
      have hDw_low : ρ / 2 ≤ ‖ζ - w‖ := by
        have h1 : ‖ζ - c‖ - ‖w - c‖ ≤ ‖ζ - c - (w - c)‖ := norm_sub_norm_le _ _
        have h2 : ζ - c - (w - c) = ζ - w := by ring
        rw [h2] at h1
        linarith
      have hDz_up : ‖ζ - z‖ ≤ 3 * ρ / 2 := by
        have h1 : ‖ζ - z‖ ≤ ‖ζ - c‖ + ‖c - z‖ := by
          have h2 : ζ - z = (ζ - c) + (c - z) := by ring
          rw [h2]; exact norm_add_le _ _
        have h3 : ‖c - z‖ = ‖z - c‖ := by rw [← neg_sub, norm_neg]
        rw [h3] at h1
        linarith
      have hDw_up : ‖ζ - w‖ ≤ 3 * ρ / 2 := by
        have h1 : ‖ζ - w‖ ≤ ‖ζ - c‖ + ‖c - w‖ := by
          have h2 : ζ - w = (ζ - c) + (c - w) := by ring
          rw [h2]; exact norm_add_le _ _
        have h3 : ‖c - w‖ = ‖w - c‖ := by rw [← neg_sub, norm_neg]
        rw [h3] at h1
        linarith
      have hZW : |‖ζ - w‖ - ‖ζ - z‖| ≤ ‖z - w‖ := by
        have h1 := abs_norm_sub_norm_le (ζ - w) (ζ - z)
        have h2 : ζ - w - (ζ - z) = z - w := by ring
        rwa [h2] at h1
      have hAZW : |‖w - c‖ - ‖z - c‖| ≤ ‖z - w‖ := by
        have h1 := abs_norm_sub_norm_le (w - c) (z - c)
        have h2 : w - c - (z - c) = w - z := by ring
        rw [h2, norm_sub_rev w z] at h1
        exact h1
      have hDz0 : (0 : ℝ) < ‖ζ - z‖ := lt_of_lt_of_le (by linarith) hDz_low
      have hDw0 : (0 : ℝ) < ‖ζ - w‖ := lt_of_lt_of_le (by linarith) hDw_low
      -- the two kernels in explicit form
      have hKz : poissonKernel c z ζ = (ρ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - z‖ ^ 2 := by
        rw [poissonKernel_def, hζρ]
        congr 2
        rw [show ζ - c - (z - c) = ζ - z from by ring]
      have hKw : poissonKernel c w ζ = (ρ ^ 2 - ‖w - c‖ ^ 2) / ‖ζ - w‖ ^ 2 := by
        rw [poissonKernel_def, hζρ]
        congr 2
        rw [show ζ - c - (w - c) = ζ - w from by ring]
      -- split the difference into two boundable pieces
      have hsplit : (ρ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - z‖ ^ 2 - (ρ ^ 2 - ‖w - c‖ ^ 2) /
          ‖ζ - w‖ ^ 2
          = (ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) / (‖ζ - z‖ ^ 2 *
              ‖ζ - w‖ ^ 2)
            + (‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2 := by
        field_simp
        ring
      have haz2 : ‖z - c‖ * ‖z - c‖ ≤ ρ / 2 * (ρ / 2) := mul_self_le_mul_self haz0
          haz.le
      have hDzsq : ρ / 2 * (ρ / 2) ≤ ‖ζ - z‖ * ‖ζ - z‖ :=
        mul_self_le_mul_self (by positivity) hDz_low
      have hDwsq : ρ / 2 * (ρ / 2) ≤ ‖ζ - w‖ * ‖ζ - w‖ :=
        mul_self_le_mul_self (by positivity) hDw_low
      have h1 : |(ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) /
          (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)| ≤ 48 / ρ * ‖z - w‖ := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ‖ζ - z‖ ^ 2 * ‖ζ - w‖
            ^ 2)]
        have e1 : |ρ ^ 2 - ‖z - c‖ ^ 2| ≤ ρ ^ 2 := by
          rw [abs_of_nonneg (by linarith [haz2, sq_nonneg ρ])]
          linarith [sq_nonneg ‖z - c‖]
        have e2 : |‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2| ≤ 3 * ρ * ‖z - w‖ := by
          have h3 : ‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2
              = (‖ζ - w‖ - ‖ζ - z‖) * (‖ζ - w‖ + ‖ζ - z‖) := by ring
          rw [h3, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖ζ - w‖ + ‖ζ - z‖)]
          calc |‖ζ - w‖ - ‖ζ - z‖| * (‖ζ - w‖ + ‖ζ - z‖)
              ≤ ‖z - w‖ * (3 * ρ) := by
                apply mul_le_mul hZW (by linarith) (by linarith) hd0
            _ = 3 * ρ * ‖z - w‖ := by ring
        have e3 : ρ ^ 4 / 16 ≤ ‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2 := by
          have e3a : ρ ^ 2 / 4 ≤ ‖ζ - z‖ ^ 2 := by linarith [hDzsq]
          have e3b : ρ ^ 2 / 4 ≤ ‖ζ - w‖ ^ 2 := by linarith [hDwsq]
          calc ρ ^ 4 / 16 = ρ ^ 2 / 4 * (ρ ^ 2 / 4) := by ring
            _ ≤ ‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2 :=
                mul_le_mul e3a e3b (by positivity) (by positivity)
        calc |ρ ^ 2 - ‖z - c‖ ^ 2| * |‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2| /
            (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)
            ≤ ρ ^ 2 * (3 * ρ * ‖z - w‖) / (ρ ^ 4 / 16) := by
              apply div_le_div₀ (by positivity)
                (mul_le_mul e1 e2 (abs_nonneg _) (by positivity)) (by positivity) e3
          _ = 48 / ρ * ‖z - w‖ := by
              field_simp
              ring
      have h2 : |(‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2| ≤ 4 / ρ * ‖z - w‖ := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ‖ζ - w‖ ^ 2)]
        have e5 : |‖w - c‖ ^ 2 - ‖z - c‖ ^ 2| ≤ ρ * ‖z - w‖ := by
          have h3 : ‖w - c‖ ^ 2 - ‖z - c‖ ^ 2
              = (‖w - c‖ - ‖z - c‖) * (‖w - c‖ + ‖z - c‖) := by ring
          rw [h3, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖w - c‖ + ‖z - c‖)]
          calc |‖w - c‖ - ‖z - c‖| * (‖w - c‖ + ‖z - c‖)
              ≤ ‖z - w‖ * ρ := by
                apply mul_le_mul hAZW (by linarith) (by linarith) hd0
            _ = ρ * ‖z - w‖ := by ring
        have e6 : ρ ^ 2 / 4 ≤ ‖ζ - w‖ ^ 2 := by linarith [hDwsq]
        calc |‖w - c‖ ^ 2 - ‖z - c‖ ^ 2| / ‖ζ - w‖ ^ 2
            ≤ ρ * ‖z - w‖ / (ρ ^ 2 / 4) := by
              apply div_le_div₀ (by positivity) e5 (by positivity) e6
          _ = 4 / ρ * ‖z - w‖ := by
              field_simp
      calc |poissonKernel c z ζ - poissonKernel c w ζ|
          = |(ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) /
              (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)
              + (‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2| := by
            rw [hKz, hKw, hsplit]
        _ ≤ |(ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) /
              (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)|
              + |(‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2| := abs_add_le _ _
        _ ≤ 48 / ρ * ‖z - w‖ + 4 / ρ * ‖z - w‖ := add_le_add h1 h2
        _ = 52 / ρ * ‖z - w‖ := by ring
    -- assemble via the circle-average difference bound
    have hhcont : ContinuousOn h (sphere c ρ) := hh.continuousOn.mono sphere_subset_closedBall
    have hFzc : ContinuousOn (fun ζ ↦ poissonKernel c z ζ * h ζ) (sphere c ρ) :=
      (hKcont c z ρ hzball).mul hhcont
    have hFwc : ContinuousOn (fun ζ ↦ poissonKernel c w ζ * h ζ) (sphere c ρ) :=
      (hKcont c w ρ hwball).mul hhcont
    have hptbd : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c z ζ * h ζ - poissonKernel c w ζ * h ζ|
          ≤ 52 / ρ * ‖z - w‖ * B := by
      intro ζ hζ
      have h1 : |poissonKernel c z ζ * h ζ - poissonKernel c w ζ * h ζ|
          = |poissonKernel c z ζ - poissonKernel c w ζ| * |h ζ| := by
        rw [← sub_mul, abs_mul]
      rw [h1]
      exact mul_le_mul (hker ζ hζ) (hbd ζ (sphere_subset_closedBall hζ)) (abs_nonneg _)
        (by positivity)
    have := havg_diff _ _ c ρ (52 / ρ * ‖z - w‖ * B) hρ hFzc hFwc hptbd
    rw [hrz', hrw'] at this
    calc |h z - h w| ≤ 52 / ρ * ‖z - w‖ * B := this
      _ = 52 * B / ρ * ‖z - w‖ := by ring
  -- ### Brick 4: chart-disk data at every point of `Ω`.
  have hdata : ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧
      closedBall (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω
          := by
    intro x hx
    have hTopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm hΩ
    have hcT : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω := by
      refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hx
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.isOpen_iff.1 hTopen _ hcT
    exact ⟨ρ₀ / 2, by positivity,
      (closedBall_subset_ball (by linarith)).trans hρ₀sub⟩
  -- ### The empty case.
  by_cases hne : Ω = ∅
  · refine ⟨id, strictMono_id, 0, ?_, ?_⟩
    · intro x hx
      rw [hne] at hx
      exact absurd hx (Set.notMem_empty x)
    · intro K hK hKΩ
      have hKe : K = ∅ := by
        rw [hne] at hKΩ
        exact Set.subset_eq_empty hKΩ rfl
      rw [hKe]
      exact tendstoUniformlyOn_empty
  -- ### A dense sequence in `Ω`.
  have hΩne : Ω.Nonempty := Set.nonempty_iff_ne_empty.2 hne
  have : Nonempty ↥Ω := hΩne.to_subtype
  obtain ⟨dd, hdd⟩ := TopologicalSpace.exists_dense_seq ↥Ω
  have hdΩ : ∀ j : ℕ, (dd j : M) ∈ Ω := fun j ↦ (dd j).2
  have hdense : ∀ O : Set M, IsOpen O → (O ∩ Ω).Nonempty → ∃ j : ℕ, (dd j : M) ∈ O := by
    intro O hO hOne
    obtain ⟨y, hyO, hyΩ⟩ := hOne
    have hpre : IsOpen ((↑) ⁻¹' O : Set ↥Ω) := hO.preimage continuous_subtype_val
    have hprene : ((↑) ⁻¹' O : Set ↥Ω).Nonempty := ⟨⟨y, hyΩ⟩, hyO⟩
    obtain ⟨j, hj⟩ := hdd.exists_mem_open hpre hprene
    exact ⟨j, hj⟩
  -- ### Diagonal extraction at the dense sequence, via compactness of a countable
  -- product of intervals.
  have hbdj : ∀ j : ℕ, ∃ B, ∀ n, |u n (dd j : M)| ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := hb {(dd j : M)} isCompact_singleton
      (Set.singleton_subset_iff.2 (hdΩ j))
    exact ⟨B, fun n ↦ hB n _ rfl⟩
  choose Bd hBd using hbdj
  have hScomp : IsCompact (Set.univ.pi fun j : ℕ ↦ Set.Icc (-(Bd j)) (Bd j)) :=
    isCompact_univ_pi fun j ↦ isCompact_Icc
  have hmemS : ∀ n, (fun j ↦ u n (dd j : M)) ∈
      Set.univ.pi fun j : ℕ ↦ Set.Icc (-(Bd j)) (Bd j) := by
    intro n
    rw [Set.mem_univ_pi]
    intro j
    exact abs_le.1 (hBd j n)
  obtain ⟨a, -, φ, hφmono, hφtend⟩ := hScomp.tendsto_subseq hmemS
  have hconv : ∀ j : ℕ, Tendsto (fun n ↦ u (φ n) (dd j : M)) atTop (𝓝 (a j)) :=
    fun j ↦ tendsto_pi_nhds.1 hφtend j
  refine ⟨φ, hφmono, ?_⟩
  -- ### The local uniform Cauchy property.
  have hlocal : ∀ x ∈ Ω, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ y ∈ V,
        |u (φ m) y - u (φ n) y| < ε := by
    intro x hx
    obtain ⟨ρ, hρ, hsub⟩ := hdata x hx
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hsubT : closedBall (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target :=
      hsub.trans Set.inter_subset_left
    -- the compact read-back of the closed chart ball
    have hKcomp : IsCompact ((chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ) :=
      (isCompact_closedBall _ _).image_of_continuousOn
        ((chartAt ℂ x).continuousOn_symm.mono hsubT)
    have hKΩ : (chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ ⊆ Ω := by
      rintro y ⟨ζ, hζ, rfl⟩
      exact (hsub hζ).2
    obtain ⟨B, hB⟩ := hb _ hKcomp hKΩ
    have hxK : x ∈ (chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ :=
      ⟨chartAt ℂ x x, mem_closedBall_self hρ.le, (chartAt ℂ x).left_inv hxsrc⟩
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 x hxK)
    -- readings are harmonic on a neighborhood of the closed ball and bounded by B
    have hread : ∀ k : ℕ, HarmonicOnNhd (u k ∘ (chartAt ℂ x).symm)
        (closedBall (chartAt ℂ x x) ρ) :=
      fun k ζ hζ ↦ htransfer x (u k) (hu k) ζ (hsub hζ)
    have hbound : ∀ k : ℕ, ∀ ζ ∈ closedBall (chartAt ℂ x x) ρ,
        |(u k ∘ (chartAt ℂ x).symm) ζ| ≤ B :=
      fun k ζ hζ ↦ hB k _ ⟨ζ, hζ, rfl⟩
    -- the Lipschitz constant on the half ball
    have hlip : ∀ k : ℕ, ∀ z ∈ ball (chartAt ℂ x x) (ρ / 2),
        ∀ w ∈ ball (chartAt ℂ x x) (ρ / 2),
        |u k ((chartAt ℂ x).symm z) - u k ((chartAt ℂ x).symm w)|
          ≤ 52 * B / ρ * ‖z - w‖ :=
      fun k z hz w hw ↦
        hplaneLip (chartAt ℂ x x) ρ B hρ hB0 (u k ∘ (chartAt ℂ x).symm)
          (hread k) (hbound k) z hz w hw
    -- the neighborhood
    refine ⟨(chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4),
      (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
        isOpen_ball,
      ⟨hxsrc, Set.mem_preimage.2 (mem_ball_self (by positivity : (0:ℝ) < ρ / 4))⟩,
      ?_, ?_⟩
    · intro y hy
      have h1 : chartAt ℂ x y ∈ closedBall (chartAt ℂ x x) ρ :=
        ball_subset_closedBall (ball_subset_ball (by linarith) hy.2)
      have h2 : (chartAt ℂ x).symm (chartAt ℂ x y) ∈ Ω := (hsub h1).2
      rwa [(chartAt ℂ x).left_inv hy.1] at h2
    · intro ε hε
      set L : ℝ := 52 * B / ρ with hLdef
      have hL0 : 0 ≤ L := by positivity
      set δ : ℝ := ε / (4 * (L + 1)) with hδdef
      have hδ0 : 0 < δ := by positivity
      -- finite δ/2-net of the quarter ball
      obtain ⟨t, -, htcover⟩ :=
        (isCompact_closedBall (chartAt ℂ x x) (ρ / 4)).elim_nhds_subcover
          (fun ζ ↦ ball ζ (δ / 2)) (fun ζ _ ↦ ball_mem_nhds ζ (by positivity))
      -- representative points of the dense sequence in each net cell
      have hchoice : ∀ ζ : ℂ, ∃ j : ℕ,
          ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
            ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))).Nonempty →
          (dd j : M) ∈ (chartAt ℂ x).source ∩
            ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
            ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2)) := by
        intro ζ
        by_cases hne2 : ((chartAt ℂ x).source ∩
            ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
            ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))).Nonempty
        · have hWopen : IsOpen ((chartAt ℂ x).source ∩
              ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
              ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))) :=
            ((chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
                isOpen_ball).inter
              ((chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
                isOpen_ball)
          obtain ⟨y, hy⟩ := hne2
          have hyΩ : y ∈ Ω := by
            have h1 : chartAt ℂ x y ∈ closedBall (chartAt ℂ x x) ρ :=
              ball_subset_closedBall (ball_subset_ball (by linarith) hy.1.2)
            have h2 : (chartAt ℂ x).symm (chartAt ℂ x y) ∈ Ω := (hsub h1).2
            rwa [(chartAt ℂ x).left_inv hy.1.1] at h2
          obtain ⟨j, hj⟩ := hdense _ hWopen ⟨y, hy, hyΩ⟩
          exact ⟨j, fun _ ↦ hj⟩
        · exact ⟨0, fun hcon ↦ absurd hcon hne2⟩
      choose jpt hjpt using hchoice
      -- Cauchy thresholds at the finitely many representatives
      have hCau : ∀ ζ : ℂ, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
          |u (φ m) (dd (jpt ζ) : M) - u (φ n) (dd (jpt ζ) : M)| < ε / 3 := by
        intro ζ
        have hcs : CauchySeq (fun n ↦ u (φ n) (dd (jpt ζ) : M)) :=
          (hconv (jpt ζ)).cauchySeq
        rw [Metric.cauchySeq_iff] at hcs
        obtain ⟨N, hN⟩ := hcs (ε / 3) (by positivity)
        exact ⟨N, fun m hm n hn ↦ by
          have := hN m hm n hn
          rwa [Real.dist_eq] at this⟩
      choose Nf hNf using hCau
      refine ⟨t.sup Nf, ?_⟩
      intro m hm n hn y hy
      -- locate `y`'s chart image in the net
      have hyQ : chartAt ℂ x y ∈ closedBall (chartAt ℂ x x) (ρ / 4) :=
        ball_subset_closedBall hy.2
      obtain ⟨ζ, hζt, hyζ⟩ := Set.mem_iUnion₂.1 (htcover hyQ)
      have hWne : ((chartAt ℂ x).source ∩
          ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
          ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))).Nonempty :=
        ⟨y, hy, hy.1, hyζ⟩
      have hdj := hjpt ζ hWne
      -- chart images of the pair lie in the half ball, at distance < δ
      have hey : chartAt ℂ x y ∈ ball (chartAt ℂ x x) (ρ / 2) :=
        ball_subset_ball (by linarith) hy.2
      have hedj : chartAt ℂ x (dd (jpt ζ) : M) ∈ ball (chartAt ℂ x x) (ρ / 2) :=
        ball_subset_ball (by linarith) hdj.1.2
      have hdist : ‖chartAt ℂ x y - chartAt ℂ x (dd (jpt ζ) : M)‖ < δ := by
        rw [← dist_eq_norm]
        calc dist (chartAt ℂ x y) (chartAt ℂ x (dd (jpt ζ) : M))
            ≤ dist (chartAt ℂ x y) ζ + dist ζ (chartAt ℂ x (dd (jpt ζ) : M)) :=
              dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := by
              apply add_lt_add (mem_ball.1 hyζ)
              rw [dist_comm]
              exact mem_ball.1 hdj.2.2
          _ = δ := by ring
      -- three-epsilon assembly
      have hyy : (chartAt ℂ x).symm (chartAt ℂ x y) = y := (chartAt ℂ x).left_inv hy.1
      have hdd' : (chartAt ℂ x).symm (chartAt ℂ x (dd (jpt ζ) : M)) = (dd (jpt ζ) : M) :=
        (chartAt ℂ x).left_inv hdj.1.1
      have hlip_m : |u (φ m) y - u (φ m) (dd (jpt ζ) : M)| ≤ L * δ := by
        have h1 := hlip (φ m) _ hey _ hedj
        rw [hyy, hdd'] at h1
        calc |u (φ m) y - u (φ m) (dd (jpt ζ) : M)|
            ≤ L * ‖chartAt ℂ x y - chartAt ℂ x (dd (jpt ζ) : M)‖ := h1
          _ ≤ L * δ := mul_le_mul_of_nonneg_left hdist.le hL0
      have hlip_n : |u (φ n) y - u (φ n) (dd (jpt ζ) : M)| ≤ L * δ := by
        have h1 := hlip (φ n) _ hey _ hedj
        rw [hyy, hdd'] at h1
        calc |u (φ n) y - u (φ n) (dd (jpt ζ) : M)|
            ≤ L * ‖chartAt ℂ x y - chartAt ℂ x (dd (jpt ζ) : M)‖ := h1
          _ ≤ L * δ := mul_le_mul_of_nonneg_left hdist.le hL0
      have hmid : |u (φ m) (dd (jpt ζ) : M) - u (φ n) (dd (jpt ζ) : M)| < ε / 3 :=
        hNf ζ m (le_trans (Finset.le_sup hζt) hm) n (le_trans (Finset.le_sup hζt) hn)
      have hLδ : L * δ ≤ ε / 4 := by
        rw [hδdef]
        rw [div_eq_mul_inv, ← mul_assoc]
        have h1 : L * ε * (4 * (L + 1))⁻¹ ≤ (L + 1) * ε * (4 * (L + 1))⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hε.le
          linarith
        calc L * ε * (4 * (L + 1))⁻¹ ≤ (L + 1) * ε * (4 * (L + 1))⁻¹ := h1
          _ = ε / 4 := by
            field_simp
      have hlip_n' : |u (φ n) (dd (jpt ζ) : M) - u (φ n) y| ≤ L * δ := by
        rw [abs_sub_comm]
        exact hlip_n
      have htri1 := abs_sub_le (u (φ m) y) (u (φ m) (dd (jpt ζ) : M)) (u (φ n) y)
      have htri2 := abs_sub_le (u (φ m) (dd (jpt ζ) : M)) (u (φ n) (dd (jpt ζ) : M))
        (u (φ n) y)
      linarith [htri1, htri2, hlip_m, hlip_n', hmid, hLδ]
  -- ### The pointwise limit function.
  have hGex : ∀ y ∈ Ω, ∃ l : ℝ, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 l) := by
    intro y hy
    obtain ⟨V, -, hyV, -, hVc⟩ := hlocal y hy
    have hcs : CauchySeq (fun n ↦ u (φ n) y) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hVc ε hε
      exact ⟨N, fun m hm n hn ↦ by
        rw [Real.dist_eq]
        exact hN m hm n hn y hyV⟩
    exact cauchySeq_tendsto_of_complete hcs
  set G : M → ℝ := fun y ↦
    if h : ∃ l : ℝ, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 l) then h.choose else 0
    with hGdef
  have hGtend : ∀ y ∈ Ω, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (G y)) := by
    intro y hy
    have h := hGex y hy
    have hGy : G y = h.choose := by
      rw [hGdef]
      exact dite_eq_left h
    rw [hGy]
    exact h.choose_spec
  -- ### Uniform convergence on each local piece.
  have hVunif : ∀ V : Set M, V ⊆ Ω →
      (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ y ∈ V,
        |u (φ m) y - u (φ n) y| < ε) →
      TendstoUniformlyOn (fun n ↦ u (φ n)) G atTop V := by
    intro V hVΩ hVc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hVc (ε / 2) (by positivity)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn y hy ↦ ?_⟩
    have h1 : Tendsto (fun m ↦ dist (u (φ m) y) (u (φ n) y)) atTop
        (𝓝 (dist (G y) (u (φ n) y))) :=
      (hGtend y (hVΩ hy)).dist tendsto_const_nhds
    have h2 : ∀ᶠ m in atTop, dist (u (φ m) y) (u (φ n) y) ≤ ε / 2 := by
      rw [Filter.eventually_atTop]
      exact ⟨N, fun m hm ↦ by
        rw [Real.dist_eq]
        exact (hN m hm n hn y hy).le⟩
    have h3 : dist (G y) (u (φ n) y) ≤ ε / 2 := le_of_tendsto h1 h2
    linarith
  -- ### Uniform convergence on compact subsets.
  have hKunif : ∀ K, IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn (fun n ↦ u (φ n)) G atTop K := by
    intro K hK hKΩ
    choose V hVopen hVmem hVsub hVc using hlocal
    obtain ⟨t, hts⟩ := hK.elim_nhds_subcover' (fun x hx ↦ V x (hKΩ hx))
      (fun x hx ↦ (hVopen x (hKΩ hx)).mem_nhds (hVmem x (hKΩ hx)))
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev : ∀ᶠ n in atTop, ∀ z ∈ t,
        ∀ y ∈ V (z : M) (hKΩ z.2), dist (G y) (u (φ n) y) < ε := by
      rw [Filter.eventually_all_finset]
      intro z hzt
      have h1 := hVunif (V (z : M) (hKΩ z.2)) (hVsub (z : M) (hKΩ z.2))
        (hVc (z : M) (hKΩ z.2))
      rw [Metric.tendstoUniformlyOn_iff] at h1
      exact h1 ε hε
    filter_upwards [hev] with n hn y hyK
    obtain ⟨z, hzt, hyV⟩ := Set.mem_iUnion₂.1 (hts hyK)
    exact hn z hzt y hyV
  -- ### Harmonicity of the limit, via the Poisson integral on chart disks.
  refine ⟨G, ?_, hKunif⟩
  intro x hx
  obtain ⟨ρ, hρ, hsub⟩ := hdata x hx
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hsubT : closedBall (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target :=
    hsub.trans Set.inter_subset_left
  have hKcomp : IsCompact ((chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt ℂ x).continuousOn_symm.mono hsubT)
  have hKΩ : (chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ ⊆ Ω := by
    rintro y ⟨ζ, hζ, rfl⟩
    exact (hsub hζ).2
  -- readings of the subsequence, harmonic on a neighborhood of the closed ball
  have hread : ∀ n : ℕ, HarmonicOnNhd (u (φ n) ∘ (chartAt ℂ x).symm)
      (closedBall (chartAt ℂ x x) ρ) :=
    fun n ζ hζ ↦ htransfer x (u (φ n)) (hu (φ n)) ζ (hsub hζ)
  -- uniform convergence of the readings on the closed chart ball
  have hunif : TendstoUniformlyOn (fun n ↦ u (φ n) ∘ (chartAt ℂ x).symm)
      (G ∘ (chartAt ℂ x).symm) atTop (closedBall (chartAt ℂ x x) ρ) := by
    have h1 := (hKunif _ hKcomp hKΩ).comp (chartAt ℂ x).symm
    exact h1.mono fun ζ hζ ↦ ⟨ζ, hζ, rfl⟩
  have hcont_n : ∀ n : ℕ, ContinuousOn (u (φ n) ∘ (chartAt ℂ x).symm)
      (closedBall (chartAt ℂ x x) ρ) :=
    fun n ↦ (hread n).continuousOn
  have hGcont : ContinuousOn (G ∘ (chartAt ℂ x).symm) (closedBall (chartAt ℂ x x) ρ) :=
    hunif.continuousOn ((Filter.Eventually.of_forall hcont_n).frequently)
  -- the limit satisfies the Poisson identity on the open ball
  have hPI : ∀ z ∈ ball (chartAt ℂ x x) ρ,
      (G ∘ (chartAt ℂ x).symm) z
        = poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z := by
    intro z hz
    have haz : ‖z - chartAt ℂ x x‖ < ρ := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hz
    have haz0 : 0 ≤ ‖z - chartAt ℂ x x‖ := norm_nonneg _
    set Kb : ℝ := (ρ + ‖z - chartAt ℂ x x‖) / (ρ - ‖z - chartAt ℂ x x‖) with hKbdef
    have hKb0 : 0 ≤ Kb := div_nonneg (by linarith) (by linarith)
    have hKbound : ∀ ζ ∈ sphere (chartAt ℂ x x) ρ, |poissonKernel (chartAt ℂ x x) z ζ|
        ≤ Kb := by
      intro ζ hζ
      have hup : poissonKernel (chartAt ℂ x x) z ζ ≤ Kb := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        exact re_herglotzRieszKernel_le hζ hz
      have hlo : 0 ≤ poissonKernel (chartAt ℂ x x) z ζ := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        refine le_trans ?_ (le_re_herglotzRieszKernel hζ hz)
        apply div_nonneg <;> linarith
      rw [abs_of_nonneg hlo]
      exact hup
    -- reproducing identity along the sequence
    have hrep : ∀ n : ℕ, (u (φ n) ∘ (chartAt ℂ x).symm) z
        = poissonIntegral (u (φ n) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z := by
      intro n
      have h1 := (hread n).circleAverage_poissonKernel_smul hz
      rw [← h1, poissonIntegral]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    -- convergence of the Poisson integrals
    have hlimPI : Tendsto
        (fun n ↦ poissonIntegral (u (φ n) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z)
        atTop (𝓝 (poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hsphunif := hunif.mono sphere_subset_closedBall
      rw [Metric.tendstoUniformlyOn_iff] at hsphunif
      have hev := hsphunif (ε / (2 * (Kb + 1))) (by positivity)
      rw [Filter.eventually_atTop] at hev
      obtain ⟨N, hN⟩ := hev
      refine ⟨N, fun n hn ↦ ?_⟩
      rw [Real.dist_eq]
      have hbd : ∀ ζ ∈ sphere (chartAt ℂ x x) ρ,
          |poissonKernel (chartAt ℂ x x) z ζ * (u (φ n) ∘ (chartAt ℂ x).symm) ζ
            - poissonKernel (chartAt ℂ x x) z ζ * (G ∘ (chartAt ℂ x).symm) ζ|
            ≤ Kb * (ε / (2 * (Kb + 1))) := by
        intro ζ hζ
        have h1 : |poissonKernel (chartAt ℂ x x) z ζ * (u (φ n) ∘ (chartAt ℂ x).symm) ζ
            - poissonKernel (chartAt ℂ x x) z ζ * (G ∘ (chartAt ℂ x).symm) ζ|
            = |poissonKernel (chartAt ℂ x x) z ζ|
              * |(u (φ n) ∘ (chartAt ℂ x).symm) ζ - (G ∘ (chartAt ℂ x).symm) ζ| := by
          rw [← mul_sub, abs_mul]
        rw [h1]
        have h2 : |(u (φ n) ∘ (chartAt ℂ x).symm) ζ - (G ∘ (chartAt ℂ x).symm) ζ|
            ≤ ε / (2 * (Kb + 1)) := by
          have h3 := hN n hn ζ hζ
          rw [Real.dist_eq, abs_sub_comm] at h3
          exact h3.le
        exact mul_le_mul (hKbound ζ hζ) h2 (abs_nonneg _) hKb0
      have hcF : ContinuousOn
          (fun ζ ↦ poissonKernel (chartAt ℂ x x) z ζ * (u (φ n) ∘ (chartAt ℂ x).symm) ζ)
          (sphere (chartAt ℂ x x) ρ) :=
        (hKcont _ z ρ hz).mul ((hcont_n n).mono sphere_subset_closedBall)
      have hcG : ContinuousOn
          (fun ζ ↦ poissonKernel (chartAt ℂ x x) z ζ * (G ∘ (chartAt ℂ x).symm) ζ)
          (sphere (chartAt ℂ x x) ρ) :=
        (hKcont _ z ρ hz).mul (hGcont.mono sphere_subset_closedBall)
      have hkey := havg_diff _ _ (chartAt ℂ x x) ρ (Kb * (ε / (2 * (Kb + 1)))) hρ hcF hcG hbd
      have hfin : Kb * (ε / (2 * (Kb + 1))) < ε := by
        rw [div_eq_mul_inv]
        have h4 : Kb * (ε * (2 * (Kb + 1))⁻¹) ≤ (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h5 : (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) = ε / 2 := by
          field_simp
        rw [h5] at h4
        linarith
      exact lt_of_le_of_lt hkey hfin
    -- limits agree
    have hGz : Tendsto
        (fun n ↦ poissonIntegral (u (φ n) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z)
        atTop (𝓝 ((G ∘ (chartAt ℂ x).symm) z)) := by
      have h1 := hunif.tendsto_at (ball_subset_closedBall hz)
      exact h1.congr hrep
    exact tendsto_nhds_unique hGz hlimPI
  -- the Poisson integral of the limit data is harmonic on the ball
  have hPharm : HarmonicOnNhd
      (poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ)
      (ball (chartAt ℂ x x) ρ) :=
    poissonIntegral_harmonicOn _ _ hρ (hGcont.mono sphere_subset_closedBall)
  have hcball : chartAt ℂ x x ∈ ball (chartAt ℂ x x) ρ := mem_ball_self hρ
  have hev : (G ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝 (chartAt ℂ x x)] poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ
          :=
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hcball) hPI
  exact (harmonicAt_congr_nhds hev).mpr (hPharm _ hcball)

end RiemannDynamics
