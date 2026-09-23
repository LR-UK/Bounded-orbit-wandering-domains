/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.SurfaceHarmonic
import RiemannDynamics.Uniformization.HolomorphicEquiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The Green envelope and the surface toolkit

The Perron family and envelope of a pole on a Riemann surface, the
`HasGreenFunction` dichotomy predicate, and the surface toolkit: connectivity
of punctured surfaces, the subharmonic puncture bound, and openness of
nonconstant holomorphic maps.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- The local coordinate at `p₀`, translated to vanish at `p₀`. -/
noncomputable def poleCoord (p₀ : M) (x : M) : ℂ :=
  chartAt ℂ p₀ x - chartAt ℂ p₀ p₀

/-- The Green's-function Perron family at `p₀`: continuous subharmonic
functions on the punctured surface, vanishing off a compact set, with
logarithmic pole growth at `p₀`. -/
def greenFamily (p₀ : M) : Set (M → ℝ) :=
  {v | MSubharmonicOn v {p₀}ᶜ ∧ ContinuousOn v {p₀}ᶜ ∧
    (∃ K : Set M, IsCompact K ∧ K ≠ Set.univ ∧ ∀ x ∉ K, v x = 0) ∧
    ∃ C, ∀ᶠ x in 𝓝[≠] p₀, v x + Real.log ‖poleCoord p₀ x‖ ≤ C}

/-- The upper envelope of the Green's-function Perron family. -/
noncomputable def greenEnvelope (p₀ : M) (x : M) : ℝ :=
  sSup ((fun v => v x) '' greenFamily p₀)

/-- The surface is hyperbolic at `p₀`: the Perron family is bounded above at
some point distinct from the pole. -/
def HasGreenFunction (p₀ : M) : Prop :=
  ∃ x, x ≠ p₀ ∧ BddAbove ((fun v => v x) '' greenFamily p₀)

/-! ## Surface toolkit -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- A connected surface with a point removed stays connected. -/
theorem isConnected_compl_singleton_of_connected [ConnectedSpace M]
    (hnt : ∃ x y : M, x ≠ y) (p₀ : M) : IsConnected ({p₀}ᶜ : Set M) := by
  have : T1Space M := ChartedSpace.t1Space ℂ M
  have hopen : IsOpen ({p₀}ᶜ : Set M) := isOpen_compl_singleton
  -- Nonemptiness of the punctured surface.
  obtain ⟨x, y, hxy⟩ := hnt
  have hne : ({p₀}ᶜ : Set M).Nonempty := by
    rcases eq_or_ne x p₀ with rfl | hx
    · exact ⟨y, Set.mem_compl_singleton_iff.2 hxy.symm⟩
    · exact ⟨x, Set.mem_compl_singleton_iff.2 hx⟩
  -- A punctured ball in `ℂ` is connected, via polar coordinates.
  have hpunc : ∀ (c : ℂ) (r : ℝ), 0 < r → IsConnected (ball c r \ {c}) := by
    intro c r hr
    have hcont : Continuous fun p : ℝ × ℝ =>
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo 0 r ×ˢ (Set.univ : Set ℝ)) = ball c r \ {c} := by
      apply Set.Subset.antisymm
      · rintro w ⟨⟨t, θ⟩, ⟨⟨ht0, htr⟩, -⟩, hw⟩
        rw [← hw]
        change c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball c r \ {c}
        have hd : dist (c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) c = t := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, hd]; exact htr
        · intro h
          rw [Set.mem_singleton_iff] at h
          rw [h, dist_self] at hd
          exact ht0.ne hd
      · rintro w ⟨hwb, hwc⟩
        rw [Set.mem_singleton_iff] at hwc
        have ht0 : 0 < ‖w - c‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hwc)
        have htr : ‖w - c‖ < r := by rw [← dist_eq_norm]; exact mem_ball.1 hwb
        refine ⟨(‖w - c‖, (w - c).arg), ⟨⟨ht0, htr⟩, Set.mem_univ _⟩, ?_⟩
        change c + (‖w - c‖ : ℂ) * Complex.exp (((w - c).arg : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    rw [← himg]
    refine ⟨Set.Nonempty.image _
      ⟨(r / 2, 0), ⟨half_pos hr, half_lt_self hr⟩, Set.mem_univ _⟩, ?_⟩
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn
  -- The punctured chart neighborhood of `p₀`.
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he
  have hp₀src : p₀ ∈ e.source := by rw [he]; exact mem_chart_source ℂ p₀
  have hctgt : e p₀ ∈ e.target := by rw [he]; exact mem_chart_target ℂ p₀
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.1 e.open_target (e p₀) hctgt
  set N : Set M := e.source ∩ e ⁻¹' ball (e p₀) r
  have hNopen : IsOpen N := e.isOpen_inter_preimage isOpen_ball
  have hp₀N : p₀ ∈ N := ⟨hp₀src, by rw [Set.mem_preimage]; exact mem_ball_self hr0⟩
  have himg : (e.symm : ℂ → M) '' (ball (e p₀) r \ {e p₀}) = N \ {p₀} := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, ⟨hwb, hwc⟩, hwz⟩
      have hwt : w ∈ e.target := hball hwb
      rw [← hwz]
      refine ⟨⟨e.map_target hwt, ?_⟩, ?_⟩
      · rw [Set.mem_preimage, e.right_inv hwt]; exact hwb
      · intro h
        rw [Set.mem_singleton_iff] at h
        exact hwc (by rw [Set.mem_singleton_iff, ← e.right_inv hwt, h])
    · rintro z ⟨⟨hzsrc, hzb⟩, hzp⟩
      refine ⟨e z, ⟨hzb, ?_⟩, e.left_inv hzsrc⟩
      intro h
      rw [Set.mem_singleton_iff] at h
      exact hzp (Set.mem_singleton_iff.2 (e.injOn hzsrc hp₀src h))
  have hN' : IsConnected (N \ {p₀}) := by
    rw [← himg]
    exact (hpunc (e p₀) r hr0).image _
      (e.continuousOn_symm.mono fun w hw => hball hw.1)
  have hsub' : N \ {p₀} ⊆ ({p₀}ᶜ : Set M) := fun z hz => hz.2
  -- Assemble preconnectedness of the punctured surface.
  refine ⟨hne, ?_⟩
  intro u v hu hv huv hsu hsv
  -- One-sided separation lemma: if the punctured chart neighborhood lies in `u'`,
  -- the separation `u', v'` of the punctured surface extends to a separation of `M`.
  have key : ∀ u' v' : Set M, IsOpen u' → IsOpen v' → ({p₀}ᶜ : Set M) ⊆ u' ∪ v' →
      (({p₀}ᶜ : Set M) ∩ v').Nonempty → N \ {p₀} ⊆ u' →
      (({p₀}ᶜ : Set M) ∩ (u' ∩ v')).Nonempty := by
    intro u' v' hu' hv' hcov hv'ne hNu'
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hU : IsOpen (u' ∪ N) := hu'.union hNopen
    have hV : IsOpen (v' ∩ ({p₀}ᶜ : Set M)) := hv'.inter hopen
    have hcover : (Set.univ : Set M) ⊆ (u' ∪ N) ∪ v' ∩ {p₀}ᶜ := by
      intro z _
      rcases eq_or_ne z p₀ with rfl | hz
      · exact Or.inl (Or.inr hp₀N)
      · rcases hcov (Set.mem_compl_singleton_iff.2 hz) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, Set.mem_compl_singleton_iff.2 hz⟩
    obtain ⟨w, hw1, hw2⟩ := hv'ne
    obtain ⟨z, -, hz⟩ := isPreconnected_univ (u' ∪ N) (v' ∩ {p₀}ᶜ) hU hV hcover
      ⟨p₀, Set.mem_univ p₀, Or.inr hp₀N⟩ ⟨w, Set.mem_univ w, hw2, hw1⟩
    obtain ⟨hz1, hzv, hzp⟩ := hz
    have hzu : z ∈ u' := by
      rcases hz1 with h | h
      · exact h
      · exact hNu' ⟨h, Set.mem_compl_singleton_iff.1 hzp⟩
    have : z ∈ ({p₀}ᶜ : Set M) ∩ (u' ∩ v') := ⟨hzp, hzu, hzv⟩
    rw [hcon] at this
    exact this
  -- Case split on which side of the separation the punctured chart ball lies.
  rcases Set.eq_empty_or_nonempty ((N \ {p₀}) ∩ v) with hv0 | hv1
  · have hNu : N \ {p₀} ⊆ u := by
      intro z hz
      rcases huv (hsub' hz) with h | h
      · exact h
      · exact absurd hv0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
    exact key u v hu hv huv hsv hNu
  · rcases Set.eq_empty_or_nonempty ((N \ {p₀}) ∩ u) with hu0 | hu1
    · have hNv : N \ {p₀} ⊆ v := by
        intro z hz
        rcases huv (hsub' hz) with h | h
        · exact absurd hu0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
        · exact h
      have h := key v u hv hu (by rw [Set.union_comm]; exact huv) hsu hNv
      rwa [Set.inter_comm v u] at h
    · obtain ⟨z, hzN, hzuv⟩ := hN'.2 u v hu hv (fun z hz => huv (hsub' hz)) hu1 hv1
      exact ⟨z, hsub' hzN, hzuv⟩

/-- **Puncture-tolerant maximum principle**: a subharmonic function on the
punctured surface that vanishes off a compact set and has at most logarithmic
pole growth is nonpositive. -/
theorem msubharmonic_le_zero_of_puncture [ConnectedSpace M]
    [NoncompactSpace M] [T2Space M] {p₀ : M} {v : M → ℝ}
    (hv : MSubharmonicOn v {p₀}ᶜ)
    (hsupp : ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, v x ≤ 0)
    (hpole : ∃ C, ∀ᶠ x in 𝓝[≠] p₀, v x ≤ C) :
    ∀ x ≠ p₀, v x ≤ 0 := by
  classical
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  obtain ⟨K, hK, hKv⟩ := hsupp
  obtain ⟨C, hC⟩ := hpole
  -- The surface has at least two points, else it would be compact.
  have hnt : ∃ x y : M, x ≠ y := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton M := ⟨fun a b => hcon a b⟩
    have : CompactSpace M := Finite.compactSpace
    exact NoncompactSpace.noncompact_univ (X := M) isCompact_univ
  have hconn : IsConnected ({p₀}ᶜ : Set M) :=
    isConnected_compl_singleton_of_connected hnt p₀
  -- Continuity of `v` off the pole.
  have hvcont : ∀ y : M, y ≠ p₀ → ContinuousAt v y :=
    fun y hy => (hv y (Set.mem_compl_singleton_iff.mpr hy)).continuousAt
  -- A far point outside `K ∪ {p₀}`.
  have hfar : ∃ y₀ : M, y₀ ∉ K ∪ {p₀} := by
    by_contra hcon
    push Not at hcon
    have huniv : K ∪ {p₀} = Set.univ := Set.eq_univ_of_forall hcon
    have hcomp : IsCompact (K ∪ {p₀} : Set M) := hK.union isCompact_singleton
    rw [huniv] at hcomp
    exact NoncompactSpace.noncompact_univ (X := M) hcomp
  /- ## Constancy propagation on a preconnected open set from an interior
  maximum (clopen argument). -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ x ∈ Ω, w x ≤ w xm) → ∀ x ∈ Ω, w x = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {x | x ∈ Ω ∧ w x = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hmax' : ∀ y ∈ Ω, w y ≤ w x := fun y hy => (hmax y hy).trans_eq hxw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hxΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy.trans hxw⟩
    have hto : IsOpen {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hcont : ContinuousAt w x := (hwsub x hxΩ).continuousAt
      filter_upwards [hcont.eventually_ne hxw, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy⟩
    have hsub : Ω ⊆ {x | x ∈ Ω ∧ w x = w xm} ∪ {x | x ∈ Ω ∧ w x ≠ w xm} := by
      intro x hx
      by_cases hxw : w x = w xm
      · exact Or.inl ⟨hx, hxw⟩
      · exact Or.inr ⟨hx, hxw⟩
    have hdisj : Disjoint {x | x ∈ Ω ∧ w x = w xm} {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro x ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun x hx => (hres hx).2
  /- ## Maximum principle on an open set `Ω ≠ univ`: a subharmonic function
  bounded by `m` off a compact set and bounded by `m` (with continuity) at
  every point of `closure Ω \ Ω` is bounded by `m` on `Ω`. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ x ∈ Ω, x ∉ Kc → w x ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ x ∈ Ω, w x ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ x ∈ Ω, w x ≤ w xm := by
      intro x hx
      by_cases hxK : x ∈ Kc
      · exact hxmax ⟨subset_closure hx, hxK⟩
      · exact (hout x hx hxK).trans hTgt.le
    -- Propagate the max through the connected component of `xm`.
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun x hx => hwsub x (hCcΩ hx)) (fun x hx => hall x (hCcΩ hx))
    -- The component has a boundary point (else it would be all of `M`).
    have hfrne : (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    -- The boundary point is outside `Ω` (components of open sets are open).
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    -- Continuity forces the maximal value at the boundary point: contradiction.
    have hne : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## Chart geometry at the pole. -/
  set e := chartAt ℂ p₀ with he
  have hp₀s : p₀ ∈ e.source := mem_chart_source ℂ p₀
  set z₀ := e p₀ with hz₀
  have hz₀t : z₀ ∈ e.target := by rw [hz₀]; exact e.map_source hp₀s
  have hsymz₀ : e.symm z₀ = p₀ := by rw [hz₀]; exact e.left_inv hp₀s
  -- Images under `e.symm` of subsets of the target, in preimage form.
  have himg : ∀ s : Set ℂ, s ⊆ e.target → e.symm '' s = e.source ∩ e ⁻¹' s := by
    intro s hs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e.map_target (hs hz), ?_⟩
      rw [Set.mem_preimage, e.right_inv (hs hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨e y, hy2, e.left_inv hy⟩
  -- A radius `r` on which the pole bound `v ≤ C` is valid.
  obtain ⟨N, hNnhds, hN⟩ := (eventually_nhdsWithin_iff.mp hC).exists_mem
  have hpre : e.target ∩ e.symm ⁻¹' N ∈ 𝓝 z₀ := by
    have h1 : ContinuousAt e.symm z₀ := e.continuousAt_symm hz₀t
    have h3 : e.symm ⁻¹' N ∈ 𝓝 z₀ := h1.preimage_mem_nhds (hsymz₀ ▸ hNnhds)
    exact Filter.inter_mem (e.open_target.mem_nhds hz₀t) h3
  obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall.mem_iff).1 hpre
  have hrt : closedBall z₀ r ⊆ e.target := fun z hz => (hrsub hz).1
  -- Detecting the pole through the chart.
  have hpid : ∀ y, y ∈ e.source → e y = z₀ → y = p₀ := by
    intro y hys hyz
    rw [← e.left_inv hys, hyz]
    exact hsymz₀
  have hnep : ∀ y, y ∈ e.source → e y ≠ z₀ → y ≠ p₀ := by
    intro y hys hyne hcon
    rw [hcon] at hyne
    exact hyne hz₀.symm
  -- The pole bound, read on the surface.
  have hCbound : ∀ y, y ∈ e.source → e y ∈ closedBall z₀ r → y ≠ p₀ → v y ≤
      C := by
    intro y hys hyball hyne
    have h3 : e y ∈ e.symm ⁻¹' N := (hrsub hyball).2
    have h4 : y ∈ N := by rwa [Set.mem_preimage, e.left_inv hys] at h3
    exact hN y h4 (Set.mem_compl_singleton_iff.mpr hyne)
  /- ## The circle `Γ` and its maximum `m₁`. -/
  set Γ : Set M := e.symm '' (sphere z₀ r) with hΓdef
  have hΓcomp : IsCompact Γ := (isCompact_sphere z₀ r).image_of_continuousOn
    (e.continuousOn_symm.mono (sphere_subset_closedBall.trans hrt))
  have hΓne : Γ.Nonempty := (NormedSpace.sphere_nonempty.2 hr.le).image _
  have hΓmem : ∀ y, y ∈ e.source → dist (e y) z₀ = r → y ∈ Γ := by
    intro y hys hyd
    exact ⟨e y, by rwa [mem_sphere], e.left_inv hys⟩
  have hΓp₀ : Γ ⊆ {p₀}ᶜ := by
    rintro q ⟨z, hz, rfl⟩
    rw [mem_sphere] at hz
    have hzt : z ∈ e.target := hrt (sphere_subset_closedBall (by rwa [mem_sphere]))
    have hzne : z ≠ z₀ := by
      intro hcon
      rw [hcon, dist_self] at hz
      exact hr.ne hz
    rw [Set.mem_compl_singleton_iff]
    intro hcon
    apply hzne
    have h5 := e.right_inv hzt
    rw [hcon] at h5
    rw [hz₀]
    exact h5.symm
  have hΓcont : ContinuousOn v Γ :=
    fun q hq => (hvcont q (Set.mem_compl_singleton_iff.1 (hΓp₀ hq))).continuousWithinAt
  obtain ⟨xΓ, hxΓ, hxΓmax⟩ := hΓcomp.exists_isMaxOn hΓne hΓcont
  set m₁ : ℝ := max (v xΓ) 0 with hm₁
  have hm₁0 : (0 : ℝ) ≤ m₁ := le_max_right _ _
  have hΓle : ∀ y ∈ Γ, v y ≤ m₁ := fun y hy => (hxΓmax hy).trans (le_max_left _ _)
  /- ## The closed coordinate disk `D` and the outer estimate. -/
  set D : Set M := e.symm '' (closedBall z₀ r) with hDdef
  have hDcomp : IsCompact D := (isCompact_closedBall z₀ r).image_of_continuousOn
    (e.continuousOn_symm.mono hrt)
  have hDcl : IsClosed D := hDcomp.isClosed
  have hp₀D : p₀ ∈ D := by
    rw [hDdef, himg _ hrt]
    refine ⟨hp₀s, ?_⟩
    rw [Set.mem_preimage, ← hz₀]
    exact mem_closedBall_self hr.le
  -- Maximum principle outside the disk.
  have houterAll : ∀ x ∈ (Dᶜ : Set M), v x ≤ m₁ := by
    refine maxPrin Dᶜ v m₁ K hDcl.isOpen_compl ?_ ?_ hK ?_ ?_
    · intro hcon
      have h5 : p₀ ∈ (Dᶜ : Set M) := by rw [hcon]; trivial
      exact h5 hp₀D
    · exact fun q hq =>
        hv q (Set.mem_compl_singleton_iff.mpr (fun hcon => hq (hcon ▸ hp₀D)))
    · exact fun q _ hqK => (hKv q hqK).trans hm₁0
    · rintro y ⟨hycl, hyc⟩
      have hyD : y ∈ D := not_not.1 hyc
      rw [hDdef, himg _ hrt] at hyD
      obtain ⟨hysrc, hyball⟩ := hyD
      have hynb : e y ∉ ball z₀ r := by
        intro hcon
        have hBopen : IsOpen (e.source ∩ e ⁻¹' ball z₀ r) :=
          e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
        have hBsubD : e.source ∩ e ⁻¹' ball z₀ r ⊆ D := by
          rw [hDdef, himg _ hrt]
          exact Set.inter_subset_inter (subset_refl _)
            (Set.preimage_mono ball_subset_closedBall)
        have hyint : y ∈ interior D := interior_maximal hBsubD hBopen ⟨hysrc, hcon⟩
        rw [closure_compl] at hycl
        exact hycl hyint
      have hyr : dist (e y) z₀ = r := by
        rw [mem_ball] at hynb
        rw [Set.mem_preimage, mem_closedBall] at hyball
        exact le_antisymm hyball (not_lt.1 hynb)
      have hyneza : e y ≠ z₀ := by
        intro hcon
        rw [hcon, dist_self] at hyr
        exact hr.ne hyr
      have hynep : y ≠ p₀ := hnep y hysrc hyneza
      exact ⟨hvcont y hynep, hΓle y (hΓmem y hysrc hyr)⟩
  /- ## Harmonicity of the logarithmic barrier through the chart. -/
  have hbharm : ∀ y, y ∈ e.source → e y ≠ z₀ →
      MHarmonicAt (fun q => Real.log (dist (e q) z₀)) y := by
    intro y hys hyne
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p₀) hys]
    have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - z₀‖) (e y) := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - z₀)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hyne
    have heqv : (fun w : ℂ => Real.log ‖w - z₀‖) =ᶠ[𝓝 (e y)]
        ((fun q => Real.log (dist (e q) z₀)) ∘ ⇑e.symm) := by
      filter_upwards [e.open_target.mem_nhds (e.map_source hys)] with w hw
      simp only [Function.comp_apply, e.right_inv hw, dist_eq_norm]
    exact (harmonicAt_congr_nhds heqv).1 hharm
  have hbcont : ∀ y, y ∈ e.source → e y ≠ z₀ →
      ContinuousAt (fun q => Real.log (dist (e q) z₀)) y := by
    intro y hys hyne
    have h2 : ContinuousAt e y := e.continuousAt hys
    have h3 : dist (e y) z₀ ≠ 0 := (dist_pos.2 hyne).ne'
    have h4 : ContinuousAt (fun q : M => dist (e q) z₀) y := h2.dist continuousAt_const
    exact h4.log h3
  -- Affine images of `MHarmonicAt` functions are `MHarmonicAt`.
  have mharm_affine : ∀ (g : M → ℝ) (x : M) (a c : ℝ), MHarmonicAt g x →
      MHarmonicAt (fun y => a * g y + c) x := by
    intro g x a c hg
    have h1 : HarmonicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hg
    have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
    have heq2 : (a • (g ∘ (chartAt ℂ x).symm) + fun _ => c) =
        (fun y => a * g y + c) ∘ (chartAt ℂ x).symm := by
      funext w
      simp [smul_eq_mul]
    rw [heq2] at h2
    exact h2
  /- ## Inner estimate: the `ε·log` barrier on the punctured disk. -/
  have hinner : ∀ x ∈ D, x ≠ p₀ → v x ≤ m₁ := by
    intro x hxD hxp
    rw [hDdef, himg _ hrt] at hxD
    obtain ⟨hxsrc, hxball⟩ := hxD
    rw [Set.mem_preimage, mem_closedBall] at hxball
    have hxz : e x ≠ z₀ := fun hcon => hxp (hpid x hxsrc hcon)
    have hdx0 : 0 < dist (e x) z₀ := dist_pos.2 hxz
    rcases eq_or_lt_of_le hxball with heqr | hdxlt
    · exact hΓle x (hΓmem x hxsrc heqr)
    -- Strict interior: show `v x ≤ m₁ + δ` for every `δ > 0`.
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    set L : ℝ := Real.log r - Real.log (dist (e x) z₀) with hLdef
    have hL0 : 0 < L := sub_pos.2 (Real.log_lt_log hdx0 hdxlt)
    set ε : ℝ := δ / L with hεdef
    have hε0 : 0 < ε := div_pos hδ hL0
    have hεL : ε * L = δ := by
      rw [hεdef]
      exact div_mul_cancel₀ δ hL0.ne'
    -- Excision radius `σ`, small enough for the barrier to beat `C`.
    set Q : ℝ := (m₁ - C) / ε + Real.log r with hQdef
    set σ : ℝ := min (dist (e x) z₀ / 2) (Real.exp Q) with hσdef
    have hσ0 : 0 < σ := lt_min (half_pos hdx0) (Real.exp_pos Q)
    have hσdx : σ < dist (e x) z₀ :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hdx0)
    have hσr : σ < r := hσdx.trans hdxlt
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) := Real.log_le_log hσ0 (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hbarrier : C + ε * (Real.log σ - Real.log r) ≤ m₁ := by
      have h5 : ε * (Real.log σ - Real.log r) ≤ ε * ((m₁ - C) / ε) := by
        apply mul_le_mul_of_nonneg_left _ hε0.le
        rw [hQdef] at hσQ
        linarith
      have h6 : ε * ((m₁ - C) / ε) = m₁ - C := by field_simp
      linarith
    -- The annulus and the barriered competitor.
    set O : Set ℂ := ball z₀ r \ closedBall z₀ σ with hOdef
    have hOopen : IsOpen O := isOpen_ball.sdiff isClosed_closedBall
    have hOsub : O ⊆ e.target := fun z hz => hrt (ball_subset_closedBall hz.1)
    set A : Set M := e.symm '' O with hAdef
    have hAopen : IsOpen A := by
      rw [hAdef, himg _ hOsub]
      exact e.continuousOn.isOpen_inter_preimage e.open_source hOopen
    have hAD : A ⊆ D := by
      rw [hAdef, hDdef, himg _ hOsub, himg _ hrt]
      exact Set.inter_subset_inter (subset_refl _)
        (Set.preimage_mono (Set.sdiff_subset.trans ball_subset_closedBall))
    have hp₀clA : p₀ ∉ closure A := by
      intro hcon
      have hU : IsOpen (e.source ∩ e ⁻¹' ball z₀ σ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hp₀U : p₀ ∈ e.source ∩ e ⁻¹' ball z₀ σ := by
        refine ⟨hp₀s, ?_⟩
        rw [Set.mem_preimage, ← hz₀]
        exact mem_ball_self hσ0
      obtain ⟨q, hq1, hq2⟩ := mem_closure_iff.1 hcon _ hU hp₀U
      rw [hAdef, himg _ hOsub] at hq2
      exact hq2.2.2 (ball_subset_closedBall hq1.2)
    have hAne : A ≠ Set.univ := by
      intro hcon
      apply hp₀clA
      apply subset_closure
      rw [hcon]
      trivial
    set W : M → ℝ := fun q => v q + ε * (Real.log (dist (e q) z₀) - Real.log r) with hW
    have hWsub : MSubharmonicOn W A := by
      intro q hqA
      rw [hAdef, himg _ hOsub] at hqA
      obtain ⟨hqs, hqO⟩ := hqA
      have hqz : e q ≠ z₀ := by
        intro hcon
        apply hqO.2
        rw [hcon, mem_closedBall, dist_self]
        exact hσ0.le
      have hqp : q ∈ ({p₀}ᶜ : Set M) :=
        Set.mem_compl_singleton_iff.mpr (hnep q hqs hqz)
      have hu : MHarmonicAt
          (fun y => (-ε) * Real.log (dist (e y) z₀) + ε * Real.log r) q :=
        mharm_affine _ q _ _ (hbharm q hqs hqz)
      have h7 := (hv q hqp).sub_mharmonicAt hu
      convert h7 using 2
      simp only [hW]
      ring
    have hWfr : ∀ y ∈ closure A \ A, ContinuousAt W y ∧ W y ≤ m₁ := by
      rintro y ⟨hycl, hyA⟩
      have hyD : y ∈ D := closure_minimal hAD hDcl hycl
      rw [hDdef, himg _ hrt] at hyD
      obtain ⟨hysrc, hyball⟩ := hyD
      rw [Set.mem_preimage, mem_closedBall] at hyball
      have hyneza : e y ≠ z₀ := by
        intro hcon
        exact hp₀clA (hpid y hysrc hcon ▸ hycl)
      have hynep : y ≠ p₀ := hnep y hysrc hyneza
      have hy0 : 0 < dist (e y) z₀ := dist_pos.2 hyneza
      have hWcont : ContinuousAt W y := by
        rw [hW]
        exact (hvcont y hynep).add
          (continuousAt_const.mul ((hbcont y hysrc hyneza).sub continuousAt_const))
      have hyO : e y ∉ O := by
        intro hcon
        apply hyA
        rw [hAdef, himg _ hOsub]
        exact ⟨hysrc, hcon⟩
      refine ⟨hWcont, ?_⟩
      by_cases hyb : e y ∈ ball z₀ r
      · -- Inner circle: the barrier beats the pole bound `C`.
        have hyσ : dist (e y) z₀ ≤ σ := by
          have h8 : e y ∈ closedBall z₀ σ := by
            by_contra h9
            exact hyO ⟨hyb, h9⟩
          rwa [mem_closedBall] at h8
        have hvy : v y ≤ C := hCbound y hysrc (by rwa [mem_closedBall]) hynep
        have hlogy : Real.log (dist (e y) z₀) ≤ Real.log σ := Real.log_le_log hy0 hyσ
        have h10 : ε * (Real.log (dist (e y) z₀) - Real.log r) ≤
            ε * (Real.log σ - Real.log r) := by
          apply mul_le_mul_of_nonneg_left _ hε0.le
          linarith
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log r) ≤ m₁
        linarith
      · -- Outer circle: the barrier vanishes and `Γ` bounds `v`.
        have hyr : dist (e y) z₀ = r := by
          rw [mem_ball] at hyb
          exact le_antisymm hyball (not_lt.1 hyb)
        have hvy : v y ≤ m₁ := hΓle y (hΓmem y hysrc hyr)
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log r) ≤ m₁
        rw [hyr, sub_self, mul_zero, add_zero]
        exact hvy
    have hAx : x ∈ A := by
      rw [hAdef, himg _ hOsub]
      refine ⟨hxsrc, ?_⟩
      rw [Set.mem_preimage]
      refine ⟨by rwa [mem_ball], ?_⟩
      rw [mem_closedBall]
      exact fun hcon => (not_le.mpr hσdx) hcon
    have hWx := maxPrin A W m₁ D hAopen hAne hWsub hDcomp
      (fun q hq hqD => absurd (hAD hq) hqD) hWfr x hAx
    have hWxval : v x + ε * (Real.log (dist (e x) z₀) - Real.log r) ≤ m₁ := hWx
    have hflip : ε * (Real.log (dist (e x) z₀) - Real.log r) = -(ε * L) := by
      rw [hLdef]
      ring
    rw [hflip, hεL] at hWxval
    linarith
  /- ## Global bound and conclusion. -/
  have hglobal : ∀ x, x ≠ p₀ → v x ≤ m₁ := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact hinner x hxD hx
    · exact houterAll x hxD
  intro x hx
  rcases le_or_gt (v xΓ) 0 with hcase | hcase
  · have h11 : m₁ = 0 := max_eq_right hcase
    have := hglobal x hx
    rwa [h11] at this
  · -- A positive interior max propagates to the far point: contradiction.
    exfalso
    have hm₁Γ : m₁ = v xΓ := max_eq_left hcase.le
    have hmax : ∀ q ∈ ({p₀}ᶜ : Set M), v q ≤ v xΓ := by
      intro q hq
      have h12 := hglobal q (Set.mem_compl_singleton_iff.1 hq)
      rwa [hm₁Γ] at h12
    have hconst := propagate {p₀}ᶜ v xΓ isOpen_compl_singleton
      hconn.isPreconnected (hΓp₀ hxΓ) hv hmax
    obtain ⟨y₀, hy₀⟩ := hfar
    have hy₀K : y₀ ∉ K := fun h => hy₀ (Or.inl h)
    have hy₀p : y₀ ∈ ({p₀}ᶜ : Set M) := fun h => hy₀ (Or.inr h)
    have h13 : v y₀ ≤ 0 := hKv y₀ hy₀K
    have h14 : v y₀ = v xΓ := hconst y₀ hy₀p
    linarith

/-- A nonconstant holomorphic function on a connected surface is an open
map. -/
theorem isOpenMap_of_contMDiff_of_not_const [ConnectedSpace M] {f : M → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnc : ¬ ∃ c, ∀ x, f x = c) :
    IsOpenMap f := by
  -- The chart reading of `f` is analytic at every point of the chart target.
  have hread : ∀ x : M, ∀ z ∈ (chartAt ℂ x).target,
      AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z := by
    intro x z hz
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm z :=
      (contMDiffOn_chart_symm (x := x)).contMDiffAt
        ((chartAt ℂ x).open_target.mem_nhds hz)
    exact (contMDiffAt_iff_contDiffAt.mp
      (ContMDiffAt.comp z hf.contMDiffAt hsymm)).analyticAt
  -- `f` agrees with its chart reading near every point.
  have hloc : ∀ x : M, f =ᶠ[𝓝 x] (f ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x) := by
    intro x
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]
  have hfix : ∀ x : M, (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = f x := by
    intro x
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hmap : ∀ x : M,
      map f (𝓝 x) = map (f ∘ (chartAt ℂ x).symm) (𝓝 (chartAt ℂ x x)) := by
    intro x
    rw [Filter.map_congr (hloc x), ← Filter.map_map,
      (chartAt ℂ x).map_nhds_eq (mem_chart_source ℂ x)]
  -- The set where `f` is locally constant is open.
  have hSopen : IsOpen {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : ∀ᶠ y in 𝓝 x, f y = f x := hx
    filter_upwards [eventually_eventually_nhds.mpr hx', hx'] with y hy hyx
    exact hy.mono fun z hz => hz.trans hyx.symm
  -- ... and closed, by the identity theorem on a chart ball.
  have hSclosed : IsClosed {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
    refine isClosed_of_closure_subset fun x hx => ?_
    obtain ⟨r, hr, hball⟩ :=
      Metric.isOpen_iff.mp (chartAt ℂ x).open_target _ (mem_chart_target ℂ x)
    have hVopen :
        IsOpen ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) r) :=
      (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source isOpen_ball
    have hxV : x ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) r :=
      ⟨mem_chart_source ℂ x, mem_ball_self hr⟩
    obtain ⟨y, hyV, hyS⟩ := _root_.mem_closure_iff.mp hx _ hVopen hxV
    -- the reading is eventually the constant `f y` near `chartAt ℂ x y`
    have hcst : (f ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x y)] fun _ => f y := by
      have h1 : ∀ᶠ w in map (chartAt ℂ x).symm (𝓝 (chartAt ℂ x y)), f w = f y := by
        rw [(chartAt ℂ x).symm_map_nhds_eq hyV.1]
        exact hyS
      exact eventually_map.mp h1
    have hgB : AnalyticOnNhd ℂ (f ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) r) :=
      fun z hz => hread x z (hball hz)
    have heq :
        Set.EqOn (f ∘ (chartAt ℂ x).symm) (fun _ => f y) (ball (chartAt ℂ x x) r) :=
      hgB.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (convex_ball ((chartAt ℂ x) x) r).isPreconnected hyV.2 hcst
    have hconstV :
        ∀ w ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) r,
          f w = f y := by
      intro w hw
      have h1 := heq hw.2
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv hw.1] at h1
      exact h1
    have hfxy : f x = f y := hconstV x hxV
    filter_upwards [hVopen.mem_nhds hxV] with w hw
    rw [hconstV w hw, hfxy]
  rcases isClopen_iff.mp ⟨hSclosed, hSopen⟩ with hempty | huniv
  · -- no point is locally constant: every point is in the open branch of the dichotomy
    rw [isOpenMap_iff_nhds_le]
    intro x
    rcases (hread x _ (mem_chart_target ℂ x)).eventually_constant_or_nhds_le_map_nhds with
      hcst | hle
    · exfalso
      have hxS : x ∈ {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
        have h1 : ∀ᶠ y in 𝓝 x,
            (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x y)
              = (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
          have h2 := hcst
          rw [← (chartAt ℂ x).map_nhds_eq (mem_chart_source ℂ x)] at h2
          exact eventually_map.mp h2
        filter_upwards [h1, hloc x] with y h1y h2y
        rw [h2y]
        exact h1y.trans (hfix x)
      rw [hempty] at hxS
      exact hxS
    · rw [hmap x, ← hfix x]
      exact hle
  · -- `f` locally constant everywhere on a connected space: contradiction
    exfalso
    have hall : ∀ x : M, ∀ᶠ y in 𝓝 x, f y = f x := by
      intro x
      have hx : x ∈ {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
        rw [huniv]; exact Set.mem_univ x
      exact hx
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_eventually_eq f).mpr hall
    obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
    exact hnc ⟨f x₀, fun y => congrFun (hlc.eq_const x₀) y⟩

end RiemannDynamics
