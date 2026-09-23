/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.Harnack

/-!
# Bipolar Green: the drift bound

The drift bound for the piece Green's functions: two piece Green's functions
with distinct poles, evaluated at a fixed third base point, differ by a
shrink-independent constant. The conditional core
`exists_pieceGreen_drift_bound_core` cancels the cross terms with the
weakest consequence of the classical cross-symmetry of the piece Green's
functions; `exists_pieceGreen_drift_bound` removes the side condition.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

/-- **The drift bound for the piece Green's functions**, conditional form: when at
least one of the two poles has an unbounded Green family at `p₃`, the two piece
Green's functions with poles `p₁` and `p₂`, evaluated at the third point `p₃`,
differ by a shrink-independent constant for all small enough shrink parameters.
`exists_pieceGreen_drift_bound` discharges the hypothesis and states the
unconditional bound. The interior maximum
principle bounds each piece Green's function off a pole ball by its maximum
on the pole circle, the two-constants estimate limits the growth of that
maximum across the chart annulus, and a Harnack chain on a fixed compact
containing the pole circles and `p₃` makes the same-pole two-point
oscillations uniform in the shrink parameter; the symmetry of the Green's
function of the pieces cancels the cross terms. -/
private theorem exists_pieceGreen_drift_bound_core (D₀ : CoordDisk M) {p₁ p₂ p₃ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hp₃ : p₃ ∉ D₀.closedCarrier) (hne : p₁ ≠ p₂) (h₃₁ : p₃ ≠ p₁)
    (h₃₂ : p₃ ≠ p₂) :
    ∃ t₀ C₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧ ∀ t (ht : 0 < t) (ht1 : t ≤ 1), t ≤ t₀ →
      |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
        pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C₀ := by
  classical
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Plane-side helper: transfer of subharmonicity along a pointwise equality. -/
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  /- ## Constancy propagation on a preconnected open set from an interior maximum. -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ z ∈ Ω, w z ≤ w xm) → ∀ z ∈ Ω, w z = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {z | z ∈ Ω ∧ w z = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hmax' : ∀ u ∈ Ω, w u ≤ w z := fun u hu ↦ (hmax u hu).trans_eq hzw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hzΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu.trans hzw⟩
    have hto : IsOpen {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hcont : ContinuousAt w z := (hwsub z hzΩ).continuousAt
      filter_upwards [hcont.eventually_ne hzw, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu⟩
    have hsub : Ω ⊆ {z | z ∈ Ω ∧ w z = w xm} ∪ {z | z ∈ Ω ∧ w z ≠ w xm} := by
      intro z hz
      by_cases hzw : w z = w xm
      · exact Or.inl ⟨hz, hzw⟩
      · exact Or.inr ⟨hz, hzw⟩
    have hdisj : Disjoint {z | z ∈ Ω ∧ w z = w xm} {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro z ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun z hz ↦ (hres hz).2
  /- ## Maximum principle on an open set `Ω ≠ univ` with compact exceptional set. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ z ∈ Ω, z ∉ Kc → w z ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ z ∈ Ω, w z ≤ m := by
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
    have hall : ∀ z ∈ Ω, w z ≤ w xm := by
      intro z hz
      by_cases hzK : z ∈ Kc
      · exact hxmax ⟨subset_closure hz, hzK⟩
      · exact (hout z hz hzK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun z hz ↦ hwsub z (hCcΩ hz)) (fun z hz ↦ hall z (hCcΩ hz))
    have hfrne :
        (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
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
    have hne2 : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ ↦ (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ ↦ harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz ↦ (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz ↦ (hf0 _ ((hρsub hz).2)).symm
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Subharmonicity at a point transfers between the surface and an open piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hnety : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hnety := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hnety]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hnety).target :=
      e'.map_subtype_source hnety hzsrc
    have heqOn : Set.EqOn (⇑e'.symm) (Subtype.val ∘ ⇑(e'.subtypeRestr hnety).symm)
        (e'.subtypeRestr hnety).target := e'.subtypeRestr_symm_eqOn hnety
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hnety).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈ (e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw ↦ (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw ↦ (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hnety).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hnety), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hnety).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to the punctured filter of the surface. -/
  have mapval : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p, hpP⟩ : ↥P)) = 𝓝[≠] p := by
    intro P p hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀eq]; exact hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## Affine images of harmonic functions are harmonic. -/
  have mharmAffine : ∀ (g : M → ℝ) (x : M) (a c : ℝ), MHarmonicAt g x →
      MHarmonicAt (fun y ↦ a * g y + c) x := by
    intro g x a c hg
    have h1 : HarmonicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hg
    have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
    have heq2 : (a • (g ∘ (chartAt ℂ x).symm) + fun _ ↦ c) =
        (fun y ↦ a * g y + c) ∘ (chartAt ℂ x).symm := by
      funext w
      simp [smul_eq_mul]
    rw [heq2] at h2
    exact h2
  /- ## Membership through an inverse chart: closed balls and spheres. -/
  have hmemCB : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      closedBall c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' closedBall c s ↔ z ∈ e.source ∧ dist (e z) c ≤ s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_closedBall.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_closedBall.2 hzd, e.left_inv hzs⟩
  have hmemSph : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      sphere c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' sphere c s ↔ z ∈ e.source ∧ dist (e z) c = s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_sphere.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_sphere.2 hzd, e.left_inv hzs⟩
  /- ## Per-candidate interior bound ([M] (18)): a compactly supported candidate is
  bounded on an open set avoiding the inner pole disk by its inner-circle maximum. -/
  have interiorBd : ∀ (p : M) (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      ∀ (Wo : Set M), IsOpen Wo →
      ∀ (vE : M → ℝ) (KE : Set M) (m : ℝ), 0 ≤ m →
        MSubharmonicOn vE {p}ᶜ → ContinuousOn vE {p}ᶜ → IsCompact KE → KE ⊆ Wo →
        (∀ y, y ∉ KE → vE y = 0) →
        (∀ z ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (rr / 2), vE z ≤ m) →
        ∀ y ∈ Wo ∩ ((chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (rr / 2))ᶜ,
          vE y ≤ m := by
    intro p rr hrr htgt Wo hWoOpen vE KE m hm0 hvsub hvcont hKE hKEW hKE0 hcirc
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    set Dh : Set M := ep.symm '' closedBall cp (rr / 2) with hDh
    have hpsrc : p ∈ ep.source := mem_chart_source ℂ p
    have hpDh : p ∈ Dh :=
      ⟨cp, mem_closedBall_self (by linarith only [hrr]), ep.left_inv hpsrc⟩
    set Ω : Set M := Wo ∩ Dhᶜ with hΩdef
    have hDhcomp : IsCompact Dh := (isCompact_closedBall _ _).image_of_continuousOn
      (ep.continuousOn_symm.mono
        ((closedBall_subset_closedBall (by linarith only [hrr])).trans htgt))
    have hΩopen : IsOpen Ω := hWoOpen.inter hDhcomp.isClosed.isOpen_compl
    have hΩne : Ω ≠ Set.univ := by
      intro hcon
      have hpΩ : p ∈ Ω := by rw [hcon]; trivial
      exact hpΩ.2 hpDh
    have hΩp : Ω ⊆ {p}ᶜ := fun z hz ↦ Set.mem_compl_singleton_iff.2
      (fun hcon ↦ hz.2 (hcon ▸ hpDh))
    apply maxPrin Ω vE m KE hΩopen hΩne (fun z hz ↦ hvsub z (hΩp hz)) hKE
    · intro z hz hzK
      rw [hKE0 z hzK]
      exact hm0
    · rintro z ⟨hzcl, hzΩ⟩
      by_cases hzW : z ∈ Wo
      · -- frontier point on the inner circle
        have hzDh : z ∈ Dh := by
          by_contra hzD
          exact hzΩ ⟨hzW, hzD⟩
        obtain ⟨w, hw, hwz⟩ := hzDh
        have hwt : w ∈ ep.target :=
          ((closedBall_subset_closedBall
            (by linarith only [hrr] : rr / 2 ≤ rr)).trans htgt) hw
        have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
        have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
        have hzle : dist (ep z) cp ≤ rr / 2 := by
          rw [hzval]
          exact mem_closedBall.1 hw
        have hzd : dist (ep z) cp = rr / 2 := by
          rcases lt_or_eq_of_le hzle with h | h
          · exfalso
            set O : Set M := ep.source ∩ ep ⁻¹' ball cp (rr / 2) with hO
            have hOopen : IsOpen O := ep.isOpen_inter_preimage isOpen_ball
            have hzO : z ∈ O := ⟨hzsrc, by rw [Set.mem_preimage]; exact mem_ball.2 h⟩
            have hOD : O ⊆ Dh := by
              rintro q ⟨hq1, hq2⟩
              rw [Set.mem_preimage] at hq2
              exact ⟨ep q, ball_subset_closedBall hq2, ep.left_inv hq1⟩
            obtain ⟨q, hqO, hqΩ⟩ := mem_closure_iff.1 hzcl O hOopen hzO
            exact hqΩ.2 (hOD hqO)
          · exact h
        have hzΓ : z ∈ ep.symm '' sphere cp (rr / 2) :=
          ⟨ep z, mem_sphere.2 hzd, ep.left_inv hzsrc⟩
        have hznp : z ≠ p := by
          intro hcon
          rw [hcon] at hzd
          rw [← hcp, dist_self] at hzd
          have : (0 : ℝ) < rr / 2 := by linarith only [hrr]
          rw [← hzd] at this
          exact lt_irrefl _ this
        refine ⟨hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.2 hznp)), ?_⟩
        exact hcirc z hzΓ
      · -- frontier point off the open set: the candidate vanishes on a neighborhood
        have hzK : z ∉ KE := fun h ↦ hzW (hKEW h)
        have hev : vE =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hKE.isClosed.isOpen_compl.mem_nhds hzK] with q hq
          exact hKE0 q hq
        refine ⟨continuousAt_const.congr_of_eventuallyEq hev, ?_⟩
        rw [hKE0 z hzK]
        exact hm0
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dite_eq_left ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dite_eq_right]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## The zero function belongs to every piece Green family. -/
  have zeroFam : ∀ (P : Opens M) (p : M) (hp : p ∈ P),
      (fun _ : ↥P ↦ (0 : ℝ)) ∈ greenFamily (⟨p, hp⟩ : ↥P) := by
    intro P p hp
    have : Nonempty ↥P := ⟨⟨p, hp⟩⟩
    refine ⟨fun z _ ↦ (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt,
      continuousOn_const, ⟨∅, isCompact_empty, Set.empty_ne_univ, fun z _ ↦ rfl⟩,
      ⟨0, ?_⟩⟩
    have hcont : ContinuousAt (poleCoord (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) := by
      have h1 : ContinuousAt (chartAt ℂ (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) :=
        (chartAt ℂ (⟨p, hp⟩ : ↥P)).continuousAt (mem_chart_source ℂ _)
      exact h1.sub continuousAt_const
    have h0 : poleCoord (⟨p, hp⟩ : ↥P) (⟨p, hp⟩ : ↥P) = 0 := sub_self _
    have hev : ∀ᶠ z in 𝓝 (⟨p, hp⟩ : ↥P), ‖poleCoord (⟨p, hp⟩ : ↥P) z‖ ≤ 1
        := by
      have h2 := hcont.tendsto
      rw [h0] at h2
      have h3 : closedBall (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ one_pos
      filter_upwards [h2 h3] with z hz
      rw [← dist_zero_right]
      exact mem_closedBall.1 hz
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
    have hlog := Real.log_nonpos (norm_nonneg _) hz
    simpa using hlog
  /- ## Zero extension of a piece candidate to the surface. -/
  have extendC : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (v : ↥P → ℝ),
      v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
      ∃ (vE : M → ℝ) (KE : Set M) (Cv : ℝ),
        (∀ z : ↥P, vE z = v z) ∧ MSubharmonicOn vE {p}ᶜ ∧ ContinuousOn vE {p}ᶜ ∧
        IsCompact KE ∧ KE ⊆ (P : Set M) ∧ (∀ y, y ∉ KE → vE y = 0) ∧
        ∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv := by
    intro P p hp v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y ↦ if h : y ∈ P then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥P, w z = v z := by
      intro z
      simp only [hwdef]
      rw [dite_eq_left z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (P : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ P
      · simp only [hwdef]
        rw [dite_eq_left hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dite_eq_right hyP]
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ P
      · have hoe : IsOpenEmbedding (Subtype.val : ↥P → M) :=
          P.2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥P) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥P)) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u ↦ (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥P → M) (𝓝 (⟨y, hyP⟩ : ↥P)) = 𝓝 y :=
          hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem ↦ hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ P
      · have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val P w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem ↦ hyP (hKwsub hmem)) (fun z hz ↦ hKwzero z hz)
    refine ⟨w, Kw, C, hwval, hwsub, hwcont, hKwcomp, hKwsub, hKwzero, ?_⟩
    rw [← mapval P p hp, Filter.eventually_map]
    filter_upwards [hC] with z hz
    have hpc : poleCoord (⟨p, hp⟩ : ↥P) z = poleCoord p (z : M) := rfl
    rw [hwval z, ← hpc]
    exact hz
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    have := hcs
    have := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon ↦ hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z ↦ pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## Growth estimate ([M] (5)): a candidate gains at most `log 2` from the
  pole circle to the half circle, by the `ε`-excised annulus maximum principle. -/
  have growth : ∀ (p : M) (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      ∀ (vE : M → ℝ) (Cv MoV : ℝ),
        MSubharmonicOn vE {p}ᶜ → ContinuousOn vE {p}ᶜ →
        (∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv) →
        (∀ z ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr, vE z ≤ MoV) →
        ∀ y ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (rr / 2),
          vE y ≤ MoV + Real.log 2 := by
    intro p rr hrr htgt vE Cv MoV hvsub hvcont hCv hMoV y hyΓ
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    have hpsrc : p ∈ ep.source := mem_chart_source ℂ p
    have hcptgt : cp ∈ ep.target := by rw [hcp]; exact ep.map_source hpsrc
    have hsymcp : ep.symm cp = p := by rw [hcp]; exact ep.left_inv hpsrc
    have hsphtgt : ∀ ρ : ℝ, ρ ≤ rr → sphere cp ρ ⊆ ep.target := fun ρ hρ ↦
      sphere_subset_closedBall.trans ((closedBall_subset_closedBall hρ).trans htgt)
    obtain ⟨wy, hwy, hwyy⟩ := hyΓ
    have hwyt : wy ∈ ep.target := hsphtgt _ (by linarith only [hrr]) hwy
    have hysrc : y ∈ ep.source := hwyy ▸ ep.map_target hwyt
    have hyval : ep y = wy := by rw [← hwyy, ep.right_inv hwyt]
    have hydist : dist (ep y) cp = rr / 2 := by rw [hyval]; exact mem_sphere.1 hwy
    have hyne : y ≠ p := by
      intro hcon
      rw [hcon, ← hcp, dist_self] at hydist
      have h0 : (0 : ℝ) < rr / 2 := by linarith only [hrr]
      rw [← hydist] at h0
      exact lt_irrefl _ h0
    -- the chart-ball pole bound
    obtain ⟨Nv, hNvnhds, hNv⟩ := (eventually_nhdsWithin_iff.mp hCv).exists_mem
    have hprev : ep.target ∩ ep.symm ⁻¹' Nv ∈ 𝓝 cp := by
      have h1 : ContinuousAt ep.symm cp := ep.continuousAt_symm hcptgt
      have h3 : ep.symm ⁻¹' Nv ∈ 𝓝 cp := h1.preimage_mem_nhds (hsymcp ▸ hNvnhds)
      exact Filter.inter_mem (ep.open_target.mem_nhds hcptgt) h3
    obtain ⟨σ₀, hσ₀pos, hσ₀sub⟩ := nhds_basis_closedBall.mem_iff.1 hprev
    have hCbound : ∀ z : M, z ∈ ep.source → ep z ∈ closedBall cp σ₀ → z ≠ p →
        vE z + Real.log (dist (ep z) cp) ≤ Cv := by
      intro z hzs hzball hzne
      have h3 : ep z ∈ ep.symm ⁻¹' Nv := (hσ₀sub hzball).2
      have h4 : z ∈ Nv := by rwa [Set.mem_preimage, ep.left_inv hzs] at h3
      have h5 := hNv z h4 (Set.mem_compl_singleton_iff.mpr hzne)
      have h6 : ‖poleCoord p z‖ = dist (ep z) cp := by
        simp only [poleCoord, ← hep, ← hcp, dist_eq_norm]
      rwa [h6] at h5
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    refine le_of_forall_pos_le_add ?_
    intro ε' hε'
    set ε : ℝ := ε' / Real.log 2 with hε
    have hεpos : 0 < ε := div_pos hε' hlog2
    have hεlog : ε * Real.log 2 = ε' := by
      rw [hε]
      exact div_mul_cancel₀ ε' hlog2.ne'
    set Q : ℝ := (MoV - Cv + (1 + ε) * Real.log rr) / ε with hQ
    set σ : ℝ := min (min σ₀ (rr / 4)) (Real.exp Q) with hσ
    have hσpos : 0 < σ :=
      lt_min (lt_min hσ₀pos (by linarith only [hrr])) (Real.exp_pos Q)
    have hσσ₀ : σ ≤ σ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hσR4 : σ ≤ rr / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) :=
            Real.log_le_log hσpos (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hεQ : ε * Q = MoV - Cv + (1 + ε) * Real.log rr := by
      rw [hQ, mul_comm]
      exact div_mul_cancel₀ _ hεpos.ne'
    -- the excised annulus region
    set Ωσ : Set M := ep.symm '' (ball cp rr \ closedBall cp σ) with hΩσ
    have hΩσsub : ball cp rr \ closedBall cp σ ⊆ ep.target :=
      (Set.sdiff_subset.trans ball_subset_closedBall).trans htgt
    have hΩσopen : IsOpen Ωσ := by
      rw [hΩσ, himg ep _ hΩσsub]
      exact ep.continuousOn.isOpen_inter_preimage ep.open_source
        (isOpen_ball.sdiff isClosed_closedBall)
    have hΩσmem : ∀ z ∈ Ωσ, z ∈ ep.source ∧ σ < dist (ep z) cp ∧
        dist (ep z) cp < rr := by
      intro z hz
      rw [hΩσ, himg ep _ hΩσsub] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall] at hz2
      exact ⟨hz1, not_le.1 hz2.2, hz2.1⟩
    have hΩσmem' : ∀ z : M, z ∈ ep.source → σ < dist (ep z) cp →
        dist (ep z) cp < rr → z ∈ Ωσ := by
      intro z hz1 hz2 hz3
      rw [hΩσ, himg ep _ hΩσsub]
      refine ⟨hz1, ?_⟩
      rw [Set.mem_preimage, Set.mem_sdiff, mem_ball, mem_closedBall]
      exact ⟨hz3, not_le.2 hz2⟩
    have hpΩσ : p ∉ Ωσ := by
      intro hcon
      obtain ⟨-, h2, -⟩ := hΩσmem p hcon
      rw [← hcp, dist_self] at h2
      exact absurd h2 (not_lt.2 hσpos.le)
    have hΩσne : Ωσ ≠ Set.univ := by
      intro hcon
      apply hpΩσ
      rw [hcon]
      trivial
    set Kσ : Set M := ep.symm '' (closedBall cp rr \ ball cp σ) with hKσ
    have hKσcomp : IsCompact Kσ :=
      ((isCompact_closedBall cp rr).diff isOpen_ball).image_of_continuousOn
        (ep.continuousOn_symm.mono (Set.sdiff_subset.trans htgt))
    have hΩσKσ : Ωσ ⊆ Kσ :=
      Set.image_mono (fun w hw ↦ ⟨ball_subset_closedBall hw.1,
        fun h ↦ hw.2 (ball_subset_closedBall h)⟩)
    -- harmonicity and continuity of the logarithmic barrier
    have hepatlas : ep ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
      rw [hep]
      exact IsManifold.chart_mem_maximalAtlas p
    have hbharm : ∀ z : M, z ∈ ep.source → ep z ≠ cp →
        MHarmonicAt (fun q ↦ Real.log (dist (ep q) cp)) z := by
      intro z hzs hzne
      have h1 : MHarmonicAt (fun q ↦ Real.log (dist (ep q) cp)) z ↔
          HarmonicAt ((fun q ↦ Real.log (dist (ep q) cp)) ∘ ep.symm) (ep z) :=
        mharmonicAt_iff_of_mem_maximalAtlas hepatlas hzs
      rw [h1]
      have hharm : HarmonicAt (fun w : ℂ ↦ Real.log ‖w - cp‖) (ep z) := by
        apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ ↦ w - cp)
        · exact analyticAt_id.sub analyticAt_const
        · exact sub_ne_zero.2 hzne
      have heqv : (fun w : ℂ ↦ Real.log ‖w - cp‖) =ᶠ[𝓝 (ep z)]
          ((fun q ↦ Real.log (dist (ep q) cp)) ∘ ep.symm) := by
        filter_upwards [ep.open_target.mem_nhds (ep.map_source hzs)] with w hw
        simp only [Function.comp_apply, ep.right_inv hw, dist_eq_norm]
      exact (harmonicAt_congr_nhds heqv).1 hharm
    have hbcont : ∀ z : M, z ∈ ep.source → ep z ≠ cp →
        ContinuousAt (fun q ↦ Real.log (dist (ep q) cp)) z := by
      intro z hzs hzne
      have h2 : ContinuousAt ep z := ep.continuousAt hzs
      have h3 : dist (ep z) cp ≠ 0 := (dist_pos.2 hzne).ne'
      exact (h2.dist continuousAt_const).log h3
    have hvCA : ∀ z : M, z ≠ p → ContinuousAt vE z := fun z hz ↦
      hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.2 hz))
    -- the competitor and its subharmonicity
    set Wf : M → ℝ :=
      fun q ↦ vE q + (1 + ε) * (Real.log (dist (ep q) cp) - Real.log rr) with hWf
    have hWfsub : MSubharmonicOn Wf Ωσ := by
      intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hΩσmem z hz
      have hzne : ep z ≠ cp := by
        intro hcon
        rw [hcon, dist_self] at hz2
        exact absurd hz2 (not_lt.2 hσpos.le)
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp] at hzne
        exact hzne rfl
      have hu : MHarmonicAt
          (fun q ↦ (-(1 + ε)) * Real.log (dist (ep q) cp) + (1 + ε) * Real.log rr)
          z := mharmAffine _ z _ _ (hbharm z hz1 hzne)
      have h7 := (hvsub z (Set.mem_compl_singleton_iff.mpr hznep)).sub_mharmonicAt hu
      have h9 : Wf = fun q ↦ vE q -
          ((-(1 + ε)) * Real.log (dist (ep q) cp) + (1 + ε) * Real.log rr) := by
        funext q
        simp only [hWf]
        ring
      rw [h9]
      exact h7
    -- boundary control on the two circles
    have hWfbd : ∀ z ∈ closure Ωσ \ Ωσ, ContinuousAt Wf z ∧ Wf z ≤ MoV := by
      rintro z ⟨hzcl, hzΩ⟩
      have hzK : z ∈ Kσ := (hKσcomp.isClosed.closure_subset_iff.2 hΩσKσ) hzcl
      obtain ⟨w, ⟨hw1, hw2⟩, hwz⟩ := hzK
      have hwt : w ∈ ep.target := htgt hw1
      have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
      have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
      have hzd1 : σ ≤ dist (ep z) cp := by
        rw [hzval]
        exact not_lt.1 (fun h ↦ hw2 (mem_ball.2 h))
      have hzd2 : dist (ep z) cp ≤ rr := by rw [hzval]; exact mem_closedBall.1 hw1
      have hzne : ep z ≠ cp := by
        intro hcon
        rw [hcon, dist_self] at hzd1
        exact absurd hzd1 (not_le.2 hσpos)
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp] at hzne
        exact hzne rfl
      have hcont : ContinuousAt Wf z := by
        rw [hWf]
        exact (hvCA z hznep).add
          (continuousAt_const.mul ((hbcont z hzsrc hzne).sub continuousAt_const))
      refine ⟨hcont, ?_⟩
      have hdisj : dist (ep z) cp = σ ∨ dist (ep z) cp = rr := by
        rcases lt_or_eq_of_le hzd1 with h1 | h1
        · rcases lt_or_eq_of_le hzd2 with h2 | h2
          · exact absurd (hΩσmem' z hzsrc h1 h2) hzΩ
          · exact Or.inr h2
        · exact Or.inl h1.symm
      rcases hdisj with hzd | hzd
      · have hσball : ep z ∈ closedBall cp σ₀ := by
          rw [mem_closedBall, hzd]
          exact hσσ₀
        have hvz : vE z + Real.log σ ≤ Cv := by
          have h5 := hCbound z hzsrc hσball hznep
          rwa [hzd] at h5
        rw [hWf]
        simp only
        rw [hzd]
        have h8 : ε * Real.log σ ≤ ε * Q := mul_le_mul_of_nonneg_left hσQ hεpos.le
        rw [hεQ] at h8
        nlinarith only [hvz, h8]
      · have hzΓ : z ∈ ep.symm '' sphere cp rr :=
          ⟨ep z, mem_sphere.2 hzd, ep.left_inv hzsrc⟩
        rw [hWf]
        simp only
        rw [hzd, sub_self, mul_zero, add_zero]
        exact hMoV z hzΓ
    have hWfle : ∀ z ∈ Ωσ, Wf z ≤ MoV := by
      apply maxPrin Ωσ Wf MoV Kσ hΩσopen hΩσne hWfsub hKσcomp ?_ hWfbd
      intro z hz hzK
      exact absurd (hΩσKσ hz) hzK
    -- evaluate on the half circle
    have hyΩσ : y ∈ Ωσ := by
      apply hΩσmem' y hysrc
      · rw [hydist]; linarith only [hσR4, hrr]
      · rw [hydist]; linarith only [hrr]
    have h9 := hWfle y hyΩσ
    rw [hWf] at h9
    simp only at h9
    rw [hydist] at h9
    have h10 : Real.log (rr / 2) = Real.log rr - Real.log 2 :=
      Real.log_div hrr.ne' two_ne_zero
    rw [h10] at h9
    have h11 : (1 + ε) * (Real.log rr - Real.log 2 - Real.log rr) =
        -(1 + ε) * Real.log 2 := by
      ring
    rw [h11] at h9
    have h12 : (1 + ε) * Real.log 2 = Real.log 2 + ε' := by
      rw [add_mul, one_mul, hεlog]
    linarith only [h9, h12]
  /- ## The per-piece pole bound: envelope interior bound and growth estimate. -/
  have poleBound : ∀ (P : Opens M), ConnectedSpace ↥P → NoncompactSpace ↥P →
      ∀ (p : M) (hp : p ∈ P), HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      (∀ y ∈ (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) rr, y ∈ P) →
      ∃ (Nt : ℝ) (xout : M),
        xout ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr ∧
        pieceGreen P p xout = Nt ∧
        (∀ y ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr,
          pieceGreen P p y ≤ Nt) ∧
        ∀ y ∈ (P : Set M) ∩
            ((chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (rr / 2))ᶜ,
          pieceGreen P p y ≤ Nt + Real.log 2 := by
    intro P hcs hnc p hp hGF rr hrr htgt hcarP
    have := hcs
    have := hnc
    have hIB := interiorBd p rr hrr htgt (P : Set M) P.2
    have hGR := growth p rr hrr htgt
    have hBdd := (mharmonicOn_greenEnvelope hGF).2
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    -- reading points of the chart circles
    have hΓread : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → ∀ z ∈ ep.symm '' sphere cp ρ,
        z ∈ ep.source ∧ dist (ep z) cp = ρ ∧ z ≠ p ∧ z ∈ P := by
      intro ρ hρ0 hρrr z hz
      obtain ⟨w, hw, hwz⟩ := hz
      have hwt : w ∈ ep.target :=
        (sphere_subset_closedBall.trans
          ((closedBall_subset_closedBall hρrr).trans htgt)) hw
      have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
      have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
      have hzd : dist (ep z) cp = ρ := by rw [hzval]; exact mem_sphere.1 hw
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp, dist_self] at hzd
        rw [← hzd] at hρ0
        exact lt_irrefl _ hρ0
      have hzP : z ∈ P := hcarP z
        ⟨w, closedBall_subset_closedBall hρrr (sphere_subset_closedBall hw), hwz⟩
      exact ⟨hzsrc, hzd, hznep, hzP⟩
    have hΓcomp : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → IsCompact (ep.symm '' sphere cp ρ) ∧
        (ep.symm '' sphere cp ρ).Nonempty := by
      intro ρ hρ0 hρrr
      constructor
      · exact (isCompact_sphere cp ρ).image_of_continuousOn
          (ep.continuousOn_symm.mono (sphere_subset_closedBall.trans
            ((closedBall_subset_closedBall hρrr).trans htgt)))
      · exact (NormedSpace.sphere_nonempty.2 hρ0.le).image _
    have hgcont : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr →
        ContinuousOn (pieceGreen P p) (ep.symm '' sphere cp ρ) := by
      intro ρ hρ0 hρrr z hz
      obtain ⟨-, -, hznep, hzP⟩ := hΓread ρ hρ0 hρrr z hz
      exact ((pgharm P p hp hcs hnc hGF z hzP hznep).continuousAt).continuousWithinAt
    have hΓoutC := hΓcomp rr hrr le_rfl
    have hΓinC := hΓcomp (rr / 2) (by linarith only [hrr]) (by linarith only [hrr])
    obtain ⟨xout, hxoutΓ, hxoutmax⟩ :=
      hΓoutC.1.exists_isMaxOn hΓoutC.2 (hgcont rr hrr le_rfl)
    obtain ⟨xin, hxinΓ, hxinmax⟩ :=
      hΓinC.1.exists_isMaxOn hΓinC.2
        (hgcont (rr / 2) (by linarith only [hrr]) (by linarith only [hrr]))
    set Nt : ℝ := pieceGreen P p xout with hNt
    set Mt : ℝ := pieceGreen P p xin with hMt
    have hMtpos : 0 < Mt := by
      obtain ⟨-, -, hnep2, hP2⟩ := hΓread (rr / 2) (by linarith only [hrr])
        (by linarith only [hrr]) xin hxinΓ
      rw [hMt, pgval P p hp xin hP2]
      exact greenEnvelope_pos hGF _ (fun hcon ↦ hnep2 (congrArg Subtype.val hcon))
    -- per-candidate circle bounds against the envelope maxima
    have hcircGen : ∀ (ρ : ℝ) (hρ0 : 0 < ρ) (hρrr : ρ ≤ rr) (xm : M)
        (hxm : IsMaxOn (pieceGreen P p) (ep.symm '' sphere cp ρ) xm)
        (v : ↥P → ℝ), v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
        ∀ (vE : M → ℝ), (∀ z : ↥P, vE z = v z) →
        ∀ z ∈ ep.symm '' sphere cp ρ, vE z ≤ pieceGreen P p xm := by
      intro ρ hρ0 hρrr xm hxm v hv vE hvEval z hz
      obtain ⟨-, -, hznep, hzP⟩ := hΓread ρ hρ0 hρrr z hz
      calc vE z = v ⟨z, hzP⟩ := hvEval ⟨z, hzP⟩
        _ ≤ greenEnvelope (⟨p, hp⟩ : ↥P) ⟨z, hzP⟩ :=
            le_csSup (hBdd _ (fun hcon ↦ hznep (congrArg Subtype.val hcon)))
              ⟨v, hv, rfl⟩
        _ = pieceGreen P p z := (pgval P p hp z hzP).symm
        _ ≤ pieceGreen P p xm := hxm hz
    -- envelope interior bound on the piece minus the inner disk
    have hIntEnv : ∀ y ∈ (P : Set M) ∩ (ep.symm '' closedBall cp (rr / 2))ᶜ,
        pieceGreen P p y ≤ Mt := by
      intro y hy
      have hyP : y ∈ P := hy.1
      rw [pgval P p hp y hyP]
      simp only [greenEnvelope]
      refine csSup_le ⟨0, (fun _ : ↥P ↦ (0 : ℝ)), zeroFam P p hp, rfl⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P p hp v hv
      have hgoal : vE y ≤ Mt := by
        apply hIB vE KE Mt hMtpos.le hvEsub hvEcont hKEc hKEP hKE0 ?_ y hy
        exact hcircGen (rr / 2) (by linarith only [hrr]) (by linarith only [hrr])
          xin hxinmax v hv vE hvEval
      have h1 : v ⟨y, hyP⟩ = vE y := (hvEval ⟨y, hyP⟩).symm
      rw [← h1] at hgoal
      exact hgoal
    -- envelope growth estimate on the half circle
    have hgrowEnv : ∀ y ∈ ep.symm '' sphere cp (rr / 2),
        pieceGreen P p y ≤ Nt + Real.log 2 := by
      intro y hy
      obtain ⟨-, -, hynep, hyP⟩ := hΓread (rr / 2) (by linarith only [hrr])
        (by linarith only [hrr]) y hy
      rw [pgval P p hp y hyP]
      simp only [greenEnvelope]
      refine csSup_le ⟨0, (fun _ : ↥P ↦ (0 : ℝ)), zeroFam P p hp, rfl⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P p hp v hv
      have hgoal : vE y ≤ Nt + Real.log 2 := by
        apply hGR vE Cv Nt hvEsub hvEcont hCv ?_ y hy
        intro z hz
        have h2 := hcircGen rr hrr le_rfl xout hxoutmax v hv vE hvEval z hz
        rw [← hNt] at h2
        exact h2
      have h1 : v ⟨y, hyP⟩ = vE y := (hvEval ⟨y, hyP⟩).symm
      rw [← h1] at hgoal
      exact hgoal
    have hMtNt : Mt ≤ Nt + Real.log 2 := by
      rw [hMt]
      exact hgrowEnv xin hxinΓ
    refine ⟨Nt, xout, hxoutΓ, hNt.symm, ?_, ?_⟩
    · intro y hy
      have h3 := hxoutmax hy
      rw [← hNt] at h3
      exact h3
    · intro y hy
      exact le_trans (hIntEnv y hy) hMtNt
  /- ## The oscillation bound on a chain compact, via the per-piece pole bound. -/
  have oscBd : ∀ (pa : M) (ra : ℝ), 0 < ra →
      closedBall (chartAt ℂ pa pa) ra ⊆ (chartAt ℂ pa).target →
      ∀ (P : Opens M), ∀ hcs : ConnectedSpace ↥P, ∀ hnc : NoncompactSpace ↥P,
      ∀ hpaP : pa ∈ P, HasGreenFunction (⟨pa, hpaP⟩ : ↥P) →
      (∀ w ∈ closedBall (chartAt ℂ pa pa) ra, (chartAt ℂ pa).symm w ∈ P) →
      ∀ (KA ΩA : Set M) (CHa : ℝ),
      (∀ u : M → ℝ, MHarmonicOn u ΩA → (∀ x ∈ ΩA, 0 ≤ u x) →
        ∀ x ∈ KA, ∀ y ∈ KA, u x ≤ CHa * u y) →
      KA ⊆ ΩA → p₃ ∈ KA →
      (∀ z ∈ ΩA, z ∈ P) →
      (∀ z ∈ ΩA, z ∉ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) (ra / 2)) →
      ((chartAt ℂ pa).symm '' sphere (chartAt ℂ pa pa) ra ⊆ KA) →
      ∀ z ∈ KA, |pieceGreen P pa z - pieceGreen P pa p₃| ≤ CHa * Real.log 2 := by
    intro pa ra hra htgtA P hcs hnc hpaP hGFa hcarA KA ΩA CHa hCHa hKAΩ hp₃KA hΩA1
      hΩA2 hΓA z hzK
    obtain ⟨Nt, xout, hxoutΓ, hxoutval, hxoutmax, hIB⟩ :=
      poleBound P hcs hnc pa hpaP hGFa ra hra htgtA
        (by rintro y ⟨w, hw, rfl⟩; exact hcarA w hw)
    have hpahalf : pa ∈ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) (ra / 2) :=
      ⟨chartAt ℂ pa pa, mem_closedBall_self (by linarith only [hra]),
        (chartAt ℂ pa).left_inv (mem_chart_source ℂ pa)⟩
    set u : M → ℝ := fun q ↦ Nt + Real.log 2 - pieceGreen P pa q with hu
    have huharm : MHarmonicOn u ΩA := by
      intro q hq
      have hqnepa : q ≠ pa := fun hcon ↦ hΩA2 q hq (hcon ▸ hpahalf)
      have h1 : MHarmonicAt (pieceGreen P pa) q :=
        pgharm P pa hpaP hcs hnc hGFa q (hΩA1 q hq) hqnepa
      refine mharm_congr _ _ q (Filter.Eventually.of_forall fun y ↦ ?_)
        (mharmAffine _ q (-1) (Nt + Real.log 2) h1)
      simp only [hu]
      ring
    have hupos : ∀ x ∈ ΩA, 0 ≤ u x := by
      intro x hx
      have h2 := hIB x ⟨hΩA1 x hx, hΩA2 x hx⟩
      simp only [hu]
      linarith only [h2]
    have hxoutK : xout ∈ KA := hΓA hxoutΓ
    have huout : u xout = Real.log 2 := by
      simp only [hu]
      rw [hxoutval]
      ring
    have h3 : u z ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos z hzK xout hxoutK
      rwa [huout] at h5
    have h4 : u p₃ ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos p₃ hp₃KA xout hxoutK
      rwa [huout] at h5
    have h5 : 0 ≤ u z := hupos z (hKAΩ hzK)
    have h6 : 0 ≤ u p₃ := hupos p₃ (hKAΩ hp₃KA)
    have h7 : pieceGreen P pa z - pieceGreen P pa p₃ = u p₃ - u z := by
      simp only [hu]
      ring
    rw [h7, abs_le]
    constructor <;> linarith only [h3, h4, h5, h6]
  /- ## The pole charts and the avoidance radii. -/
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  have havoid1 : ∃ S : ℝ, 0 < S ∧ closedBall c₁ S ⊆ e₁.target ∧
      ∀ w ∈ closedBall c₁ S, e₁.symm w ∉ D₀.closedCarrier ∧ e₁.symm w ≠ p₂ ∧
        e₁.symm w ≠ p₃ := by
    have hopen : IsOpen (e₁.target ∩
        e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ ({p₂}ᶜ ∩ {p₃}ᶜ))) :=
      e₁.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter
          (isOpen_compl_singleton.inter isOpen_compl_singleton))
    have hmem : c₁ ∈ e₁.target ∩
        e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ ({p₂}ᶜ ∩ {p₃}ᶜ)) := by
      refine ⟨by rw [hc₁]; exact e₁.map_source hp₁src, ?_⟩
      rw [Set.mem_preimage, hc₁, e₁.left_inv hp₁src]
      exact ⟨hp₁, Set.mem_compl_singleton_iff.2 hne,
        Set.mem_compl_singleton_iff.2 (Ne.symm h₃₁)⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw ↦ (hSsub hw).1, fun w hw ↦ ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, Set.mem_compl_singleton_iff.1 h2.2.1,
      Set.mem_compl_singleton_iff.1 h2.2.2⟩
  obtain ⟨S₁, hS₁0, hS₁tgt, hS₁av⟩ := havoid1
  set r₁ : ℝ := S₁ / 2 with hr₁def
  have hr₁ : 0 < r₁ := by rw [hr₁def]; exact half_pos hS₁0
  have h2r₁ : 2 * r₁ ≤ S₁ := by rw [hr₁def]; linarith only []
  have htgt1 : closedBall c₁ (2 * r₁) ⊆ e₁.target :=
    (closedBall_subset_closedBall h2r₁).trans hS₁tgt
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  have hCar1cp : IsCompact Car1 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono htgt1)
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ ∧ z ≠ p₃ := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₁av w (closedBall_subset_closedBall h2r₁ hw)
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have havoid2 : ∃ S : ℝ, 0 < S ∧ closedBall c₂ S ⊆ e₂.target ∧
      ∀ w ∈ closedBall c₂ S, e₂.symm w ∉ D₀.closedCarrier ∧ e₂.symm w ∉ Car1 ∧
        e₂.symm w ≠ p₃ := by
    have hopen : IsOpen (e₂.target ∩
        e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ (Car1ᶜ ∩ {p₃}ᶜ))) :=
      e₂.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter
          (hCar1cp.isClosed.isOpen_compl.inter isOpen_compl_singleton))
    have hmem : c₂ ∈ e₂.target ∩
        e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ (Car1ᶜ ∩ {p₃}ᶜ)) := by
      refine ⟨by rw [hc₂]; exact e₂.map_source hp₂src, ?_⟩
      rw [Set.mem_preimage, hc₂, e₂.left_inv hp₂src]
      exact ⟨hp₂, fun hmem2 ↦ (hCar1av p₂ hmem2).2.1 rfl,
        Set.mem_compl_singleton_iff.2 (Ne.symm h₃₂)⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw ↦ (hSsub hw).1, fun w hw ↦ ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, h2.2.1, Set.mem_compl_singleton_iff.1 h2.2.2⟩
  obtain ⟨S₂, hS₂0, hS₂tgt, hS₂av⟩ := havoid2
  set r₂ : ℝ := S₂ / 2 with hr₂def
  have hr₂ : 0 < r₂ := by rw [hr₂def]; exact half_pos hS₂0
  have h2r₂ : 2 * r₂ ≤ S₂ := by rw [hr₂def]; linarith only []
  have htgt2 : closedBall c₂ (2 * r₂) ⊆ e₂.target :=
    (closedBall_subset_closedBall h2r₂).trans hS₂tgt
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 ∧ z ≠ p₃ := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₂av w (closedBall_subset_closedBall h2r₂ hw)
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  /- ## The half pole disks and the Harnack chain domains. -/
  set half1 : CoordDisk M := ⟨p₁, r₁ / 2, by linarith only [hr₁],
    (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1⟩ with hhalf1
  set half2 : CoordDisk M := ⟨p₂, r₂ / 2, by linarith only [hr₂],
    (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2⟩ with hhalf2
  have hhalf1car : half1.closedCarrier = e₁.symm '' closedBall c₁ (r₁ / 2) := rfl
  have hhalf2car : half2.closedCarrier = e₂.symm '' closedBall c₂ (r₂ / 2) := rfl
  have hhalf1Car : half1.closedCarrier ⊆ Car1 := by
    rw [hhalf1car, hCar1]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₁]))
  have hhalf2Car : half2.closedCarrier ⊆ Car2 := by
    rw [hhalf2car, hCar2]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₂]))
  have hdisj1 : Disjoint D₀.closedCarrier half1.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz1
    exact (hCar1av z (hhalf1Car hz1)).1 hzQ
  have hdisj2 : Disjoint D₀.closedCarrier half2.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz2
    exact (hCar2av z (hhalf2Car hz2)).1 hzQ
  set Ω₁ : Set M := (D₀.closedCarrier ∪ half1.closedCarrier)ᶜ with hΩ₁
  set Ω₂ : Set M := (D₀.closedCarrier ∪ half2.closedCarrier)ᶜ with hΩ₂
  have hΩ₁open : IsOpen Ω₁ := (D₀.isCompact_closedCarrier.union
    half1.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₂open : IsOpen Ω₂ := (D₀.isCompact_closedCarrier.union
    half2.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₁conn : IsPreconnected Ω₁ :=
    (isConnected_two_coordDisk_compl D₀ half1 hdisj1).isPreconnected
  have hΩ₂conn : IsPreconnected Ω₂ :=
    (isConnected_two_coordDisk_compl D₀ half2 hdisj2).isPreconnected
  /- ## The chain compacts: the pole circles with the two marked points. -/
  set Γ₁ : Set M := e₁.symm '' sphere c₁ r₁ with hΓ₁
  set Γ₂ : Set M := e₂.symm '' sphere c₂ r₂ with hΓ₂
  have hsph1tgt : sphere c₁ r₁ ⊆ e₁.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1
  have hsph2tgt : sphere c₂ r₂ ⊆ e₂.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2
  have hΓ₁cp : IsCompact Γ₁ := (isCompact_sphere _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono hsph1tgt)
  have hΓ₂cp : IsCompact Γ₂ := (isCompact_sphere _ _).image_of_continuousOn
    (e₂.continuousOn_symm.mono hsph2tgt)
  have hΓ₁Car : Γ₁ ⊆ Car1 := by
    rw [hΓ₁, hCar1]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁])))
  have hΓ₂Car : Γ₂ ⊆ Car2 := by
    rw [hΓ₂, hCar2]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂])))
  have hΓ₁half : ∀ z ∈ Γ₁, z ∉ half1.closedCarrier := by
    intro z hz hmem
    rw [hhalf1car] at hmem
    obtain ⟨hzs, hzd⟩ := (hmemCB e₁ c₁ (r₁ / 2)
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1) z).1 hmem
    obtain ⟨-, hzd'⟩ := (hmemSph e₁ c₁ r₁ hsph1tgt z).1 hz
    rw [hzd'] at hzd
    linarith only [hzd, hr₁]
  have hΓ₂half : ∀ z ∈ Γ₂, z ∉ half2.closedCarrier := by
    intro z hz hmem
    rw [hhalf2car] at hmem
    obtain ⟨hzs, hzd⟩ := (hmemCB e₂ c₂ (r₂ / 2)
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2) z).1 hmem
    obtain ⟨-, hzd'⟩ := (hmemSph e₂ c₂ r₂ hsph2tgt z).1 hz
    rw [hzd'] at hzd
    linarith only [hzd, hr₂]
  set K₁ : Set M := Γ₁ ∪ {p₂} ∪ {p₃} with hK₁
  set K₂ : Set M := Γ₂ ∪ {p₁} ∪ {p₃} with hK₂
  have hK₁cp : IsCompact K₁ :=
    (hΓ₁cp.union isCompact_singleton).union isCompact_singleton
  have hK₂cp : IsCompact K₂ :=
    (hΓ₂cp.union isCompact_singleton).union isCompact_singleton
  have hp₂K₁ : p₂ ∈ K₁ := Or.inl (Or.inr rfl)
  have hp₃K₁ : p₃ ∈ K₁ := Or.inr rfl
  have hp₁K₂ : p₁ ∈ K₂ := Or.inl (Or.inr rfl)
  have hp₃K₂ : p₃ ∈ K₂ := Or.inr rfl
  have hK₁Ω₁ : K₁ ⊆ Ω₁ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar1av z (hΓ₁Car hz)).1 hmem
      · exact hΓ₁half z hz hmem
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₂ hmem
      · exact (hCar1av z (hhalf1Car hmem)).2.1 rfl
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃ hmem
      · exact (hCar1av z (hhalf1Car hmem)).2.2 rfl
  have hK₂Ω₂ : K₂ ⊆ Ω₂ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar2av z (hΓ₂Car hz)).1 hmem
      · exact hΓ₂half z hz hmem
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₁ hmem
      · exact (hCar2av z (hhalf2Car hmem)).2.1 hp₁Car1
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃ hmem
      · exact (hCar2av z (hhalf2Car hmem)).2.2 rfl
  obtain ⟨CH₁, hCH₁0, hCH₁⟩ := exists_harnack_chain_const hΩ₁open hΩ₁conn hK₁cp hK₁Ω₁
  obtain ⟨CH₂, hCH₂0, hCH₂⟩ := exists_harnack_chain_const hΩ₂open hΩ₂conn hK₂cp hK₂Ω₂
  /- ## The packaged bound at `t₀ = 1`. -/
  refine ⟨1, CH₁ * Real.log 2 + CH₂ * Real.log 2, one_pos, le_refl 1, ?_⟩
  intro t ht ht1 _
  set Pt : Opens M := (D₀.shrink t ht ht1).compl with hPt
  have hcarsubt : (D₀.shrink t ht ht1).closedCarrier ⊆ D₀.closedCarrier := by
    have h1 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    have h2 : D₀.closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) D₀.radius := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left D₀.radius_pos.le ht1))
  have hp₁t : p₁ ∈ Pt := fun hmem ↦ hp₁ (hcarsubt hmem)
  have hp₂t : p₂ ∈ Pt := fun hmem ↦ hp₂ (hcarsubt hmem)
  have hconnT : ConnectedSpace ↥Pt :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  have hncT : NoncompactSpace ↥Pt := noncompactSpace_coordDisk_compl _
  have hGF1t : HasGreenFunction (⟨p₁, hp₁t⟩ : ↥Pt) :=
    hasGreenFunction_coordDisk_compl _ p₁ hp₁t
  have hGF2t : HasGreenFunction (⟨p₂, hp₂t⟩ : ↥Pt) :=
    hasGreenFunction_coordDisk_compl _ p₂ hp₂t
  have hcarP1 : ∀ w ∈ closedBall c₁ r₁, e₁.symm w ∈ Pt := by
    intro w hw hmem
    exact (hS₁av w (closedBall_subset_closedBall
      (by linarith only [hr₁, h2r₁]) hw)).1 (hcarsubt hmem)
  have hcarP2 : ∀ w ∈ closedBall c₂ r₂, e₂.symm w ∈ Pt := by
    intro w hw hmem
    exact (hS₂av w (closedBall_subset_closedBall
      (by linarith only [hr₂, h2r₂]) hw)).1 (hcarsubt hmem)
  /- ## The two oscillation bounds pinned at the drift base point. -/
  have osc1 : |pieceGreen Pt p₁ p₂ - pieceGreen Pt p₁ p₃| ≤ CH₁ * Real.log 2 := by
    refine oscBd p₁ r₁ hr₁
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      Pt hconnT hncT hp₁t hGF1t hcarP1 K₁ Ω₁ CH₁ hCH₁ hK₁Ω₁ hp₃K₁ ?_ ?_ ?_ p₂ hp₂K₁
    · intro z hz hmem
      exact hz (Or.inl (hcarsubt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inl hz)
  have osc2 : |pieceGreen Pt p₂ p₁ - pieceGreen Pt p₂ p₃| ≤ CH₂ * Real.log 2 := by
    refine oscBd p₂ r₂ hr₂
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      Pt hconnT hncT hp₂t hGF2t hcarP2 K₂ Ω₂ CH₂ hCH₂ hK₂Ω₂ hp₃K₂ ?_ ?_ ?_ p₁ hp₁K₂
    · intro z hz hmem
      exact hz (Or.inl (hcarsubt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inl hz)
  /- ## Symmetry of the piece Green's function at the two poles. -/
  have hsymm : pieceGreen Pt p₁ p₂ = pieceGreen Pt p₂ p₁ := by
    rw [pgval Pt p₁ hp₁t p₂ hp₂t, pgval Pt p₂ hp₂t p₁ hp₁t]
    exact greenEnvelope_symm hGF1t (fun hcon ↦ hne (congrArg Subtype.val hcon))
  /- ## Assembly: the cross terms cancel by symmetry. -/
  have h1 := abs_le.1 osc1
  have h2 := abs_le.1 osc2
  rw [abs_le]
  constructor
  · linarith only [h1.2, h2.1, hsymm]
  · linarith only [h1.1, h2.2, hsymm]

/-- **The drift bound** (the irreducible core of the classical cross-symmetry
of Green's functions, in its weakest sufficient form): the two piece Green's
functions, evaluated at a fixed third base point, differ by a
shrink-independent constant. -/
theorem exists_pieceGreen_drift_bound (D₀ : CoordDisk M) {p₁ p₂ p₃ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hp₃ : p₃ ∉ D₀.closedCarrier) (hne : p₁ ≠ p₂) (h₃₁ : p₃ ≠ p₁)
    (h₃₂ : p₃ ≠ p₂) :
    ∃ C : ℝ, ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
        pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C := by
  classical
  /- ## Geometry of the shrinking disks. -/
  have hcarsub : ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      (D₀.shrink t ht ht1).closedCarrier ⊆ D₀.closedCarrier := by
    intro t ht ht1
    have h1 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    have h2 : D₀.closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) D₀.radius := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left D₀.radius_pos.le ht1))
  have hcarmono : ∀ t t' (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t')
      (ht1' : t' ≤ 1), t' ≤ t →
      (D₀.shrink t' ht' ht1').closedCarrier ⊆
        (D₀.shrink t ht ht1).closedCarrier := by
    intro t t' ht ht1 ht' ht1' htt
    have h1 : (D₀.shrink t' ht' ht1').closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t' * D₀.radius) := rfl
    have h2 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right htt D₀.radius_pos.le))
  have hWmem : ∀ t (ht : 0 < t) (ht1 : t ≤ 1) {y : M}, y ∉ D₀.closedCarrier →
      y ∈ (D₀.shrink t ht ht1).compl := by
    intro t ht ht1 y hy hmem
    exact hy (hcarsub t ht ht1 hmem)
  have hWsub : ∀ t t' (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t')
      (ht1' : t' ≤ 1), t' ≤ t →
      ((D₀.shrink t ht ht1).compl : Set M) ⊆
        ((D₀.shrink t' ht' ht1').compl : Set M) := by
    intro t t' ht ht1 ht' ht1' htt y hy hmem
    exact hy (hcarmono t t' ht ht1 ht' ht1' htt hmem)
  have hqW : ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      D₀.center ∉ ((D₀.shrink t ht ht1).compl : Set M) := by
    intro t ht ht1 hmem
    exact hmem ⟨chartAt ℂ D₀.center D₀.center,
      mem_closedBall_self (mul_pos ht D₀.radius_pos).le,
      (chartAt ℂ D₀.center).left_inv (mem_chart_source ℂ D₀.center)⟩
  have hWne : ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      ((D₀.shrink t ht ht1).compl : Set M) ≠ Set.univ := by
    intro t ht ht1 hcon
    have hmem : D₀.center ∈ ((D₀.shrink t ht ht1).compl : Set M) := by
      rw [hcon]; trivial
    exact hqW t ht ht1 hmem
  /- ## Plane-side helper: transfer of subharmonicity along an equality. -/
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈
        (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ ↦ (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ ↦ harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz ↦ (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz ↦ (hf0 _ ((hρsub hz).2)).symm
  /- ## Subharmonicity at a point transfers between the surface and a piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ),
      (∀ z : ↥P, f z = g z) →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hnem : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hnem := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hnem]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hnem).target :=
      e'.map_subtype_source hnem hzsrc
    have heqOn : Set.EqOn (⇑e'.symm)
        (Subtype.val ∘ ⇑(e'.subtypeRestr hnem).symm)
        (e'.subtypeRestr hnem).target := e'.subtypeRestr_symm_eqOn hnem
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hnem).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hnem).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈
          (e'.subtypeRestr hnem).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw ↦ (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw ↦ (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hnem).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hnem), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hnem).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to that of the surface. -/
  have hmapval : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p, hpP⟩ : ↥P)) = 𝓝[≠] p := by
    intro P p hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by
          rw [hU₀eq]; exact hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne
              (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## The zero function belongs to the Green's family of a piece. -/
  have hbaseP : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      (fun _ : ↥P ↦ (0 : ℝ)) ∈ greenFamily (⟨p, hpP⟩ : ↥P) := by
    intro P p hpP
    have : Nonempty ↥P := ⟨⟨p, hpP⟩⟩
    refine ⟨fun x _ ↦ mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ ↦ rfl⟩, ⟨0, ?_⟩⟩
    set q₀ : ↥P := ⟨p, hpP⟩ with hq₀
    have hpc : ContinuousAt (poleCoord q₀) q₀ := by
      have h1 : ContinuousAt (chartAt ℂ q₀) q₀ :=
        (chartAt ℂ q₀).continuousAt (mem_chart_source ℂ q₀)
      exact h1.sub continuousAt_const
    have h0 : ‖poleCoord q₀ q₀‖ < 1 := by
      simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have hx1 : ‖poleCoord q₀ x‖ < 1 := hx
    have h6 : Real.log ‖poleCoord q₀ x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) hx1.le
    simpa using h6
  /- ## The zero function belongs to the Green's family of the surface. -/
  have hbaseM : ∀ p : M, (fun _ : M ↦ (0 : ℝ)) ∈ greenFamily p := by
    intro p
    have : Nonempty M := ⟨p⟩
    refine ⟨fun x _ ↦ mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ ↦ rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord p) p := by
      have h1 : ContinuousAt (chartAt ℂ p) p :=
        (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
      exact h1.sub continuousAt_const
    have h0 : ‖poleCoord p p‖ < 1 := by
      simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have hx1 : ‖poleCoord p x‖ < 1 := hx
    have h6 : Real.log ‖poleCoord p x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) hx1.le
    simpa using h6
  /- ## Boundedness of the piece family at every point off the pole. -/
  have hEnvB : ∀ t (ht : 0 < t) (ht1 : t ≤ 1) (p : M)
      (hpW : p ∈ (D₀.shrink t ht ht1).compl)
      (z : ↥(D₀.shrink t ht ht1).compl), z ≠ ⟨p, hpW⟩ →
      BddAbove ((fun v ↦ v z) ''
        greenFamily (⟨p, hpW⟩ : ↥(D₀.shrink t ht ht1).compl)) := by
    intro t ht ht1 p hpW z hz
    have : ConnectedSpace ↥(D₀.shrink t ht ht1).compl :=
      isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
    have : NoncompactSpace ↥(D₀.shrink t ht ht1).compl :=
      noncompactSpace_coordDisk_compl _
    exact (mharmonicOn_greenEnvelope
      (hasGreenFunction_coordDisk_compl _ p hpW)).2 z hz
  /- ## Unfolding the piece Green's function. -/
  have hPG : ∀ (P : Opens M) (p x : M) (hp' : p ∈ P) (hx' : x ∈ P),
      pieceGreen P p x = greenEnvelope (⟨p, hp'⟩ : ↥P) ⟨x, hx'⟩ := by
    intro P p x hp' hx'
    simp only [pieceGreen]
    rw [dite_eq_left (⟨hp', hx'⟩ : p ∈ P ∧ x ∈ P)]
  /- ## Zero extension of a piece family member into the surface family. -/
  have brickE : ∀ (P : Opens M), (P : Set M) ≠ Set.univ → ∀ (p : M) (hpP : p ∈ P)
      (v : ↥P → ℝ), v ∈ greenFamily (⟨p, hpP⟩ : ↥P) →
      ∃ w : M → ℝ, w ∈ greenFamily p ∧ (∀ z : ↥P, w z = v z) ∧
        ∃ Kw : Set M, IsCompact Kw ∧ Kw ⊆ (P : Set M) ∧ ∀ y, y ∉ Kw → w y = 0 := by
    intro P hPne p hpP v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y ↦ if h : y ∈ P then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥P, w z = v z := by
      intro z
      simp only [hwdef]
      rw [dite_eq_left z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (P : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ P
      · simp only [hwdef]
        rw [dite_eq_left hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dite_eq_right hyP]
    have hKwne : Kw ≠ Set.univ := by
      intro hcon
      apply hPne
      apply Set.eq_univ_of_univ_subset
      rw [← hcon]
      exact hKwsub
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ P
      · have hoe : IsOpenEmbedding (Subtype.val : ↥P → M) :=
          P.2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hpP⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥P) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥P)) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u ↦ (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥P → M) (𝓝 (⟨y, hyP⟩ : ↥P)) =
            𝓝 y := hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem ↦ hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ P
      · have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hpP⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val P w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem ↦ hyP (hKwsub hmem)) (fun z hz ↦ hKwzero z hz)
    have hwpole : ∃ C', ∀ᶠ y' in 𝓝[≠] p,
        w y' + Real.log ‖poleCoord p y'‖ ≤ C' := by
      refine ⟨C, ?_⟩
      rw [← hmapval P p hpP, Filter.eventually_map]
      filter_upwards [hC] with z hz
      have hpc : poleCoord (⟨p, hpP⟩ : ↥P) z = poleCoord p (z : M) := rfl
      rw [hwval z]
      rw [← hpc]
      exact hz
    exact ⟨w, ⟨hwsub, hwcont, ⟨Kw, hKwcomp, hKwne, hKwzero⟩, hwpole⟩, hwval,
      Kw, hKwcomp, hKwsub, hKwzero⟩
  /- ## Restriction of a compactly supported surface member into a piece. -/
  have brickR : ∀ (P : Opens M), NoncompactSpace ↥P → ∀ (p : M) (hpP : p ∈ P)
      (w : M → ℝ) (Kw : Set M),
      MSubharmonicOn w {p}ᶜ → ContinuousOn w {p}ᶜ →
      IsCompact Kw → Kw ⊆ (P : Set M) → (∀ y, y ∉ Kw → w y = 0) →
      (∃ C, ∀ᶠ y' in 𝓝[≠] p, w y' + Real.log ‖poleCoord p y'‖ ≤ C) →
      (fun z : ↥P ↦ w z) ∈ greenFamily (⟨p, hpP⟩ : ↥P) := by
    intro P hnc p hpP w Kw hwsub hwcont hKwcomp hKwsub hKwzero hwpole
    have := hnc
    have hKpre : IsCompact (Subtype.val ⁻¹' Kw : Set ↥P) := by
      have : CompactSpace ↥Kw := isCompact_iff_compactSpace.mp hKwcomp
      have himgK : (Subtype.val ⁻¹' Kw : Set ↥P) =
          (fun z : ↥Kw ↦ (⟨z.1, hKwsub z.2⟩ : ↥P)) '' Set.univ := by
        ext z
        constructor
        · intro hz
          exact ⟨⟨z.1, hz⟩, Set.mem_univ _, rfl⟩
        · rintro ⟨u, -, rfl⟩
          exact u.2
      rw [himgK]
      exact isCompact_univ.image (continuous_subtype_val.subtype_mk _)
    refine ⟨?_, ?_, ⟨Subtype.val ⁻¹' Kw, hKpre, ?_, fun z hz ↦ hKwzero z hz⟩, ?_⟩
    · intro z hz
      have hzp : (z : M) ≠ p := fun hcon ↦
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      exact (msub_val P w _ (fun _ ↦ rfl) z).mp
        (hwsub z (Set.mem_compl_singleton_iff.mpr hzp))
    · intro z hz
      have hzp : (z : M) ≠ p := fun hcon ↦
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      have h1 : ContinuousAt w (z : M) :=
        hwcont.continuousAt (isOpen_compl_singleton.mem_nhds hzp)
      exact (h1.comp continuous_subtype_val.continuousAt).continuousWithinAt
    · intro hcon
      rw [hcon] at hKpre
      exact NoncompactSpace.noncompact_univ hKpre
    · obtain ⟨C, hC⟩ := hwpole
      refine ⟨C, ?_⟩
      have h2 : ∀ᶠ y' in Filter.map (Subtype.val : ↥P → M)
          (𝓝[≠] (⟨p, hpP⟩ : ↥P)), w y' + Real.log ‖poleCoord p y'‖ ≤ C := by
        rw [hmapval P p hpP]
        exact hC
      rw [Filter.eventually_map] at h2
      filter_upwards [h2] with z hz
      have hpc : poleCoord (⟨p, hpP⟩ : ↥P) z = poleCoord p (z : M) := rfl
      rw [hpc]
      exact hz
  /- ## Nonnegativity of the piece Green's function. -/
  have hPGnonneg : ∀ (p x : M), p ∉ D₀.closedCarrier → x ∉ D₀.closedCarrier →
      x ≠ p → ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      0 ≤ pieceGreen (D₀.shrink t ht ht1).compl p x := by
    intro p x hp hx hxp t ht ht1
    have hpW := hWmem t ht ht1 hp
    have hxW := hWmem t ht ht1 hx
    rw [hPG _ p x hpW hxW]
    have hzx : (⟨x, hxW⟩ : ↥(D₀.shrink t ht ht1).compl) ≠ ⟨p, hpW⟩ :=
      fun hcon ↦ hxp (congrArg Subtype.val hcon)
    simp only [greenEnvelope]
    exact le_csSup (hEnvB t ht ht1 p hpW ⟨x, hxW⟩ hzx) ⟨_, hbaseP _ p hpW, rfl⟩
  /- ## Monotonicity of the piece Green's function under shrinking. -/
  have hPGmono : ∀ (p x : M), p ∉ D₀.closedCarrier → x ∉ D₀.closedCarrier →
      x ≠ p → ∀ t t' (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t')
      (ht1' : t' ≤ 1), t' ≤ t →
      pieceGreen (D₀.shrink t ht ht1).compl p x ≤
        pieceGreen (D₀.shrink t' ht' ht1').compl p x := by
    intro p x hp hx hxp t t' ht ht1 ht' ht1' htt
    have hpW := hWmem t ht ht1 hp
    have hxW := hWmem t ht ht1 hx
    have hpW' := hWmem t' ht' ht1' hp
    have hxW' := hWmem t' ht' ht1' hx
    rw [hPG _ p x hpW hxW, hPG _ p x hpW' hxW']
    simp only [greenEnvelope]
    have hzx' : (⟨x, hxW'⟩ : ↥(D₀.shrink t' ht' ht1').compl) ≠ ⟨p, hpW'⟩ :=
      fun hcon ↦ hxp (congrArg Subtype.val hcon)
    refine Real.sSup_le ?_ ?_
    · rintro a ⟨v, hv, rfl⟩
      obtain ⟨w, hwfam, hwval, Kw, hKwc, hKws, hKw0⟩ :=
        brickE _ (hWne t ht ht1) p hpW v hv
      have hwmem' : (fun z : ↥(D₀.shrink t' ht' ht1').compl ↦ w z) ∈
          greenFamily (⟨p, hpW'⟩ : ↥(D₀.shrink t' ht' ht1').compl) :=
        brickR _ (noncompactSpace_coordDisk_compl _) p hpW' w Kw hwfam.1
          hwfam.2.1 hKwc (hKws.trans (hWsub t t' ht ht1 ht' ht1' htt)) hKw0
          hwfam.2.2.2
      have h4 : v ⟨x, hxW⟩ = w x := (hwval ⟨x, hxW⟩).symm
      exact (le_of_eq h4).trans
        (le_csSup (hEnvB t' ht' ht1' p hpW' ⟨x, hxW'⟩ hzx') ⟨_, hwmem', rfl⟩)
    · exact le_csSup (hEnvB t' ht' ht1' p hpW' ⟨x, hxW'⟩ hzx')
        ⟨_, hbaseP _ p hpW', rfl⟩
  /- ## Hyperbolic bound: the ambient envelope dominates every piece. -/
  have hPGle : ∀ (p x : M), p ∉ D₀.closedCarrier → x ∉ D₀.closedCarrier →
      BddAbove ((fun v ↦ v x) '' greenFamily p) →
      ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      pieceGreen (D₀.shrink t ht ht1).compl p x ≤ greenEnvelope p x := by
    intro p x hp hx hbdd t ht ht1
    have hpW := hWmem t ht ht1 hp
    have hxW := hWmem t ht ht1 hx
    rw [hPG _ p x hpW hxW]
    simp only [greenEnvelope]
    refine Real.sSup_le ?_ ?_
    · rintro a ⟨v, hv, rfl⟩
      obtain ⟨w, hwfam, hwval, -⟩ := brickE _ (hWne t ht ht1) p hpW v hv
      have h4 : v ⟨x, hxW⟩ = w x := (hwval ⟨x, hxW⟩).symm
      exact (le_of_eq h4).trans (le_csSup hbdd ⟨w, hwfam, rfl⟩)
    · exact le_csSup hbdd ⟨_, hbaseM p, rfl⟩
  /- ## The monotone tail: a small-shrink bound propagates to all shrinks. -/
  have tail : (∃ t₀ C₀, 0 < t₀ ∧ t₀ ≤ 1 ∧ ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      t ≤ t₀ → |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
        pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C₀) →
      ∃ C, ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
        |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
          pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C := by
    rintro ⟨t₀, C₀, ht₀, ht₀1, hC₀⟩
    refine ⟨max C₀ (pieceGreen (D₀.shrink t₀ ht₀ ht₀1).compl p₁ p₃ +
      pieceGreen (D₀.shrink t₀ ht₀ ht₀1).compl p₂ p₃), fun t ht ht1 ↦ ?_⟩
    rcases le_total t t₀ with h | h
    · exact (hC₀ t ht ht1 h).trans (le_max_left _ _)
    · have m1 := hPGmono p₁ p₃ hp₁ hp₃ h₃₁ t t₀ ht ht1 ht₀ ht₀1 h
      have m2 := hPGmono p₂ p₃ hp₂ hp₃ h₃₂ t t₀ ht ht1 ht₀ ht₀1 h
      have n1 := hPGnonneg p₁ p₃ hp₁ hp₃ h₃₁ t ht ht1
      have n2 := hPGnonneg p₂ p₃ hp₂ hp₃ h₃₂ t ht ht1
      have n1' := hPGnonneg p₁ p₃ hp₁ hp₃ h₃₁ t₀ ht₀ ht₀1
      have n2' := hPGnonneg p₂ p₃ hp₂ hp₃ h₃₂ t₀ ht₀ ht₀1
      refine le_trans ?_ (le_max_right _ _)
      rw [abs_sub_le_iff]
      constructor
      · linarith
      · linarith
  /- ## Assembly: dichotomy on the ambient boundedness at the base point. -/
  by_cases hb : BddAbove ((fun v ↦ v p₃) '' greenFamily p₁) ∧
      BddAbove ((fun v ↦ v p₃) '' greenFamily p₂)
  · -- Ambient-hyperbolic regime: both piece families are dominated, at the
    -- base point, by the corresponding ambient envelopes.
    refine ⟨greenEnvelope p₁ p₃ + greenEnvelope p₂ p₃, fun t ht ht1 ↦ ?_⟩
    have h1 := hPGle p₁ p₃ hp₁ hp₃ hb.1 t ht ht1
    have h2 := hPGle p₂ p₃ hp₂ hp₃ hb.2 t ht ht1
    have h3 := hPGnonneg p₁ p₃ hp₁ hp₃ h₃₁ t ht ht1
    have h4 := hPGnonneg p₂ p₃ hp₂ hp₃ h₃₂ t ht ht1
    rw [abs_sub_le_iff]
    constructor
    · linarith
    · linarith
  · -- RESIDUAL CORE (the C-SYM wall): the ambient Perron family is unbounded
    -- at `p₃` for at least one of the two poles (the non-hyperbolic regime,
    -- covering compact `M` and ambient-parabolic noncompact `M`); both piece
    -- Green's functions then increase to `+∞` at `p₃` along the exhaustion,
    -- and the shrink-uniform boundedness of their difference for SMALL shrink
    -- parameters is the genuine content of approximate Green symmetry
    -- (`|M₁(t) − M₂(t)| = O(1)`, capacity additivity of the Robin heights).
    -- No soft (Harnack/monotonicity/per-candidate) argument can close it; it
    -- requires either a surface Green-identity (Stokes/flux on chart annuli)
    -- or the universal-cover transfer.
    exact tail (exists_pieceGreen_drift_bound_core D₀ hp₁ hp₂ hp₃ hne h₃₁ h₃₂)

end RiemannDynamics
