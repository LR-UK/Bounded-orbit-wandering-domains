/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.Injective

/-!
# Bipolar Green: the compact case and the non-hyperbolic assembly

Compact surfaces carry no Green's function
(`not_bddAbove_image_greenFamily_of_compactSpace`), and the bricks of the
bipolar Green construction assemble to the non-hyperbolic case of the
planarity theorem
(`exists_diffeomorph_opens_of_forall_not_hasGreenFunction`): a simply
connected surface without a Green's function at any point is holomorphically
diffeomorphic to a domain of the sphere.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

/-! ### The compact case and the non-hyperbolic assembly -/

/-- **Compact surfaces carry no Green's function**: the Perron family is
unbounded at every point distinct from the pole. -/
theorem not_bddAbove_image_greenFamily_of_compactSpace [CompactSpace M]
    (p₀ x : M) (hx : x ≠ p₀) :
    ¬ BddAbove ((fun v ↦ v x) '' greenFamily p₀) := by
  classical
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  intro hbdd
  obtain ⟨s, hs⟩ := hbdd
  set B' : ℝ := max s 0 with hB'
  have hB'0 : (0 : ℝ) ≤ B' := le_max_right _ _
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
    have hne : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hne := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hne]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hne).target := e'.map_subtype_source hne hzsrc
    have heqOn : Set.EqOn (⇑e'.symm) (Subtype.val ∘ ⇑(e'.subtypeRestr hne).symm)
        (e'.subtypeRestr hne).target := e'.subtypeRestr_symm_eqOn hne
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hne).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hne).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈ (e'.subtypeRestr hne).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw ↦ (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw ↦ (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hne).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hne), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hne).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to the punctured filter of the surface. -/
  have hmapval : ∀ (P : Opens M) (hpP : p₀ ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p₀, hpP⟩ : ↥P)) = 𝓝[≠] p₀ := by
    intro P hpP
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
      · have h4 : (⟨p₀, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀eq]; exact
          hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p₀, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## An auxiliary point distinct from the pole and the test point. -/
  obtain ⟨q, hqp, hqx⟩ : ∃ q : M, q ≠ p₀ ∧ q ≠ x := by
    set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he₀
    have hsrc₀ : p₀ ∈ e₀.source := mem_chart_source ℂ p₀
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp e₀.open_target (e₀ p₀) (e₀.map_source hsrc₀)
    have hmem : ∀ t : ℝ, 0 < t → t < ε → e₀ p₀ + (t : ℂ) ∈ e₀.target := by
      intro t' ht0' htε'
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg ht0'.le]
      exact htε'
    have hyne : ∀ t : ℝ, 0 < t → t < ε → e₀.symm (e₀ p₀ + (t : ℂ)) ≠ p₀ := by
      intro t' ht0' htε' hcon
      have h1 : e₀ (e₀.symm (e₀ p₀ + (t' : ℂ))) = e₀ p₀ + (t' : ℂ) :=
        e₀.right_inv (hmem t' ht0' htε')
      rw [hcon] at h1
      have h2 : e₀ p₀ + (t' : ℂ) = e₀ p₀ + 0 := by rw [add_zero]; exact h1.symm
      have h3 : (t' : ℂ) = 0 := add_left_cancel h2
      rw [Complex.ofReal_eq_zero] at h3
      exact ht0'.ne' h3
    have h₁ : (0 : ℝ) < ε / 2 := by linarith
    have h₂ : ε / 2 < ε := by linarith
    have h₃ : (0 : ℝ) < ε / 4 := by linarith
    have h₄ : ε / 4 < ε := by linarith
    by_contra hcon
    have hy1 : e₀.symm (e₀ p₀ + ((ε / 2 : ℝ) : ℂ)) = x := by
      by_contra hne
      exact hcon ⟨_, hyne _ h₁ h₂, hne⟩
    have hy2 : e₀.symm (e₀ p₀ + ((ε / 4 : ℝ) : ℂ)) = x := by
      by_contra hne
      exact hcon ⟨_, hyne _ h₃ h₄, hne⟩
    have h5 := congrArg (⇑e₀) (hy1.trans hy2.symm)
    rw [e₀.right_inv (hmem _ h₁ h₂), e₀.right_inv (hmem _ h₃ h₄)] at h5
    have h6 : ((ε / 2 : ℝ) : ℂ) = ((ε / 4 : ℝ) : ℂ) := add_left_cancel h5
    rw [Complex.ofReal_inj] at h6
    linarith
  /- ## The auxiliary coordinate disk avoiding the pole and the test point. -/
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ q with he
  have hqsrc : q ∈ e.source := mem_chart_source ℂ q
  have hUopen : IsOpen (e.target ∩ e.symm ⁻¹' ({p₀}ᶜ ∩ {x}ᶜ)) :=
    e.isOpen_inter_preimage_symm (isOpen_compl_singleton.inter isOpen_compl_singleton)
  have hqU : e q ∈ e.target ∩ e.symm ⁻¹' ({p₀}ᶜ ∩ {x}ᶜ) := by
    refine ⟨e.map_source hqsrc, ?_⟩
    rw [Set.mem_preimage, e.left_inv hqsrc]
    exact ⟨Set.mem_compl_singleton_iff.mpr hqp, Set.mem_compl_singleton_iff.mpr hqx⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hUopen _ hqU
  set r : ℝ := εa / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrsub : closedBall (e q) r ⊆ e.target ∩ e.symm ⁻¹' ({p₀}ᶜ ∩ {x}ᶜ) :=
    (Metric.closedBall_subset_ball (by rw [hrdef]; linarith)).trans hballa
  set D : CoordDisk M := ⟨q, r, hr0, fun w hw ↦ (hrsub hw).1⟩ with hD
  have hDcar : D.closedCarrier = e.symm '' closedBall (e q) r := rfl
  have hDavoid : ∀ y ∈ D.closedCarrier, y ≠ p₀ ∧ y ≠ x := by
    rintro y ⟨w, hw, rfl⟩
    have h2 := (hrsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨Set.mem_compl_singleton_iff.mp h2.1, Set.mem_compl_singleton_iff.mp h2.2⟩
  have hqD : q ∈ D.closedCarrier := ⟨e q, mem_closedBall_self hr0.le, e.left_inv hqsrc⟩
  have hxq : x ≠ q := fun hcon ↦ (hDavoid q hqD).2 hcon.symm
  /- ## The shrinking pieces. -/
  set t : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 2) with ht
  have ht0 : ∀ n, 0 < t n := fun n ↦ by rw [ht]; positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n ↦ pow_le_one₀ (by norm_num) (by norm_num)
  have htq : ∀ n, t n ≤ 1 / 4 := by
    intro n
    calc t n = (1 / 2 : ℝ) ^ (n + 2) := rfl
      _ ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have htanti : ∀ n m, n ≤ m → t m ≤ t n := fun n m h ↦
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htlim : ∀ δ : ℝ, 0 < δ → ∃ n, t n < δ := by
    intro δ hδ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn⟩
  set DN : ℕ → CoordDisk M := fun n ↦ D.shrink (t n) (ht0 n) (ht1 n) with hDN
  set Wp : ℕ → Opens M := fun n ↦ (DN n).compl with hWp
  have hcarN : ∀ n, (DN n).closedCarrier = e.symm '' closedBall (e q) (t n * r) :=
    fun n ↦ rfl
  have hcarNsub : ∀ n, (DN n).closedCarrier ⊆ D.closedCarrier := by
    intro n
    rw [hcarN n, hDcar]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr0.le (ht1 n)))
  have hcarmono : ∀ n m, n ≤ m → (DN m).closedCarrier ⊆ (DN n).closedCarrier := by
    intro n m hnm
    rw [hcarN n, hcarN m]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (htanti n m hnm) hr0.le))
  have hp₀W : ∀ n, p₀ ∈ Wp n := fun n hmem ↦ (hDavoid p₀ (hcarNsub n hmem)).1 rfl
  have hxW : ∀ n, x ∈ Wp n := fun n hmem ↦ (hDavoid x (hcarNsub n hmem)).2 rfl
  have hqW : ∀ n, q ∉ (Wp n : Set M) := by
    intro n hmem
    exact hmem ⟨e q, mem_closedBall_self (mul_pos (ht0 n) hr0).le, e.left_inv hqsrc⟩
  have hWmono : ∀ n m, n ≤ m → (Wp n : Set M) ⊆ (Wp m : Set M) :=
    fun n m hnm y hy hmem ↦ hy (hcarmono n m hnm hmem)
  have hWexh : ∀ y : M, y ≠ q → ∃ n, y ∈ Wp n := by
    intro y hyq
    by_cases hysrc : y ∈ e.source
    · have hne2 : e y ≠ e q := fun hcon ↦ hyq (e.injOn hysrc hqsrc hcon)
      have hd : 0 < ‖e y - e q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne2)
      obtain ⟨n, hn⟩ := htlim (‖e y - e q‖ / r) (by positivity)
      refine ⟨n, fun hmem ↦ ?_⟩
      rw [hcarN n] at hmem
      obtain ⟨w, hw, hwy⟩ := hmem
      have hwt : w ∈ e.target := D.closedBall_subset
        (closedBall_subset_closedBall (mul_le_of_le_one_left hr0.le (ht1 n)) hw)
      have h1 : e y = w := by rw [← hwy, e.right_inv hwt]
      rw [mem_closedBall, dist_eq_norm, ← h1] at hw
      have h2 : t n * r < ‖e y - e q‖ :=
        calc t n * r < ‖e y - e q‖ / r * r := mul_lt_mul_of_pos_right hn hr0
          _ = ‖e y - e q‖ := div_mul_cancel₀ _ hr0.ne'
      linarith
    · refine ⟨0, fun hmem ↦ hysrc ?_⟩
      rw [hcarN 0] at hmem
      obtain ⟨w, hw, hwy⟩ := hmem
      rw [← hwy]
      exact e.map_target (D.closedBall_subset
        (closedBall_subset_closedBall (mul_le_of_le_one_left hr0.le (ht1 0)) hw))
  /- ## Instances and Green data on the pieces. -/
  have hConnW : ∀ n, ConnectedSpace ↥(Wp n) := fun n ↦
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl (DN n))
  have hNcW : ∀ n, NoncompactSpace ↥(Wp n) := fun n ↦ noncompactSpace_coordDisk_compl (DN n)
  have hGF : ∀ n, HasGreenFunction (⟨p₀, hp₀W n⟩ : ↥(Wp n)) := fun n ↦
    hasGreenFunction_coordDisk_compl (DN n) p₀ (hp₀W n)
  have hEnvH : ∀ n, MHarmonicOn (greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)))
      ({(⟨p₀, hp₀W n⟩ : ↥(Wp n))}ᶜ) ∧
      ∀ z : ↥(Wp n), z ≠ ⟨p₀, hp₀W n⟩ →
        BddAbove ((fun v ↦ v z) '' greenFamily (⟨p₀, hp₀W n⟩ : ↥(Wp n))) := by
    intro n
    have := hConnW n
    have := hNcW n
    exact ⟨(mharmonicOn_greenEnvelope (hGF n)).1,
      fun z hz ↦ (mharmonicOn_greenEnvelope (hGF n)).2 z hz⟩
  have hEnvPos : ∀ n (z : ↥(Wp n)), z ≠ ⟨p₀, hp₀W n⟩ →
      0 < greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)) z := by
    intro n
    have := hConnW n
    have := hNcW n
    exact greenEnvelope_pos (hGF n)
  /- ## The piece Green's functions read on the surface. -/
  set V : ℕ → M → ℝ := fun n y ↦
    if h : y ∈ Wp n then greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)) ⟨y, h⟩ else 0 with
        hV
  have hVmem : ∀ n (y : M) (h : y ∈ Wp n),
      V n y = greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)) ⟨y, h⟩ := by
    intro n y h
    simp only [hV]
    rw [dite_eq_left h]
  have hVzero : ∀ n (y : M), y ∉ Wp n → V n y = 0 := by
    intro n y h
    simp only [hV]
    rw [dite_eq_right h]
  /- ## Zero extension of a piece family member into the surface family. -/
  have brickE : ∀ n (v : ↥(Wp n) → ℝ), v ∈ greenFamily (⟨p₀, hp₀W n⟩ : ↥(Wp n))
      →
      ∃ w : M → ℝ, w ∈ greenFamily p₀ ∧ (∀ z : ↥(Wp n), w z = v z) ∧
        ∃ Kw : Set M, IsCompact Kw ∧ Kw ⊆ (Wp n : Set M) ∧ ∀ y, y ∉ Kw → w y = 0 := by
    intro n v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y ↦ if h : y ∈ Wp n then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥(Wp n), w z = v z := by
      intro z
      simp only [hwdef]
      rw [dite_eq_left z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (Wp n : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ Wp n
      · simp only [hwdef]
        rw [dite_eq_left hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dite_eq_right hyP]
    have hKwne : Kw ≠ Set.univ := by
      intro hcon
      have h1 : q ∈ Kw := by rw [hcon]; trivial
      exact hqW n (hKwsub h1)
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p₀}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ Wp n
      · have hoe : IsOpenEmbedding (Subtype.val : ↥(Wp n) → M) :=
          (Wp n).2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥(Wp n)) ≠ ⟨p₀, hp₀W n⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥(Wp n)) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥(Wp n))) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u ↦ (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥(Wp n) → M) (𝓝 (⟨y, hyP⟩ : ↥(Wp n))) =
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
    have hwsub : MSubharmonicOn w {p₀}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ Wp n
      · have hnz : (⟨y, hyP⟩ : ↥(Wp n)) ≠ ⟨p₀, hp₀W n⟩ := fun hcon ↦
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val (Wp n) w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem ↦ hyP (hKwsub hmem)) (fun z hz ↦ hKwzero z hz)
    have hwpole : ∃ C', ∀ᶠ y' in 𝓝[≠] p₀, w y' + Real.log ‖poleCoord p₀ y'‖ ≤
        C' := by
      refine ⟨C, ?_⟩
      rw [← hmapval (Wp n) (hp₀W n), Filter.eventually_map]
      filter_upwards [hC] with z hz
      have hpc : poleCoord (⟨p₀, hp₀W n⟩ : ↥(Wp n)) z = poleCoord p₀ (z : M) := rfl
      rw [hwval z]
      rw [← hpc]
      exact hz
    exact ⟨w, ⟨hwsub, hwcont, ⟨Kw, hKwcomp, hKwne, hKwzero⟩, hwpole⟩, hwval,
      Kw, hKwcomp, hKwsub, hKwzero⟩
  /- ## Restriction of a compactly supported surface member into a piece family. -/
  have brickR : ∀ m (w : M → ℝ) (Kw : Set M),
      MSubharmonicOn w {p₀}ᶜ → ContinuousOn w {p₀}ᶜ →
      IsCompact Kw → Kw ⊆ (Wp m : Set M) → (∀ y, y ∉ Kw → w y = 0) →
      (∃ C, ∀ᶠ y' in 𝓝[≠] p₀, w y' + Real.log ‖poleCoord p₀ y'‖ ≤ C) →
      (fun z : ↥(Wp m) ↦ w z) ∈ greenFamily (⟨p₀, hp₀W m⟩ : ↥(Wp m)) := by
    intro m w Kw hwsub hwcont hKwcomp hKwsub hKwzero hwpole
    have := hNcW m
    have hKpre : IsCompact (Subtype.val ⁻¹' Kw : Set ↥(Wp m)) := by
      have : CompactSpace ↥Kw := isCompact_iff_compactSpace.mp hKwcomp
      have himgK : (Subtype.val ⁻¹' Kw : Set ↥(Wp m)) =
          (fun z : ↥Kw ↦ (⟨z.1, hKwsub z.2⟩ : ↥(Wp m))) '' Set.univ := by
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
      have hzp : (z : M) ≠ p₀ := fun hcon ↦
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      exact (msub_val (Wp m) w _ (fun _ ↦ rfl) z).mp
        (hwsub z (Set.mem_compl_singleton_iff.mpr hzp))
    · intro z hz
      have hzp : (z : M) ≠ p₀ := fun hcon ↦
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      have h1 : ContinuousAt w (z : M) :=
        hwcont.continuousAt (isOpen_compl_singleton.mem_nhds hzp)
      exact (h1.comp continuous_subtype_val.continuousAt).continuousWithinAt
    · intro hcon
      rw [hcon] at hKpre
      exact NoncompactSpace.noncompact_univ hKpre
    · obtain ⟨C, hC⟩ := hwpole
      refine ⟨C, ?_⟩
      have h2 : ∀ᶠ y' in Filter.map (Subtype.val : ↥(Wp m) → M)
          (𝓝[≠] (⟨p₀, hp₀W m⟩ : ↥(Wp m))), w y' + Real.log ‖poleCoord p₀ y'‖
              ≤ C := by
        rw [hmapval (Wp m) (hp₀W m)]
        exact hC
      rw [Filter.eventually_map] at h2
      filter_upwards [h2] with z hz
      have hpc : poleCoord (⟨p₀, hp₀W m⟩ : ↥(Wp m)) z = poleCoord p₀ (z : M) := rfl
      rw [hpc]
      exact hz
  /- ## Boundedness at the test point, positivity, monotonicity of the `V n`. -/
  have hVx : ∀ n, V n x ≤ B' := by
    intro n
    rw [hVmem n x (hxW n)]
    simp only [greenEnvelope]
    refine Real.sSup_le ?_ hB'0
    rintro a ⟨v, hvmem, rfl⟩
    obtain ⟨w, hwfam, hwval, -⟩ := brickE n v hvmem
    have h1 : w x ∈ (fun v ↦ v x) '' greenFamily p₀ := ⟨w, hwfam, rfl⟩
    have h2 : w x ≤ s := hs h1
    have h3 : w x = v ⟨x, hxW n⟩ := hwval ⟨x, hxW n⟩
    exact (le_of_eq h3.symm).trans (h2.trans (le_max_left s 0))
  have hVnonneg : ∀ n (y : M), y ≠ p₀ → 0 ≤ V n y := by
    intro n y hy
    by_cases hyP : y ∈ Wp n
    · rw [hVmem n y hyP]
      exact (hEnvPos n ⟨y, hyP⟩ (fun hcon ↦ hy (congrArg Subtype.val hcon))).le
    · rw [hVzero n y hyP]
  have hVmono : ∀ (y : M), y ≠ p₀ → Monotone fun n ↦ V n y := by
    intro y hy n m hnm
    simp only
    by_cases hyn : y ∈ Wp n
    · have hym : y ∈ Wp m := hWmono n m hnm hyn
      rw [hVmem n y hyn, hVmem m y hym]
      simp only [greenEnvelope]
      refine Real.sSup_le ?_ ?_
      · rintro a ⟨v, hvmem, rfl⟩
        obtain ⟨w, hwfam, hwval, Kw, hKwc, hKws, hKw0⟩ := brickE n v hvmem
        have hwmem' : (fun z : ↥(Wp m) ↦ w z) ∈ greenFamily (⟨p₀, hp₀W m⟩ : ↥(Wp m))
            :=
          brickR m w Kw hwfam.1 hwfam.2.1 hKwc (hKws.trans (hWmono n m hnm)) hKw0
            hwfam.2.2.2
        have h4 : v ⟨y, hyn⟩ = (fun z : ↥(Wp m) ↦ w z) ⟨y, hym⟩ := (hwval ⟨y,
            hyn⟩).symm
        exact (le_of_eq h4).trans (le_csSup ((hEnvH m).2 ⟨y, hym⟩
          (fun hcon ↦ hy (congrArg Subtype.val hcon))) ⟨_, hwmem', rfl⟩)
      · exact (hEnvPos m ⟨y, hym⟩ (fun hcon ↦ hy (congrArg Subtype.val hcon))).le
    · rw [hVzero n y hyn]
      exact hVnonneg m y hy
  /- ## The monotone limit is harmonic away from the pole and the auxiliary point. -/
  set gs : M → ℝ := fun y ↦ ⨆ n, V n y with hgs
  have hblock : ∀ (n₀ : ℕ) (y : M), y ∈ Wp n₀ → y ≠ p₀ →
      MHarmonicAt gs y ∧ ∀ n, V n y ≤ gs y := by
    intro n₀
    set Ω : Opens M := ⟨(Wp n₀ : Set M) ∩ {p₀}ᶜ,
      (Wp n₀).2.inter isOpen_compl_singleton⟩ with hΩ
    have := hConnW n₀
    have hnt : ∃ a b : ↥(Wp n₀), a ≠ b :=
      ⟨⟨x, hxW n₀⟩, ⟨p₀, hp₀W n₀⟩, fun hcon ↦ hx (congrArg Subtype.val hcon)⟩
    have hpcn : IsConnected ({(⟨p₀, hp₀W n₀⟩ : ↥(Wp n₀))}ᶜ : Set ↥(Wp n₀)) :=
      isConnected_compl_singleton_of_connected hnt _
    have himgc : Subtype.val '' ({(⟨p₀, hp₀W n₀⟩ : ↥(Wp n₀))}ᶜ : Set ↥(Wp n₀)) =
        (Wp n₀ : Set M) ∩ {p₀}ᶜ := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z.2, ?_⟩
        intro hcon
        rw [Set.mem_singleton_iff] at hcon
        exact (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      · rintro ⟨hyP, hyne⟩
        refine ⟨⟨y, hyP⟩, ?_, rfl⟩
        intro hcon
        rw [Set.mem_singleton_iff] at hcon
        exact hyne (congrArg Subtype.val hcon)
    have hΩconn : IsConnected ((Wp n₀ : Set M) ∩ {p₀}ᶜ) := by
      rw [← himgc]
      exact hpcn.image _ continuous_subtype_val.continuousOn
    have hΩcs : ConnectedSpace ↥Ω := isConnected_iff_connectedSpace.mp hΩconn
    have hzW : ∀ (k : ℕ) (z : ↥Ω), (z : M) ∈ Wp (n₀ + k) :=
      fun k z ↦ hWmono n₀ (n₀ + k) (Nat.le_add_right n₀ k) z.2.1
    have hznp : ∀ z : ↥Ω, (z : M) ≠ p₀ := fun z ↦ z.2.2
    have hVharmAt : ∀ (k : ℕ) (y : M) (h1 : y ∈ Wp (n₀ + k)), y ≠ p₀ →
        MHarmonicAt (V (n₀ + k)) y := by
      intro k y h1 hyp
      have h2 : MHarmonicAt (greenEnvelope (⟨p₀, hp₀W (n₀ + k)⟩ : ↥(Wp (n₀ + k))))
          (⟨y, h1⟩ : ↥(Wp (n₀ + k))) := by
        apply (hEnvH (n₀ + k)).1
        exact Set.mem_compl_singleton_iff.mpr
          (fun hcon ↦ hyp (congrArg Subtype.val hcon))
      exact (mharm_val (Wp (n₀ + k)) (V (n₀ + k)) _
        (fun u ↦ hVmem (n₀ + k) u u.2) ⟨y, h1⟩).mpr h2
    have hV'harm : ∀ k, MHarmonicOn (fun z : ↥Ω ↦ V (n₀ + k) (z : M)) Set.univ := by
      intro k z _
      exact (mharm_val Ω (V (n₀ + k)) _ (fun _ ↦ rfl) z).mp
        (hVharmAt k z (hzW k z) (hznp z))
    have hV'mono : ∀ z : ↥Ω, Monotone fun k ↦ V (n₀ + k) (z : M) :=
      fun z k k' hkk' ↦ hVmono (z : M) (hznp z) (Nat.add_le_add_left hkk' n₀)
    rcases mharmonic_dichotomy_of_monotone hV'harm hV'mono with hup | hlim
    · exfalso
      have hxΩ : x ∈ (Wp n₀ : Set M) ∩ {p₀}ᶜ :=
        ⟨hxW n₀, Set.mem_compl_singleton_iff.mpr hx⟩
      have h5 := (hup ⟨x, hxΩ⟩).eventually_gt_atTop B'
      obtain ⟨k, hk⟩ := h5.exists
      exact absurd (hVx (n₀ + k)) (not_le.mpr hk)
    · obtain ⟨VL, hVLharm, hVLtend⟩ := hlim
      have hid : ∀ z : ↥Ω, gs (z : M) = VL z ∧ ∀ n, V n (z : M) ≤ VL z := by
        intro z
        have hmonoz : Monotone fun n ↦ V n (z : M) := hVmono _ (hznp z)
        have htail : ∀ k, V (n₀ + k) (z : M) ≤ VL z :=
          fun k ↦ (hV'mono z).ge_of_tendsto (hVLtend z) k
        have hall : ∀ n, V n (z : M) ≤ VL z := fun n ↦
          (hmonoz (Nat.le_add_left n n₀)).trans (htail n)
        have hbdd2 : BddAbove (Set.range fun n ↦ V n (z : M)) := by
          refine ⟨VL z, ?_⟩
          rintro a ⟨n, rfl⟩
          exact hall n
        have htends : Tendsto (fun n ↦ V n (z : M)) atTop (𝓝 (⨆ n, V n (z : M))) :=
          tendsto_atTop_ciSup hmonoz hbdd2
        have hcomp : Tendsto (fun k ↦ V (n₀ + k) (z : M)) atTop
            (𝓝 (⨆ n, V n (z : M))) := by
          have h6 : Tendsto (fun k : ℕ ↦ k + n₀) atTop atTop := tendsto_add_atTop_nat n₀
          have h7 := htends.comp h6
          have h8 : ((fun n ↦ V n (z : M)) ∘ fun k : ℕ ↦ k + n₀) =
              fun k ↦ V (n₀ + k) (z : M) := by
            funext k
            simp only [Function.comp_apply, Nat.add_comm]
          rwa [h8] at h7
        have h9 : VL z = ⨆ n, V n (z : M) := tendsto_nhds_unique (hVLtend z) hcomp
        exact ⟨h9.symm, hall⟩
      intro y hyW hyp
      have hyΩ : y ∈ (Wp n₀ : Set M) ∩ {p₀}ᶜ := ⟨hyW, Set.mem_compl_singleton_iff.mpr
          hyp⟩
      constructor
      · exact (mharm_val Ω gs VL (fun u ↦ (hid u).1) ⟨y, hyΩ⟩).mpr
          (hVLharm ⟨y, hyΩ⟩ (Set.mem_univ _))
      · intro n
        exact le_of_le_of_eq ((hid ⟨y, hyΩ⟩).2 n) ((hid ⟨y, hyΩ⟩).1).symm
  have hgs_all : ∀ y : M, y ≠ p₀ → y ≠ q → MHarmonicAt gs y ∧ ∀ n, V n y ≤ gs y := by
    intro y hyp hyq
    obtain ⟨n₀, hn₀⟩ := hWexh y hyq
    exact hblock n₀ y hn₀ hyp
  have hgs_nonneg : ∀ y : M, y ≠ p₀ → y ≠ q → 0 ≤ gs y :=
    fun y hyp hyq ↦ (hVnonneg 0 y hyp).trans ((hgs_all y hyp hyq).2 0)
  have hgs_x : gs x ≤ B' := ciSup_le fun n ↦ hVx n
  /- ## The uniform bound near the auxiliary point, via the annulus maximum principle. -/
  set ρ : ℝ := r / 2 with hρdef
  have hρ0 : 0 < ρ := half_pos hr0
  have hρr : ρ < r := half_lt_self hr0
  have hcballρ : closedBall (e q) ρ ⊆ e.target :=
    (closedBall_subset_closedBall hρr.le).trans D.closedBall_subset
  have hballρ : ball (e q) ρ ⊆ e.target := ball_subset_closedBall.trans hcballρ
  set Bimg : Set M := e.symm '' ball (e q) ρ with hBimg
  have hBopen : IsOpen Bimg := by
    rw [hBimg, himg e _ hballρ]
    exact e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hBsub : Bimg ⊆ D.closedCarrier := by
    rw [hBimg, hDcar]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall hρr.le))
  have hqB : q ∈ Bimg := ⟨e q, mem_ball_self hρ0, e.left_inv hqsrc⟩
  set Dρ : Set M := e.symm '' closedBall (e q) ρ with hDρ
  have hDρcl : IsClosed Dρ := ((isCompact_closedBall _ _).image_of_continuousOn
    (e.continuousOn_symm.mono hcballρ)).isClosed
  have hBDρ : Bimg ⊆ Dρ := by
    rw [hBimg, hDρ]
    exact Set.image_mono ball_subset_closedBall
  set S : Set M := e.symm '' sphere (e q) ρ with hSdef
  have hScomp : IsCompact S := (isCompact_sphere _ _).image_of_continuousOn
    (e.continuousOn_symm.mono (sphere_subset_closedBall.trans hcballρ))
  have hSne : S.Nonempty := (NormedSpace.sphere_nonempty.mpr hρ0.le).image _
  have hSsub : S ⊆ D.closedCarrier := by
    rw [hSdef, hDcar]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall hρr.le))
  have hSq : ∀ y ∈ S, y ≠ q := by
    rintro y ⟨w, hw, rfl⟩ hcon
    have hwt : w ∈ e.target := hcballρ (sphere_subset_closedBall hw)
    have h1 : e (e.symm w) = w := e.right_inv hwt
    rw [hcon] at h1
    rw [mem_sphere] at hw
    rw [← h1, dist_self] at hw
    exact hρ0.ne hw
  have hSp₀ : ∀ y ∈ S, y ≠ p₀ := fun y hy ↦ (hDavoid y (hSsub hy)).1
  have hSW : ∀ n, S ⊆ (Wp n : Set M) := by
    intro n
    rintro y ⟨w, hw, rfl⟩ hmem
    rw [hcarN n] at hmem
    obtain ⟨w', hw', hww'⟩ := hmem
    have hwt : w ∈ e.target := hcballρ (sphere_subset_closedBall hw)
    have hw't : w' ∈ e.target := D.closedBall_subset
      (closedBall_subset_closedBall (mul_le_of_le_one_left hr0.le (ht1 n)) hw')
    have heq2 : w' = w := e.symm.injOn (by rw [e.symm_source]; exact hw't)
      (by rw [e.symm_source]; exact hwt) hww'
    rw [mem_sphere] at hw
    rw [mem_closedBall, heq2, hw] at hw'
    have h3 : t n * r ≤ r / 4 := by
      have := mul_le_mul_of_nonneg_right (htq n) hr0.le
      linarith
    rw [hρdef] at hw'
    linarith
  have hgsScont : ContinuousOn gs S := fun y hy ↦
    ((hgs_all y (hSp₀ y hy) (hSq y hy)).1.continuousAt).continuousWithinAt
  obtain ⟨yS, hySmem, hySmax⟩ := hScomp.exists_isMaxOn hSne hgsScont
  set B₀ : ℝ := max (gs yS) 0 with hB₀
  have hB₀0 : (0 : ℝ) ≤ B₀ := le_max_right _ _
  have hVann : ∀ n (y : M), y ∈ Bimg → y ∈ Wp n → V n y ≤ B₀ := by
    intro n y₀ hy₀B hy₀W
    rw [hVmem n y₀ hy₀W]
    simp only [greenEnvelope]
    refine Real.sSup_le ?_ hB₀0
    rintro a ⟨v, hvmem, rfl⟩
    obtain ⟨w, hwfam, hwval, Kw, hKwc, hKws, hKw0⟩ := brickE n v hvmem
    set A : Set M := Bimg \ (DN n).closedCarrier with hA
    have hAopen : IsOpen A := hBopen.sdiff (DN n).isCompact_closedCarrier.isClosed
    have hAp₀ : p₀ ∉ A := fun hmem ↦ (hDavoid p₀ (hBsub hmem.1)).1 rfl
    have hAne : A ≠ Set.univ := fun hcon ↦ hAp₀ (hcon ▸ Set.mem_univ p₀)
    have hAsubp : A ⊆ ({p₀}ᶜ : Set M) := fun z hz ↦
      Set.mem_compl_singleton_iff.mpr (hDavoid z (hBsub hz.1)).1
    have hfr : ∀ z ∈ closure A \ A, ContinuousAt w z ∧ w z ≤ B₀ := by
      rintro z ⟨hzc, hzA⟩
      have hzD : z ∈ Dρ := hDρcl.closure_subset_iff.mpr
        (fun u hu ↦ hBDρ hu.1) hzc
      by_cases hzcar : z ∈ (DN n).closedCarrier
      · have hzKw : z ∉ Kw := fun hmem ↦ (hKws hmem) hzcar
        have hev : w =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hKwc.isClosed.isOpen_compl.mem_nhds hzKw] with u hu
          exact hKw0 u hu
        refine ⟨continuousAt_const.congr_of_eventuallyEq hev, ?_⟩
        rw [hKw0 z hzKw]
        exact hB₀0
      · have hzB : z ∉ Bimg := fun hmem ↦ hzA ⟨hmem, hzcar⟩
        have hzS : z ∈ S := by
          rw [hDρ] at hzD
          obtain ⟨ζ, hζ, hζz⟩ := hzD
          rw [mem_closedBall] at hζ
          rcases lt_or_eq_of_le hζ with hlt | heqd
          · exact absurd ⟨ζ, mem_ball.mpr hlt, hζz⟩ hzB
          · exact ⟨ζ, by rw [mem_sphere]; exact heqd, hζz⟩
        have hzp : z ≠ p₀ := hSp₀ z hzS
        refine ⟨hwfam.2.1.continuousAt (isOpen_compl_singleton.mem_nhds hzp), ?_⟩
        have hzW : z ∈ Wp n := hSW n hzS
        have h1 : w z = v ⟨z, hzW⟩ := hwval ⟨z, hzW⟩
        have h2 : v ⟨z, hzW⟩ ≤ V n z := by
          rw [hVmem n z hzW]
          exact le_csSup ((hEnvH n).2 ⟨z, hzW⟩
            (fun hcon ↦ hzp (congrArg Subtype.val hcon))) ⟨v, hvmem, rfl⟩
        have h3 : V n z ≤ gs z := (hgs_all z hzp (hSq z hzS)).2 n
        have h4 : gs z ≤ gs yS := hySmax hzS
        rw [h1]
        exact ((h2.trans h3).trans h4).trans (le_max_left _ _)
    have hwA := maxPrin A w B₀ Kw hAopen hAne
      (fun z hz ↦ hwfam.1 z (hAsubp hz)) hKwc
      (fun z _ hzK ↦ (hKw0 z hzK).le.trans hB₀0) hfr
    exact (le_of_eq (hwval ⟨y₀, hy₀W⟩).symm).trans (hwA y₀ ⟨hy₀B, hy₀W⟩)
  have hgsB : ∀ y ∈ Bimg, y ≠ q → gs y ≤ B₀ := by
    intro y hyB hyq
    refine ciSup_le fun n ↦ ?_
    by_cases hyW : y ∈ Wp n
    · exact hVann n y hyB hyW
    · rw [hVzero n y hyW]
      exact hB₀0
  /- ## Removability at the auxiliary point. -/
  have hharmU : HarmonicOnNhd (fun ζ ↦ gs (e.symm ζ)) (ball (e q) ρ \ {e q}) := by
    rintro ζ ⟨hζ, hζq⟩
    have hζt : ζ ∈ e.target := hballρ hζ
    have hysrc : e.symm ζ ∈ e.source := e.map_target hζt
    have hyq : e.symm ζ ≠ q := by
      intro hcon
      apply hζq
      rw [Set.mem_singleton_iff, ← e.right_inv hζt, hcon]
    have hyp : e.symm ζ ≠ p₀ := (hDavoid _ (hBsub ⟨ζ, hζ, rfl⟩)).1
    have hMH : MHarmonicAt gs (e.symm ζ) := (hgs_all _ hyp hyq).1
    have h1 := (mharmonicAt_iff_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas q) hysrc).mp hMH
    rw [e.right_inv hζt] at h1
    exact h1
  have hbddU : ∀ ζ ∈ ball (e q) ρ \ {e q}, |gs (e.symm ζ)| ≤ B₀ := by
    rintro ζ ⟨hζ, hζq⟩
    have hζt : ζ ∈ e.target := hballρ hζ
    have hyq : e.symm ζ ≠ q := by
      intro hcon
      apply hζq
      rw [Set.mem_singleton_iff, ← e.right_inv hζt, hcon]
    have hyp : e.symm ζ ≠ p₀ := (hDavoid _ (hBsub ⟨ζ, hζ, rfl⟩)).1
    rw [abs_le]
    constructor
    · linarith [hgs_nonneg (e.symm ζ) hyp hyq]
    · exact hgsB _ ⟨ζ, hζ, rfl⟩ hyq
  obtain ⟨hf, hfharm, hfeq⟩ :=
    exists_harmonicOnNhd_of_bounded_punctured hρ0 hharmU ⟨B₀, hbddU⟩
  set gh : M → ℝ := fun y ↦ if y = q then hf (e q) else gs y with hgh
  have ghq : ∀ y : M, y ≠ q → gh y = gs y := by
    intro y hy
    simp only [hgh]
    rw [ite_eq_right hy]
  have ghqq : gh q = hf (e q) := ite_eq_left rfl
  have hghharm : MHarmonicOn gh {p₀}ᶜ := by
    intro y hy
    have hyp : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hy
    by_cases hyq : y = q
    · have hMH : MHarmonicAt (fun z ↦ hf (e z)) q := by
        have h2 : HarmonicAt hf (e q) := hfharm _ (mem_ball_self hρ0)
        have h3 : ((fun z ↦ hf (e z)) ∘ (e.symm : ℂ → M)) =ᶠ[𝓝 (e q)] hf := by
          filter_upwards [e.open_target.mem_nhds (e.map_source hqsrc)] with ζ hζ
          simp only [Function.comp_apply]
          rw [e.right_inv hζ]
        exact (harmonicAt_congr_nhds h3).mpr h2
      rw [hyq]
      refine mharm_congr (fun z ↦ hf (e z)) gh q ?_ hMH
      filter_upwards [hBopen.mem_nhds hqB] with z hz
      obtain ⟨ζ, hζ, rfl⟩ := hz
      have hζt : ζ ∈ e.target := hballρ hζ
      by_cases hzq : e.symm ζ = q
      · rw [hzq, ghqq]
      · have hζq : ζ ≠ e q := by
          intro hcon
          apply hzq
          rw [hcon]
          exact e.left_inv hqsrc
        have h4 : hf ζ = gs (e.symm ζ) := hfeq ⟨hζ, hζq⟩
        rw [e.right_inv hζt, h4, ghq _ hzq]
    · refine mharm_congr gs gh y ?_ ((hgs_all y hyp hyq).1)
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hyq)] with z hz
      exact (ghq z (Set.mem_compl_singleton_iff.mp hz)).symm
  have hghx : gh x ≤ B' := by
    rw [ghq x hxq]
    exact hgs_x
  /- ## The truncated-logarithm family member at the pole. -/
  set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with hep
  have hpsrc : p₀ ∈ ep.source := mem_chart_source ℂ p₀
  set cp : ℂ := ep p₀ with hcp
  have hUp : IsOpen (ep.target ∩ ep.symm ⁻¹' (D.closedCarrierᶜ ∩ {x}ᶜ)) :=
    ep.isOpen_inter_preimage_symm
      ((D.isCompact_closedCarrier.isClosed.isOpen_compl).inter isOpen_compl_singleton)
  have hcpU : cp ∈ ep.target ∩ ep.symm ⁻¹' (D.closedCarrierᶜ ∩ {x}ᶜ) := by
    refine ⟨ep.map_source hpsrc, ?_⟩
    rw [Set.mem_preimage, hcp, ep.left_inv hpsrc]
    exact ⟨fun hmem ↦ (hDavoid p₀ hmem).1 rfl,
      Set.mem_compl_singleton_iff.mpr (Ne.symm hx)⟩
  obtain ⟨εp, hεp, hεpsub⟩ := Metric.isOpen_iff.mp hUp _ hcpU
  set rp : ℝ := εp / 2 with hrp
  have hrp0 : 0 < rp := half_pos hεp
  have hrpsub : closedBall cp rp ⊆ ep.target ∩ ep.symm ⁻¹' (D.closedCarrierᶜ ∩ {x}ᶜ) :=
    (Metric.closedBall_subset_ball (half_lt_self hεp)).trans hεpsub
  have hrpt : closedBall cp rp ⊆ ep.target := fun w hw ↦ (hrpsub hw).1
  set Kp : Set M := ep.symm '' closedBall cp rp with hKpdef
  have hKpcomp : IsCompact Kp := (isCompact_closedBall _ _).image_of_continuousOn
    (ep.continuousOn_symm.mono hrpt)
  have hKpavoid : ∀ y ∈ Kp, y ∉ D.closedCarrier ∧ y ≠ x := by
    rintro y ⟨w, hw, rfl⟩
    have h2 := (hrpsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, Set.mem_compl_singleton_iff.mp h2.2⟩
  have hKpW : ∀ n, Kp ⊆ (Wp n : Set M) :=
    fun n y hy hmem ↦ (hKpavoid y hy).1 (hcarNsub n hmem)
  have hKpsrc : Kp ⊆ ep.source := by
    rintro y ⟨w, hw, rfl⟩
    exact ep.map_target (hrpt hw)
  have hexc : ∀ y, y ∈ ep.source → y ≠ p₀ → ep y ≠ cp := by
    intro y hys hyp heq
    exact hyp (ep.injOn hys hpsrc (by rw [← hcp]; exact heq))
  set gp : ℂ → ℝ := fun z ↦ max (Real.log rp - Real.log ‖z - cp‖) 0 with hgp
  have hgpharm : HarmonicOnNhd (fun z ↦ Real.log rp - Real.log ‖z - cp‖) {cp}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun u : ℂ ↦ u - cp) z := analyticAt_id.sub analyticAt_const
    have hne2 : z - cp ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log rp)).sub (hana.harmonicAt_log_norm hne2)
  have hgpsub : SubharmonicOn gp {cp}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ ↦ (0 : ℝ)) {cp}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ ↦ harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hgpharm) h0
  have hgpzero : ∀ z, z ∉ ball cp rp → gp z = 0 := by
    intro z hz
    have hzr : rp ≤ ‖z - cp‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hz
      exact hz
    have hle : Real.log rp ≤ Real.log ‖z - cp‖ := Real.log_le_log hrp0 hzr
    simp only [hgp]
    exact max_eq_right (by linarith)
  set v₀ : M → ℝ := fun y ↦ if y ∈ ep.source then gp (ep y) else 0 with hv₀def
  have hv₀zero : ∀ y, y ∉ Kp → v₀ y = 0 := by
    intro y hy
    by_cases hys : y ∈ ep.source
    · simp only [hv₀def]
      rw [ite_eq_left hys]
      apply hgpzero
      intro hball2
      exact hy ⟨ep y, ball_subset_closedBall hball2, ep.left_inv hys⟩
    · simp only [hv₀def]
      rw [ite_eq_right hys]
  have hv₀sub : MSubharmonicOn v₀ {p₀}ᶜ := by
    intro y hy
    have hyp : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hy
    by_cases hys : y ∈ ep.source
    · refine (msubharmonicAt_iff_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas p₀) hys).mpr ?_
      have hopen2 : IsOpen (ep.target ∩ {cp}ᶜ) :=
        ep.open_target.inter isOpen_compl_singleton
      have hmem2 : ep y ∈ ep.target ∩ {cp}ᶜ :=
        ⟨ep.map_source hys, Set.mem_compl_singleton_iff.mpr (hexc y hys hyp)⟩
      obtain ⟨ρ', hρ', hρ'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      have heqon : Set.EqOn gp (v₀ ∘ ep.symm) (ball (ep y) ρ') := by
        intro z hz
        have hzt : z ∈ ep.target := (hρ'sub hz).1
        have hzs : ep.symm z ∈ ep.source := ep.map_target hzt
        simp only [Function.comp_apply, hv₀def]
        rw [ite_eq_left hzs, ep.right_inv hzt]
      exact ⟨ρ', hρ', fun z hz ↦ (hρ'sub hz).1,
        transfer _ _ _ _ hgpsub (fun z hz ↦ (hρ'sub hz).2) heqon⟩
    · have hyK : y ∉ Kp := fun hmem ↦ hys (hKpsrc hmem)
      exact msub_zero v₀ Kpᶜ y hKpcomp.isClosed.isOpen_compl hyK
        (fun z hz ↦ hv₀zero z hz)
  have hv₀cont : ContinuousOn v₀ {p₀}ᶜ := by
    intro y hy
    have hyp : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hy
    apply ContinuousAt.continuousWithinAt
    by_cases hys : y ∈ ep.source
    · have hgc : ContinuousAt gp (ep y) := hgpsub.1.continuousAt
        (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.mpr (hexc y hys hyp)))
      refine (hgc.comp (ep.continuousAt hys)).congr_of_eventuallyEq ?_
      filter_upwards [ep.open_source.mem_nhds hys] with u hu
      simp only [Function.comp_apply, hv₀def]
      rw [ite_eq_left hu]
    · have hyK : y ∉ Kp := fun hmem ↦ hys (hKpsrc hmem)
      have hev : v₀ =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hKpcomp.isClosed.isOpen_compl.mem_nhds hyK] with u hu
        exact hv₀zero u hu
      exact continuousAt_const.congr_of_eventuallyEq hev
  have hv₀pole : ∀ᶠ y' in 𝓝[≠] p₀, v₀ y' + Real.log ‖poleCoord p₀ y'‖ ≤
      Real.log rp := by
    have hopen2 : IsOpen (ep.source ∩ ep ⁻¹' ball cp rp) :=
      ep.continuousOn.isOpen_inter_preimage ep.open_source isOpen_ball
    have hnb : ep.source ∩ ep ⁻¹' ball cp rp ∈ 𝓝 p₀ := by
      refine hopen2.mem_nhds ⟨hpsrc, ?_⟩
      rw [Set.mem_preimage, ← hcp]
      exact mem_ball_self hrp0
    filter_upwards [nhdsWithin_le_nhds hnb, eventually_mem_nhdsWithin] with y hy hyp
    have hysrc : y ∈ ep.source := hy.1
    have hyne : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hyp
    have hpole_eq : poleCoord p₀ y = ep y - cp := by
      simp only [poleCoord, ← hep, ← hcp]
    rw [hpole_eq]
    have hpos : 0 < ‖ep y - cp‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hexc y hysrc hyne))
    have hlt : ‖ep y - cp‖ < rp := by
      have hball2 : ep y ∈ ball cp rp := hy.2
      rw [mem_ball, dist_eq_norm] at hball2
      exact hball2
    have hBA : Real.log ‖ep y - cp‖ < Real.log rp := Real.log_lt_log hpos hlt
    simp only [hv₀def]
    rw [ite_eq_left hysrc]
    simp only [hgp]
    rw [max_eq_left (by linarith)]
    linarith
  have hv₀piece : ∀ n, (fun z : ↥(Wp n) ↦ v₀ z) ∈
      greenFamily (⟨p₀, hp₀W n⟩ : ↥(Wp n)) := fun n ↦
    brickR n v₀ Kp hv₀sub hv₀cont hKpcomp (hKpW n) hv₀zero ⟨Real.log rp, hv₀pole⟩
  have hgs_ge : ∀ y : M, y ≠ p₀ → y ∈ Kp → v₀ y ≤ gs y := by
    intro y hyp hyK
    have hyq : y ≠ q := fun hcon ↦ (hKpavoid y hyK).1 (hcon ▸ hqD)
    have hyW : y ∈ Wp 0 := hKpW 0 hyK
    have h1 : v₀ y ≤ V 0 y := by
      rw [hVmem 0 y hyW]
      exact le_csSup ((hEnvH 0).2 ⟨y, hyW⟩
        (fun hcon ↦ hyp (congrArg Subtype.val hcon))) ⟨_, hv₀piece 0, rfl⟩
    exact h1.trans ((hgs_all y hyp hyq).2 0)
  /- ## The endgame: minimum principle on the compact surface. -/
  set σ : ℝ := rp * Real.exp (-(B' + 1)) with hσdef
  have hσ0 : 0 < σ := mul_pos hrp0 (Real.exp_pos _)
  have hσrp : σ < rp := by
    have h1 : Real.exp (-(B' + 1)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    calc σ = rp * Real.exp (-(B' + 1)) := rfl
      _ < rp * 1 := by
        apply mul_lt_mul_of_pos_left h1 hrp0
      _ = rp := mul_one rp
  have hlogσ : Real.log σ = Real.log rp - (B' + 1) := by
    rw [hσdef, Real.log_mul hrp0.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  set τ : ℝ := rp * Real.exp (-(B' + 1 / 2)) with hτdef
  have hτ0 : 0 < τ := mul_pos hrp0 (Real.exp_pos _)
  have hστ : σ < τ := by
    apply mul_lt_mul_of_pos_left _ hrp0
    exact Real.exp_lt_exp.mpr (by linarith)
  have hτrp : τ < rp := by
    have h1 : Real.exp (-(B' + 1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    calc τ = rp * Real.exp (-(B' + 1 / 2)) := rfl
      _ < rp * 1 := by
        apply mul_lt_mul_of_pos_left h1 hrp0
      _ = rp := mul_one rp
  have hlogτ : Real.log τ = Real.log rp - (B' + 1 / 2) := by
    rw [hτdef, Real.log_mul hrp0.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hσt : closedBall cp σ ⊆ ep.target :=
    (closedBall_subset_closedBall hσrp.le).trans hrpt
  set Dp : CoordDisk M := ⟨p₀, σ, hσ0, hσt⟩ with hDp
  have hDpcar : Dp.closedCarrier = ep.symm '' closedBall cp σ := rfl
  set Uσ : Set M := ep.symm '' ball cp σ with hUσ
  have hUσopen : IsOpen Uσ := by
    rw [hUσ, himg ep _ (ball_subset_closedBall.trans hσt)]
    exact ep.continuousOn.isOpen_inter_preimage ep.open_source isOpen_ball
  have hp₀Uσ : p₀ ∈ Uσ := ⟨cp, mem_ball_self hσ0, by rw [hcp]; exact ep.left_inv hpsrc⟩
  have hUσC : Uσ ⊆ Dp.closedCarrier := by
    rw [hUσ, hDpcar]
    exact Set.image_mono ball_subset_closedBall
  have hCKp : Dp.closedCarrier ⊆ Kp := by
    rw [hDpcar, hKpdef]
    exact Set.image_mono (closedBall_subset_closedBall hσrp.le)
  set Kσ : Set M := Uσᶜ with hKσ
  have hKσcomp : IsCompact Kσ := hUσopen.isClosed_compl.isCompact
  have hKσp₀ : ∀ z ∈ Kσ, z ≠ p₀ := fun z hz hcon ↦ hz (hcon ▸ hp₀Uσ)
  have hxKσ : x ∈ Kσ := fun hmem ↦ (hKpavoid x (hCKp (hUσC hmem))).2 rfl
  have hKσcont : ContinuousOn gh Kσ := fun z hz ↦
    ((hghharm z (Set.mem_compl_singleton_iff.mpr (hKσp₀ z hz))).continuousAt).continuousWithinAt
  obtain ⟨ym, hymK, hymmin⟩ := hKσcomp.exists_isMinOn ⟨x, hxKσ⟩ hKσcont
  have hymB : gh ym ≤ B' := (hymmin hxKσ).trans hghx
  have hτcb : cp + (τ : ℂ) ∈ closedBall cp rp := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hτ0.le]
    exact hτrp.le
  set zst : M := ep.symm (cp + (τ : ℂ)) with hzst
  have hzstK : zst ∈ Kp := ⟨cp + τ, hτcb, rfl⟩
  have hzstval : ep zst = cp + τ := ep.right_inv (hrpt hτcb)
  have hzstnorm : ‖ep zst - cp‖ = τ := by
    rw [hzstval, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
  have hzstp₀ : zst ≠ p₀ := by
    intro hcon
    have h1 : ep p₀ = cp := rfl
    rw [hcon, h1, sub_self, norm_zero] at hzstnorm
    exact hτ0.ne hzstnorm
  have hzstq : zst ≠ q := fun hcon ↦ (hKpavoid zst hzstK).1 (hcon ▸ hqD)
  have hzstCσ : zst ∉ Dp.closedCarrier := by
    rintro ⟨w, hw, hweq⟩
    have hwt : w ∈ ep.target := hσt hw
    have h1 : ep zst = w := by rw [← hweq, ep.right_inv hwt]
    rw [h1] at hzstnorm
    rw [mem_closedBall, dist_eq_norm, hzstnorm] at hw
    linarith
  have hv₀zst : B' + 1 / 2 ≤ v₀ zst := by
    have hsrc : zst ∈ ep.source := ep.map_target (hrpt hτcb)
    have h1 : v₀ zst = max (Real.log rp - Real.log ‖ep zst - cp‖) 0 := by
      simp only [hv₀def]
      rw [ite_eq_left hsrc]
    rw [h1, hzstnorm, hlogτ]
    have h2 : Real.log rp - (Real.log rp - (B' + 1 / 2)) = B' + 1 / 2 := by ring
    rw [h2]
    exact le_max_left _ _
  have hgszst : B' + 1 / 2 ≤ gs zst := hv₀zst.trans (hgs_ge zst hzstp₀ hzstK)
  by_cases hymC : ym ∈ Dp.closedCarrier
  · -- The minimum sits on the σ-circle, where the truncated logarithm is `B' + 1`.
    obtain ⟨w, hw, hweq⟩ := hymC
    have hwt : w ∈ ep.target := hσt hw
    have hymval : ep ym = w := by rw [← hweq, ep.right_inv hwt]
    have hwnb : w ∉ ball cp σ := fun hcon ↦ hymK ⟨w, hcon, hweq⟩
    have hwσ : ‖w - cp‖ = σ := by
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_eq_norm, not_lt] at hwnb
      linarith
    have hymp₀ : ym ≠ p₀ := hKσp₀ ym hymK
    have hymKp : ym ∈ Kp := hCKp ⟨w, hw, hweq⟩
    have hymq : ym ≠ q := fun hcon ↦ (hKpavoid ym hymKp).1 (hcon ▸ hqD)
    have hymsrc : ym ∈ ep.source := by
      rw [← hweq]
      exact ep.map_target hwt
    have hv₀ym : v₀ ym = max (Real.log rp - Real.log σ) 0 := by
      simp only [hv₀def]
      rw [ite_eq_left hymsrc, hymval]
      simp only [hgp]
      rw [hwσ]
    have hchain : B' + 1 ≤ gh ym := by
      rw [ghq ym hymq]
      have h2 : v₀ ym ≤ gs ym := hgs_ge ym hymp₀ hymKp
      rw [hv₀ym, hlogσ] at h2
      have h3 : Real.log rp - (Real.log rp - (B' + 1)) = B' + 1 := by ring
      rw [h3] at h2
      exact (le_max_left _ _).trans h2
    linarith
  · -- The minimum is interior: the strong minimum principle makes `gh` constant on the
    -- connected complement of the σ-disk, contradicting the growth at the witness point.
    have hymΩ : ym ∈ (Dp.compl : Set M) := hymC
    have hΩσconn : IsConnected (Dp.compl : Set M) := isConnected_coordDisk_compl Dp
    have hΩσopen : IsOpen (Dp.compl : Set M) :=
      Dp.isCompact_closedCarrier.isClosed.isOpen_compl
    have hΩσp₀ : ∀ z ∈ (Dp.compl : Set M), z ≠ p₀ := by
      intro z hz hcon
      exact hz (hcon ▸ hUσC hp₀Uσ)
    have hsubΩ : MSubharmonicOn (-gh) (Dp.compl : Set M) := fun z hz ↦
      ((hghharm z (Set.mem_compl_singleton_iff.mpr (hΩσp₀ z hz))).neg).msubharmonicAt
    have hmaxΩ : ∀ z ∈ (Dp.compl : Set M), (-gh) z ≤ (-gh) ym := by
      intro z hz
      simp only [Pi.neg_apply]
      have h5 : gh ym ≤ gh z := hymmin (fun hmem ↦ hz (hUσC hmem))
      linarith
    have hconst := propagate (Dp.compl : Set M) (-gh) ym hΩσopen
      hΩσconn.isPreconnected hymΩ hsubΩ hmaxΩ
    have h6 := hconst zst hzstCσ
    simp only [Pi.neg_apply, neg_inj] at h6
    have h7 : gh zst ≤ B' := h6 ▸ hymB
    rw [ghq zst hzstq] at h7
    linarith

/-- **The non-hyperbolic case of planarity**: a simply connected surface
without a Green's function embeds onto a domain of the Riemann sphere via the
dipole map. -/
theorem exists_diffeomorph_opens_of_forall_not_hasGreenFunction
    [SimplyConnectedSpace M] [SecondCountableTopology M]
    (hnon : ∀ p₀ : M, ¬ HasGreenFunction p₀) :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  classical
  /- ## Two distinct points and a disk center, all in one chart ball. -/
  obtain ⟨p₁⟩ : Nonempty M := inferInstance
  have hp₁src : p₁ ∈ (chartAt ℂ p₁).source := mem_chart_source ℂ p₁
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp (chartAt ℂ p₁).open_target
    (chartAt ℂ p₁ p₁) ((chartAt ℂ p₁).map_source hp₁src)
  have hmemt : ∀ t : ℝ, 0 < t → t < r₀ →
      chartAt ℂ p₁ p₁ + (t : ℂ) ∈ (chartAt ℂ p₁).target := by
    intro t ht0 htr
    apply hball₀
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
    exact htr
  have h2mem : chartAt ℂ p₁ p₁ + ((r₀ / 2 : ℝ) : ℂ) ∈ (chartAt ℂ p₁).target :=
    hmemt _ (by linarith) (by linarith)
  have h4mem : chartAt ℂ p₁ p₁ + ((r₀ / 4 : ℝ) : ℂ) ∈ (chartAt ℂ p₁).target :=
    hmemt _ (by linarith) (by linarith)
  have hsymmne : ∀ t : ℝ, 0 < t → t < r₀ →
      (chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + (t : ℂ)) ≠ p₁ := by
    intro t ht0 htr hcon
    have h1 : chartAt ℂ p₁ ((chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + (t : ℂ)))
        = chartAt ℂ p₁ p₁ + (t : ℂ) := (chartAt ℂ p₁).right_inv (hmemt t ht0 htr)
    rw [hcon] at h1
    have h2 : chartAt ℂ p₁ p₁ + (t : ℂ) = chartAt ℂ p₁ p₁ + 0 := by
      rw [add_zero]; exact h1.symm
    have h3 : (t : ℂ) = 0 := add_left_cancel h2
    rw [Complex.ofReal_eq_zero] at h3
    exact ht0.ne' h3
  set p₂ : M := (chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + ((r₀ / 2 : ℝ) : ℂ)) with
      hp₂def
  set q : M := (chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + ((r₀ / 4 : ℝ) : ℂ)) with hqdef
  have hp₁p₂ : p₁ ≠ p₂ := fun hcon ↦
    hsymmne (r₀ / 2) (by linarith) (by linarith) hcon.symm
  have hp₁q : p₁ ≠ q := fun hcon ↦
    hsymmne (r₀ / 4) (by linarith) (by linarith) hcon.symm
  have hp₂q : p₂ ≠ q := by
    intro hcon
    rw [hp₂def, hqdef] at hcon
    have h1 := congrArg (⇑(chartAt ℂ p₁)) hcon
    rw [(chartAt ℂ p₁).right_inv h2mem, (chartAt ℂ p₁).right_inv h4mem] at h1
    have h2 : ((r₀ / 2 : ℝ) : ℂ) = ((r₀ / 4 : ℝ) : ℂ) := add_left_cancel h1
    rw [Complex.ofReal_inj] at h2
    linarith
  /- ## The coordinate disk at `q` avoiding both poles. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ q with he₀def
  have hqsrc : q ∈ e₀.source := mem_chart_source ℂ q
  have hUopen : IsOpen (e₀.target ∩ ⇑e₀.symm ⁻¹' ({p₁}ᶜ ∩ {p₂}ᶜ)) :=
    e₀.isOpen_inter_preimage_symm (isOpen_compl_singleton.inter isOpen_compl_singleton)
  have hqU : e₀ q ∈ e₀.target ∩ ⇑e₀.symm ⁻¹' ({p₁}ᶜ ∩ {p₂}ᶜ) := by
    refine ⟨e₀.map_source hqsrc, ?_⟩
    rw [Set.mem_preimage, e₀.left_inv hqsrc]
    exact ⟨Set.mem_compl_singleton_iff.mpr hp₁q.symm,
      Set.mem_compl_singleton_iff.mpr hp₂q.symm⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hUopen _ hqU
  have hra0 : (0 : ℝ) < εa / 2 := half_pos hεa
  have hrsub : closedBall (e₀ q) (εa / 2) ⊆ e₀.target ∩ ⇑e₀.symm ⁻¹' ({p₁}ᶜ ∩
      {p₂}ᶜ) :=
    (Metric.closedBall_subset_ball (half_lt_self hεa)).trans hballa
  set D₀ : CoordDisk M := ⟨q, εa / 2, hra0, fun w hw ↦ (hrsub hw).1⟩ with hD₀def
  have hD₀car : D₀.closedCarrier = e₀.symm '' closedBall (e₀ q) (εa / 2) := rfl
  have hD₀avoid : ∀ y ∈ D₀.closedCarrier, y ≠ p₁ ∧ y ≠ p₂ := by
    rintro y ⟨w, hw, rfl⟩
    have h2 := (hrsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨Set.mem_compl_singleton_iff.mp h2.1, Set.mem_compl_singleton_iff.mp h2.2⟩
  have hp₁D : p₁ ∉ D₀.closedCarrier := fun hmem ↦ (hD₀avoid p₁ hmem).1 rfl
  have hp₂D : p₂ ∉ D₀.closedCarrier := fun hmem ↦ (hD₀avoid p₂ hmem).2 rfl
  /- ## The bipolar Green's function and the injective dipole map. -/
  obtain ⟨Gb, hGb, hpole₁, hpole₂, hbdd⟩ := exists_bipolar_green D₀ hp₁D hp₂D hp₁p₂
  obtain ⟨φ, hφ, hφ₁, hφ₂, habs⟩ := exists_bipolar_map hp₁p₂ hGb hpole₁ hpole₂
  have hinj : Function.Injective φ :=
    injective_bipolar_map hnon hp₁p₂ hpole₂ hbdd hφ hφ₁ hφ₂ habs
  /- ## Plane-level helpers: an injective analytic map is locally open. -/
  have keyPlane : ∀ (g : ℂ → ℂ) (T : Set ℂ), IsOpen T → (∀ w ∈ T, AnalyticAt ℂ g
      w) →
      Set.InjOn g T → ∀ w ∈ T, 𝓝 (g w) ≤ Filter.map g (𝓝 w) := by
    intro g T hTopen hgan hginjT w hw
    rcases (hgan w hw).eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have h1 : ∀ᶠ w' in 𝓝[≠] w, g w' = g w ∧ w' ∈ T :=
        (hconst.and (hTopen.eventually_mem hw)).filter_mono nhdsWithin_le_nhds
      obtain ⟨w', ⟨hgw', hw'T⟩, hw'ne⟩ := (h1.and eventually_mem_nhdsWithin).exists
      exact hw'ne (Set.mem_singleton_iff.mpr (hginjT hw'T hw hgw'))
    · exact hle
  have imgOpen : ∀ (g : ℂ → ℂ) (T : Set ℂ), IsOpen T → (∀ w ∈ T, AnalyticAt ℂ g w)
      →
      Set.InjOn g T → ∀ S : Set ℂ, S ⊆ T → IsOpen S → IsOpen (g '' S) := by
    intro g T hTopen hgan hginjT S hST hSopen
    rw [isOpen_iff_mem_nhds]
    rintro ζ ⟨w, hwS, rfl⟩
    exact Filter.le_def.mp (keyPlane g T hTopen hgan hginjT w (hST hwS)) _
      (Filter.image_mem_map (hSopen.mem_nhds hwS))
  /- ## The dipole map is open: read it in charts around each point. -/
  have hopenM : IsOpenMap φ := by
    rw [isOpenMap_iff_nhds_le]
    intro x
    obtain ⟨χ, hxsrc, hχmax⟩ : ∃ χ : OpenPartialHomeomorph M ℂ,
        x ∈ χ.source ∧ χ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M :=
      ⟨chartAt ℂ x, mem_chart_source ℂ x, IsManifold.chart_mem_maximalAtlas x⟩
    obtain ⟨e, hφxsrc, hemax⟩ : ∃ e : OpenPartialHomeomorph ℂ̂ ℂ,
        φ x ∈ e.source ∧ e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
      ⟨chartAt ℂ (φ x), mem_chart_source ℂ (φ x),
        IsManifold.chart_mem_maximalAtlas (φ x)⟩
    have hTopen : IsOpen (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) :=
      χ.continuousOn_symm.isOpen_inter_preimage χ.open_target
        (e.open_source.preimage hφ.continuous)
    have hχxT : χ x ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source) := by
      refine ⟨χ.map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, Set.mem_preimage, χ.left_inv hxsrc]
      exact hφxsrc
    have hgan : ∀ w ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source),
        AnalyticAt ℂ (⇑e ∘ φ ∘ ⇑χ.symm) w := by
      intro w hw
      have hw2 : φ (χ.symm w) ∈ e.source := hw.2
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑χ.symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas hχmax hw.1
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ (χ.symm w) := hφ.contMDiffAt
      have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) (φ (χ.symm w)) :=
        contMDiffAt_of_mem_maximalAtlas hemax hw2
      exact (contMDiffAt_iff_contDiffAt.mp
        ((h3.comp (χ.symm w) h2).comp w h1)).analyticAt
    have hginjT : Set.InjOn (⇑e ∘ φ ∘ ⇑χ.symm)
        (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) := by
      intro w₁ h₁ w₂ h₂ hgw
      have h₁2 : φ (χ.symm w₁) ∈ e.source := h₁.2
      have h₂2 : φ (χ.symm w₂) ∈ e.source := h₂.2
      have h3 : φ (χ.symm w₁) = φ (χ.symm w₂) := e.injOn h₁2 h₂2 hgw
      have h4 : χ.symm w₁ = χ.symm w₂ := hinj h3
      have h5 := congrArg (⇑χ) h4
      rwa [χ.right_inv h₁.1, χ.right_inv h₂.1] at h5
    have hle : 𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) (χ x)) ≤
        Filter.map (⇑e ∘ φ ∘ ⇑χ.symm) (𝓝 (χ x)) :=
      keyPlane _ _ hTopen hgan hginjT (χ x) hχxT
    have hev : φ =ᶠ[𝓝 x] ⇑e.symm ∘ (⇑e ∘ φ ∘ ⇑χ.symm) ∘ ⇑χ := by
      have hnb : χ.source ∩ φ ⁻¹' e.source ∈ 𝓝 x :=
        (χ.open_source.inter (e.open_source.preimage hφ.continuous)).mem_nhds
          ⟨hxsrc, hφxsrc⟩
      filter_upwards [hnb] with y hy
      have hy2 : φ y ∈ e.source := hy.2
      simp only [Function.comp_apply, χ.left_inv hy.1]
      exact (e.left_inv hy2).symm
    have hgx : (⇑e ∘ φ ∘ ⇑χ.symm) (χ x) = e (φ x) := by
      simp only [Function.comp_apply, χ.left_inv hxsrc]
    have h6 : Filter.map φ (𝓝 x) =
        Filter.map (⇑e.symm) (Filter.map (⇑e ∘ φ ∘ ⇑χ.symm) (𝓝 (χ x))) := by
      rw [Filter.map_congr hev, ← χ.map_nhds_eq hxsrc, Filter.map_map, Filter.map_map]
      rfl
    have h7 : 𝓝 (φ x) = Filter.map (⇑e.symm) (𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) (χ x))) := by
      rw [hgx, e.symm_map_nhds_eq hφxsrc]
    rw [h6, h7]
    exact Filter.map_mono hle
  /- ## The image domain and the two structure maps. -/
  let U : Opens ℂ̂ := ⟨Set.range φ, hopenM.isOpen_range⟩
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun x : M ↦ (⟨φ x, Set.mem_range_self x⟩ : ↥U)) := by
    intro x
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (Subtype.val ∘ fun x : M ↦ (⟨φ x, Set.mem_range_self x⟩ : ↥U)) x :=
      hφ.contMDiffAt
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  /- ## Inverse smoothness: read the inverse through the sphere chart at the
  image point and a surface chart at the preimage point, where it is the
  local inverse of an injective analytic plane map. -/
  have hGsm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun y : ↥U ↦ Function.invFun φ (y : ℂ̂)) := by
    intro y₀
    obtain ⟨x₀, hφx₀⟩ : ∃ x, φ x = (y₀ : ℂ̂) := y₀.2
    obtain ⟨χ, hx₀src, hχmax⟩ : ∃ χ : OpenPartialHomeomorph M ℂ,
        x₀ ∈ χ.source ∧ χ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M :=
      ⟨chartAt ℂ x₀, mem_chart_source ℂ x₀, IsManifold.chart_mem_maximalAtlas x₀⟩
    obtain ⟨e, hy₀esrc, hemax⟩ : ∃ e : OpenPartialHomeomorph ℂ̂ ℂ,
        (y₀ : ℂ̂) ∈ e.source ∧ e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
      ⟨chartAt ℂ ((y₀ : ℂ̂)), mem_chart_source ℂ ((y₀ : ℂ̂)),
        IsManifold.chart_mem_maximalAtlas ((y₀ : ℂ̂))⟩
    have hφx₀src : φ x₀ ∈ e.source := by rw [hφx₀]; exact hy₀esrc
    have hTopen : IsOpen (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) :=
      χ.continuousOn_symm.isOpen_inter_preimage χ.open_target
        (e.open_source.preimage hφ.continuous)
    have hχx₀T : χ x₀ ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source) := by
      refine ⟨χ.map_source hx₀src, ?_⟩
      rw [Set.mem_preimage, Set.mem_preimage, χ.left_inv hx₀src]
      exact hφx₀src
    -- The chart reading of `φ` is analytic and injective near the base point.
    have hgan : ∀ w ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source),
        AnalyticAt ℂ (⇑e ∘ φ ∘ ⇑χ.symm) w := by
      intro w hw
      have hw2 : φ (χ.symm w) ∈ e.source := hw.2
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑χ.symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas hχmax hw.1
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ (χ.symm w) := hφ.contMDiffAt
      have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) (φ (χ.symm w)) :=
        contMDiffAt_of_mem_maximalAtlas hemax hw2
      exact (contMDiffAt_iff_contDiffAt.mp
        ((h3.comp (χ.symm w) h2).comp w h1)).analyticAt
    have hginjT : Set.InjOn (⇑e ∘ φ ∘ ⇑χ.symm)
        (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) := by
      intro w₁ h₁ w₂ h₂ hgw
      have h₁2 : φ (χ.symm w₁) ∈ e.source := h₁.2
      have h₂2 : φ (χ.symm w₂) ∈ e.source := h₂.2
      have h3 : φ (χ.symm w₁) = φ (χ.symm w₂) := e.injOn h₁2 h₂2 hgw
      have h4 : χ.symm w₁ = χ.symm w₂ := hinj h3
      have h5 := congrArg (⇑χ) h4
      rwa [χ.right_inv h₁.1, χ.right_inv h₂.1] at h5
    obtain ⟨r, hr, hBsub⟩ := Metric.isOpen_iff.mp hTopen (χ x₀) hχx₀T
    -- The inverse chart reading.
    let η : ℂ → ℂ := fun ζ ↦ χ (Function.invFun φ (e.symm ζ))
    have hηg : ∀ w ∈ ball (χ x₀) r, η ((⇑e ∘ φ ∘ ⇑χ.symm) w) = w := by
      intro w hwB
      have hwT := hBsub hwB
      have hwT2 : φ (χ.symm w) ∈ e.source := hwT.2
      have h5 : Function.invFun φ (φ (χ.symm w)) = χ.symm w :=
        Function.leftInverse_invFun hinj (χ.symm w)
      change χ (Function.invFun φ (e.symm (e (φ (χ.symm w))))) = w
      rw [e.left_inv hwT2, h5]
      exact χ.right_inv hwT.1
    -- The image `W` of the coordinate ball, an open plane neighborhood.
    have hWopen : IsOpen ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r) :=
      imgOpen _ _ hTopen hgan hginjT _ hBsub isOpen_ball
    have hy₀W : e (y₀ : ℂ̂) ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r := by
      refine ⟨χ x₀, mem_ball_self hr, ?_⟩
      simp only [Function.comp_apply]
      rw [χ.left_inv hx₀src, hφx₀]
    have himg : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        ∃ w ∈ ball (χ x₀) r, (⇑e ∘ φ ∘ ⇑χ.symm) w = ζ := by
      rintro ζ ⟨w, hwB, rfl⟩
      exact ⟨w, hwB, rfl⟩
    have hgη : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ) = ζ := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
    have hηB : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r, η ζ ∈ ball (χ
        x₀) r := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
      exact hwB
    -- Continuity of the inverse reading, from openness of the reading.
    have hηc : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r, ContinuousAt η ζ := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      have hgoal : Filter.Tendsto η (𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) w)) (𝓝 w) := by
        rw [Filter.tendsto_def]
        intro N hN
        obtain ⟨N', hN'sub, hN'open, hwN'⟩ :=
          _root_.mem_nhds_iff.mp (Filter.inter_mem hN (isOpen_ball.mem_nhds hwB))
        have hsub' : N' ⊆ ball (χ x₀) r := fun z hz ↦ (hN'sub hz).2
        have hopenimg : IsOpen ((⇑e ∘ φ ∘ ⇑χ.symm) '' N') :=
          imgOpen _ _ hTopen hgan hginjT _ (hsub'.trans hBsub) hN'open
        have hgmem : (⇑e ∘ φ ∘ ⇑χ.symm) w ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' N' :=
          ⟨w, hwN', rfl⟩
        refine Filter.mem_of_superset (hopenimg.mem_nhds hgmem) ?_
        rintro ζ' ⟨w', hw'N', rfl⟩
        rw [Set.mem_preimage, hηg w' (hsub' hw'N')]
        exact (hN'sub hw'N').1
      have hηw : η ((⇑e ∘ φ ∘ ⇑χ.symm) w) = w := hηg w hwB
      change Filter.Tendsto η (𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) w))
        (𝓝 (η ((⇑e ∘ φ ∘ ⇑χ.symm) w)))
      rw [hηw]
      exact hgoal
    -- Differentiability of the inverse reading at noncritical values.
    have hd_nc : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        deriv (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ) ≠ 0 → DifferentiableAt ℂ η ζ := by
      intro ζ hζ hder
      have hfd : HasDerivAt (⇑e ∘ φ ∘ ⇑χ.symm)
          (deriv (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ)) (η ζ) :=
        ((hgan (η ζ) (hBsub (hηB ζ hζ))).differentiableAt).hasDerivAt
      have hev : ∀ᶠ ζ' in 𝓝 ζ, (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ') = ζ' := by
        filter_upwards [hWopen.mem_nhds hζ] with ζ' hζ' using hgη ζ' hζ'
      exact (HasDerivAt.of_local_left_inverse (hηc ζ hζ) hfd hder hev).differentiableAt
    -- Critical points of the chart reading are isolated (injectivity).
    have hganN : AnalyticOnNhd ℂ (⇑e ∘ φ ∘ ⇑χ.symm)
        (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) := fun w hw ↦ hgan w hw
    have hcrit : ∀ w ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source),
        ∀ᶠ w' in 𝓝[≠] w, deriv (⇑e ∘ φ ∘ ⇑χ.symm) w' ≠ 0 := by
      intro w hw
      rcases (hganN.deriv w hw).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · exfalso
        obtain ⟨ρ, hρ0, hballρ⟩ :=
          Metric.eventually_nhds_iff_ball.mp (h0.and (hTopen.eventually_mem hw))
        have hconst : ∀ w' ∈ ball w ρ,
            (⇑e ∘ φ ∘ ⇑χ.symm) w' = (⇑e ∘ φ ∘ ⇑χ.symm) w := by
          intro w' hw'
          refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball w ρ)
            (fun u hu ↦ ((hgan u (hballρ u hu).2).differentiableAt).differentiableWithinAt)
            ?_ hw' (mem_ball_self hρ0)
          intro u hu
          rw [fderivWithin_of_isOpen isOpen_ball hu]
          refine ContinuousLinearMap.ext_ring ?_
          rw [fderiv_apply_one_eq_deriv, (hballρ u hu).1]
          simp
        have hmem : w + ((ρ / 2 : ℝ) : ℂ) ∈ ball w ρ := by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith
        have heq2 : w + ((ρ / 2 : ℝ) : ℂ) = w :=
          hginjT (hballρ _ hmem).2 hw (hconst _ hmem)
        have hρ2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
          have h4 : w + ((ρ / 2 : ℝ) : ℂ) = w + 0 := by rw [add_zero]; exact heq2
          exact add_left_cancel h4
        rw [Complex.ofReal_eq_zero] at hρ2
        linarith
      · exact hne
    -- Differentiability everywhere on `W` (removable singularity at critical values).
    have hdiff : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        DifferentiableAt ℂ η ζ := by
      intro ζ hζ
      by_cases hder : deriv (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ) = 0
      swap
      · exact hd_nc ζ hζ hder
      obtain ⟨ρ, hρ0, hballρ⟩ := Metric.eventually_nhds_iff_ball.mp
        ((eventually_nhdsWithin_iff.mp (hcrit (η ζ) (hBsub (hηB ζ hζ)))).and
          (isOpen_ball.eventually_mem (hηB ζ hζ)))
      have hsub' : ball (η ζ) ρ ⊆ ball (χ x₀) r := fun z hz ↦ (hballρ z hz).2
      have hW'open : IsOpen ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ) :=
        imgOpen _ _ hTopen hgan hginjT _ (hsub'.trans hBsub) isOpen_ball
      have hζW' : ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ :=
        ⟨η ζ, mem_ball_self hρ0, hgη ζ hζ⟩
      have hW'W : (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ ⊆
          (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r :=
        Set.image_mono hsub'
      have hoff : DifferentiableOn ℂ η
          (((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ) \ {ζ}) := by
        rintro ζ' ⟨hζ'W', hζ'ne⟩
        obtain ⟨w', hw'ball, rfl⟩ := hζ'W'
        refine (hd_nc _ (hW'W ⟨w', hw'ball, rfl⟩) ?_).differentiableWithinAt
        rw [hηg w' (hsub' hw'ball)]
        refine (hballρ w' hw'ball).1 ?_
        intro hmem
        apply hζ'ne
        rw [Set.mem_singleton_iff] at hmem ⊢
        rw [hmem]
        exact hgη ζ hζ
      have hW'diff : DifferentiableOn ℂ η ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ) :=
        (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
          (hW'open.mem_nhds hζW')).mp ⟨hoff, hηc ζ hζ⟩
      exact hW'diff.differentiableAt (hW'open.mem_nhds hζW')
    -- The inverse reading is analytic at the base point; assemble the composite.
    have hWdiff : DifferentiableOn ℂ η ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r) :=
      fun ζ hζ ↦ (hdiff ζ hζ).differentiableWithinAt
    have hηan : AnalyticAt ℂ η (e (y₀ : ℂ̂)) := (hWdiff.analyticOnNhd hWopen) _ hy₀W
    have hval : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : ↥U → ℂ̂) y₀ :=
      contMDiff_subtype_val.contMDiffAt
    have hesm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) ((y₀ : ℂ̂)) :=
      contMDiffAt_of_mem_maximalAtlas hemax hy₀esrc
    have hηsm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω η (e (y₀ : ℂ̂)) :=
      contMDiffAt_iff_contDiffAt.mpr hηan.contDiffAt
    have hχsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑χ.symm) (η (e (y₀ : ℂ̂))) :=
      contMDiffAt_symm_of_mem_maximalAtlas hχmax (hBsub (hηB _ hy₀W)).1
    have hcomp2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        ((⇑χ.symm ∘ η ∘ ⇑e) ∘ (Subtype.val : ↥U → ℂ̂)) y₀ :=
      ContMDiffAt.comp y₀
        (ContMDiffAt.comp ((y₀ : ℂ̂)) hχsymm
          (ContMDiffAt.comp ((y₀ : ℂ̂)) hηsm hesm)) hval
    refine hcomp2.congr_of_eventuallyEq ?_
    have hSopen : IsOpen (e.source ∩ ⇑e ⁻¹' ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀)
        r)) :=
      e.continuousOn.isOpen_inter_preimage e.open_source hWopen
    have hy₀S : (y₀ : ℂ̂) ∈
        e.source ∩ ⇑e ⁻¹' ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r) :=
      ⟨hy₀esrc, hy₀W⟩
    have hmemS : (Subtype.val : ↥U → ℂ̂) ⁻¹'
        (e.source ∩ ⇑e ⁻¹' ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r)) ∈ 𝓝 y₀
            :=
      (hSopen.preimage continuous_subtype_val).mem_nhds hy₀S
    filter_upwards [hmemS] with y hy
    obtain ⟨w, hwB, hgw⟩ := himg (e (y : ℂ̂)) hy.2
    have hwT := hBsub hwB
    have hwT2 : φ (χ.symm w) ∈ e.source := hwT.2
    have h7 : (y : ℂ̂) = φ (χ.symm w) := by
      have h8 := e.left_inv hy.1
      rw [← hgw] at h8
      have h9 : e.symm ((⇑e ∘ φ ∘ ⇑χ.symm) w) = φ (χ.symm w) := by
        simp only [Function.comp_apply]
        exact e.left_inv hwT2
      rw [← h8]
      exact h9
    change Function.invFun φ (y : ℂ̂) = χ.symm (η (e (y : ℂ̂)))
    rw [← hgw, hηg w hwB, h7, Function.leftInverse_invFun hinj (χ.symm w)]
  exact ⟨U, ⟨{
    toFun := fun x ↦ ⟨φ x, Set.mem_range_self x⟩
    invFun := fun y ↦ Function.invFun φ (y : ℂ̂)
    left_inv := fun x ↦ Function.leftInverse_invFun hinj x
    right_inv := fun y ↦ Subtype.ext (Function.invFun_eq y.2)
    contMDiff_toFun := hF
    contMDiff_invFun := hGsm }⟩⟩

end RiemannDynamics
