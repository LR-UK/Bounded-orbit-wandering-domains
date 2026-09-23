/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.BipolarGreen.DriftBound

/-!
# Bipolar Green: the exterior bound

The shrink-uniform master bound `exists_pieceGreen_dipole_exterior_bound`:
around two marked points off a closed coordinate disk there are pole radii,
with doubled closed chart balls avoiding the disk and each other, and a
constant bounding the dipole difference of the Green's functions of every
sufficiently shrunken piece outside the two pole balls — by the interior
and growth estimates, the chain Harnack comparison pinned at the drift base
point, and the one-sided extension bound.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ) ω M]
variable [T2Space M] [ConnectedSpace M]

/-- The shrink-uniform master bound: around two marked points off a closed coordinate
disk there are pole radii, with doubled closed chart balls avoiding the disk and each
other, and a constant bounding the dipole difference of the Green's functions of every
sufficiently shrunken piece outside the two pole balls — by the interior and growth
estimates, the chain Harnack comparison pinned at the drift base point, and the
one-sided extension bound. -/
theorem exists_pieceGreen_dipole_exterior_bound (D₀ : CoordDisk M) {p₁ p₂ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier) (hne : p₁ ≠
        p₂) :
    ∃ r₁ r₂ C₀ : ℝ, 0 < r₁ ∧ 0 < r₂ ∧ 1 ≤ C₀ ∧
      closedBall (chartAt ℂ p₁ p₁) (2 * r₁) ⊆ (chartAt ℂ p₁).target ∧
      closedBall (chartAt ℂ p₂ p₂) (2 * r₂) ⊆ (chartAt ℂ p₂).target ∧
      (∀ w ∈ closedBall (chartAt ℂ p₁ p₁) (2 * r₁),
        (chartAt ℂ p₁).symm w ∉ D₀.closedCarrier ∧ (chartAt ℂ p₁).symm w ≠ p₂) ∧
      (∀ w ∈ closedBall (chartAt ℂ p₂ p₂) (2 * r₂),
        (chartAt ℂ p₂).symm w ∉ D₀.closedCarrier ∧
          (chartAt ℂ p₂).symm w ∉
            (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) (2 * r₁)) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht1 : t ≤ 1, t ≤ 1 / 4 → ∀ x : M,
        x ∉ (chartAt ℂ p₁).source ∩ ⇑(chartAt ℂ p₁) ⁻¹' ball (chartAt ℂ p₁
            p₁) r₁ →
        x ∉ (chartAt ℂ p₂).source ∩ ⇑(chartAt ℂ p₂) ⁻¹' ball (chartAt ℂ p₂
            p₂) r₂ →
        |pieceGreen (D₀.shrink t ht ht1).compl p₁ x -
          pieceGreen (D₀.shrink t ht ht1).compl p₂ x| ≤ C₀ := by
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
  have pgnonneg : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ≠ p → 0 ≤ pieceGreen P p y := by
    intro P p hp hcs hnc hGF y hyp
    have := hcs
    have := hnc
    by_cases hy : y ∈ P
    · rw [pgval P p hp y hy]
      exact (greenEnvelope_pos hGF _
        (fun hcon ↦ hyp (congrArg Subtype.val hcon))).le
    · rw [pgzero P p y hy]
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
  /- ## The one-sided extension bound: away from both pole disks, every candidate
  for one pole is dominated by the other Green's function plus the circle constant. -/
  have side : ∀ (P : Opens M), ConnectedSpace ↥P → NoncompactSpace ↥P →
      ∀ (pa : M) (hpa : pa ∈ P) (pb : M) (hpb : pb ∈ P),
      HasGreenFunction (⟨pa, hpa⟩ : ↥P) → HasGreenFunction (⟨pb, hpb⟩ : ↥P) →
      ∀ (ra rb Cc : ℝ), 0 < ra → 0 < rb → 0 ≤ Cc →
      closedBall (chartAt ℂ pa pa) ra ⊆ (chartAt ℂ pa).target →
      closedBall (chartAt ℂ pb pb) rb ⊆ (chartAt ℂ pb).target →
      (∀ y ∈ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) ra, y ∈ P) →
      (∀ y ∈ (chartAt ℂ pb).symm '' closedBall (chartAt ℂ pb pb) rb, y ∈ P) →
      (∀ y ∈ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) ra,
        y ∉ (chartAt ℂ pb).symm '' closedBall (chartAt ℂ pb pb) rb) →
      (∀ z ∈ (chartAt ℂ pa).symm '' sphere (chartAt ℂ pa pa) ra,
        pieceGreen P pa z - pieceGreen P pb z ≤ Cc) →
      ∀ x, x ∈ P →
        x ∉ (chartAt ℂ pa).source ∩ chartAt ℂ pa ⁻¹' ball (chartAt ℂ pa pa) ra →
        x ∉ (chartAt ℂ pb).source ∩ chartAt ℂ pb ⁻¹' ball (chartAt ℂ pb pb) rb →
        pieceGreen P pa x ≤ pieceGreen P pb x + Cc := by
    intro P hcs hnc pa hpa pb hpb hGa hGb ra rb Cc hra hrb hCc0 htga htgb hcarPa
      hcarPb hdisjab hcirc x hxP hxVa hxVb
    have := hcs
    have := hnc
    have hBdda := (mharmonicOn_greenEnvelope hGa).2
    set ea : OpenPartialHomeomorph M ℂ := chartAt ℂ pa with hea
    set ca : ℂ := ea pa with hca
    set eb : OpenPartialHomeomorph M ℂ := chartAt ℂ pb with heb
    set cb : ℂ := eb pb with hcb
    have hpasrc : pa ∈ ea.source := mem_chart_source ℂ pa
    have hpbsrc : pb ∈ eb.source := mem_chart_source ℂ pb
    have hpaDa : pa ∈ ea.symm '' closedBall ca ra :=
      ⟨ca, mem_closedBall_self hra.le, by rw [hca]; exact ea.left_inv hpasrc⟩
    have hpbDb : pb ∈ eb.symm '' closedBall cb rb :=
      ⟨cb, mem_closedBall_self hrb.le, by rw [hcb]; exact eb.left_inv hpbsrc⟩
    have hpanb : pa ≠ pb := fun hcon ↦ hdisjab pa hpaDa (hcon ▸ hpbDb)
    have hgb_nonneg : ∀ z : M, z ≠ pb → 0 ≤ pieceGreen P pb z :=
      pgnonneg P pb hpb hcs hnc hGb
    have hgb_harm : ∀ z : M, z ∈ P → z ≠ pb → MHarmonicAt (pieceGreen P pb) z :=
      fun z h1 h2 ↦ pgharm P pb hpb hcs hnc hGb z h1 h2
    have hsymcb : eb.symm cb = pb := by rw [hcb]; exact eb.left_inv hpbsrc
    -- per-candidate bound at the point `x`
    have percand : ∀ (v : ↥P → ℝ), v ∈ greenFamily (⟨pa, hpa⟩ : ↥P) →
        v ⟨x, hxP⟩ ≤ pieceGreen P pb x + Cc := by
      intro v hv
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P pa hpa v hv
      -- bound for `vE` near `pb`
      have hvbCA : ContinuousAt vE pb :=
        hvEcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.2 hpanb.symm))
      set bv : ℝ := vE pb + 1 with hbv
      have hev : ∀ᶠ z in 𝓝 pb, vE z ≤ bv := by
        have h1 : vE pb < bv := by rw [hbv]; linarith only []
        filter_upwards [hvbCA (Iio_mem_nhds h1)] with z hz
        exact (Set.mem_Iio.1 hz).le
      have hcbt : cb ∈ eb.target := by rw [hcb]; exact eb.map_source hpbsrc
      have hprevb : eb.symm ⁻¹' {z | vE z ≤ bv} ∈ 𝓝 cb := by
        have h1 : ContinuousAt eb.symm cb := eb.continuousAt_symm hcbt
        exact h1.preimage_mem_nhds (hsymcb ▸ hev)
      obtain ⟨ρv, hρv, hρvsub⟩ := nhds_basis_closedBall.mem_iff.1 hprevb
      -- the harmonic extension across the pole `pb`
      obtain ⟨rP, hrP, hrPsub, h, hharm, hval⟩ := exists_harmonic_pole_extension hGb
      have hnety : Nonempty ↥P := ⟨⟨pb, hpb⟩⟩
      have hctb : chartAt ℂ (⟨pb, hpb⟩ : ↥P) = eb.subtypeRestr hnety :=
        Opens.chartAt_eq
      have hcenterb : chartAt ℂ (⟨pb, hpb⟩ : ↥P) (⟨pb, hpb⟩ : ↥P) = cb := by
        rw [hctb, eb.subtypeRestr_coe hnety, hcb]
        rfl
      rw [hcenterb] at hrPsub hharm hval
      have hhc : ContinuousOn h (closedBall cb (rP / 2)) :=
        hharm.continuousOn.mono (closedBall_subset_ball (by linarith only [hrP]))
      obtain ⟨wm, hwm, hwmmin⟩ := (isCompact_closedBall cb (rP / 2)).exists_isMinOn
        ⟨cb, mem_closedBall_self (by linarith only [hrP])⟩ hhc
      set mh : ℝ := h wm with hmh
      -- the excision radius
      set δ : ℝ := min (min (rP / 2) ρv) (min (rb / 2) (Real.exp (mh - bv))) with hδ
      have hδ0 : 0 < δ := lt_min (lt_min (by linarith only [hrP]) hρv)
        (lt_min (by linarith only [hrb]) (Real.exp_pos _))
      have hδrP : δ ≤ rP / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
      have hδρv : δ ≤ ρv := le_trans (min_le_left _ _) (min_le_right _ _)
      have hδrb : δ ≤ rb / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hδexp : δ ≤ Real.exp (mh - bv) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hlogδ : Real.log δ ≤ mh - bv := by
        calc Real.log δ ≤ Real.log (Real.exp (mh - bv)) := Real.log_le_log hδ0 hδexp
          _ = mh - bv := Real.log_exp _
      -- the δ-circle facts
      have hΓδ : ∀ z : M, z ∈ eb.source → dist (eb z) cb = δ →
          vE z ≤ bv ∧ bv ≤ pieceGreen P pb z ∧ z ≠ pb ∧ z ∈ P := by
        intro z hzs hzd
        have hzval : eb.symm (eb z) = z := eb.left_inv hzs
        have hznepb : z ≠ pb := by
          intro hcon
          rw [hcon, ← hcb, dist_self] at hzd
          rw [← hzd] at hδ0
          exact lt_irrefl _ hδ0
        have hzDb : z ∈ eb.symm '' closedBall cb rb :=
          ⟨eb z, mem_closedBall.2 (by rw [hzd]; linarith only [hδrb, hrb]), hzval⟩
        have hzP : z ∈ P := hcarPb z hzDb
        refine ⟨?_, ?_, hznepb, hzP⟩
        · have h1 : eb z ∈ closedBall cb ρv := by
            rw [mem_closedBall, hzd]
            exact hδρv
          have h2 := hρvsub h1
          rw [Set.mem_preimage, hzval] at h2
          exact h2
        · have hwball : eb z ∈ ball cb rP := by
            rw [mem_ball, hzd]
            linarith only [hδrP, hrP]
          have hwnc : eb z ≠ cb := by
            intro hcon
            rw [← dist_eq_zero] at hcon
            rw [hcon] at hzd
            rw [← hzd] at hδ0
            exact lt_irrefl _ hδ0
          have h2 := hval (eb z) ⟨hwball, by
            simp only [Set.mem_singleton_iff]
            exact hwnc⟩
          have hwtgt : eb z ∈ (chartAt ℂ (⟨pb, hpb⟩ : ↥P)).target := hrPsub hwball
          have hzsubval : ((chartAt ℂ (⟨pb, hpb⟩ : ↥P)).symm (eb z) : M) = z := by
            have heqO := eb.subtypeRestr_symm_eqOn hnety
            have h3 : eb.symm (eb z) =
                (Subtype.val ∘ (eb.subtypeRestr hnety).symm) (eb z) := by
              apply heqO
              rw [← hctb]
              exact hwtgt
            rw [hzval] at h3
            rw [hctb]
            exact h3.symm
          have h4 : (chartAt ℂ (⟨pb, hpb⟩ : ↥P)).symm (eb z) = (⟨z, hzP⟩ : ↥P) :=
            Subtype.ext hzsubval
          rw [h4] at h2
          have h5 : greenEnvelope (⟨pb, hpb⟩ : ↥P) ⟨z, hzP⟩ = h (eb z) - Real.log δ := by
            have h6 : ‖eb z - cb‖ = δ := by rw [← dist_eq_norm]; exact hzd
            rw [h6] at h2
            linarith only [h2]
          rw [pgval P pb hpb z hzP, h5]
          have h7 : mh ≤ h (eb z) := hwmmin (mem_closedBall.2 (by rw [hzd]; exact hδrP))
          linarith only [h7, hlogδ]
      -- the capped competitor on the excised region
      set Dδ : Set M := eb.symm '' closedBall cb δ with hDδ
      have hDδtgt : closedBall cb δ ⊆ eb.target :=
        (closedBall_subset_closedBall (by linarith only [hδrb, hrb])).trans htgb
      have hDδcomp : IsCompact Dδ := (isCompact_closedBall _ _).image_of_continuousOn
        (eb.continuousOn_symm.mono hDδtgt)
      have hpbDδ : pb ∈ Dδ := ⟨cb, mem_closedBall_self hδ0.le, hsymcb⟩
      have hDδVb : Dδ ⊆ eb.source ∩ eb ⁻¹' ball cb rb := by
        rintro z ⟨w, hw, hwz⟩
        have hwt : w ∈ eb.target := hDδtgt hw
        refine ⟨hwz ▸ eb.map_target hwt, ?_⟩
        rw [Set.mem_preimage, ← hwz, eb.right_inv hwt, mem_ball]
        have h1 := mem_closedBall.1 hw
        linarith only [h1, hδrb, hrb]
      set Da : Set M := ea.symm '' closedBall ca ra with hDa
      have hDacomp : IsCompact Da := (isCompact_closedBall _ _).image_of_continuousOn
        (ea.continuousOn_symm.mono htga)
      set Ω : Set M := (P : Set M) ∩ Daᶜ ∩ Dδᶜ with hΩdef
      have hΩopen : IsOpen Ω := (P.2.inter hDacomp.isClosed.isOpen_compl).inter
        hDδcomp.isClosed.isOpen_compl
      have hΩne : Ω ≠ Set.univ := by
        intro hcon
        have hpaΩ : pa ∈ Ω := by rw [hcon]; trivial
        exact hpaΩ.1.2 hpaDa
      set wc : M → ℝ := fun z ↦ max (vE z - pieceGreen P pb z) 0 with hwc
      have hΩnepa : ∀ z ∈ Ω, z ≠ pa := fun z hz hcon ↦ hz.1.2 (hcon ▸ hpaDa)
      have hΩnepb : ∀ z ∈ Ω, z ≠ pb := fun z hz hcon ↦ hz.2 (hcon ▸ hpbDδ)
      have hwcsub : MSubharmonicOn wc Ω := by
        intro z hz
        have h1 : MSubharmonicAt (fun q ↦ vE q - pieceGreen P pb q) z :=
          (hvEsub z (Set.mem_compl_singleton_iff.2 (hΩnepa z hz))).sub_mharmonicAt
            (hgb_harm z hz.1.1 (hΩnepb z hz))
        have h2 : MSubharmonicAt (fun _ : M ↦ (0 : ℝ)) z :=
          (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt
        rw [hwc]
        exact h1.max h2
      have hwcout : ∀ z ∈ Ω, z ∉ KE → wc z ≤ Cc := by
        intro z hz hzK
        rw [hwc]
        simp only
        rw [hKE0 z hzK]
        have h1 : 0 ≤ pieceGreen P pb z := hgb_nonneg z (hΩnepb z hz)
        exact max_le (by linarith only [h1, hCc0]) hCc0
      have hwcfr : ∀ y ∈ closure Ω \ Ω, ContinuousAt wc y ∧ wc y ≤ Cc := by
        rintro y ⟨hycl, hyΩ⟩
        by_cases hyP : y ∈ P
        · by_cases hyDa : y ∈ Da
          · -- on the `pa` circle
            obtain ⟨w, hw, hwz⟩ := hyDa
            have hwt : w ∈ ea.target := htga hw
            have hysrc : y ∈ ea.source := hwz ▸ ea.map_target hwt
            have hyval : ea y = w := by rw [← hwz, ea.right_inv hwt]
            have hyled : dist (ea y) ca ≤ ra := by
              rw [hyval]
              exact mem_closedBall.1 hw
            have hyd : dist (ea y) ca = ra := by
              rcases lt_or_eq_of_le hyled with h1 | h1
              · exfalso
                have hOopen : IsOpen (ea.source ∩ ea ⁻¹' ball ca ra) :=
                  ea.isOpen_inter_preimage isOpen_ball
                have hyO : y ∈ ea.source ∩ ea ⁻¹' ball ca ra :=
                  ⟨hysrc, by rw [Set.mem_preimage]; exact mem_ball.2 h1⟩
                have hODa : ea.source ∩ ea ⁻¹' ball ca ra ⊆ Da := by
                  rintro q ⟨hq1, hq2⟩
                  rw [Set.mem_preimage] at hq2
                  exact ⟨ea q, ball_subset_closedBall hq2, ea.left_inv hq1⟩
                obtain ⟨q, hqO, hqΩ⟩ := mem_closure_iff.1 hycl _ hOopen hyO
                exact hqΩ.1.2 (hODa hqO)
              · exact h1
            have hyΓa : y ∈ ea.symm '' sphere ca ra :=
              ⟨ea y, mem_sphere.2 hyd, ea.left_inv hysrc⟩
            have hynepa : y ≠ pa := by
              intro hcon
              rw [hcon, ← hca, dist_self] at hyd
              rw [← hyd] at hra
              exact lt_irrefl _ hra
            have hynepb : y ≠ pb := fun hcon ↦
              hdisjab y ⟨w, hw, hwz⟩ (by rw [hcon]; exact hpbDb)
            have hcg : ContinuousAt (pieceGreen P pb) y :=
              (hgb_harm y hyP hynepb).continuousAt
            have hcv : ContinuousAt vE y := hvEcont.continuousAt
              (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hynepa))
            refine ⟨by rw [hwc]; exact (hcv.sub hcg).max continuousAt_const, ?_⟩
            rw [hwc]
            simp only
            have h2 : vE y ≤ pieceGreen P pa y := by
              have h3 : v ⟨y, hyP⟩ ≤ greenEnvelope (⟨pa, hpa⟩ : ↥P) ⟨y, hyP⟩ :=
                le_csSup (hBdda _ (fun hcon ↦ hynepa (congrArg Subtype.val hcon)))
                  ⟨v, hv, rfl⟩
              have h3' : vE y = v ⟨y, hyP⟩ := hvEval ⟨y, hyP⟩
              rw [h3', pgval P pa hpa y hyP]
              exact h3
            have h4 := hcirc y hyΓa
            exact max_le (by linarith only [h2, h4]) hCc0
          · -- on the `δ` circle
            have hyDδ : y ∈ Dδ := by
              by_contra hyD
              exact hyΩ ⟨⟨hyP, hyDa⟩, hyD⟩
            obtain ⟨w, hw, hwz⟩ := hyDδ
            have hwt : w ∈ eb.target := hDδtgt hw
            have hysrc : y ∈ eb.source := hwz ▸ eb.map_target hwt
            have hyval : eb y = w := by rw [← hwz, eb.right_inv hwt]
            have hyled : dist (eb y) cb ≤ δ := by
              rw [hyval]
              exact mem_closedBall.1 hw
            have hyd : dist (eb y) cb = δ := by
              rcases lt_or_eq_of_le hyled with h1 | h1
              · exfalso
                have hOopen : IsOpen (eb.source ∩ eb ⁻¹' ball cb δ) :=
                  eb.isOpen_inter_preimage isOpen_ball
                have hyO : y ∈ eb.source ∩ eb ⁻¹' ball cb δ :=
                  ⟨hysrc, by rw [Set.mem_preimage]; exact mem_ball.2 h1⟩
                have hODδ : eb.source ∩ eb ⁻¹' ball cb δ ⊆ Dδ := by
                  rintro q ⟨hq1, hq2⟩
                  rw [Set.mem_preimage] at hq2
                  exact ⟨eb q, ball_subset_closedBall hq2, eb.left_inv hq1⟩
                obtain ⟨q, hqO, hqΩ⟩ := mem_closure_iff.1 hycl _ hOopen hyO
                exact hqΩ.2 (hODδ hqO)
              · exact h1
            obtain ⟨hb1, hb2, hynepb, hyP'⟩ := hΓδ y hysrc hyd
            have hynepa : y ≠ pa := by
              intro hcon
              apply hdisjab pa hpaDa
              rw [← hcon]
              exact ⟨w, closedBall_subset_closedBall
                (by linarith only [hδrb, hrb]) hw, hwz⟩
            have hcg : ContinuousAt (pieceGreen P pb) y :=
              (hgb_harm y hyP hynepb).continuousAt
            have hcv : ContinuousAt vE y := hvEcont.continuousAt
              (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hynepa))
            refine ⟨by rw [hwc]; exact (hcv.sub hcg).max continuousAt_const, ?_⟩
            rw [hwc]
            simp only
            exact max_le (by linarith only [hb1, hb2, hCc0]) hCc0
        · -- off the piece: the competitor vanishes on a neighborhood
          have hyKE : y ∉ KE := fun hmem ↦ hyP (hKEP hmem)
          have hynepb : y ≠ pb := fun hcon ↦ hyP (by rw [hcon]; exact hpb)
          have hOn : IsOpen (KEᶜ ∩ {pb}ᶜ) := hKEc.isClosed.isOpen_compl.inter
            isOpen_compl_singleton
          have hyO : y ∈ KEᶜ ∩ {pb}ᶜ := ⟨hyKE, Set.mem_compl_singleton_iff.2 hynepb⟩
          have hev0 : wc =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
            filter_upwards [hOn.mem_nhds hyO] with q hq
            rw [hwc]
            simp only
            rw [hKE0 q hq.1]
            have h1 : 0 ≤ pieceGreen P pb q := hgb_nonneg q
              (Set.mem_compl_singleton_iff.1 hq.2)
            rw [max_eq_right (by linarith only [h1])]
          refine ⟨continuousAt_const.congr_of_eventuallyEq hev0, ?_⟩
          have h2 : wc y = 0 := hev0.eq_of_nhds
          rw [h2]
          exact hCc0
      have hwcle : ∀ z ∈ Ω, wc z ≤ Cc :=
        maxPrin Ω wc Cc KE hΩopen hΩne hwcsub hKEc hwcout hwcfr
      -- conclude at the point `x`
      by_cases hxDa : x ∈ Da
      · obtain ⟨w, hw, hwz⟩ := hxDa
        have hwt : w ∈ ea.target := htga hw
        have hxsrc : x ∈ ea.source := hwz ▸ ea.map_target hwt
        have hxval : ea x = w := by rw [← hwz, ea.right_inv hwt]
        have hxled : dist (ea x) ca ≤ ra := by
          rw [hxval]
          exact mem_closedBall.1 hw
        have hxd : dist (ea x) ca = ra := by
          rcases lt_or_eq_of_le hxled with h1 | h1
          · exact absurd ⟨hxsrc, by rw [Set.mem_preimage]; exact mem_ball.2 h1⟩ hxVa
          · exact h1
        have hxΓa : x ∈ ea.symm '' sphere ca ra :=
          ⟨ea x, mem_sphere.2 hxd, ea.left_inv hxsrc⟩
        have hxnepa : x ≠ pa := by
          intro hcon
          rw [hcon, ← hca, dist_self] at hxd
          rw [← hxd] at hra
          exact lt_irrefl _ hra
        have h3 : v ⟨x, hxP⟩ ≤ greenEnvelope (⟨pa, hpa⟩ : ↥P) ⟨x, hxP⟩ :=
          le_csSup (hBdda _ (fun hcon ↦ hxnepa (congrArg Subtype.val hcon)))
            ⟨v, hv, rfl⟩
        have h4 := hcirc x hxΓa
        have h5 : greenEnvelope (⟨pa, hpa⟩ : ↥P) ⟨x, hxP⟩ = pieceGreen P pa x :=
          (pgval P pa hpa x hxP).symm
        rw [h5] at h3
        linarith only [h3, h4]
      · have hxDδ : x ∉ Dδ := fun hmem ↦ hxVb (hDδVb hmem)
        have hxΩ : x ∈ Ω := ⟨⟨hxP, hxDa⟩, hxDδ⟩
        have h5 := hwcle x hxΩ
        rw [hwc] at h5
        simp only at h5
        have h6 : vE x - pieceGreen P pb x ≤ Cc := le_trans (le_max_left _ _) h5
        have h7 : v ⟨x, hxP⟩ = vE x := (hvEval ⟨x, hxP⟩).symm
        linarith only [h6, h7]
    -- close the supremum over the family
    rw [pgval P pa hpa x hxP]
    simp only [greenEnvelope]
    refine csSup_le ⟨0, (fun _ : ↥P ↦ (0 : ℝ)), zeroFam P pa hpa, rfl⟩ ?_
    rintro b ⟨v, hv, rfl⟩
    exact percand v hv
  /- ## The center chart. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D₀.center with he₀
  set c₀ : ℂ := e₀ D₀.center with hc₀
  set r₀ : ℝ := D₀.radius with hr₀def
  have hr₀ : 0 < r₀ := D₀.radius_pos
  have hcb₀tgt : closedBall c₀ r₀ ⊆ e₀.target := D₀.closedBall_subset
  have hcar₀ : D₀.closedCarrier = e₀.symm '' closedBall c₀ r₀ := rfl
  have hcen₀src : D₀.center ∈ e₀.source := mem_chart_source ℂ D₀.center
  have hcen₀car : D₀.center ∈ D₀.closedCarrier :=
    ⟨c₀, mem_closedBall_self hr₀.le, e₀.left_inv hcen₀src⟩
  /- ## The pole charts and the avoidance radii. -/
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  have havoid1 : ∃ S : ℝ, 0 < S ∧ closedBall c₁ S ⊆ e₁.target ∧
      ∀ w ∈ closedBall c₁ S, e₁.symm w ∉ D₀.closedCarrier ∧ e₁.symm w ≠ p₂ := by
    have hopen : IsOpen (e₁.target ∩ e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ {p₂}ᶜ)) :=
      e₁.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter isOpen_compl_singleton)
    have hmem : c₁ ∈ e₁.target ∩ e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ {p₂}ᶜ) := by
      refine ⟨by rw [hc₁]; exact e₁.map_source hp₁src, ?_⟩
      rw [Set.mem_preimage, hc₁, e₁.left_inv hp₁src]
      exact ⟨hp₁, Set.mem_compl_singleton_iff.2 hne⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw ↦ (hSsub hw).1, fun w hw ↦ ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, Set.mem_compl_singleton_iff.1 h2.2⟩
  obtain ⟨S₁, hS₁0, hS₁tgt, hS₁av⟩ := havoid1
  set r₁ : ℝ := S₁ / 2 with hr₁def
  have hr₁ : 0 < r₁ := by rw [hr₁def]; exact half_pos hS₁0
  have h2r₁ : 2 * r₁ ≤ S₁ := by rw [hr₁def]; linarith only []
  have htgt1 : closedBall c₁ (2 * r₁) ⊆ e₁.target :=
    (closedBall_subset_closedBall h2r₁).trans hS₁tgt
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  have hCar1cp : IsCompact Car1 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono htgt1)
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₁av w (closedBall_subset_closedBall h2r₁ hw)
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have havoid2 : ∃ S : ℝ, 0 < S ∧ closedBall c₂ S ⊆ e₂.target ∧
      ∀ w ∈ closedBall c₂ S, e₂.symm w ∉ D₀.closedCarrier ∧ e₂.symm w ∉ Car1 := by
    have hopen : IsOpen (e₂.target ∩ e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ Car1ᶜ)) :=
      e₂.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter
          hCar1cp.isClosed.isOpen_compl)
    have hmem : c₂ ∈ e₂.target ∩ e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ Car1ᶜ) := by
      refine ⟨by rw [hc₂]; exact e₂.map_source hp₂src, ?_⟩
      rw [Set.mem_preimage, hc₂, e₂.left_inv hp₂src]
      exact ⟨hp₂, fun hmem2 ↦ (hCar1av p₂ hmem2).2 rfl⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw ↦ (hSsub hw).1, fun w hw ↦ ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, h2.2⟩
  obtain ⟨S₂, hS₂0, hS₂tgt, hS₂av⟩ := havoid2
  set r₂ : ℝ := S₂ / 2 with hr₂def
  have hr₂ : 0 < r₂ := by rw [hr₂def]; exact half_pos hS₂0
  have h2r₂ : 2 * r₂ ≤ S₂ := by rw [hr₂def]; linarith only []
  have htgt2 : closedBall c₂ (2 * r₂) ⊆ e₂.target :=
    (closedBall_subset_closedBall h2r₂).trans hS₂tgt
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar2cp : IsCompact Car2 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₂.continuousOn_symm.mono htgt2)
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₂av w (closedBall_subset_closedBall h2r₂ hw)
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  have hp₁ne₂ : p₁ ∉ Car2 := fun hmem ↦ (hCar2av p₁ hmem).2 hp₁Car1
  /- ## The interior pole balls. -/
  set B₁ : Set M := e₁.source ∩ e₁ ⁻¹' ball c₁ r₁ with hB₁
  set B₂ : Set M := e₂.source ∩ e₂ ⁻¹' ball c₂ r₂ with hB₂
  have hB₁open : IsOpen B₁ := e₁.isOpen_inter_preimage isOpen_ball
  have hB₂open : IsOpen B₂ := e₂.isOpen_inter_preimage isOpen_ball
  have hp₁B₁ : p₁ ∈ B₁ :=
    ⟨hp₁src, by rw [Set.mem_preimage, ← hc₁]; exact mem_ball_self hr₁⟩
  have hp₂B₂ : p₂ ∈ B₂ :=
    ⟨hp₂src, by rw [Set.mem_preimage, ← hc₂]; exact mem_ball_self hr₂⟩
  have hB₁img : e₁.symm '' ball c₁ r₁ = B₁ :=
    himg e₁ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1)
  have hB₂img : e₂.symm '' ball c₂ r₂ = B₂ :=
    himg e₂ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2)
  have hB₁Car : B₁ ⊆ Car1 := by
    rw [← hB₁img, hCar1]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁])))
  have hB₂Car : B₂ ⊆ Car2 := by
    rw [← hB₂img, hCar2]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂])))
  /- ## The auxiliary base point away from the three disks. -/
  have hp₃ex : ∃ p₃ : M, p₃ ∉ D₀.closedCarrier ∧ p₃ ∉ Car1 ∧ p₃ ∉ Car2 := by
    by_contra hcon
    push Not at hcon
    have hAopen : IsOpen D₀.closedCarrier := by
      have heq : D₀.closedCarrier = (Car1 ∪ Car2)ᶜ := by
        apply Set.Subset.antisymm
        · intro z hz
          rintro (h | h)
          · exact (hCar1av z h).1 hz
          · exact (hCar2av z h).1 hz
        · intro z hz
          by_cases h1 : z ∈ D₀.closedCarrier
          · exact h1
          by_cases h2 : z ∈ Car1
          · exact absurd (Or.inl h2) hz
          · exact absurd (Or.inr (hcon z h1 h2)) hz
      rw [heq]
      exact (hCar1cp.union hCar2cp).isClosed.isOpen_compl
    have hclopen : IsClopen D₀.closedCarrier :=
      ⟨D₀.isCompact_closedCarrier.isClosed, hAopen⟩
    have huniv := hclopen.eq_univ ⟨D₀.center, hcen₀car⟩
    apply hp₁
    rw [huniv]
    trivial
  obtain ⟨p₃, hp₃car, hp₃C1, hp₃C2⟩ := hp₃ex
  have h₃₁ : p₃ ≠ p₁ := fun hcon ↦ hp₃C1 (hcon ▸ hp₁Car1)
  have h₃₂ : p₃ ≠ p₂ := fun hcon ↦ hp₃C2 (hcon ▸ hp₂Car2)
  /- ## The Harnack chain domains, the chain compact and the constants. -/
  set Dq : CoordDisk M := D₀.shrink (1 / 4) (by norm_num) (by norm_num) with hDq
  have hDqcar : Dq.closedCarrier = e₀.symm '' closedBall c₀ (1 / 4 * r₀) := rfl
  have hDqsub : Dq.closedCarrier ⊆ D₀.closedCarrier := by
    rw [hDqcar, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₀]))
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
  have hp₁half : p₁ ∈ half1.closedCarrier := by
    rw [hhalf1car]
    exact ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂half : p₂ ∈ half2.closedCarrier := by
    rw [hhalf2car]
    exact ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  have hdisjQ1 : Disjoint Dq.closedCarrier half1.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz1
    exact (hCar1av z (hhalf1Car hz1)).1 (hDqsub hzQ)
  have hdisjQ2 : Disjoint Dq.closedCarrier half2.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz2
    exact (hCar2av z (hhalf2Car hz2)).1 (hDqsub hzQ)
  set Ω₁ : Set M := (Dq.closedCarrier ∪ half1.closedCarrier)ᶜ with hΩ₁
  set Ω₂ : Set M := (Dq.closedCarrier ∪ half2.closedCarrier)ᶜ with hΩ₂
  have hΩ₁open : IsOpen Ω₁ := (Dq.isCompact_closedCarrier.union
    half1.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₂open : IsOpen Ω₂ := (Dq.isCompact_closedCarrier.union
    half2.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₁conn : IsPreconnected Ω₁ :=
    (isConnected_two_coordDisk_compl Dq half1 hdisjQ1).isPreconnected
  have hΩ₂conn : IsPreconnected Ω₂ :=
    (isConnected_two_coordDisk_compl Dq half2 hdisjQ2).isPreconnected
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
  set K : Set M := Γ₁ ∪ Γ₂ ∪ {p₃} with hK
  have hKcp : IsCompact K := (hΓ₁cp.union hΓ₂cp).union isCompact_singleton
  have hp₃K : p₃ ∈ K := Or.inr rfl
  have hKΩ₁ : K ⊆ Ω₁ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar1av z (hΓ₁Car hz)).1 (hDqsub hmem)
      · exact hΓ₁half z hz hmem
    · rintro (hmem | hmem)
      · exact (hCar2av z (hΓ₂Car hz)).1 (hDqsub hmem)
      · exact (hCar2av z (hΓ₂Car hz)).2 (hhalf1Car hmem)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃car (hDqsub hmem)
      · exact hp₃C1 (hhalf1Car hmem)
  have hKΩ₂ : K ⊆ Ω₂ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar1av z (hΓ₁Car hz)).1 (hDqsub hmem)
      · exact (hCar2av z (hhalf2Car hmem)).2 (hΓ₁Car hz)
    · rintro (hmem | hmem)
      · exact (hCar2av z (hΓ₂Car hz)).1 (hDqsub hmem)
      · exact hΓ₂half z hz hmem
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃car (hDqsub hmem)
      · exact hp₃C2 (hhalf2Car hmem)
  obtain ⟨CH₁, hCH₁0, hCH₁⟩ := exists_harnack_chain_const hΩ₁open hΩ₁conn hKcp
      hKΩ₁
  obtain ⟨CH₂, hCH₂0, hCH₂⟩ := exists_harnack_chain_const hΩ₂open hΩ₂conn hKcp
      hKΩ₂
  /- ## The oscillation bound on the chain compact, via the per-piece pole bound. -/
  have oscBd : ∀ (pa : M) (ra : ℝ), 0 < ra →
      closedBall (chartAt ℂ pa pa) ra ⊆ (chartAt ℂ pa).target →
      ∀ (P : Opens M), ∀ hcs : ConnectedSpace ↥P, ∀ hnc : NoncompactSpace ↥P,
      ∀ hpaP : pa ∈ P, HasGreenFunction (⟨pa, hpaP⟩ : ↥P) →
      (∀ w ∈ closedBall (chartAt ℂ pa pa) ra, (chartAt ℂ pa).symm w ∈ P) →
      ∀ (ΩA : Set M) (CHa : ℝ),
      (∀ u : M → ℝ, MHarmonicOn u ΩA → (∀ x ∈ ΩA, 0 ≤ u x) →
        ∀ x ∈ K, ∀ y ∈ K, u x ≤ CHa * u y) →
      K ⊆ ΩA →
      (∀ z ∈ ΩA, z ∈ P) →
      (∀ z ∈ ΩA, z ∉ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) (ra / 2)) →
      ((chartAt ℂ pa).symm '' sphere (chartAt ℂ pa pa) ra ⊆ K) →
      ∀ z ∈ K, |pieceGreen P pa z - pieceGreen P pa p₃| ≤ CHa * Real.log 2 := by
    intro pa ra hra htgtA P hcs hnc hpaP hGFa hcarA ΩA CHa hCHa hKA hΩA1 hΩA2 hΓA z hzK
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
    have hxoutK : xout ∈ K := hΓA hxoutΓ
    have huout : u xout = Real.log 2 := by
      simp only [hu]
      rw [hxoutval]
      ring
    have h3 : u z ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos z hzK xout hxoutK
      rwa [huout] at h5
    have h4 : u p₃ ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos p₃ hp₃K xout hxoutK
      rwa [huout] at h5
    have h5 : 0 ≤ u z := hupos z (hKA hzK)
    have h6 : 0 ≤ u p₃ := hupos p₃ (hKA hp₃K)
    have h7 : pieceGreen P pa z - pieceGreen P pa p₃ = u p₃ - u z := by
      simp only [hu]
      ring
    rw [h7, abs_le]
    constructor <;> linarith only [h3, h4, h5, h6]
  /- ## The drift constant and the packaged bound. -/
  obtain ⟨Cd, hCd⟩ := exists_pieceGreen_drift_bound D₀ hp₁ hp₂ hp₃car hne h₃₁
      h₃₂
  set C₀ : ℝ := max (|Cd| + (CH₁ + CH₂) * Real.log 2) 1 with hC₀def
  have hC₀1 : (1 : ℝ) ≤ C₀ := le_max_right _ _
  have hC₀0 : (0 : ℝ) ≤ C₀ := by linarith only [hC₀1]
  refine ⟨r₁, r₂, C₀, hr₁, hr₂, hC₀1, htgt1, htgt2,
    (fun w hw ↦ hS₁av w (closedBall_subset_closedBall h2r₁ hw)),
    (fun w hw ↦ hS₂av w (closedBall_subset_closedBall h2r₂ hw)), ?_⟩
  intro tt htt htt1 htt4 x hx1 hx2
  /- ## The piece for the given shrink parameter. -/
  set Pt : Opens M := (D₀.shrink tt htt htt1).compl with hPt
  have hcart : (D₀.shrink tt htt htt1).closedCarrier =
      e₀.symm '' closedBall c₀ (tt * r₀) := rfl
  have hcarsubt : (D₀.shrink tt htt htt1).closedCarrier ⊆ D₀.closedCarrier := by
    rw [hcart, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htt1))
  have hcarqt : (D₀.shrink tt htt htt1).closedCarrier ⊆ Dq.closedCarrier := by
    rw [hcart, hDqcar]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right htt4 hr₀.le))
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
  /- ## The oscillation bounds and the chain-compact bound for this piece. -/
  have osc1 : ∀ z ∈ K, |pieceGreen Pt p₁ z - pieceGreen Pt p₁ p₃|
      ≤ CH₁ * Real.log 2 := by
    refine oscBd p₁ r₁ hr₁
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      Pt hconnT hncT hp₁t hGF1t hcarP1 Ω₁ CH₁ hCH₁ hKΩ₁ ?_ ?_ ?_
    · intro z hz hmem
      exact hz (Or.inl (hcarqt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inl hz)
  have osc2 : ∀ z ∈ K, |pieceGreen Pt p₂ z - pieceGreen Pt p₂ p₃|
      ≤ CH₂ * Real.log 2 := by
    refine oscBd p₂ r₂ hr₂
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      Pt hconnT hncT hp₂t hGF2t hcarP2 Ω₂ CH₂ hCH₂ hKΩ₂ ?_ ?_ ?_
    · intro z hz hmem
      exact hz (Or.inl (hcarqt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inr hz)
  have hKbd : ∀ z ∈ K, |pieceGreen Pt p₁ z - pieceGreen Pt p₂ z| ≤ C₀ := by
    intro z hz
    have h1 := osc1 z hz
    have h2 := osc2 z hz
    have h3 : |pieceGreen Pt p₁ p₃ - pieceGreen Pt p₂ p₃| ≤ Cd := hCd tt htt htt1
    have h6 : pieceGreen Pt p₁ z - pieceGreen Pt p₂ z =
        (pieceGreen Pt p₁ z - pieceGreen Pt p₁ p₃)
        + -(pieceGreen Pt p₂ z - pieceGreen Pt p₂ p₃)
        + (pieceGreen Pt p₁ p₃ - pieceGreen Pt p₂ p₃) := by
      ring
    have h5 := abs_add_three
      (pieceGreen Pt p₁ z - pieceGreen Pt p₁ p₃)
      (-(pieceGreen Pt p₂ z - pieceGreen Pt p₂ p₃))
      (pieceGreen Pt p₁ p₃ - pieceGreen Pt p₂ p₃)
    rw [abs_neg] at h5
    rw [h6]
    have h7 : Cd ≤ |Cd| := le_abs_self Cd
    have h8 : |Cd| + (CH₁ + CH₂) * Real.log 2 ≤ C₀ := le_max_left _ _
    calc |_ + _ + _| ≤ _ := h5
      _ ≤ C₀ := by linarith only [h1, h2, h3, h7, h8]
  /- ## The one-sided extension bounds close the master estimate. -/
  by_cases hxP : x ∈ Pt
  · have hs1 : ∀ z ∈ (chartAt ℂ p₁).symm '' sphere (chartAt ℂ p₁ p₁) r₁,
        pieceGreen Pt p₁ z - pieceGreen Pt p₂ z ≤ C₀ := by
      intro z hz
      have h1 := (abs_le.1 (hKbd z (Or.inl (Or.inl hz)))).2
      linarith only [h1]
    have hs2 : ∀ z ∈ (chartAt ℂ p₂).symm '' sphere (chartAt ℂ p₂ p₂) r₂,
        pieceGreen Pt p₂ z - pieceGreen Pt p₁ z ≤ C₀ := by
      intro z hz
      have h1 := (abs_le.1 (hKbd z (Or.inl (Or.inr hz)))).1
      linarith only [h1]
    have hsubCar1 : (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) r₁ ⊆ Car1 := by
      rw [hCar1]
      exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₁]))
    have hsubCar2 : (chartAt ℂ p₂).symm '' closedBall (chartAt ℂ p₂ p₂) r₂ ⊆ Car2 := by
      rw [hCar2]
      exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₂]))
    have hdisj12 : ∀ y ∈ (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) r₁,
        y ∉ (chartAt ℂ p₂).symm '' closedBall (chartAt ℂ p₂ p₂) r₂ := by
      intro y hy hmem
      exact (hCar2av y (hsubCar2 hmem)).2 (hsubCar1 hy)
    have hdisj21 : ∀ y ∈ (chartAt ℂ p₂).symm '' closedBall (chartAt ℂ p₂ p₂) r₂,
        y ∉ (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) r₁ := by
      intro y hy hmem
      exact (hCar2av y (hsubCar2 hy)).2 (hsubCar1 hmem)
    have hside1 := side Pt hconnT hncT p₁ hp₁t p₂ hp₂t hGF1t hGF2t r₁ r₂ C₀ hr₁
        hr₂
      hC₀0 ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP1 w hw)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP2 w hw)
      hdisj12 hs1 x hxP hx1 hx2
    have hside2 := side Pt hconnT hncT p₂ hp₂t p₁ hp₁t hGF2t hGF1t r₂ r₁ C₀ hr₂
        hr₁
      hC₀0 ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP2 w hw)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP1 w hw)
      hdisj21 hs2 x hxP hx2 hx1
    rw [abs_le]
    constructor
    · linarith only [hside2]
    · linarith only [hside1]
  · have h1 : pieceGreen Pt p₁ x = 0 := pgzero _ _ _ hxP
    have h2 : pieceGreen Pt p₂ x = 0 := pgzero _ _ _ hxP
    rw [h1, h2, sub_zero, abs_zero]
    exact hC₀0

end RiemannDynamics
