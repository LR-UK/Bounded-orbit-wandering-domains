/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreensFunction.Injective
import RiemannDynamics.Analysis.Winding.GridPrimitives.Primitives
import FunctionTheory.Conformal.RiemannMapping

/-!
# Green envelopes under Riemann maps

Simple connectivity yields holomorphic primitives and a Riemann map; the Green
envelope of the unit disc is the explicit hyperbolic kernel, and Green
envelopes transport under diffeomorphisms onto plane domains.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]


variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-! ## From simple connectivity to holomorphic primitives -/

/-- In a simply connected open plane set, every connected component of the
complement is unbounded: a bounded complementary component would be enclosed
by an essential loop of the domain. -/
theorem unbounded_connectedComponentIn_compl_of_simplyConnectedSpace
    {U : Set ℂ} (hU : IsOpen U) (hsc : SimplyConnectedSpace ↥U) :
    ∀ z ∉ U, ¬Bornology.IsBounded (connectedComponentIn Uᶜ z) := by
  classical
  intro z hzU hbdd
  -- ## Stage 1: an essential grid loop in `U` about `z`.  The bounded
  -- component of `z` in the closed complement has a compact relatively
  -- clopen piece `A` (Šura-Bura in a compact truncation), metrically
  -- separated from the rest of the complement; the grid boundary of the
  -- union of small squares meeting `A` is a loop in `U` with nonzero
  -- winding about `z`.
  obtain ⟨γ, hγcl, hγmem, hγwind⟩ : ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧
      (∀ t : unitInterval, γ t ∈ U) ∧ windingNumber γ z ≠ 0 := by
    set F : Set ℂ := Uᶜ
    have hFclosed : IsClosed F := hU.isClosed_compl
    have hzF : z ∈ F := hzU
    set C : Set ℂ := connectedComponentIn F z
    have hzC : z ∈ C := mem_connectedComponentIn hzF
    have hCsub : C ⊆ F := connectedComponentIn_subset _ _
    obtain ⟨R, hRC⟩ := hbdd.subset_closedBall 0
    set K : Set ℂ := F ∩ Metric.closedBall 0 (R + 1)
    have hKcpt : IsCompact K :=
      (isCompact_closedBall 0 (R + 1)).inter_left hFclosed
    have hCK : C ⊆ K := fun x hx =>
      ⟨hCsub hx, Metric.closedBall_subset_closedBall (by linarith) (hRC hx)⟩
    have hzK : z ∈ K := hCK hzC
    -- the component in the truncation agrees with the component in `F`
    have hCKeq : connectedComponentIn K z = C := by
      apply Set.Subset.antisymm
      · exact connectedComponentIn_mono _ Set.inter_subset_left
      · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hzC hCK
    -- the boundary shell of the truncation, compact and missed by `C`
    set W : Set ℂ := K \ Metric.ball 0 (R + 1)
    have hCW : C ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxC hxW
      apply hxW.2
      have hx := hRC hxC
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    -- pass to the compact subspace `K`
    have : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
    set z' : K := ⟨z, hzK⟩
    have hccinter := connectedComponent_eq_iInter_isClopen z'
    have hWclosed : IsClosed W := hKcpt.isClosed.sdiff Metric.isOpen_ball
    have hW'cpt : IsCompact (Subtype.val ⁻¹' W : Set K) :=
      (hWclosed.preimage continuous_subtype_val).isCompact
    -- the shell misses every point of the component of `z` in `K`
    have hdisj : (Subtype.val ⁻¹' W : Set K) ∩
        (⋂ Z : {Z : Set K // IsClopen Z ∧ z' ∈ Z}, (Z : Set K)) = ∅ := by
      rw [← hccinter]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxW hxcc
      have hximg : (x : ℂ) ∈ connectedComponentIn K z := by
        rw [connectedComponentIn_eq_image hzK]
        exact ⟨x, hxcc, rfl⟩
      rw [hCKeq] at hximg
      have hmem : (x : ℂ) ∈ C ∩ W := ⟨hximg, hxW⟩
      rw [hCW] at hmem
      exact hmem
    -- compactness of the shell extracts a single clopen neighborhood
    obtain ⟨u, hu⟩ := hW'cpt.elim_finite_subfamily_closed
      (fun Z : {Z : Set K // IsClopen Z ∧ z' ∈ Z} => (Z : Set K))
      (fun Z => Z.2.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mpr hdisj)
    set A'' : Set K := ⋂ Z ∈ u, (Z : Set K) with hA''def
    have hA''clopen : IsClopen A'' := by
      apply Set.Finite.isClopen_biInter u.finite_toSet
      intro Z _
      exact Z.2.1
    have hzA'' : z' ∈ A'' := by
      rw [hA''def]
      exact Set.mem_biInter fun Z _ => Z.2.2
    -- the piece downstairs: compact, clopen in `F`, containing `z`, off the shell
    set A : Set ℂ := Subtype.val '' A''
    have hA''cpt : IsCompact A'' := hA''clopen.isClosed.isCompact
    have hAcpt : IsCompact A := hA''cpt.image continuous_subtype_val
    have hzA : z ∈ A := ⟨z', hzA'', rfl⟩
    have hAK : A ⊆ K := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have hAF : A ⊆ F := fun x hx => (hAK hx).1
    have hAW : A ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨y, hyA'', rfl⟩ hxW
      have hmem : y ∈ (Subtype.val ⁻¹' W : Set K) ∩ ⋂ Z ∈ u, (Z : Set K) :=
        ⟨hxW, hyA''⟩
      rw [Set.disjoint_iff_inter_eq_empty.mp hu] at hmem
      exact hmem
    -- `A` is relatively open in `F`
    obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hA''clopen.isOpen
    have hAeq : A = F ∩ (V ∩ Metric.ball 0 (R + 1)) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hyA'', rfl⟩
        refine ⟨y.2.1, ?_, ?_⟩
        · rw [← hVeq] at hyA''
          exact hyA''
        · by_contra hball
          have hmem : (y : ℂ) ∈ A ∩ W := ⟨⟨y, hyA'', rfl⟩, ⟨y.2, hball⟩⟩
          rw [hAW] at hmem
          exact hmem
      · rintro x ⟨hxF, hxV, hxball⟩
        have hxK : x ∈ K := ⟨hxF, Metric.ball_subset_closedBall hxball⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        rw [← hVeq]
        exact hxV
    have hFAclosed : IsClosed (F \ A) := by
      rw [hAeq, Set.sdiff_self_inter]
      exact hFclosed.sdiff (hVopen.inter Metric.isOpen_ball)
    -- metric separation of the compact clopen piece from the rest
    have hdisjAB : Disjoint A (F \ A) := disjoint_sdiff_self_right
    obtain ⟨ε, hε, hthick⟩ := hdisjAB.exists_thickenings hAcpt hFAclosed
    have hsep : ∀ w ∈ Uᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a := by
      intro w hwF hwA a haA
      by_contra hlt
      push Not at hlt
      have hw₁ : w ∈ Metric.thickening ε A :=
        Metric.mem_thickening_iff.mpr ⟨a, haA, hlt⟩
      have hw₂ : w ∈ Metric.thickening ε (F \ A) :=
        Metric.self_subset_thickening hε _ ⟨hwF, hwA⟩
      exact (Set.disjoint_left.mp hthick hw₁) hw₂
    exact exists_gridLoop_winding_ne_zero hU A ε hε hAcpt hzA hAF hsep
  -- ## Stage 2: simple connectivity null-homotopes the subtype lift of the loop.
  have hγ0z : γ 0 ≠ z := fun heq => hzU (heq ▸ hγmem 0)
  let x₀ : ↥U := ⟨γ 0, hγmem 0⟩
  let pγ : Path x₀ x₀ :=
    { toFun := fun s => ⟨γ s, hγmem s⟩
      continuous_toFun := γ.continuous.subtype_mk hγmem
      source' := rfl
      target' := Subtype.ext hγcl.symm }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic pγ (Path.refl x₀)
  -- ## Stage 3: push the homotopy through `↥U ↪ ℂ` and kill the winding number.
  let Hrel : ContinuousMap.HomotopyRel γ
      (ContinuousMap.const unitInterval (γ 0)) {0, 1} :=
    { toFun := fun q => ((F q : ↥U) : ℂ)
      continuous_toFun := continuous_subtype_val.comp F.continuous
      map_zero_left := fun s => congrArg Subtype.val (F.apply_zero s)
      map_one_left := fun s => congrArg Subtype.val (F.apply_one s)
      prop' := by
        intro t s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact congrArg Subtype.val (Path.Homotopy.source F t)
        · exact (congrArg Subtype.val (Path.Homotopy.target F t)).trans hγcl }
  have havoid : ∀ (t s : unitInterval), Hrel (t, s) ≠ z := by
    intro t s heq
    have heq' : ((F (t, s) : ↥U) : ℂ) = z := heq
    have h1 : ((F (t, s) : ↥U) : ℂ) ∈ U := (F (t, s)).2
    rw [heq'] at h1
    exact hzU h1
  have h0 : windingNumber γ z =
      windingNumber (ContinuousMap.const unitInterval (γ 0)) z :=
    windingNumber_eq_of_homotopicRel hγcl Hrel havoid
  rw [windingNumber_const (γ 0) z hγ0z] at h0
  exact hγwind h0

/-- A simply connected open plane set admits holomorphic primitives for all
holomorphic functions. -/
theorem has_primitives_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    (hsc : SimplyConnectedSpace ↥U) : has_primitives U := by
  exact has_primitives_of_unbounded_components hU
    (unbounded_connectedComponentIn_compl_of_simplyConnectedSpace hU hsc)

/-- **The Riemann mapping theorem** for simply connected plane domains: a
simply connected (hence nonempty and connected) open proper subset of `ℂ`
maps holomorphically and injectively onto the unit disc. -/
theorem exists_riemannMap_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    (hne : U ≠ Set.univ) (hsc : SimplyConnectedSpace ↥U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ Set.InjOn f U ∧
      f '' U = Metric.ball 0 1 := by
  obtain ⟨f, hbij, hf, -, -, -⟩ :=
    TauCeti.exists_bijOn_ball_differentiableOn_invFunOn hU hsc hne
  exact ⟨f, hf, hbij.injOn, hbij.image_eq⟩

/-- The open unit disc, as an open set of the plane carrying the charted-space
structure of an open submanifold. -/
def discOpens : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- **The Green's function of the unit disc**: the Perron Green's envelope of
the disc equals the classical Möbius-invariant kernel. -/
theorem greenEnvelope_unitDisc_eq {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hab : b ≠ a) :
    greenEnvelope (⟨a, mem_ball_zero_iff.mpr ha⟩ : ↥discOpens)
        ⟨b, mem_ball_zero_iff.mpr hb⟩ =
      -Real.log ‖(b - a) / (1 - (starRingEnd ℂ) a * b)‖ := by
  classical
  set T : ℂ → ℂ := fun z => (z - a) / (1 - (starRingEnd ℂ) a * z) with hT
  set p₀ : ↥discOpens := ⟨a, mem_ball_zero_iff.mpr ha⟩ with hp₀def
  set xb : ↥discOpens := ⟨b, mem_ball_zero_iff.mpr hb⟩ with hxbdef
  -- Points of the disc have norm below one.
  have hmem : ∀ y : ↥discOpens, ‖(↑y : ℂ)‖ < 1 := fun y => mem_ball_zero_iff.mp y.2
  -- Instances on the disc subtype.
  have hne : Nonempty ↥discOpens := ⟨p₀⟩
  have : ConnectedSpace ↥discOpens :=
    Subtype.connectedSpace ((convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩)
  have : NoncompactSpace ↥discOpens := by
    rw [← not_compactSpace_iff]
    intro hcomp
    have hK : IsCompact (ball (0 : ℂ) 1) := by
      rw [isCompact_iff_compactSpace]
      exact hcomp
    have h1 : closedBall (0 : ℂ) 1 = ball (0 : ℂ) 1 := by
      rw [← closure_ball (0 : ℂ) one_ne_zero]
      exact hK.isClosed.closure_eq
    have h2 : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (by norm_num)
    rw [h1, mem_ball_zero_iff] at h2
    norm_num at h2
  -- Denominator estimates for the Möbius kernel.
  have hdenlb : ∀ z : ℂ, ‖z‖ < 1 → 1 - ‖a‖ ≤ ‖1 - (starRingEnd ℂ) a * z‖ := by
    intro z hz
    have e2 : ‖(1 : ℂ)‖ - ‖(starRingEnd ℂ) a * z‖ ≤ ‖1 - (starRingEnd ℂ) a * z‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, norm_mul, Complex.norm_conj] at e2
    have e3 : ‖a‖ * ‖z‖ ≤ ‖a‖ := mul_le_of_le_one_right (norm_nonneg a) hz.le
    linarith
  have hden : ∀ z : ℂ, ‖z‖ < 1 → 1 - (starRingEnd ℂ) a * z ≠ 0 := by
    intro z hz hcon
    have h1 := hdenlb z hz
    rw [hcon, norm_zero] at h1
    linarith
  have hdenpos : ∀ z : ℂ, ‖z‖ < 1 → 0 < ‖1 - (starRingEnd ℂ) a * z‖ :=
    fun z hz => norm_pos_iff.mpr (hden z hz)
  have hdenub : ∀ z : ℂ, ‖z‖ < 1 → ‖1 - (starRingEnd ℂ) a * z‖ ≤ 2 := by
    intro z hz
    have e1 : ‖1 - (starRingEnd ℂ) a * z‖ ≤ ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) a * z‖ :=
      norm_sub_le _ _
    rw [norm_one, norm_mul, Complex.norm_conj] at e1
    have e3 : ‖a‖ * ‖z‖ ≤ ‖a‖ := mul_le_of_le_one_right (norm_nonneg a) hz.le
    linarith
  -- The Möbius identity `|1 - āz|² - |z - a|² = (1 - |a|²)(1 - |z|²)`.
  have hkey : ∀ z : ℂ, ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 - ‖z - a‖ ^ 2
      = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    intro z
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im]
    ring
  -- Norm formula, nonvanishing, and the strict disc bound for `T`.
  have hTnorm : ∀ z : ℂ, ‖T z‖ = ‖z - a‖ / ‖1 - (starRingEnd ℂ) a * z‖ := by
    intro z
    rw [hT]
    exact norm_div _ _
  have hTne : ∀ z : ℂ, ‖z‖ < 1 → z ≠ a → T z ≠ 0 := by
    intro z hz hza
    rw [hT]
    exact div_ne_zero (sub_ne_zero_of_ne hza) (hden z hz)
  have hT1 : ∀ z : ℂ, ‖z‖ < 1 → ‖T z‖ < 1 := by
    intro z hz
    have h1 := hkey z
    have h2 := hdenpos z hz
    have hpa : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have hpz : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h3 : ‖z - a‖ ^ 2 < ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
      nlinarith [mul_pos hpa hpz]
    have h4 : ‖z - a‖ < ‖1 - (starRingEnd ℂ) a * z‖ := by
      nlinarith [norm_nonneg (z - a)]
    rw [hTnorm z, div_lt_one h2]
    exact h4
  have hlogT : ∀ z : ℂ, ‖z‖ < 1 → z ≠ a →
      Real.log ‖T z‖ = Real.log ‖z - a‖ - Real.log ‖1 - (starRingEnd ℂ) a * z‖ := by
    intro z hz hza
    rw [hTnorm z]
    exact Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hza))
      (norm_ne_zero_iff.mpr (hden z hz))
  -- Harmonicity of `log ‖T‖` off the pole, in the plane.
  have hHlog : ∀ z : ℂ, ‖z‖ < 1 → z ≠ a → HarmonicAt (fun w => Real.log ‖T w‖) z := by
    intro z hz hza
    have h1 : AnalyticAt ℂ T z := by
      rw [hT]
      exact AnalyticAt.div (analyticAt_id.sub analyticAt_const)
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (hden z hz)
    exact h1.harmonicAt_log_norm (hTne z hz hza)
  -- Plane harmonicity transfers to the disc subtype through the identity chart.
  have mharmVal : ∀ (G : ℂ → ℝ) (y : ↥discOpens), HarmonicAt G (↑y : ℂ) →
      MHarmonicAt (fun w : ↥discOpens => G ↑w) y := by
    intro G y hG
    have hev : ⇑(chartAt ℂ (↑y : ℂ)).symm =ᶠ[𝓝 (↑y : ℂ)]
        Subtype.val ∘ ⇑(chartAt ℂ y).symm :=
      Opens.chartAt_subtype_val_symm_eventuallyEq discOpens (x := y)
    have hev2 : ((fun w : ↥discOpens => G ↑w) ∘ ⇑(chartAt ℂ y).symm) =ᶠ[𝓝 (↑y : ℂ)] G := by
      filter_upwards [hev] with w hw
      have h2 : (chartAt ℂ (↑y : ℂ)).symm w = w := rfl
      simp only [Function.comp_apply] at hw ⊢
      rw [← hw, h2]
    exact (harmonicAt_congr_nhds hev2).mpr hG
  -- Punctured points have coordinate different from the pole coordinate.
  have hval_ne : ∀ y : ↥discOpens, y ≠ p₀ → (↑y : ℂ) ≠ a := by
    intro y hy hcon
    exact hy (Subtype.ext hcon)
  have hpc : ∀ x : ↥discOpens, poleCoord p₀ x = (↑x : ℂ) - a := fun _ => rfl
  -- ## Upper bound: every member of the family lies below the Möbius kernel.
  have hle_all : ∀ v ∈ greenFamily p₀, v xb ≤ -Real.log ‖T b‖ := by
    intro v hv
    obtain ⟨hsub, -, ⟨K, hKcpt, -, hKv⟩, C, hC⟩ := hv
    have hwsub : MSubharmonicOn (fun y : ↥discOpens => v y + Real.log ‖T ↑y‖) {p₀}ᶜ := by
      intro y hy
      have hyne : (↑y : ℂ) ≠ a := hval_ne y (Set.mem_compl_singleton_iff.mp hy)
      have hH : MHarmonicAt (fun q : ↥discOpens => -Real.log ‖T ↑q‖) y := by
        refine mharmVal (fun z => -Real.log ‖T z‖) y ?_
        exact (hHlog ↑y (hmem y) hyne).neg
      have h1 := (hsub y hy).sub_mharmonicAt hH
      simp only [sub_neg_eq_add] at h1
      exact h1
    have hwsupp : ∃ Kc : Set ↥discOpens, IsCompact Kc ∧
        ∀ x ∉ Kc, (fun y : ↥discOpens => v y + Real.log ‖T ↑y‖) x ≤ 0 := by
      refine ⟨K, hKcpt, fun x hx => ?_⟩
      change v x + Real.log ‖T ↑x‖ ≤ 0
      rw [hKv x hx, zero_add]
      exact Real.log_nonpos (norm_nonneg _) (hT1 ↑x (hmem x)).le
    have hwpole : ∃ C', ∀ᶠ x in 𝓝[≠] p₀,
        (fun y : ↥discOpens => v y + Real.log ‖T ↑y‖) x ≤ C' := by
      refine ⟨C - Real.log (1 - ‖a‖), ?_⟩
      filter_upwards [hC, self_mem_nhdsWithin] with x hx1 hx2
      have hxne : (↑x : ℂ) ≠ a := hval_ne x (Set.mem_compl_singleton_iff.mp hx2)
      change v x + Real.log ‖T ↑x‖ ≤ C - Real.log (1 - ‖a‖)
      rw [hpc x] at hx1
      have h1 := hlogT ↑x (hmem x) hxne
      have h2 : Real.log (1 - ‖a‖) ≤ Real.log ‖1 - (starRingEnd ℂ) a * ↑x‖ :=
        Real.log_le_log (by linarith) (hdenlb ↑x (hmem x))
      linarith
    have hzero := msubharmonic_le_zero_of_puncture hwsub hwsupp hwpole
    have hxbne : xb ≠ p₀ := by
      intro h
      exact hab (congrArg Subtype.val h)
    have h3 : v xb + Real.log ‖T b‖ ≤ 0 := hzero xb hxbne
    linarith
  -- ## The zero function is a family member.
  have hzero_mem : (fun _ : ↥discOpens => (0 : ℝ)) ∈ greenFamily p₀ := by
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, Real.log 2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : (↑x : ℂ) ≠ a := hval_ne x (Set.mem_compl_singleton_iff.mp hx)
    change (0 : ℝ) + Real.log ‖poleCoord p₀ x‖ ≤ Real.log 2
    rw [hpc x, zero_add]
    have h1 : 0 < ‖(↑x : ℂ) - a‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hxne)
    have h2 : ‖(↑x : ℂ) - a‖ ≤ 2 := by
      have h3 := norm_sub_le (↑x : ℂ) a
      have h4 := hmem x
      linarith
    exact Real.log_le_log h1 h2
  -- ## The evaluation image is bounded above by the kernel value.
  have hbdd : BddAbove ((fun v => v xb) '' greenFamily p₀) := by
    refine ⟨-Real.log ‖T b‖, ?_⟩
    rintro q ⟨v, hv, rfl⟩
    exact hle_all v hv
  -- ## Lower bound: the truncated kernels are family members.
  have heps_mem : ∀ ε : ℝ, 0 < ε →
      (fun y : ↥discOpens => max (-Real.log ‖T ↑y‖ - ε) 0) ∈ greenFamily p₀ := by
    intro ε hε
    refine ⟨?_, ?_, ?_, Real.log 2, ?_⟩
    · -- Subharmonic off the pole: max of a harmonic function and zero.
      intro y hy
      have hyne : (↑y : ℂ) ≠ a := hval_ne y (Set.mem_compl_singleton_iff.mp hy)
      have hH : MHarmonicAt (fun q : ↥discOpens => -Real.log ‖T ↑q‖ - ε) y := by
        refine mharmVal (fun z => -Real.log ‖T z‖ - ε) y ?_
        exact ((hHlog ↑y (hmem y) hyne).neg).sub (harmonicAt_const ε)
      have h0 : MSubharmonicAt (fun _ : ↥discOpens => (0 : ℝ)) y :=
        mharmonicAt_const.msubharmonicAt
      exact hH.msubharmonicAt.max h0
    · -- Continuity off the pole.
      intro y hy
      have hyne : (↑y : ℂ) ≠ a := hval_ne y (Set.mem_compl_singleton_iff.mp hy)
      have hnum : ContinuousAt T (↑y : ℂ) := by
        rw [hT]
        exact ContinuousAt.div (continuousAt_id.sub continuousAt_const)
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
          (hden ↑y (hmem y))
      have hne0 : ‖T (↑y : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (hTne ↑y (hmem y) hyne)
      have hc1 : ContinuousAt (fun q : ↥discOpens => -Real.log ‖T ↑q‖ - ε) y := by
        have h2 : ContinuousAt (fun q : ↥discOpens => T ↑q) y :=
          hnum.comp continuous_subtype_val.continuousAt
        exact ((h2.norm.log hne0).neg).sub continuousAt_const
      have hc2 : ContinuousAt (fun q : ↥discOpens => max (-Real.log ‖T ↑q‖ - ε) 0) y :=
        hc1.max continuousAt_const
      exact hc2.continuousWithinAt
    · -- Compact support: the closed pseudohyperbolic ball.
      have hr0 : (0 : ℝ) < Real.exp (-ε) := Real.exp_pos _
      have hr1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      set S : Set ℂ :=
        {z : ℂ | ‖z - a‖ ≤ Real.exp (-ε) * ‖1 - (starRingEnd ℂ) a * z‖} with hS
      have hSclosed : IsClosed S := by
        rw [hS]
        exact isClosed_le (by fun_prop) (by fun_prop)
      set c0 : ℝ := (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) / (1 + ‖a‖) with hc0
      have hc0pos : 0 < c0 := by
        rw [hc0]
        have h1 : 0 < 1 - Real.exp (-ε) ^ 2 := by nlinarith
        have h2 : 0 < 1 - ‖a‖ := by linarith
        have h3 : 0 < 1 + ‖a‖ := by linarith [norm_nonneg a]
        positivity
      have hc0le : c0 ≤ 1 := by
        rw [hc0, div_le_one (by linarith [norm_nonneg a])]
        nlinarith [norm_nonneg a, hr0]
      have hρnn : (0 : ℝ) ≤ 1 - c0 := by linarith
      have hρ1 : Real.sqrt (1 - c0) < 1 := by
        rw [Real.sqrt_lt' one_pos]
        nlinarith
      have hρ0 : (0 : ℝ) ≤ Real.sqrt (1 - c0) := Real.sqrt_nonneg _
      -- Points of the sublevel set inside the disc stay in a compact sub-disc.
      have hbound : ∀ z : ℂ, ‖z‖ < 1 → z ∈ S → ‖z‖ ≤ Real.sqrt (1 - c0) := by
        intro z hz hzS
        have h1 : ‖z - a‖ ≤ Real.exp (-ε) * ‖1 - (starRingEnd ℂ) a * z‖ := hzS
        have h2 : ‖z - a‖ ^ 2 ≤ Real.exp (-ε) ^ 2 * ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
          nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]
        have h3 := hkey z
        have h4 : (1 - ‖a‖) ^ 2 ≤ ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
          nlinarith [hdenlb z hz, ha]
        have hr2 : 0 ≤ 1 - Real.exp (-ε) ^ 2 := by nlinarith [hr0, hr1]
        have h5a : (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) ^ 2
            ≤ (1 - Real.exp (-ε) ^ 2) * ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h4 hr2
        have h5 : (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) ^ 2
            ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
          nlinarith [h5a, h2, h3]
        have h6 : ((1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖)) * (1 - ‖a‖)
            ≤ ((1 + ‖a‖) * (1 - ‖z‖ ^ 2)) * (1 - ‖a‖) := by nlinarith [h5]
        have h7 : (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) ≤ (1 + ‖a‖) * (1 - ‖z‖ ^ 2) :=
          le_of_mul_le_mul_right h6 (by linarith)
        have h8 : c0 ≤ 1 - ‖z‖ ^ 2 := by
          rw [hc0, div_le_iff₀ (by linarith [norm_nonneg a])]
          nlinarith [h7]
        have h9 : ‖z‖ ^ 2 ≤ Real.sqrt (1 - c0) ^ 2 := by
          rw [Real.sq_sqrt hρnn]
          linarith
        calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
          _ ≤ Real.sqrt (Real.sqrt (1 - c0) ^ 2) := Real.sqrt_le_sqrt h9
          _ = Real.sqrt (1 - c0) := Real.sqrt_sq hρ0
      have hKcpt : IsCompact (Subtype.val ⁻¹' S : Set ↥discOpens) := by
        rw [Subtype.isCompact_iff]
        have himg2 : Subtype.val '' (Subtype.val ⁻¹' S : Set ↥discOpens)
            = S ∩ closedBall 0 (Real.sqrt (1 - c0)) := by
          ext z
          constructor
          · rintro ⟨y, hyS, rfl⟩
            exact ⟨hyS, mem_closedBall_zero_iff.mpr (hbound ↑y (hmem y) hyS)⟩
          · rintro ⟨hzS, hzB⟩
            refine ⟨⟨z, ?_⟩, hzS, rfl⟩
            exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hzB) hρ1)
        rw [himg2]
        exact (isCompact_closedBall 0 _).inter_left hSclosed
      refine ⟨Subtype.val ⁻¹' S, hKcpt, ?_, ?_⟩
      · intro hcon
        rw [hcon] at hKcpt
        exact NoncompactSpace.noncompact_univ (X := ↥discOpens) hKcpt
      · intro x hx
        have h1 : ¬ ‖(↑x : ℂ) - a‖ ≤ Real.exp (-ε) * ‖1 - (starRingEnd ℂ) a * ↑x‖ := hx
        have h2 : Real.exp (-ε) < ‖T ↑x‖ := by
          rw [hTnorm ↑x, lt_div_iff₀ (hdenpos ↑x (hmem x))]
          exact not_le.mp h1
        have h4 : -ε < Real.log ‖T ↑x‖ := by
          have h5 := Real.log_lt_log hr0 h2
          rwa [Real.log_exp] at h5
        change max (-Real.log ‖T ↑x‖ - ε) 0 = 0
        exact max_eq_right (by linarith)
    · -- Pole bound: near the pole the truncation is dominated by the kernel.
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxne : (↑x : ℂ) ≠ a := hval_ne x (Set.mem_compl_singleton_iff.mp hx)
      change max (-Real.log ‖T ↑x‖ - ε) 0 + Real.log ‖poleCoord p₀ x‖ ≤ Real.log 2
      rw [hpc x]
      have h1 := hlogT ↑x (hmem x) hxne
      have hTle : Real.log ‖T ↑x‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) (hT1 ↑x (hmem x)).le
      have hmax2 : max (-Real.log ‖T ↑x‖ - ε) 0 ≤ -Real.log ‖T ↑x‖ :=
        max_le (by linarith) (by linarith)
      have hlog2 : Real.log ‖1 - (starRingEnd ℂ) a * ↑x‖ ≤ Real.log 2 :=
        Real.log_le_log (hdenpos ↑x (hmem x)) (hdenub ↑x (hmem x))
      linarith
  -- ## Assembly of the supremum.
  have hgoal : -Real.log ‖(b - a) / (1 - (starRingEnd ℂ) a * b)‖ = -Real.log ‖T b‖ := by
    rw [hT]
  rw [hgoal]
  have henv : greenEnvelope p₀ xb = sSup ((fun v => v xb) '' greenFamily p₀) := rfl
  rw [henv]
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨0, ⟨fun _ => 0, hzero_mem, rfl⟩⟩ ?_
    rintro q ⟨v, hv, rfl⟩
    exact hle_all v hv
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    rcases lt_or_ge ε (-Real.log ‖T b‖) with hlt | hge
    · have hmem2 := heps_mem ε hε
      have h1 : (fun y : ↥discOpens => max (-Real.log ‖T ↑y‖ - ε) 0) xb
          ≤ sSup ((fun v => v xb) '' greenFamily p₀) :=
        le_csSup hbdd ⟨_, hmem2, rfl⟩
      have hval : (fun y : ↥discOpens => max (-Real.log ‖T ↑y‖ - ε) 0) xb
          = -Real.log ‖T b‖ - ε := by
        change max (-Real.log ‖T b‖ - ε) 0 = -Real.log ‖T b‖ - ε
        exact max_eq_left (by linarith)
      rw [hval] at h1
      linarith
    · have h0 : (0 : ℝ) ≤ sSup ((fun v => v xb) '' greenFamily p₀) :=
        le_csSup hbdd ⟨fun _ => 0, hzero_mem, rfl⟩
      linarith

/-- **Conformal invariance of the Green's envelope**: a biholomorphism carries
the Perron Green's family at a pole bijectively onto the family at the image
pole, so the envelopes agree. -/
theorem greenEnvelope_comp_diffeomorph {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]
    (e : M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ N) (p₀ x : M) :
    greenEnvelope (e p₀) (e x) = greenEnvelope p₀ x := by
  -- Forward transfer: pulling back a family member along `e` gives a family member.
  have hfwd : ∀ (q : M) (v : N → ℝ), v ∈ greenFamily (e q) → v ∘ ⇑e ∈ greenFamily q := by
    obtain ⟨f, g, hfeq, hgf, hfg, hfc, hgc⟩ :
        ∃ (f : M → N) (g : N → M), f = ⇑e ∧ (∀ a, g (f a) = a) ∧ (∀ b, f (g b) = b) ∧
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g :=
      ⟨⇑e, ⇑e.symm, rfl, e.symm_apply_apply, e.apply_symm_apply, e.contMDiff, e.symm.contMDiff⟩
    intro q v hv
    rw [← hfeq] at hv ⊢
    obtain ⟨hsub, hcont, ⟨K, hKc, hKuniv, hKzero⟩, C, hC⟩ := hv
    have hfinj : Function.Injective f := Function.LeftInverse.injective hgf
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
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Subharmonicity of the pullback on the punctured surface.
      intro x' hx'
      have hfx' : f x' ∈ ({f q}ᶜ : Set _) :=
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      obtain ⟨s, hs0, -, hsubOn⟩ := hsub (f x') hfx'
      obtain ⟨fH, hfH1, hfH2⟩ : ∃ fH : _ ≃ₜ _, ⇑fH = f ∧ ⇑fH.symm = g :=
        ⟨{ toEquiv := ⟨f, g, hgf, hfg⟩
           continuous_toFun := hfc.continuous
           continuous_invFun := hgc.continuous }, rfl, rfl⟩
      set T := ((chartAt ℂ x').symm ≫ₕ fH.toOpenPartialHomeomorph) ≫ₕ chartAt ℂ (f x') with hT
      have hTcoe : ⇑T = ⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
          hfH1]
      have hTsymmcoe : ⇑T.symm = ⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Function.comp_assoc]
      have hTsrc_iff : ∀ z, z ∈ T.source ↔
          z ∈ (chartAt ℂ x').target ∧ f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source := by
        intro z
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
          Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.coe_trans,
          Homeomorph.toOpenPartialHomeomorph_apply, hfH1, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_univ, and_true, Function.comp_apply]
      have hTtgt_iff : ∀ w, w ∈ T.target ↔
          w ∈ (chartAt ℂ (f x')).target ∧
            g ((chartAt ℂ (f x')).symm w) ∈ (chartAt ℂ x').source := by
        intro w
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
          Homeomorph.toOpenPartialHomeomorph_target,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_univ, true_and]
      have hTdiff : DifferentiableOn ℂ (⇑T) T.source := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := (hTsrc_iff z).mp hz
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x').symm) z :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x').open_target.mem_nhds hz1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ x').symm z) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x'))) (f ((chartAt ℂ x').symm z)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ (f x')).open_source.mem_nhds hz2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm)) z :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp z (h2.comp z h1))).analyticAt
        rw [hTcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hTsymmdiff : DifferentiableOn ℂ (⇑T.symm) T.target := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := (hTtgt_iff w).mp hw
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x')).symm) w :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ (f x')).open_target.mem_nhds hw1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f x')).symm w) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x')) (g ((chartAt ℂ (f x')).symm w)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ x').open_source.mem_nhds hw2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm)) w :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp w (h2.comp w h1))).analyticAt
        rw [hTsymmcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hu2 : SubharmonicOn (v ∘ ⇑(chartAt ℂ (f x')).symm)
          (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) :=
        transfer _ _ _ _ hsubOn Set.inter_subset_left fun _ _ => rfl
      have hcomp := subharmonicOn_comp_biholo T hTdiff hTsymmdiff hu2 Set.inter_subset_right
      have hopenS : IsOpen (T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target)) :=
        T.isOpen_inter_preimage (isOpen_ball.inter T.open_target)
      have hz₀src : chartAt ℂ x' x' ∈ T.source := by
        refine (hTsrc_iff _).mpr ⟨mem_chart_target ℂ x', ?_⟩
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
        exact mem_chart_source ℂ (f x')
      have hTz₀ : T (chartAt ℂ x' x') = chartAt ℂ (f x') (f x') := by
        rw [hTcoe]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
      have hz₀mem : chartAt ℂ x' x' ∈
          T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) := by
        refine ⟨hz₀src, ?_⟩
        have h7 : T (chartAt ℂ x' x') ∈ T.target := T.map_source hz₀src
        rw [hTz₀] at h7
        rw [Set.mem_preimage, hTz₀]
        exact ⟨mem_ball_self hs0, h7⟩
      obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hopenS _ hz₀mem
      change ∃ r > 0, ball (chartAt ℂ x' x') r ⊆ (chartAt ℂ x').target ∧
        SubharmonicOn ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) (ball (chartAt ℂ x' x') r)
      refine ⟨r, hr0, ?_, ?_⟩
      · intro z hz
        exact ((hTsrc_iff z).mp (hrsub hz).1).1
      · refine transfer _ _ _ _ hcomp hrsub ?_
        intro z hz
        have hzn : f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source :=
          ((hTsrc_iff z).mp (hrsub hz).1).2
        calc ((v ∘ ⇑(chartAt ℂ (f x')).symm) ∘ ⇑T) z
            = v ((chartAt ℂ (f x')).symm (T z)) := rfl
          _ = v ((chartAt ℂ (f x')).symm (chartAt ℂ (f x') (f ((chartAt ℂ x').symm z)))) := by
              rw [hTcoe]
              simp only [Function.comp_apply]
          _ = ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) z := by
              rw [(chartAt ℂ (f x')).left_inv hzn]
              simp only [Function.comp_apply]
    · -- Continuity of the pullback on the punctured surface.
      exact hcont.comp hfc.continuous.continuousOn fun x' hx' =>
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
    · -- Compact support of the pullback.
      refine ⟨g '' K, hKc.image hgc.continuous, ?_, ?_⟩
      · intro hgKuniv
        obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem K).mp hKuniv
        have hmem : g y ∈ g '' K := by rw [hgKuniv]; exact Set.mem_univ _
        obtain ⟨k, hk, hgk⟩ := hmem
        have hky : k = y := by
          have h := congrArg f hgk
          rwa [hfg, hfg] at h
        exact hy (hky ▸ hk)
      · intro x' hx'
        have hfx' : f x' ∉ K := fun hfK => hx' ⟨f x', hfK, hgf x'⟩
        exact hKzero _ hfx'
    · -- Logarithmic pole bound for the pullback.
      set z₀ := chartAt ℂ q q with hz₀def
      set w₀ := chartAt ℂ (f q) (f q) with hw₀def
      set hfun := ⇑(chartAt ℂ (f q)) ∘ (f ∘ ⇑(chartAt ℂ q).symm) with hfundef
      set ψ := ⇑(chartAt ℂ q) ∘ (g ∘ ⇑(chartAt ℂ (f q)).symm) with hψdef
      have hqz : (chartAt ℂ q).symm z₀ = q := by
        rw [hz₀def]; exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
      have hpz : (chartAt ℂ (f q)).symm w₀ = f q := by
        rw [hw₀def]; exact (chartAt ℂ (f q)).left_inv (mem_chart_source ℂ (f q))
      have hh0 : hfun z₀ = w₀ := by
        rw [hfundef, hw₀def]
        simp only [Function.comp_apply]
        rw [hqz]
      have hfa : AnalyticAt ℂ hfun z₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q).symm) z₀ := by
          rw [hz₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ q).open_target.mem_nhds (mem_chart_target ℂ q))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ q).symm z₀) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q))) (f ((chartAt ℂ q).symm z₀)) := by
          rw [hqz]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ (f q)).open_source.mem_nhds (mem_chart_source ℂ (f q)))
        rw [hfundef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp z₀ (h2.comp z₀ h1))).analyticAt
      have hψa : AnalyticAt ℂ ψ w₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q)).symm) w₀ := by
          rw [hw₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ (f q)).open_target.mem_nhds (mem_chart_target ℂ (f q)))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f q)).symm w₀) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q)) (g ((chartAt ℂ (f q)).symm w₀)) := by
          rw [hpz, hgf]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q))
        rw [hψdef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp w₀ (h2.comp w₀ h1))).analyticAt
      have hΩopen : IsOpen ((chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source)) :=
        (chartAt ℂ q).isOpen_inter_preimage_symm
          ((chartAt ℂ (f q)).open_source.preimage hfc.continuous)
      have hz₀Ω : z₀ ∈ (chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source) := by
        refine ⟨?_, ?_⟩
        · rw [hz₀def]; exact mem_chart_target ℂ q
        · rw [Set.mem_preimage, Set.mem_preimage, hqz]
          exact mem_chart_source ℂ (f q)
      have hid : ψ ∘ hfun =ᶠ[𝓝 z₀] id := by
        filter_upwards [hΩopen.mem_nhds hz₀Ω] with z hz
        obtain ⟨hz1, hz2⟩ := hz
        rw [Set.mem_preimage, Set.mem_preimage] at hz2
        rw [hfundef, hψdef]
        simp only [Function.comp_apply, id_eq]
        rw [(chartAt ℂ (f q)).left_inv hz2, hgf, (chartAt ℂ q).right_inv hz1]
      have hfd : DifferentiableAt ℂ hfun z₀ := hfa.differentiableAt
      have hψd : DifferentiableAt ℂ ψ (hfun z₀) := by
        rw [hh0]; exact hψa.differentiableAt
      have hd1 : deriv (ψ ∘ hfun) z₀ = 1 := by
        rw [hid.deriv_eq, deriv_id]
      have hd2 : deriv (ψ ∘ hfun) z₀ = deriv ψ (hfun z₀) * deriv hfun z₀ :=
        deriv_comp z₀ hψd hfd
      have hd0 : deriv hfun z₀ ≠ 0 := by
        intro h0
        rw [hd2, h0, mul_zero] at hd1
        exact zero_ne_one hd1
      have hdpos : 0 < ‖deriv hfun z₀‖ := norm_pos_iff.mpr hd0
      have hhalf : 0 < ‖deriv hfun z₀‖ / 2 := half_pos hdpos
      have hslope : Tendsto (fun z => ‖slope hfun z₀ z‖) (𝓝[≠] z₀) (𝓝 ‖deriv hfun z₀‖) :=
        (hasDerivAt_iff_tendsto_slope.mp hfd.hasDerivAt).norm
      have hev : ∀ᶠ z in 𝓝[≠] z₀, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ z‖ :=
        hslope.eventually_const_lt (half_lt_self hdpos)
      have htends : Tendsto f (𝓝[≠] q) (𝓝[≠] (f q)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hfc.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [eventually_mem_nhdsWithin] with x' hx'
        exact Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      have hct : Tendsto (⇑(chartAt ℂ q)) (𝓝[≠] q) (𝓝[≠] z₀) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · rw [hz₀def]
          exact ((chartAt ℂ q).continuousAt (mem_chart_source ℂ q)).mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
            eventually_mem_nhdsWithin] with x' hx'src hx'ne
          refine Set.mem_compl_singleton_iff.mpr fun hzz => ?_
          rw [hz₀def] at hzz
          exact Set.mem_compl_singleton_iff.mp hx'ne
            ((chartAt ℂ q).injOn hx'src (mem_chart_source ℂ q) hzz)
      have hCk : ∀ᶠ x' in 𝓝[≠] q, v (f x') + Real.log ‖poleCoord (f q) (f x')‖ ≤ C :=
        htends.eventually hC
      have hsl' : ∀ᶠ x' in 𝓝[≠] q, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ (chartAt ℂ q x')‖ :=
        hct.eventually hev
      refine ⟨C - Real.log (‖deriv hfun z₀‖ / 2), ?_⟩
      filter_upwards [hCk, hsl', nhdsWithin_le_nhds
        ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
        eventually_mem_nhdsWithin] with x' h1 h2 h3 h5
      have hx'q : x' ≠ q := Set.mem_compl_singleton_iff.mp h5
      have hzz : chartAt ℂ q x' ≠ z₀ := by
        intro hzz
        rw [hz₀def] at hzz
        exact hx'q ((chartAt ℂ q).injOn h3 (mem_chart_source ℂ q) hzz)
      have hnp : 0 < ‖chartAt ℂ q x' - z₀‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzz)
      have hval : hfun (chartAt ℂ q x') = chartAt ℂ (f q) (f x') := by
        rw [hfundef]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ q).left_inv h3]
      have hslope_val : ‖slope hfun z₀ (chartAt ℂ q x')‖
          = ‖hfun (chartAt ℂ q x') - w₀‖ / ‖chartAt ℂ q x' - z₀‖ := by
        rw [slope_def_field, hh0, norm_div]
      rw [hslope_val] at h2
      have hprod : ‖deriv hfun z₀‖ / 2 * ‖chartAt ℂ q x' - z₀‖
          < ‖hfun (chartAt ℂ q x') - w₀‖ := (lt_div_iff₀ hnp).mp h2
      have hlog : Real.log (‖deriv hfun z₀‖ / 2) + Real.log ‖chartAt ℂ q x' - z₀‖
          ≤ Real.log ‖hfun (chartAt ℂ q x') - w₀‖ := by
        rw [← Real.log_mul (ne_of_gt hhalf) (ne_of_gt hnp)]
        exact Real.log_le_log (mul_pos hhalf hnp) hprod.le
      have hpole_src : poleCoord q x' = chartAt ℂ q x' - z₀ := by
        rw [hz₀def]
        simp only [poleCoord]
      have hpole_tgt : poleCoord (f q) (f x') = hfun (chartAt ℂ q x') - w₀ := by
        rw [hval, hw₀def]
        simp only [poleCoord]
      rw [hpole_tgt] at h1
      simp only [Function.comp_apply]
      rw [hpole_src]
      linarith
  -- Backward transfer: pulling back along `e.symm`.
  have hbwd : ∀ (q : N) (v : M → ℝ),
      v ∈ greenFamily (e.symm q) → v ∘ ⇑e.symm ∈ greenFamily q := by
    obtain ⟨f, g, hfeq, hgf, hfg, hfc, hgc⟩ :
        ∃ (f : N → M) (g : M → N), f = ⇑e.symm ∧ (∀ a, g (f a) = a) ∧ (∀ b, f (g b) = b) ∧
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g :=
      ⟨⇑e.symm, ⇑e, rfl, e.apply_symm_apply, e.symm_apply_apply, e.symm.contMDiff, e.contMDiff⟩
    intro q v hv
    rw [← hfeq] at hv ⊢
    obtain ⟨hsub, hcont, ⟨K, hKc, hKuniv, hKzero⟩, C, hC⟩ := hv
    have hfinj : Function.Injective f := Function.LeftInverse.injective hgf
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
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Subharmonicity of the pullback on the punctured surface.
      intro x' hx'
      have hfx' : f x' ∈ ({f q}ᶜ : Set _) :=
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      obtain ⟨s, hs0, -, hsubOn⟩ := hsub (f x') hfx'
      obtain ⟨fH, hfH1, hfH2⟩ : ∃ fH : _ ≃ₜ _, ⇑fH = f ∧ ⇑fH.symm = g :=
        ⟨{ toEquiv := ⟨f, g, hgf, hfg⟩
           continuous_toFun := hfc.continuous
           continuous_invFun := hgc.continuous }, rfl, rfl⟩
      set T := ((chartAt ℂ x').symm ≫ₕ fH.toOpenPartialHomeomorph) ≫ₕ chartAt ℂ (f x') with hT
      have hTcoe : ⇑T = ⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
          hfH1]
      have hTsymmcoe : ⇑T.symm = ⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Function.comp_assoc]
      have hTsrc_iff : ∀ z, z ∈ T.source ↔
          z ∈ (chartAt ℂ x').target ∧ f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source := by
        intro z
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
          Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.coe_trans,
          Homeomorph.toOpenPartialHomeomorph_apply, hfH1, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_univ, and_true, Function.comp_apply]
      have hTtgt_iff : ∀ w, w ∈ T.target ↔
          w ∈ (chartAt ℂ (f x')).target ∧
            g ((chartAt ℂ (f x')).symm w) ∈ (chartAt ℂ x').source := by
        intro w
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
          Homeomorph.toOpenPartialHomeomorph_target,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_univ, true_and]
      have hTdiff : DifferentiableOn ℂ (⇑T) T.source := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := (hTsrc_iff z).mp hz
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x').symm) z :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x').open_target.mem_nhds hz1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ x').symm z) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x'))) (f ((chartAt ℂ x').symm z)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ (f x')).open_source.mem_nhds hz2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm)) z :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp z (h2.comp z h1))).analyticAt
        rw [hTcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hTsymmdiff : DifferentiableOn ℂ (⇑T.symm) T.target := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := (hTtgt_iff w).mp hw
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x')).symm) w :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ (f x')).open_target.mem_nhds hw1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f x')).symm w) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x')) (g ((chartAt ℂ (f x')).symm w)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ x').open_source.mem_nhds hw2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm)) w :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp w (h2.comp w h1))).analyticAt
        rw [hTsymmcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hu2 : SubharmonicOn (v ∘ ⇑(chartAt ℂ (f x')).symm)
          (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) :=
        transfer _ _ _ _ hsubOn Set.inter_subset_left fun _ _ => rfl
      have hcomp := subharmonicOn_comp_biholo T hTdiff hTsymmdiff hu2 Set.inter_subset_right
      have hopenS : IsOpen (T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target)) :=
        T.isOpen_inter_preimage (isOpen_ball.inter T.open_target)
      have hz₀src : chartAt ℂ x' x' ∈ T.source := by
        refine (hTsrc_iff _).mpr ⟨mem_chart_target ℂ x', ?_⟩
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
        exact mem_chart_source ℂ (f x')
      have hTz₀ : T (chartAt ℂ x' x') = chartAt ℂ (f x') (f x') := by
        rw [hTcoe]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
      have hz₀mem : chartAt ℂ x' x' ∈
          T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) := by
        refine ⟨hz₀src, ?_⟩
        have h7 : T (chartAt ℂ x' x') ∈ T.target := T.map_source hz₀src
        rw [hTz₀] at h7
        rw [Set.mem_preimage, hTz₀]
        exact ⟨mem_ball_self hs0, h7⟩
      obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hopenS _ hz₀mem
      change ∃ r > 0, ball (chartAt ℂ x' x') r ⊆ (chartAt ℂ x').target ∧
        SubharmonicOn ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) (ball (chartAt ℂ x' x') r)
      refine ⟨r, hr0, ?_, ?_⟩
      · intro z hz
        exact ((hTsrc_iff z).mp (hrsub hz).1).1
      · refine transfer _ _ _ _ hcomp hrsub ?_
        intro z hz
        have hzn : f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source :=
          ((hTsrc_iff z).mp (hrsub hz).1).2
        calc ((v ∘ ⇑(chartAt ℂ (f x')).symm) ∘ ⇑T) z
            = v ((chartAt ℂ (f x')).symm (T z)) := rfl
          _ = v ((chartAt ℂ (f x')).symm (chartAt ℂ (f x') (f ((chartAt ℂ x').symm z)))) := by
              rw [hTcoe]
              simp only [Function.comp_apply]
          _ = ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) z := by
              rw [(chartAt ℂ (f x')).left_inv hzn]
              simp only [Function.comp_apply]
    · -- Continuity of the pullback on the punctured surface.
      exact hcont.comp hfc.continuous.continuousOn fun x' hx' =>
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
    · -- Compact support of the pullback.
      refine ⟨g '' K, hKc.image hgc.continuous, ?_, ?_⟩
      · intro hgKuniv
        obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem K).mp hKuniv
        have hmem : g y ∈ g '' K := by rw [hgKuniv]; exact Set.mem_univ _
        obtain ⟨k, hk, hgk⟩ := hmem
        have hky : k = y := by
          have h := congrArg f hgk
          rwa [hfg, hfg] at h
        exact hy (hky ▸ hk)
      · intro x' hx'
        have hfx' : f x' ∉ K := fun hfK => hx' ⟨f x', hfK, hgf x'⟩
        exact hKzero _ hfx'
    · -- Logarithmic pole bound for the pullback.
      set z₀ := chartAt ℂ q q with hz₀def
      set w₀ := chartAt ℂ (f q) (f q) with hw₀def
      set hfun := ⇑(chartAt ℂ (f q)) ∘ (f ∘ ⇑(chartAt ℂ q).symm) with hfundef
      set ψ := ⇑(chartAt ℂ q) ∘ (g ∘ ⇑(chartAt ℂ (f q)).symm) with hψdef
      have hqz : (chartAt ℂ q).symm z₀ = q := by
        rw [hz₀def]; exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
      have hpz : (chartAt ℂ (f q)).symm w₀ = f q := by
        rw [hw₀def]; exact (chartAt ℂ (f q)).left_inv (mem_chart_source ℂ (f q))
      have hh0 : hfun z₀ = w₀ := by
        rw [hfundef, hw₀def]
        simp only [Function.comp_apply]
        rw [hqz]
      have hfa : AnalyticAt ℂ hfun z₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q).symm) z₀ := by
          rw [hz₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ q).open_target.mem_nhds (mem_chart_target ℂ q))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ q).symm z₀) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q))) (f ((chartAt ℂ q).symm z₀)) := by
          rw [hqz]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ (f q)).open_source.mem_nhds (mem_chart_source ℂ (f q)))
        rw [hfundef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp z₀ (h2.comp z₀ h1))).analyticAt
      have hψa : AnalyticAt ℂ ψ w₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q)).symm) w₀ := by
          rw [hw₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ (f q)).open_target.mem_nhds (mem_chart_target ℂ (f q)))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f q)).symm w₀) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q)) (g ((chartAt ℂ (f q)).symm w₀)) := by
          rw [hpz, hgf]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q))
        rw [hψdef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp w₀ (h2.comp w₀ h1))).analyticAt
      have hΩopen : IsOpen ((chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source)) :=
        (chartAt ℂ q).isOpen_inter_preimage_symm
          ((chartAt ℂ (f q)).open_source.preimage hfc.continuous)
      have hz₀Ω : z₀ ∈ (chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source) := by
        refine ⟨?_, ?_⟩
        · rw [hz₀def]; exact mem_chart_target ℂ q
        · rw [Set.mem_preimage, Set.mem_preimage, hqz]
          exact mem_chart_source ℂ (f q)
      have hid : ψ ∘ hfun =ᶠ[𝓝 z₀] id := by
        filter_upwards [hΩopen.mem_nhds hz₀Ω] with z hz
        obtain ⟨hz1, hz2⟩ := hz
        rw [Set.mem_preimage, Set.mem_preimage] at hz2
        rw [hfundef, hψdef]
        simp only [Function.comp_apply, id_eq]
        rw [(chartAt ℂ (f q)).left_inv hz2, hgf, (chartAt ℂ q).right_inv hz1]
      have hfd : DifferentiableAt ℂ hfun z₀ := hfa.differentiableAt
      have hψd : DifferentiableAt ℂ ψ (hfun z₀) := by
        rw [hh0]; exact hψa.differentiableAt
      have hd1 : deriv (ψ ∘ hfun) z₀ = 1 := by
        rw [hid.deriv_eq, deriv_id]
      have hd2 : deriv (ψ ∘ hfun) z₀ = deriv ψ (hfun z₀) * deriv hfun z₀ :=
        deriv_comp z₀ hψd hfd
      have hd0 : deriv hfun z₀ ≠ 0 := by
        intro h0
        rw [hd2, h0, mul_zero] at hd1
        exact zero_ne_one hd1
      have hdpos : 0 < ‖deriv hfun z₀‖ := norm_pos_iff.mpr hd0
      have hhalf : 0 < ‖deriv hfun z₀‖ / 2 := half_pos hdpos
      have hslope : Tendsto (fun z => ‖slope hfun z₀ z‖) (𝓝[≠] z₀) (𝓝 ‖deriv hfun z₀‖) :=
        (hasDerivAt_iff_tendsto_slope.mp hfd.hasDerivAt).norm
      have hev : ∀ᶠ z in 𝓝[≠] z₀, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ z‖ :=
        hslope.eventually_const_lt (half_lt_self hdpos)
      have htends : Tendsto f (𝓝[≠] q) (𝓝[≠] (f q)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hfc.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [eventually_mem_nhdsWithin] with x' hx'
        exact Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      have hct : Tendsto (⇑(chartAt ℂ q)) (𝓝[≠] q) (𝓝[≠] z₀) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · rw [hz₀def]
          exact ((chartAt ℂ q).continuousAt (mem_chart_source ℂ q)).mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
            eventually_mem_nhdsWithin] with x' hx'src hx'ne
          refine Set.mem_compl_singleton_iff.mpr fun hzz => ?_
          rw [hz₀def] at hzz
          exact Set.mem_compl_singleton_iff.mp hx'ne
            ((chartAt ℂ q).injOn hx'src (mem_chart_source ℂ q) hzz)
      have hCk : ∀ᶠ x' in 𝓝[≠] q, v (f x') + Real.log ‖poleCoord (f q) (f x')‖ ≤ C :=
        htends.eventually hC
      have hsl' : ∀ᶠ x' in 𝓝[≠] q, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ (chartAt ℂ q x')‖ :=
        hct.eventually hev
      refine ⟨C - Real.log (‖deriv hfun z₀‖ / 2), ?_⟩
      filter_upwards [hCk, hsl', nhdsWithin_le_nhds
        ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
        eventually_mem_nhdsWithin] with x' h1 h2 h3 h5
      have hx'q : x' ≠ q := Set.mem_compl_singleton_iff.mp h5
      have hzz : chartAt ℂ q x' ≠ z₀ := by
        intro hzz
        rw [hz₀def] at hzz
        exact hx'q ((chartAt ℂ q).injOn h3 (mem_chart_source ℂ q) hzz)
      have hnp : 0 < ‖chartAt ℂ q x' - z₀‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzz)
      have hval : hfun (chartAt ℂ q x') = chartAt ℂ (f q) (f x') := by
        rw [hfundef]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ q).left_inv h3]
      have hslope_val : ‖slope hfun z₀ (chartAt ℂ q x')‖
          = ‖hfun (chartAt ℂ q x') - w₀‖ / ‖chartAt ℂ q x' - z₀‖ := by
        rw [slope_def_field, hh0, norm_div]
      rw [hslope_val] at h2
      have hprod : ‖deriv hfun z₀‖ / 2 * ‖chartAt ℂ q x' - z₀‖
          < ‖hfun (chartAt ℂ q x') - w₀‖ := (lt_div_iff₀ hnp).mp h2
      have hlog : Real.log (‖deriv hfun z₀‖ / 2) + Real.log ‖chartAt ℂ q x' - z₀‖
          ≤ Real.log ‖hfun (chartAt ℂ q x') - w₀‖ := by
        rw [← Real.log_mul (ne_of_gt hhalf) (ne_of_gt hnp)]
        exact Real.log_le_log (mul_pos hhalf hnp) hprod.le
      have hpole_src : poleCoord q x' = chartAt ℂ q x' - z₀ := by
        rw [hz₀def]
        simp only [poleCoord]
      have hpole_tgt : poleCoord (f q) (f x') = hfun (chartAt ℂ q x') - w₀ := by
        rw [hval, hw₀def]
        simp only [poleCoord]
      rw [hpole_tgt] at h1
      simp only [Function.comp_apply]
      rw [hpole_src]
      linarith
  -- The evaluation images coincide, hence the envelopes agree.
  have himg : (fun v : N → ℝ => v (e x)) '' greenFamily (e p₀) =
      (fun w : M → ℝ => w x) '' greenFamily p₀ := by
    apply Set.Subset.antisymm
    · rintro a ⟨v, hv, rfl⟩
      exact ⟨v ∘ ⇑e, hfwd p₀ v hv, rfl⟩
    · rintro a ⟨w, hw, rfl⟩
      have hw' : w ∈ greenFamily (e.symm (e p₀)) := by
        rw [e.symm_apply_apply]; exact hw
      refine ⟨w ∘ ⇑e.symm, hbwd (e p₀) w hw', ?_⟩
      change w (e.symm (e x)) = w x
      rw [e.symm_apply_apply]
  change sSup ((fun v : N → ℝ => v (e x)) '' greenFamily (e p₀)) =
    sSup ((fun w : M → ℝ => w x) '' greenFamily p₀)
  rw [himg]

end RiemannDynamics
