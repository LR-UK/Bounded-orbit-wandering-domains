/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreenSymmetry.Transport

/-!
# Symmetry and existence of the Green's function

The plane has no Green's function; on a simply connected surface the Green
envelope is symmetric and the Green's function exists away from the parabolic
case; subharmonic bounds pass across finitely many punctures, and harmonic
functions agreeing on an open piece agree on a connected open set.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **The plane carries no Green's function**: the truncated logarithms
`max (log (R/‖z - p₀‖)) 0` are members of the Perron Green's family with
unbounded evaluations. -/
theorem not_hasGreenFunction_complex (p₀ : ℂ) : ¬ HasGreenFunction p₀ := by
  rintro ⟨x, hx, B, hB⟩
  -- The truncation radius, chosen so the family member exceeds the bound at `x`.
  set R : ℝ := Real.exp (B + 1 + Real.log ‖x - p₀‖) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hlogR : Real.log R = B + 1 + Real.log ‖x - p₀‖ := by
    rw [hR]; exact Real.log_exp _
  -- The truncated logarithm.
  set v : ℂ → ℝ := fun z => max (Real.log R - Real.log ‖z - p₀‖) 0 with hv
  -- Charts on the plane are the identity, so the pole coordinate is `z - p₀`.
  have hpole_eq : ∀ y : ℂ, poleCoord p₀ y = y - p₀ := fun y => rfl
  -- The logarithmic kernel is harmonic off the pole.
  have hharm : HarmonicOnNhd (fun z : ℂ => Real.log R - Real.log ‖z - p₀‖) {p₀}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun t : ℂ => t - p₀) z := by
      exact analyticAt_id.sub analyticAt_const
    have hne : z - p₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log R)).sub (hana.harmonicAt_log_norm hne)
  have hvsub : SubharmonicOn v {p₀}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) {p₀}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hharm) h0
  -- Restriction of plane subharmonicity to subsets of the punctured plane.
  have hmono : ∀ W : Set ℂ, W ⊆ {p₀}ᶜ → SubharmonicOn v W := by
    intro W hW
    refine ⟨hvsub.1.mono hW, ?_⟩
    intro c hc ρ hρ hb
    exact hvsub.2 c (hW hc) ρ hρ (hb.trans hW)
  -- The member vanishes off the closed ball of radius `R`.
  have hvzero : ∀ z : ℂ, z ∉ closedBall p₀ R → v z = 0 := by
    intro z hz
    have hzr : R < ‖z - p₀‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      exact hz
    have hle : Real.log R ≤ Real.log ‖z - p₀‖ := Real.log_le_log hR0 hzr.le
    simp only [hv]
    exact max_eq_right (by linarith)
  -- Membership in the Perron family.
  have hmem : v ∈ greenFamily p₀ := by
    refine ⟨?_, hvsub.1, ⟨closedBall p₀ R, isCompact_closedBall _ _, ?_, hvzero⟩,
      Real.log R, ?_⟩
    · -- Subharmonicity, read in the identity charts of the plane.
      intro z hz
      have hzp : z ≠ p₀ := Set.mem_compl_singleton_iff.mp hz
      have hr0 : 0 < ‖z - p₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
      have hballsub : ball z ‖z - p₀‖ ⊆ ({p₀}ᶜ : Set ℂ) := by
        intro w hw
        rw [Set.mem_compl_singleton_iff]
        intro hwp
        rw [mem_ball, hwp, dist_eq_norm, norm_sub_rev] at hw
        exact lt_irrefl _ hw
      exact ⟨‖z - p₀‖, hr0, fun w _ => Set.mem_univ w, hmono _ hballsub⟩
    · -- The closed ball is not the whole plane.
      exact (isCompact_closedBall p₀ R).ne_univ
    · -- Logarithmic pole growth with constant `log R`.
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds p₀ hR0),
        eventually_mem_nhdsWithin] with y hy hyp
      have hyne : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hyp
      have hypos : 0 < ‖y - p₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
      have hlt : ‖y - p₀‖ < R := by
        rw [mem_ball, dist_eq_norm] at hy
        exact hy
      have hlog : Real.log ‖y - p₀‖ < Real.log R := Real.log_lt_log hypos hlt
      rw [hpole_eq]
      simp only [hv]
      rw [max_eq_left (by linarith)]
      linarith
  -- The member exceeds the upper bound at the witness point.
  have hvx : v x ≤ B := hB ⟨v, hmem, rfl⟩
  have hgt : B + 1 ≤ v x := by
    have heq : Real.log R - Real.log ‖x - p₀‖ = B + 1 := by
      rw [hlogR]; ring
    calc B + 1 = Real.log R - Real.log ‖x - p₀‖ := heq.symm
      _ ≤ v x := le_max_left _ _
  linarith

/-- **Symmetry of the Green's function on simply connected surfaces**: a
simply connected hyperbolic surface is biholomorphic to a plane domain, the
Riemann map takes the domain to the unit disc, and the disc kernel is
symmetric. -/
theorem greenEnvelope_symm_of_simplyConnected [T2Space M] [ConnectedSpace M]
    [SimplyConnectedSpace M] [NoncompactSpace M] {p q : M}
    (hG : HasGreenFunction p) (hpq : p ≠ q) :
    greenEnvelope p q = greenEnvelope q p := by
  classical
  -- ## The biholomorphism onto a plane domain, from the Green's map.
  obtain ⟨φ, hφ, h0, habs⟩ := exists_green_map hG
  have hinj : Function.Injective φ := injective_green_map hG hφ h0 habs
  obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_complex_of_injective hφ hinj
  by_cases hne : (U : Set ℂ) = Set.univ
  · -- ## The full-plane case contradicts hyperbolicity.
    exfalso
    have hU : U = ⊤ := Opens.ext (by simpa using hne)
    subst hU
    obtain ⟨etop⟩ := nonempty_diffeomorph_top ℂ
    obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := ⟨e.trans etop⟩
    have hpos := greenEnvelope_pos hG q (Ne.symm hpq)
    have htrans := greenEnvelope_comp_diffeomorph E p q
    have hnb : ¬ BddAbove ((fun v => v (E q)) '' greenFamily (E p)) := fun hb =>
      not_hasGreenFunction_complex (E p)
        ⟨E q, fun h => Ne.symm hpq (E.toEquiv.injective h), hb⟩
    have hzero : greenEnvelope (E p) (E q) = 0 := Real.sSup_of_not_bddAbove hnb
    rw [htrans] at hzero
    linarith
  · -- ## The Riemann map to the disc; transfer and the explicit kernel.
    have hscU : SimplyConnectedSpace ↥U :=
      simplyConnectedSpace_of_homeomorph e.toHomeomorph inferInstance
    obtain ⟨f, hf, hfinj, hfimg⟩ :=
      exists_riemannMap_of_simplyConnectedSpace U.isOpen hne hscU
    obtain ⟨e₂⟩ := nonempty_diffeomorph_of_injOn_differentiableOn U discOpens f hf
      hfinj hfimg
    obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥discOpens) := ⟨e.trans e₂⟩
    have ha : ‖(E p : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E p).2
    have hb : ‖(E q : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E q).2
    have hba : (E q : ℂ) ≠ (E p : ℂ) := fun h =>
      hpq (E.toEquiv.injective (Subtype.ext h)).symm
    have hab : (E p : ℂ) ≠ (E q : ℂ) := hba.symm
    -- The two explicit disc values, with the two poles.
    have key1 : greenEnvelope (E p) (E q) =
        -Real.log ‖((E q : ℂ) - (E p : ℂ)) /
          (1 - (starRingEnd ℂ) (E p : ℂ) * (E q : ℂ))‖ :=
      greenEnvelope_unitDisc_eq ha hb hba
    have key2 : greenEnvelope (E q) (E p) =
        -Real.log ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ :=
      greenEnvelope_unitDisc_eq hb ha hab
    -- Symmetry of the Möbius kernel: conjugate the denominator.
    have hden : ‖(1 : ℂ) - (starRingEnd ℂ) (E p : ℂ) * (E q : ℂ)‖ =
        ‖(1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)‖ := by
      rw [← Complex.norm_conj ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)),
        map_sub, map_one, map_mul, Complex.conj_conj]
      congr 1
      ring
    have hker : ‖((E q : ℂ) - (E p : ℂ)) /
          (1 - (starRingEnd ℂ) (E p : ℂ) * (E q : ℂ))‖ =
        ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ := by
      rw [norm_div, norm_div, norm_sub_rev ((E q : ℂ)) ((E p : ℂ)), hden]
    -- Conformal transfer at both pole/point pairs.
    have t1 : greenEnvelope (E p) (E q) = greenEnvelope p q :=
      greenEnvelope_comp_diffeomorph E p q
    have t2 : greenEnvelope (E q) (E p) = greenEnvelope q p :=
      greenEnvelope_comp_diffeomorph E q p
    rw [← t1, ← t2, key1, key2, hker]

/-- **Pole independence on simply connected surfaces**: a simply connected
hyperbolic surface is hyperbolic at every pole, via the biholomorphism onto a
plane domain and the disc kernel. -/
theorem hasGreenFunction_of_simplyConnected [T2Space M] [ConnectedSpace M]
    [SimplyConnectedSpace M] [NoncompactSpace M] {p q : M}
    (hG : HasGreenFunction p) : HasGreenFunction q := by
  classical
  by_cases hqp : q = p
  · subst hqp
    exact hG
  · -- ## The biholomorphism onto a plane domain, from the Green's map.
    obtain ⟨φ, hφ, h0, habs⟩ := exists_green_map hG
    have hinj : Function.Injective φ := injective_green_map hG hφ h0 habs
    obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_complex_of_injective hφ hinj
    by_cases hne : (U : Set ℂ) = Set.univ
    · -- ## The full-plane case contradicts hyperbolicity.
      exfalso
      have hU : U = ⊤ := Opens.ext (by simpa using hne)
      subst hU
      obtain ⟨etop⟩ := nonempty_diffeomorph_top ℂ
      obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := ⟨e.trans etop⟩
      have hpos := greenEnvelope_pos hG q hqp
      have htrans := greenEnvelope_comp_diffeomorph E p q
      have hnb : ¬ BddAbove ((fun v => v (E q)) '' greenFamily (E p)) := fun hb =>
        not_hasGreenFunction_complex (E p)
          ⟨E q, fun h => hqp (E.toEquiv.injective h), hb⟩
      have hzero : greenEnvelope (E p) (E q) = 0 := Real.sSup_of_not_bddAbove hnb
      rw [htrans] at hzero
      linarith
    · -- ## The disc case: positivity of the kernel forces boundedness.
      have hscU : SimplyConnectedSpace ↥U :=
        simplyConnectedSpace_of_homeomorph e.toHomeomorph inferInstance
      obtain ⟨f, hf, hfinj, hfimg⟩ :=
        exists_riemannMap_of_simplyConnectedSpace U.isOpen hne hscU
      obtain ⟨e₂⟩ := nonempty_diffeomorph_of_injOn_differentiableOn U discOpens f hf
        hfinj hfimg
      obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥discOpens) := ⟨e.trans e₂⟩
      have ha : ‖(E q : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E q).2
      have hb : ‖(E p : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E p).2
      have hab : (E p : ℂ) ≠ (E q : ℂ) := fun h =>
        hqp (E.toEquiv.injective (Subtype.ext h)).symm
      have hval : greenEnvelope (E q) (E p) =
          -Real.log ‖((E p : ℂ) - (E q : ℂ)) /
            (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ :=
        greenEnvelope_unitDisc_eq ha hb hab
      -- ### Positivity: the pseudohyperbolic distance lies strictly in `(0, 1)`.
      have hnum : (E p : ℂ) - (E q : ℂ) ≠ 0 := sub_ne_zero_of_ne hab
      have hdenne : (1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ) ≠ 0 := by
        intro h
        have h1 : (1 : ℂ) = (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ) := sub_eq_zero.mp h
        have h2 : (1 : ℝ) = ‖(E q : ℂ)‖ * ‖(E p : ℂ)‖ := by
          calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
            _ = ‖(starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)‖ := by rw [← h1]
            _ = ‖(E q : ℂ)‖ * ‖(E p : ℂ)‖ := by rw [norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg ((E q : ℂ)), norm_nonneg ((E p : ℂ))]
      have htpos : 0 < ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ :=
        norm_pos_iff.mpr (div_ne_zero hnum hdenne)
      have htlt : ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hdenne)]
        have hA2 : Complex.normSq (E q : ℂ) < 1 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg ((E q : ℂ))]
        have hB2 : Complex.normSq (E p : ℂ) < 1 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg ((E p : ℂ))]
        have hkey : Complex.normSq ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)) -
            Complex.normSq ((E p : ℂ) - (E q : ℂ)) =
            (1 - Complex.normSq (E q : ℂ)) * (1 - Complex.normSq (E p : ℂ)) := by
          simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
            Complex.mul_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
          ring
        have hsq : Complex.normSq ((E p : ℂ) - (E q : ℂ)) <
            Complex.normSq ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)) := by
          nlinarith [hkey, hA2, hB2]
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
        nlinarith [norm_nonneg ((E p : ℂ) - (E q : ℂ)),
          norm_nonneg ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))]
      have hlog : Real.log ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ < 0 := Real.log_neg htpos htlt
      have hpos : 0 < greenEnvelope (E q) (E p) := by
        rw [hval]
        linarith
      -- ### From the positive value to boundedness of the family at `p`.
      have htrans : greenEnvelope (E q) (E p) = greenEnvelope q p :=
        greenEnvelope_comp_diffeomorph E q p
      refine ⟨p, Ne.symm hqp, ?_⟩
      by_contra hnb
      have hzero : greenEnvelope q p = 0 := Real.sSup_of_not_bddAbove hnb
      rw [htrans, hzero] at hpos
      exact lt_irrefl 0 hpos

/-- **The finitely-punctured maximum principle**: a subharmonic function on
the complement of a finite set that vanishes off a compact set and is bounded
above near each puncture is nonpositive away from the punctures. -/
theorem msubharmonic_le_zero_of_finite_punctures [ConnectedSpace M]
    [NoncompactSpace M] [T2Space M] {F : Finset M} {v : M → ℝ}
    (hv : MSubharmonicOn v (↑F : Set M)ᶜ)
    (hsupp : ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, v x ≤ 0)
    (hpole : ∀ p ∈ F, ∃ C, ∀ᶠ x in 𝓝[≠] p, v x ≤ C) :
    ∀ x ∉ F, v x ≤ 0 := by
  classical
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  have : Infinite M := by
    by_contra hcon
    rw [not_infinite_iff_finite] at hcon
    have : CompactSpace M := Finite.compactSpace
    exact NoncompactSpace.noncompact_univ (X := M) isCompact_univ
  obtain ⟨K, hK, hKv⟩ := hsupp
  -- Continuity of `v` off the punctures.
  have hvcont : ∀ y : M, y ∉ (↑F : Set M) → ContinuousAt v y :=
    fun y hy => (hv y hy).continuousAt
  /- ## Connectivity of finite complements, by induction on the puncture set. -/
  have hconnF : ∀ G : Finset M, IsConnected ((↑G : Set M)ᶜ) := by
    intro G
    induction G using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty, Set.compl_empty]
      exact isConnected_univ
    | insert p G' hpG' IH =>
      have hG'cl : IsClosed (↑G' : Set M) := G'.finite_toSet.isClosed
      set S : Opens M := ⟨(↑G' : Set M)ᶜ, hG'cl.isOpen_compl⟩ with hSdef
      have : ConnectedSpace ↥S := Subtype.connectedSpace IH
      have hpS : p ∈ S := by
        change p ∉ (↑G' : Set M)
        exact fun hcon => hpG' (Finset.mem_coe.mp hcon)
      have hinfc : ((↑G' : Set M)ᶜ).Infinite := G'.finite_toSet.infinite_compl
      obtain ⟨a, haS, b, hbS, hab⟩ := hinfc.nontrivial
      have hnt' : ∃ u w : ↥S, u ≠ w :=
        ⟨⟨a, haS⟩, ⟨b, hbS⟩, fun h => hab (congrArg Subtype.val h)⟩
      have hc := isConnected_compl_singleton_of_connected (M := ↥S) hnt' ⟨p, hpS⟩
      have himgc := hc.image Subtype.val continuous_subtype_val.continuousOn
      have heq : Subtype.val '' ({(⟨p, hpS⟩ : ↥S)}ᶜ : Set ↥S) =
          (↑(insert p G') : Set M)ᶜ := by
        ext w
        constructor
        · rintro ⟨⟨a', ha'⟩, hane, rfl⟩
          intro hw
          rw [Finset.coe_insert, Set.mem_insert_iff] at hw
          rcases hw with hw | hw
          · exact hane (Set.mem_singleton_iff.mpr (Subtype.ext hw))
          · exact ha' hw
        · intro hw
          have hw' : w ∉ insert p G' := hw
          have hwp : w ≠ p := fun h => hw' (h ▸ Finset.mem_insert_self p G')
          have hwG' : w ∉ (↑G' : Set M) :=
            fun h => hw' (Finset.mem_insert_of_mem (Finset.mem_coe.mp h))
          refine ⟨⟨w, hwG'⟩, ?_, rfl⟩
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hwp (congrArg Subtype.val hcon)
      rwa [heq] at himgc
  rcases F.eq_empty_or_nonempty with rfl | hFne
  /- ## No punctures: reduce to the single-puncture principle at an artificial pole. -/
  · intro x _
    obtain ⟨p₀, hp₀⟩ := exists_ne x
    have hv' : MSubharmonicOn v {p₀}ᶜ := fun q _ => hv q (by simp)
    have hpole' : ∃ C, ∀ᶠ y in 𝓝[≠] p₀, v y ≤ C := by
      have hcont : ContinuousAt v p₀ := hvcont p₀ (by simp)
      refine ⟨v p₀ + 1, ?_⟩
      have h1 : ∀ᶠ y in 𝓝 p₀, v y < v p₀ + 1 := hcont.eventually_lt_const (lt_add_one _)
      exact (h1.filter_mono nhdsWithin_le_nhds).mono fun y hy => hy.le
    exact msubharmonic_le_zero_of_puncture hv' ⟨K, hK, hKv⟩ hpole' x hp₀.symm
  /- ## Per-puncture data: pole constants and chart radii avoiding other punctures. -/
  have hpoleC : ∀ p : M, ∃ C : ℝ, p ∈ F → ∀ᶠ x in 𝓝[≠] p, v x ≤ C := by
    intro p
    by_cases hp : p ∈ F
    · obtain ⟨C, hC⟩ := hpole p hp
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose C hC using hpoleC
  -- Images under `(chartAt ℂ p).symm` of subsets of the target, in preimage form.
  have himg : ∀ (p : M) (s : Set ℂ), s ⊆ (chartAt ℂ p).target →
      (chartAt ℂ p).symm '' s = (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' s := by
    intro p s hs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(chartAt ℂ p).map_target (hs hz), ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ p).right_inv (hs hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨chartAt ℂ p y, hy2, (chartAt ℂ p).left_inv hy⟩
  -- Chart radii on which the pole bound holds and no other puncture appears.
  have hrad : ∀ p : M, ∃ r : ℝ, 0 < r ∧ (p ∈ F →
      closedBall (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧
      (∀ y ∈ (chartAt ℂ p).source,
        chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) r → y ≠ p → v y ≤ C p) ∧
      ∀ y ∈ (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) r,
        y ∈ (↑F : Set M) → y = p) := by
    intro p
    by_cases hp : p ∈ F
    swap
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
    set e := chartAt ℂ p with he
    have hps : p ∈ e.source := mem_chart_source ℂ p
    set z₀ := e p with hz₀
    have hz₀t : z₀ ∈ e.target := e.map_source hps
    obtain ⟨N, hNnhds, hN⟩ := (eventually_nhdsWithin_iff.mp (hC p hp)).exists_mem
    have hFcl : IsClosed (↑(F.erase p) : Set M) := (F.erase p).finite_toSet.isClosed
    have hpav : p ∈ ((↑(F.erase p) : Set M)ᶜ) := by simp
    have hpre : e.target ∩ e.symm ⁻¹' (N ∩ (↑(F.erase p) : Set M)ᶜ) ∈ 𝓝 z₀ := by
      have h1 : ContinuousAt e.symm z₀ := e.continuousAt_symm hz₀t
      have hsymz₀ : e.symm z₀ = p := e.left_inv hps
      have h2 : N ∩ (↑(F.erase p) : Set M)ᶜ ∈ 𝓝 p :=
        Filter.inter_mem hNnhds (hFcl.isOpen_compl.mem_nhds hpav)
      have h3 : e.symm ⁻¹' (N ∩ (↑(F.erase p) : Set M)ᶜ) ∈ 𝓝 z₀ :=
        h1.preimage_mem_nhds (hsymz₀ ▸ h2)
      exact Filter.inter_mem (e.open_target.mem_nhds hz₀t) h3
    obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall.mem_iff).1 hpre
    refine ⟨r, hr, fun _ => ⟨fun z hz => (hrsub hz).1, ?_, ?_⟩⟩
    · intro y hys hyball hyne
      have h3 : e y ∈ e.symm ⁻¹' (N ∩ (↑(F.erase p) : Set M)ᶜ) := (hrsub hyball).2
      rw [Set.mem_preimage, e.left_inv hys] at h3
      exact hN y h3.1 (Set.mem_compl_singleton_iff.mpr hyne)
    · intro y hy hyF
      obtain ⟨z, hz, rfl⟩ := hy
      have h4 : e.symm z ∈ N ∩ (↑(F.erase p) : Set M)ᶜ := (hrsub hz).2
      by_contra hne
      exact h4.2 (Finset.mem_coe.mpr
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hyF⟩))
  choose r hr0 hrP using hrad
  /- ## The coordinate disks, circles, and their unions. -/
  set D : M → Set M :=
    fun p => (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (r p) with hDdef
  set Γ : M → Set M :=
    fun p => (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (r p) with hΓdef
  have hpD : ∀ p : M, p ∈ D p := by
    intro p
    simp only [hDdef]
    exact ⟨chartAt ℂ p p, mem_closedBall_self (hr0 p).le,
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)⟩
  have hDcomp : ∀ p ∈ (↑F : Set M), IsCompact (D p) := by
    intro p hp
    simp only [hDdef]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt ℂ p).continuousOn_symm.mono (hrP p (Finset.mem_coe.mp hp)).1)
  have hΓcomp : ∀ p ∈ (↑F : Set M), IsCompact (Γ p) := by
    intro p hp
    simp only [hΓdef]
    exact (isCompact_sphere _ _).image_of_continuousOn
      ((chartAt ℂ p).continuousOn_symm.mono
        (sphere_subset_closedBall.trans (hrP p (Finset.mem_coe.mp hp)).1))
  have hΓmem : ∀ (p : M), ∀ y ∈ (chartAt ℂ p).source,
      dist (chartAt ℂ p y) (chartAt ℂ p p) = r p → y ∈ Γ p := by
    intro p y hys hyd
    simp only [hΓdef]
    exact ⟨chartAt ℂ p y, by rwa [mem_sphere], (chartAt ℂ p).left_inv hys⟩
  -- Circles avoid all punctures.
  have hΓF : ∀ p ∈ (↑F : Set M), ∀ y ∈ Γ p, y ∉ (↑F : Set M) := by
    intro p hp y hyΓ hyF
    obtain ⟨hrtp, -, havoidp⟩ := hrP p (Finset.mem_coe.mp hp)
    have hyD : y ∈ D p := by
      simp only [hDdef]
      simp only [hΓdef] at hyΓ
      exact Set.image_mono sphere_subset_closedBall hyΓ
    have hyp : y = p := havoidp y (by simpa only [hDdef] using hyD) hyF
    simp only [hΓdef] at hyΓ
    obtain ⟨z, hz, hzy⟩ := hyΓ
    rw [mem_sphere] at hz
    have hzt : z ∈ (chartAt ℂ p).target :=
      hrtp (sphere_subset_closedBall (by rwa [mem_sphere]))
    have hzne : z ≠ chartAt ℂ p p := by
      intro hcon
      rw [hcon, dist_self] at hz
      exact (hr0 p).ne hz
    apply hzne
    have h5 := (chartAt ℂ p).right_inv hzt
    rw [hzy, hyp] at h5
    exact h5.symm
  set Dtot : Set M := ⋃ p ∈ (↑F : Set M), D p with hDtotdef
  have hDtotcomp : IsCompact Dtot :=
    F.finite_toSet.isCompact_biUnion fun p hp => hDcomp p hp
  have hDtotcl : IsClosed Dtot := hDtotcomp.isClosed
  set Γtot : Set M := ⋃ p ∈ (↑F : Set M), Γ p with hΓtotdef
  have hΓtotcomp : IsCompact Γtot :=
    F.finite_toSet.isCompact_biUnion fun p hp => hΓcomp p hp
  have hΓtotne : Γtot.Nonempty := by
    obtain ⟨p, hp⟩ := hFne
    have h1 : (Γ p).Nonempty := by
      simp only [hΓdef]
      exact (NormedSpace.sphere_nonempty.2 (hr0 p).le).image _
    obtain ⟨q, hq⟩ := h1
    rw [hΓtotdef]
    exact ⟨q, Set.mem_biUnion (Finset.mem_coe.mpr hp) hq⟩
  have hΓtotF : ∀ y ∈ Γtot, y ∉ (↑F : Set M) := by
    intro y hy
    rw [hΓtotdef] at hy
    obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
    exact hΓF p hp y hyp
  have hΓtotcont : ContinuousOn v Γtot :=
    fun q hq => (hvcont q (hΓtotF q hq)).continuousWithinAt
  obtain ⟨xΓ, hxΓ, hxΓmax⟩ := hΓtotcomp.exists_isMaxOn hΓtotne hΓtotcont
  set m₁ : ℝ := max (v xΓ) 0 with hm₁
  have hm₁0 : (0 : ℝ) ≤ m₁ := le_max_right _ _
  have hΓle : ∀ y ∈ Γtot, v y ≤ m₁ := fun y hy => (hxΓmax hy).trans (le_max_left _ _)
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
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun x hx => hwsub x (hCcΩ hx)) (fun x hx => hall x (hCcΩ hx))
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
  /- ## A far point outside `K` and all the punctures. -/
  have hfar : ∃ y₀ : M, y₀ ∉ K ∪ (↑F : Set M) := by
    by_contra hcon
    push Not at hcon
    have huniv : K ∪ (↑F : Set M) = Set.univ := Set.eq_univ_of_forall hcon
    have hcomp : IsCompact (K ∪ (↑F : Set M)) := hK.union F.finite_toSet.isCompact
    rw [huniv] at hcomp
    exact NoncompactSpace.noncompact_univ (X := M) hcomp
  /- ## Outer estimate: maximum principle outside the union of disks. -/
  have houterAll : ∀ x ∈ (Dtotᶜ : Set M), v x ≤ m₁ := by
    refine maxPrin Dtotᶜ v m₁ K hDtotcl.isOpen_compl ?_ ?_ hK ?_ ?_
    · intro hcon
      obtain ⟨p, hp⟩ := hFne
      have h5 : p ∈ (Dtotᶜ : Set M) := by rw [hcon]; trivial
      apply h5
      rw [hDtotdef]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hp) (hpD p)
    · intro q hq
      refine hv q ?_
      intro hqF
      apply hq
      rw [hDtotdef]
      exact Set.mem_biUnion hqF (hpD q)
    · exact fun q _ hqK => (hKv q hqK).trans hm₁0
    · rintro y ⟨hycl, hyc⟩
      have hyD : y ∈ Dtot := not_not.1 hyc
      rw [hDtotdef] at hyD
      obtain ⟨p, hpFc, hyDp⟩ := Set.mem_iUnion₂.mp hyD
      obtain ⟨hrtp, -, havoidp⟩ := hrP p (Finset.mem_coe.mp hpFc)
      have hyDp' : y ∈ (chartAt ℂ p).source ∩
          chartAt ℂ p ⁻¹' closedBall (chartAt ℂ p p) (r p) := by
        rw [← himg p _ hrtp]
        simpa only [hDdef] using hyDp
      obtain ⟨hysrc, hyball⟩ := hyDp'
      have hynb : chartAt ℂ p y ∉ ball (chartAt ℂ p p) (r p) := by
        intro hcon
        have hBopen : IsOpen ((chartAt ℂ p).source ∩
            chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) (r p)) :=
          (chartAt ℂ p).continuousOn.isOpen_inter_preimage
            (chartAt ℂ p).open_source isOpen_ball
        have hBsubD : (chartAt ℂ p).source ∩
            chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) (r p) ⊆ Dtot := by
          rw [hDtotdef]
          refine Set.Subset.trans ?_ (Set.subset_biUnion_of_mem hpFc)
          simp only [hDdef]
          rw [himg p _ hrtp]
          exact Set.inter_subset_inter (subset_refl _)
            (Set.preimage_mono ball_subset_closedBall)
        have hyint : y ∈ interior Dtot := interior_maximal hBsubD hBopen ⟨hysrc, hcon⟩
        rw [closure_compl] at hycl
        exact hycl hyint
      have hyr : dist (chartAt ℂ p y) (chartAt ℂ p p) = r p := by
        rw [mem_ball] at hynb
        rw [Set.mem_preimage, mem_closedBall] at hyball
        exact le_antisymm hyball (not_lt.1 hynb)
      have hyneza : chartAt ℂ p y ≠ chartAt ℂ p p := by
        intro hcon
        rw [hcon, dist_self] at hyr
        exact (hr0 p).ne hyr
      have hynep : y ≠ p := by
        intro hcon
        rw [hcon] at hyneza
        exact hyneza rfl
      have hynF : y ∉ (↑F : Set M) := by
        intro hyF
        exact hynep (havoidp y (by simpa only [hDdef] using hyDp) hyF)
      exact ⟨hvcont y hynF,
        hΓle y (by rw [hΓtotdef]; exact Set.mem_biUnion hpFc (hΓmem p y hysrc hyr))⟩
  /- ## Inner estimate: the `ε·log` barrier on each punctured disk. -/
  have hinner : ∀ p ∈ F, ∀ x ∈ D p, x ≠ p → v x ≤ m₁ := by
    intro p hpF x hxD hxp
    obtain ⟨hrtp, hCbp, havoidp⟩ := hrP p hpF
    have hDpcomp : IsCompact (D p) := hDcomp p (Finset.mem_coe.mpr hpF)
    have hDpcl : IsClosed (D p) := hDpcomp.isClosed
    set e := chartAt ℂ p with he
    have hps : p ∈ e.source := mem_chart_source ℂ p
    set z₀ := e p with hz₀
    have hz₀t : z₀ ∈ e.target := e.map_source hps
    have hsymz₀ : e.symm z₀ = p := e.left_inv hps
    have hpid : ∀ y, y ∈ e.source → e y = z₀ → y = p := by
      intro y hys hyz
      rw [← e.left_inv hys, hyz]
      exact hsymz₀
    have hnep : ∀ y, y ∈ e.source → e y ≠ z₀ → y ≠ p := by
      intro y hys hyne hcon
      rw [hcon] at hyne
      exact hyne hz₀.symm
    have himgE : ∀ s : Set ℂ, s ⊆ e.target → e.symm '' s = e.source ∩ e ⁻¹' s := by
      intro s hs
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨e.map_target (hs hz), ?_⟩
        rw [Set.mem_preimage, e.right_inv (hs hz)]
        exact hz
      · rintro ⟨hy, hy2⟩
        exact ⟨e y, hy2, e.left_inv hy⟩
    have hDp : D p = e.symm '' closedBall z₀ (r p) := by
      simp only [hDdef]
      rw [← he, ← hz₀]
    rw [hDp, himgE _ hrtp] at hxD
    obtain ⟨hxsrc, hxball⟩ := hxD
    rw [Set.mem_preimage, mem_closedBall] at hxball
    have hxz : e x ≠ z₀ := fun hcon => hxp (hpid x hxsrc hcon)
    have hdx0 : 0 < dist (e x) z₀ := dist_pos.2 hxz
    rcases eq_or_lt_of_le hxball with heqr | hdxlt
    · refine hΓle x ?_
      rw [hΓtotdef]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpF) (hΓmem p x hxsrc heqr)
    -- Strict interior: show `v x ≤ m₁ + δ` for every `δ > 0`.
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    set L : ℝ := Real.log (r p) - Real.log (dist (e x) z₀) with hLdef
    have hL0 : 0 < L := sub_pos.2 (Real.log_lt_log hdx0 hdxlt)
    set ε : ℝ := δ / L with hεdef
    have hε0 : 0 < ε := div_pos hδ hL0
    have hεL : ε * L = δ := by
      rw [hεdef]
      exact div_mul_cancel₀ δ hL0.ne'
    -- Excision radius `σ`, small enough for the barrier to beat `C p`.
    set Q : ℝ := (m₁ - C p) / ε + Real.log (r p) with hQdef
    set σ : ℝ := min (dist (e x) z₀ / 2) (Real.exp Q) with hσdef
    have hσ0 : 0 < σ := lt_min (half_pos hdx0) (Real.exp_pos Q)
    have hσdx : σ < dist (e x) z₀ :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hdx0)
    have hσr : σ < r p := hσdx.trans hdxlt
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) := Real.log_le_log hσ0 (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hbarrier : C p + ε * (Real.log σ - Real.log (r p)) ≤ m₁ := by
      have h5 : ε * (Real.log σ - Real.log (r p)) ≤ ε * ((m₁ - C p) / ε) := by
        apply mul_le_mul_of_nonneg_left _ hε0.le
        rw [hQdef] at hσQ
        linarith
      have h6 : ε * ((m₁ - C p) / ε) = m₁ - C p := by field_simp
      linarith
    -- The annulus and the barriered competitor.
    set O : Set ℂ := ball z₀ (r p) \ closedBall z₀ σ with hOdef
    have hOopen : IsOpen O := isOpen_ball.sdiff isClosed_closedBall
    have hOsub : O ⊆ e.target := fun z hz => hrtp (ball_subset_closedBall hz.1)
    set A : Set M := e.symm '' O with hAdef
    have hAopen : IsOpen A := by
      rw [hAdef, himgE _ hOsub]
      exact e.continuousOn.isOpen_inter_preimage e.open_source hOopen
    have hAD : A ⊆ D p := by
      rw [hAdef, hDp, himgE _ hOsub, himgE _ hrtp]
      exact Set.inter_subset_inter (subset_refl _)
        (Set.preimage_mono (Set.sdiff_subset.trans ball_subset_closedBall))
    have hpclA : p ∉ closure A := by
      intro hcon
      have hU : IsOpen (e.source ∩ e ⁻¹' ball z₀ σ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hpU : p ∈ e.source ∩ e ⁻¹' ball z₀ σ := by
        refine ⟨hps, ?_⟩
        rw [Set.mem_preimage, ← hz₀]
        exact mem_ball_self hσ0
      obtain ⟨q, hq1, hq2⟩ := mem_closure_iff.1 hcon _ hU hpU
      rw [hAdef, himgE _ hOsub] at hq2
      exact hq2.2.2 (ball_subset_closedBall hq1.2)
    have hAne : A ≠ Set.univ := by
      intro hcon
      apply hpclA
      apply subset_closure
      rw [hcon]
      trivial
    set W : M → ℝ := fun q => v q + ε * (Real.log (dist (e q) z₀) - Real.log (r p))
      with hW
    -- Harmonicity of the logarithmic barrier through the chart.
    have hbharm : ∀ y, y ∈ e.source → e y ≠ z₀ →
        MHarmonicAt (fun q => Real.log (dist (e q) z₀)) y := by
      intro y hys hyne
      rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hys]
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
    have mharm_affine : ∀ (g : M → ℝ) (y : M) (a c : ℝ), MHarmonicAt g y →
        MHarmonicAt (fun q => a * g q + c) y := by
      intro g y a c hg
      have h1 : HarmonicAt (g ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hg
      have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
      have heq2 : (a • (g ∘ (chartAt ℂ y).symm) + fun _ => c) =
          (fun q => a * g q + c) ∘ (chartAt ℂ y).symm := by
        funext w
        simp [smul_eq_mul]
      rw [heq2] at h2
      exact h2
    have hWsub : MSubharmonicOn W A := by
      intro q hqA
      rw [hAdef, himgE _ hOsub] at hqA
      obtain ⟨hqs, hqO⟩ := hqA
      have hqz : e q ≠ z₀ := by
        intro hcon
        apply hqO.2
        rw [hcon, mem_closedBall, dist_self]
        exact hσ0.le
      have hqnF : q ∉ (↑F : Set M) := by
        intro hqF
        have hqDp : q ∈ e.symm '' closedBall z₀ (r p) := by
          rw [← hDp]
          exact hAD (by rw [hAdef, himgE _ hOsub]; exact ⟨hqs, hqO⟩)
        exact hnep q hqs hqz (havoidp q hqDp hqF)
      have hu : MHarmonicAt
          (fun y => (-ε) * Real.log (dist (e y) z₀) + ε * Real.log (r p)) q :=
        mharm_affine _ q _ _ (hbharm q hqs hqz)
      have h7 := (hv q hqnF).sub_mharmonicAt hu
      convert h7 using 2
      simp only [hW]
      ring
    have hWfr : ∀ y ∈ closure A \ A, ContinuousAt W y ∧ W y ≤ m₁ := by
      rintro y ⟨hycl, hyA⟩
      have hyDp : y ∈ e.source ∩ e ⁻¹' closedBall z₀ (r p) := by
        rw [← himgE _ hrtp, ← hDp]
        exact closure_minimal hAD hDpcl hycl
      obtain ⟨hysrc, hyball⟩ := hyDp
      rw [Set.mem_preimage, mem_closedBall] at hyball
      have hyneza : e y ≠ z₀ := by
        intro hcon
        exact hpclA (hpid y hysrc hcon ▸ hycl)
      have hynep : y ≠ p := hnep y hysrc hyneza
      have hynF : y ∉ (↑F : Set M) := by
        intro hyF
        apply hynep
        refine havoidp y ?_ hyF
        rw [himgE _ hrtp]
        refine ⟨hysrc, ?_⟩
        rw [Set.mem_preimage, mem_closedBall]
        exact hyball
      have hy0 : 0 < dist (e y) z₀ := dist_pos.2 hyneza
      have hWcont : ContinuousAt W y := by
        rw [hW]
        exact (hvcont y hynF).add
          (continuousAt_const.mul ((hbcont y hysrc hyneza).sub continuousAt_const))
      have hyO : e y ∉ O := by
        intro hcon
        apply hyA
        rw [hAdef, himgE _ hOsub]
        exact ⟨hysrc, hcon⟩
      refine ⟨hWcont, ?_⟩
      by_cases hyb : e y ∈ ball z₀ (r p)
      · -- Inner circle: the barrier beats the pole bound `C p`.
        have hyσ : dist (e y) z₀ ≤ σ := by
          have h8 : e y ∈ closedBall z₀ σ := by
            by_contra h9
            exact hyO ⟨hyb, h9⟩
          rwa [mem_closedBall] at h8
        have hvy : v y ≤ C p := hCbp y hysrc (by rwa [mem_closedBall]) hynep
        have hlogy : Real.log (dist (e y) z₀) ≤ Real.log σ := Real.log_le_log hy0 hyσ
        have h10 : ε * (Real.log (dist (e y) z₀) - Real.log (r p)) ≤
            ε * (Real.log σ - Real.log (r p)) := by
          apply mul_le_mul_of_nonneg_left _ hε0.le
          linarith
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log (r p)) ≤ m₁
        linarith
      · -- Outer circle: the barrier vanishes and the circles bound `v`.
        have hyr : dist (e y) z₀ = r p := by
          rw [mem_ball] at hyb
          exact le_antisymm hyball (not_lt.1 hyb)
        have hvy : v y ≤ m₁ := by
          refine hΓle y ?_
          rw [hΓtotdef]
          exact Set.mem_biUnion (Finset.mem_coe.mpr hpF) (hΓmem p y hysrc hyr)
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log (r p)) ≤ m₁
        rw [hyr, sub_self, mul_zero, add_zero]
        exact hvy
    have hAx : x ∈ A := by
      rw [hAdef, himgE _ hOsub]
      refine ⟨hxsrc, ?_⟩
      rw [Set.mem_preimage]
      refine ⟨by rwa [mem_ball], ?_⟩
      rw [mem_closedBall]
      exact fun hcon => (not_le.mpr hσdx) hcon
    have hWx := maxPrin A W m₁ (D p) hAopen hAne hWsub hDpcomp
      (fun q hq hqD => absurd (hAD hq) hqD) hWfr x hAx
    have hWxval : v x + ε * (Real.log (dist (e x) z₀) - Real.log (r p)) ≤ m₁ := hWx
    have hflip : ε * (Real.log (dist (e x) z₀) - Real.log (r p)) = -(ε * L) := by
      rw [hLdef]
      ring
    rw [hflip, hεL] at hWxval
    linarith
  /- ## Global bound and conclusion. -/
  have hglobal : ∀ x, x ∉ (↑F : Set M) → v x ≤ m₁ := by
    intro x hx
    by_cases hxD : x ∈ Dtot
    · rw [hDtotdef] at hxD
      obtain ⟨p, hpFc, hxDp⟩ := Set.mem_iUnion₂.mp hxD
      have hxp : x ≠ p := by
        intro hcon
        rw [hcon] at hx
        exact hx hpFc
      exact hinner p (Finset.mem_coe.mp hpFc) x hxDp hxp
    · exact houterAll x hxD
  intro x hx
  have hx' : x ∉ (↑F : Set M) := fun h => hx (Finset.mem_coe.mp h)
  rcases le_or_gt (v xΓ) 0 with hcase | hcase
  · have h11 : m₁ = 0 := max_eq_right hcase
    have h12 := hglobal x hx'
    rwa [h11] at h12
  · exfalso
    have hm₁Γ : m₁ = v xΓ := max_eq_left hcase.le
    have hmax : ∀ q ∈ ((↑F : Set M)ᶜ), v q ≤ v xΓ := by
      intro q hq
      have h12 := hglobal q hq
      rwa [hm₁Γ] at h12
    have hFopen : IsOpen ((↑F : Set M)ᶜ) := F.finite_toSet.isClosed.isOpen_compl
    have hxΓF : xΓ ∈ ((↑F : Set M)ᶜ) := hΓtotF xΓ hxΓ
    have hconst := propagate ((↑F : Set M)ᶜ) v xΓ hFopen (hconnF F).isPreconnected
      hxΓF hv hmax
    obtain ⟨y₀, hy₀⟩ := hfar
    have hy₀K : y₀ ∉ K := fun h => hy₀ (Or.inl h)
    have hy₀F : y₀ ∈ ((↑F : Set M)ᶜ) := fun h => hy₀ (Or.inr h)
    have h13 : v y₀ ≤ 0 := hKv y₀ hy₀K
    have h14 : v y₀ = v xΓ := hconst y₀ hy₀F
    linarith

/-- **The identity theorem for harmonic functions**: two functions harmonic on
a connected open set that agree on a nonempty open subset agree everywhere on
the set. -/
theorem MHarmonicOn.eqOn_of_eqOn {u v : M → ℝ} {s t : Set M} (hs : IsOpen s)
    (hsc : IsPreconnected s) (hu : MHarmonicOn u s) (hv : MHarmonicOn v s)
    (ht : IsOpen t) (htne : t.Nonempty) (hts : t ⊆ s) (heq : Set.EqOn u v t) :
    Set.EqOn u v s := by
  -- The set of points of `s` around which `u` and `v` agree.
  set A : Set M := {x | x ∈ s ∧ ∀ᶠ y in 𝓝 x, u y = v y}
  -- `A` is open.
  have hA_open : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxs, hxev⟩
    filter_upwards [hxev.eventually_nhds, hs.mem_nhds hxs] with y hy1 hy2
    exact ⟨hy2, hy1⟩
  -- `A` meets `s` (it contains `t`).
  obtain ⟨x₀, hx₀⟩ := htne
  have hx₀A : x₀ ∈ A := by
    refine ⟨hts hx₀, ?_⟩
    filter_upwards [ht.mem_nhds hx₀] with y hy using heq hy
  -- Limit points of `A` in `s` lie in `A`: analytic continuation through a chart ball.
  have hA_closed : closure A ∩ s ⊆ A := by
    rintro x ⟨hxcl, hxs⟩
    set e := chartAt ℂ x
    -- A chart ball around `e x` whose `e.symm`-image lies in `s`.
    have hopen : IsOpen (e.symm.source ∩ ↑e.symm ⁻¹' (s ∩ e.source)) :=
      e.symm.isOpen_inter_preimage (hs.inter e.open_source)
    have hmem : e x ∈ e.symm.source ∩ ↑e.symm ⁻¹' (s ∩ e.source) := by
      refine ⟨?_, ?_⟩
      · rw [e.symm_source]; exact mem_chart_target ℂ x
      · rw [Set.mem_preimage, e.left_inv (mem_chart_source ℂ x)]
        exact ⟨hxs, mem_chart_source ℂ x⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (e x) hmem
    -- Both chart readings are real-analytic on the ball.
    have hread : ∀ w : M → ℝ, MHarmonicOn w s →
        AnalyticOnNhd ℝ (w ∘ ↑e.symm) (ball (e x) r) := by
      intro w hw z hz
      obtain ⟨hz_tgt, hz_pre⟩ := hball hz
      rw [e.symm_source] at hz_tgt
      rw [Set.mem_preimage] at hz_pre
      have h1 : MHarmonicAt w (e.symm z) := hw _ hz_pre.1
      have h2 : HarmonicAt (w ∘ ↑e.symm) (e (e.symm z)) :=
        (mharmonicAt_iff_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x) hz_pre.2).mp h1
      rw [e.right_inv hz_tgt] at h2
      exact HarmonicAt.analyticAt h2
    -- A point of `A` inside the chart-ball neighbourhood of `x`.
    have hVopen : IsOpen (e.source ∩ ↑e ⁻¹' ball (e x) r) :=
      e.isOpen_inter_preimage isOpen_ball
    have hxV : x ∈ e.source ∩ ↑e ⁻¹' ball (e x) r :=
      ⟨mem_chart_source ℂ x, Set.mem_preimage.mpr (mem_ball_self hr)⟩
    obtain ⟨y, hyV, hyA⟩ := _root_.mem_closure_iff.mp hxcl _ hVopen hxV
    have hy_ball : e y ∈ ball (e x) r := hyV.2
    -- Transfer the eventual agreement at `y` into the chart.
    have hy_ev : (u ∘ ↑e.symm) =ᶠ[𝓝 (e y)] (v ∘ ↑e.symm) :=
      (e.tendsto_symm hyV.1).eventually hyA.2
    -- The identity theorem for real-analytic functions on the ball.
    have h_eqOn : Set.EqOn (u ∘ ↑e.symm) (v ∘ ↑e.symm) (ball (e x) r) :=
      (hread u hu).eqOn_of_preconnected_of_eventuallyEq (hread v hv)
        (convex_ball (e x) r).isPreconnected hy_ball hy_ev
    -- Hence `u = v` near `x`.
    refine ⟨hxs, ?_⟩
    filter_upwards [hVopen.mem_nhds hxV] with p hp
    have hp2 : e p ∈ ball (e x) r := hp.2
    have hp' : (u ∘ ↑e.symm) (e p) = (v ∘ ↑e.symm) (e p) := h_eqOn hp2
    simpa only [Function.comp_apply, e.left_inv hp.1] using hp'
  -- Preconnectedness spreads `A` over all of `s`.
  have hsA : s ⊆ A :=
    hsc.subset_of_closure_inter_subset hA_open ⟨x₀, hts hx₀, hx₀A⟩ hA_closed
  intro x hxs
  exact ((hsA hxs).2).self_of_nhds

end RiemannDynamics
