/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li

Adapted 23 September 2026 for noncompact second-countable surfaces in the
Lasse Rempe formalisation project: replace the finite chart subcover by a
countable subcover; generalise the path-cover countability theorem.
Original proofs and Apache 2.0 attribution retained.
-/
import RiemannDynamics.Uniformization.Perron.PathCover

/-!
# Second countability of the path cover

On any second-countable Hausdorff surface charted on `ℂ`, the path
classes between two points form a countable type (`countable_pathClasses`): the sheets of
the path cover over a countable cover of the surface by chart-convex opens form a family in
which each sheet meets at most countably many others, the sheets chain-reachable from the
basepoint sheet form a countable clopen family, and the tautological lift places every point
of the cover in that family, so the path classes inject into it. Consequently the path cover
of the surface has countable fibres over a countable base of good opens, the sheets
over that base form a countable topological basis, and the cover is second countable
(`secondCountableTopology_pathCover`).
-/

open scoped Manifold ContDiff

namespace RiemannDynamics

/-- **Countability of path classes** on a second-countable Hausdorff surface charted on `ℂ`: every path
normalizes rel endpoints to a chain path determined by countable data over a countable cover
by open sets with convex chart images. -/
theorem countable_pathClasses (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] [T2Space M]
    [SecondCountableTopology M] (x y : M) :
    Countable (Path.Homotopic.Quotient x y) := by
  classical
  have hdisc : ∀ (ycen : M) (W : Set M), IsOpen W → ycen ∈ W →
      ∃ V : Set M, V ⊆ W ∧ IsOpen V ∧ ycen ∈ V ∧
        (∀ z, z ∈ V → ∀ w, w ∈ V → ∃ η : Path z w, ∀ t, η t ∈ V) ∧
        (∀ (a b : M) (η₁ η₂ : Path a b), (∀ t, η₁ t ∈ V) → (∀ t, η₂ t ∈ V) →
          Path.Homotopic.Quotient.mk η₁ = Path.Homotopic.Quotient.mk η₂) := by
    intro ycen W hW hyW
    set φ := chartAt ℂ ycen
    have hy : ycen ∈ φ.source := mem_chart_source ℂ ycen
    have hOopen : IsOpen (φ.target ∩ φ.symm ⁻¹' (W ∩ φ.source)) :=
      φ.continuousOn_symm.isOpen_inter_preimage φ.open_target (hW.inter φ.open_source)
    have hyO : φ ycen ∈ φ.target ∩ φ.symm ⁻¹' (W ∩ φ.source) := by
      refine ⟨φ.map_source hy, ?_⟩
      rw [Set.mem_preimage, φ.left_inv hy]
      exact ⟨hyW, hy⟩
    obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hOopen (φ ycen) hyO
    have hmemV : ∀ c ∈ Metric.ball (φ ycen) r,
        φ.symm c ∈ φ.source ∩ φ ⁻¹' Metric.ball (φ ycen) r := by
      intro c hc
      refine ⟨φ.map_target (hball hc).1, ?_⟩
      rw [Set.mem_preimage, φ.right_inv (hball hc).1]
      exact hc
    refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ ycen) r, ?_, ?_, ⟨hy, ?_⟩, ?_, ?_⟩
    · intro z hz
      have h3 : φ.symm (φ z) ∈ W ∩ φ.source := (hball hz.2).2
      rw [φ.left_inv hz.1] at h3
      exact h3.1
    · exact φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
    · exact Metric.mem_ball_self hr0
    · intro z hz w hw
      have hcm : ∀ t : unitInterval,
          (1 - (t : ℝ)) • φ z + (t : ℝ) • φ w ∈ Metric.ball (φ ycen) r := by
        intro t
        have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by
          have := t.2.2
          linarith
        exact (convex_ball (φ ycen) r) hz.2 hw.2 h1 t.2.1 (by ring)
      have hcombo : Continuous fun t : unitInterval => (1 - (t : ℝ)) • φ z + (t : ℝ) • φ w := by
        have hcoe : Continuous fun t : unitInterval => (t : ℝ) := continuous_subtype_val
        have h2 : Continuous fun t : unitInterval =>
            ((1 - (t : ℝ) : ℝ) : ℂ) * φ z + ((t : ℝ) : ℂ) * φ w :=
          ((Complex.continuous_ofReal.comp (continuous_const.sub hcoe)).mul
            continuous_const).add ((Complex.continuous_ofReal.comp hcoe).mul continuous_const)
        refine h2.congr fun t => ?_
        rw [Complex.real_smul, Complex.real_smul]
      refine ⟨⟨⟨fun t => φ.symm ((1 - (t : ℝ)) • φ z + (t : ℝ) • φ w), ?_⟩, ?_, ?_⟩, ?_⟩
      · exact φ.continuousOn_symm.comp_continuous hcombo fun t => (hball (hcm t)).1
      · change φ.symm ((1 - ((0 : unitInterval) : ℝ)) • φ z + ((0 : unitInterval) : ℝ) • φ w) = z
        norm_num
        exact φ.left_inv hz.1
      · change φ.symm ((1 - ((1 : unitInterval) : ℝ)) • φ z + ((1 : unitInterval) : ℝ) • φ w) = w
        norm_num
        exact φ.left_inv hw.1
      · intro t
        exact hmemV _ (hcm t)
    · intro a b η₁ η₂ hη₁ hη₂
      have hcm : ∀ st : unitInterval × unitInterval,
          (1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2) ∈
            Metric.ball (φ ycen) r := by
        intro st
        have h1 : (0 : ℝ) ≤ 1 - (st.1 : ℝ) := by
          have := st.1.2.2
          linarith
        exact (convex_ball (φ ycen) r) (hη₁ st.2).2 (hη₂ st.2).2 h1 st.1.2.1 (by ring)
      have hc1 : Continuous fun st : unitInterval × unitInterval => φ (η₁ st.2) :=
        φ.continuousOn.comp_continuous (η₁.continuous.comp continuous_snd)
          fun st => (hη₁ st.2).1
      have hc2 : Continuous fun st : unitInterval × unitInterval => φ (η₂ st.2) :=
        φ.continuousOn.comp_continuous (η₂.continuous.comp continuous_snd)
          fun st => (hη₂ st.2).1
      have hcombo : Continuous fun st : unitInterval × unitInterval =>
          (1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2) := by
        have hcoe : Continuous fun st : unitInterval × unitInterval => (st.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have h2 : Continuous fun st : unitInterval × unitInterval =>
            ((1 - (st.1 : ℝ) : ℝ) : ℂ) * φ (η₁ st.2) + ((st.1 : ℝ) : ℂ) * φ (η₂ st.2) :=
          ((Complex.continuous_ofReal.comp (continuous_const.sub hcoe)).mul hc1).add
            ((Complex.continuous_ofReal.comp hcoe).mul hc2)
        refine h2.congr fun st => ?_
        rw [Complex.real_smul, Complex.real_smul]
      refine Quotient.sound ⟨⟨⟨⟨fun st =>
        φ.symm ((1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2)), ?_⟩, ?_, ?_⟩, ?_⟩⟩
      · exact φ.continuousOn_symm.comp_continuous hcombo fun st => (hball (hcm st)).1
      · intro t
        change φ.symm ((1 - ((0 : unitInterval) : ℝ)) • φ (η₁ t) +
          ((0 : unitInterval) : ℝ) • φ (η₂ t)) = η₁ t
        norm_num
        exact φ.left_inv (hη₁ t).1
      · intro t
        change φ.symm ((1 - ((1 : unitInterval) : ℝ)) • φ (η₁ t) +
          ((1 : unitInterval) : ℝ) • φ (η₂ t)) = η₂ t
        norm_num
        exact φ.left_inv (hη₂ t).1
      · intro s t ht
        have hcoinc : η₁ t = η₂ t := by
          rcases ht with h0 | h1
          · rw [h0, η₁.source, η₂.source]
          · rw [Set.mem_singleton_iff] at h1
            rw [h1, η₁.target, η₂.target]
        have hmemsrc : η₁ t ∈ φ.source := (hη₁ t).1
        change φ.symm ((1 - (s : ℝ)) • φ (η₁ t) + (s : ℝ) • φ (η₂ t)) = η₁ t
        rw [← hcoinc]
        have hone : (1 - (s : ℝ)) • φ (η₁ t) + (s : ℝ) • φ (η₁ t) = φ (η₁ t) := by
          module
        rw [hone]
        exact φ.left_inv hmemsrc
  -- Concatenations of paths inside a set stay inside the set.
  have htmem : ∀ (S : Set M) {a b c : M} (p : Path a b)
      (q : Path b c),
      (∀ t, p t ∈ S) → (∀ t, q t ∈ S) → ∀ t, (p.trans q) t ∈ S := by
    intro S a b c p q hp hq t
    have h := Set.mem_range_self (f := ⇑(p.trans q)) t
    rw [Path.trans_range] at h
    rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact hs ▸ hp s
    · exact hs ▸ hq s
  -- Concatenation of homotopy classes of paths.
  have hq1 : ∀ {a b c : M} (p : Path a b) (q : Path b c),
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q) =
        Path.Homotopic.Quotient.mk (p.trans q) := by
    intros
    rfl
  -- Reversals of paths inside a set stay inside the set.
  have hsymmem : ∀ (S : Set M) {a b : M} (p : Path a b),
      (∀ t, p t ∈ S) → ∀ t, p.symm t ∈ S := by
    intro S a b p hp t
    rw [Path.symm_apply]
    exact hp _
  -- Cancellation of a path class against its reverse.
  have hcancel : ∀ {a b : M} (cls : Path.Homotopic.Quotient x a) (η : Path a b),
      (cls.trans (Path.Homotopic.Quotient.mk η)).trans (Path.Homotopic.Quotient.mk η.symm) =
        cls := by
    intro a b cls η
    rw [Path.Homotopic.Quotient.trans_assoc, hq1 η η.symm]
    have h2 : Path.Homotopic.Quotient.mk (η.trans η.symm) =
        Path.Homotopic.Quotient.refl a :=
      Quotient.sound (Path.Homotopic.trans_symm η)
    rw [h2, Path.Homotopic.Quotient.trans_refl]
  -- Sheets over open sets containing the endpoint are open.
  have hopen : ∀ (pc : PathCover x) (U : Set M), IsOpen U → pc.pt ∈ U →
      IsOpen (pathCoverSheet x pc U) := fun pc U hU hpU =>
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨pc, U, hU, hpU, rfl⟩
  -- Every point lies on its own sheet.
  have hself : ∀ (pc : PathCover x) (U : Set M), pc.pt ∈ U →
      pc ∈ pathCoverSheet x pc U := fun pc U hpU =>
    ⟨Path.refl pc.pt, fun _ => hpU, (Path.Homotopic.Quotient.trans_refl pc.cls).symm⟩
  -- Members of a sheet have endpoint inside the base open.
  have hpt : ∀ (pc qc : PathCover x) (U : Set M),
      qc ∈ pathCoverSheet x pc U → qc.pt ∈ U := by
    intro pc qc U h
    obtain ⟨η, hη, -⟩ := h
    exact η.target ▸ hη 1
  -- Sheets are monotone in the base open.
  have hmono : ∀ (pc : PathCover x) {U U' : Set M}, U ⊆ U' →
      pathCoverSheet x pc U ⊆ pathCoverSheet x pc U' := by
    intro pc U U' hUU' qc hqc
    obtain ⟨η, hη, hcls⟩ := hqc
    exact ⟨η, fun t => hUU' (hη t), hcls⟩
  -- The sheet through a member of a sheet is inside that sheet.
  have htrans : ∀ (pc qc : PathCover x) (U : Set M), qc ∈ pathCoverSheet x pc U →
      pathCoverSheet x qc U ⊆ pathCoverSheet x pc U := by
    intro pc qc U hqc rc hrc
    obtain ⟨η₀, hη₀, hcls₀⟩ := hqc
    obtain ⟨η₁, hη₁, hcls₁⟩ := hrc
    refine ⟨η₀.trans η₁, htmem U η₀ η₁ hη₀ hη₁, ?_⟩
    rw [hcls₁, hcls₀, Path.Homotopic.Quotient.trans_assoc, hq1 η₀ η₁]
  -- Sheet membership is symmetric.
  have hsymm : ∀ (pc qc : PathCover x) (U : Set M), qc ∈ pathCoverSheet x pc U →
      pc ∈ pathCoverSheet x qc U := by
    intro pc qc U hqc
    obtain ⟨η, hη, hcls⟩ := hqc
    refine ⟨η.symm, hsymmem U η hη, ?_⟩
    rw [hcls, hcancel pc.cls η]
  -- Two sheets over a common open sharing a point coincide.
  have hsheeteq : ∀ (pc rc : PathCover x) (U : Set M), rc ∈ pathCoverSheet x pc U →
      pathCoverSheet x rc U = pathCoverSheet x pc U := fun pc rc U hrc =>
    Set.Subset.antisymm (htrans pc rc U hrc) (htrans rc pc U (hsymm pc rc U hrc))
  -- Sheets over chart-linearly connected opens surject onto the open.
  have hsurj : ∀ (pc : PathCover x) (V : Set M),
      (∀ a, a ∈ V → ∀ b, b ∈ V → ∃ η : Path a b, ∀ t, η t ∈ V) → pc.pt ∈ V →
      ∀ z ∈ V, ∃ rc, rc ∈ pathCoverSheet x pc V ∧ rc.pt = z := by
    intro pc V hlinV hpV z hzV
    obtain ⟨η, hη⟩ := hlinV pc.pt hpV z hzV
    exact ⟨⟨z, pc.cls.trans (Path.Homotopic.Quotient.mk η)⟩, ⟨η, hη, rfl⟩, rfl⟩
  -- A sheet over a homotopy-rigid open meets each fiber at most once.
  have hfiber1 : ∀ (pc : PathCover x) (V : Set M),
      (∀ (a b : M) (η₁ η₂ : Path a b), (∀ t, η₁ t ∈ V) → (∀ t, η₂ t ∈ V) →
        Path.Homotopic.Quotient.mk η₁ = Path.Homotopic.Quotient.mk η₂) →
      ∀ qc rc : PathCover x, qc ∈ pathCoverSheet x pc V → rc ∈ pathCoverSheet x pc V →
        qc.pt = rc.pt → qc = rc := by
    intro pc V hhomoV qc rc hqc hrc hpteq
    obtain ⟨qpt, qcls⟩ := qc
    obtain ⟨rpt, rcls⟩ := rc
    obtain rfl : qpt = rpt := hpteq
    obtain ⟨η₁, hη₁, hcls₁⟩ := hqc
    obtain ⟨η₂, hη₂, hcls₂⟩ := hrc
    have hcls₁' : qcls = pc.cls.trans (Path.Homotopic.Quotient.mk η₁) := hcls₁
    have hcls₂' : rcls = pc.cls.trans (Path.Homotopic.Quotient.mk η₂) := hcls₂
    have hcc : qcls = rcls := by
      rw [hcls₁', hcls₂', hhomoV pc.pt qpt η₁ η₂ hη₁ hη₂]
    exact congrArg (PathCover.mk qpt) hcc
  have hkey : ∀ {a b c d : M} (γ' : Path c d) (p q : Path a b) (f g : unitInterval → ℝ),
      Continuous f → Continuous g → f 0 = g 0 → f 1 = g 1 →
      (∀ u, p u = γ'.extend (f u)) → (∀ u, q u = γ'.extend (g u)) →
      Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := by
    intro a b c d γ' p q f g hf hg h0 h1 hp hq
    refine Quotient.sound ⟨⟨⟨⟨fun st =>
      γ'.extend ((1 - (st.1 : ℝ)) * f st.2 + (st.1 : ℝ) * g st.2), ?_⟩, ?_, ?_⟩, ?_⟩⟩
    · exact γ'.continuous_extend.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (hf.comp continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).mul (hg.comp continuous_snd)))
    · intro u
      change γ'.extend ((1 - ((0 : unitInterval) : ℝ)) * f u + ((0 : unitInterval) : ℝ) * g u) = p u
      rw [hp u, show ((1 - ((0 : unitInterval) : ℝ)) * f u +
        ((0 : unitInterval) : ℝ) * g u) = f u by norm_num]
    · intro u
      change γ'.extend ((1 - ((1 : unitInterval) : ℝ)) * f u + ((1 : unitInterval) : ℝ) * g u) = q u
      rw [hq u, show ((1 - ((1 : unitInterval) : ℝ)) * f u +
        ((1 : unitInterval) : ℝ) * g u) = g u by norm_num]
    · intro s u hu
      rcases hu with h0' | h1'
      · rw [h0']
        change γ'.extend ((1 - (s : ℝ)) * f 0 + (s : ℝ) * g 0) = p 0
        rw [hp 0, ← h0, show ((1 - (s : ℝ)) * f 0 + (s : ℝ) * f 0) = f 0 by ring]
      · rw [Set.mem_singleton_iff] at h1'
        rw [h1']
        change γ'.extend ((1 - (s : ℝ)) * f 1 + (s : ℝ) * g 1) = p 1
        rw [hp 1, ← h1, show ((1 - (s : ℝ)) * f 1 + (s : ℝ) * f 1) = f 1 by ring]
  -- Equality of cover points across an equality of endpoints, through `Path.cast`.
  have hPC : ∀ {a b : M} (h : a = b) (p : Path x a),
      (⟨a, Path.Homotopic.Quotient.mk p⟩ : PathCover x) =
        ⟨b, Path.Homotopic.Quotient.mk (p.cast rfl h.symm)⟩ := by
    rintro a b rfl p
    rfl
  -- Every point of the cover is joined to the basepoint class by the canonical lift.
  have hjoin : ∀ pc : PathCover x, Joined (pathCoverBase x) pc := by
    rintro ⟨w, cls⟩
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep cls
    -- The initial segments of `γ`, reparametrized to full paths.
    obtain ⟨sp, hspfun⟩ : ∃ sp : ∀ t : unitInterval, Path x (γ t),
        ∀ t u, (sp t) u = γ.extend ((u : ℝ) * (t : ℝ)) := by
      refine ⟨fun t => ⟨⟨fun u => γ.extend ((u : ℝ) * (t : ℝ)),
        γ.continuous_extend.comp (continuous_subtype_val.mul continuous_const)⟩, ?_, ?_⟩,
        fun t u => rfl⟩
      · change γ.extend (((0 : unitInterval) : ℝ) * (t : ℝ)) = x
        norm_num
      · change γ.extend (((1 : unitInterval) : ℝ) * (t : ℝ)) = γ t
        rw [show (((1 : unitInterval) : ℝ) * (t : ℝ)) = (t : ℝ) by norm_num]
        exact γ.extend_extends' t
    -- Continuity of the canonical lift into the sheet topology.
    have hLcont : Continuous fun t : unitInterval =>
        (⟨γ t, Path.Homotopic.Quotient.mk (sp t)⟩ : PathCover x) := by
      refine continuous_generateFrom_iff.mpr ?_
      rintro s ⟨pc, U, hUopen, -, rfl⟩
      rw [isOpen_iff_forall_mem_open]
      intro t₀ ht₀
      obtain ⟨η₀, hη₀, hcls₀⟩ := ht₀
      have hcls₀' : Path.Homotopic.Quotient.mk (sp t₀) =
          pc.cls.trans (Path.Homotopic.Quotient.mk η₀) := hcls₀
      have hγt₀U : γ t₀ ∈ U := by
        have h := hη₀ 1
        rw [η₀.target] at h
        exact h
      have hJopen : IsOpen {u : unitInterval | γ u ∈ U} := hUopen.preimage γ.continuous
      obtain ⟨δ, hδ0, hδball⟩ := Metric.isOpen_iff.mp hJopen t₀ hγt₀U
      refine ⟨Metric.ball t₀ δ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hδ0⟩
      intro t ht
      -- The parameter segment from `t₀` to `t` stays in the unit interval and in the ball.
      have hseg : ∀ u : unitInterval,
          ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
        intro u
        constructor
        · nlinarith [t₀.2.1, t.2.1, u.2.1, u.2.2]
        · nlinarith [t₀.2.2, t.2.2, u.2.1, u.2.2]
      have hsegBall : ∀ u : unitInterval,
          (⟨(1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ), hseg u⟩ : unitInterval) ∈
            Metric.ball t₀ δ := by
        intro u
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
        have htd : |(t : ℝ) - (t₀ : ℝ)| < δ := by
          have h := ht
          rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at h
          exact h
        have hd : |((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ) : ℝ) - (t₀ : ℝ)| =
            (u : ℝ) * |(t : ℝ) - (t₀ : ℝ)| := by
          rw [show ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ) - (t₀ : ℝ) : ℝ) =
            (u : ℝ) * ((t : ℝ) - (t₀ : ℝ)) by ring, abs_mul, abs_of_nonneg u.2.1]
        change |((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ) : ℝ) - (t₀ : ℝ)| < δ
        rw [hd]
        have habs : (0 : ℝ) ≤ |(t : ℝ) - (t₀ : ℝ)| := abs_nonneg _
        nlinarith [u.2.1, u.2.2]
      have hsegU : ∀ u : unitInterval,
          γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) ∈ U := by
        intro u
        have hmem := hδball (hsegBall u)
        have hx : γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) =
            γ (⟨(1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ), hseg u⟩ : unitInterval) :=
          γ.extend_extends'
            (⟨(1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ), hseg u⟩ : unitInterval)
        rw [hx]
        exact hmem
      -- The chart-free connector along `γ` from `γ t₀` to `γ t`.
      obtain ⟨c, hcfun⟩ : ∃ c : Path (γ t₀) (γ t),
          ∀ u, c u = γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)) := by
        refine ⟨⟨⟨fun u => γ.extend ((1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * (t : ℝ)),
          γ.continuous_extend.comp
            (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
              (continuous_subtype_val.mul continuous_const))⟩, ?_, ?_⟩, fun u => rfl⟩
        · change γ.extend
              ((1 - ((0 : unitInterval) : ℝ)) * (t₀ : ℝ) +
                ((0 : unitInterval) : ℝ) * (t : ℝ)) = γ t₀
          rw [show ((1 - ((0 : unitInterval) : ℝ)) * (t₀ : ℝ) +
            ((0 : unitInterval) : ℝ) * (t : ℝ)) = (t₀ : ℝ) by norm_num]
          exact γ.extend_extends' t₀
        · change γ.extend
              ((1 - ((1 : unitInterval) : ℝ)) * (t₀ : ℝ) +
                ((1 : unitInterval) : ℝ) * (t : ℝ)) = γ t
          rw [show ((1 - ((1 : unitInterval) : ℝ)) * (t₀ : ℝ) +
            ((1 : unitInterval) : ℝ) * (t : ℝ)) = (t : ℝ) by norm_num]
          exact γ.extend_extends' t
      -- The concatenated witness runs inside `U`.
      have htmem : ∀ u, (η₀.trans c) u ∈ U := by
        intro u
        have h := Set.mem_range_self (f := ⇑(η₀.trans c)) u
        rw [Path.trans_range] at h
        rcases h with ⟨v, hv⟩ | ⟨v, hv⟩
        · exact hv ▸ hη₀ v
        · have hcv : c v ∈ U := by
            rw [hcfun v]
            exact hsegU v
          exact hv ▸ hcv
      -- The class of `sp t` is the class of `sp t₀` continued by the connector.
      have hclseq : Path.Homotopic.Quotient.mk (sp t) =
          Path.Homotopic.Quotient.mk ((sp t₀).trans c) := by
        refine hkey γ (sp t) ((sp t₀).trans c) (fun u => (u : ℝ) * (t : ℝ))
          (fun u => if (u : ℝ) ≤ 1 / 2 then 2 * (u : ℝ) * (t₀ : ℝ)
            else (1 - (2 * (u : ℝ) - 1)) * (t₀ : ℝ) + (2 * (u : ℝ) - 1) * (t : ℝ))
          (continuous_subtype_val.mul continuous_const) ?_ ?_ ?_ (fun u => hspfun t u) ?_
        · refine Continuous.if_le ?_ ?_ continuous_subtype_val continuous_const ?_
          · exact (continuous_const.mul continuous_subtype_val).mul continuous_const
          · exact ((continuous_const.sub ((continuous_const.mul continuous_subtype_val).sub
              continuous_const)).mul continuous_const).add
              (((continuous_const.mul continuous_subtype_val).sub continuous_const).mul
                continuous_const)
          · intro u hu
            rw [hu]
            norm_num
        · norm_num
        · norm_num
        · intro u
          rw [Path.trans_apply]
          split_ifs with h
          · rw [hspfun t₀]
          · rw [hcfun]
      refine ⟨η₀.trans c, htmem, ?_⟩
      have hfin : Path.Homotopic.Quotient.mk (sp t) =
          pc.cls.trans (Path.Homotopic.Quotient.mk (η₀.trans c)) := by
        rw [hclseq, ← hq1 (sp t₀) c, hcls₀', Path.Homotopic.Quotient.trans_assoc, hq1]
      exact hfin
    -- Endpoint identifications of the canonical lift.
    have hL0 : (⟨γ 0, Path.Homotopic.Quotient.mk (sp 0)⟩ : PathCover x) = pathCoverBase x := by
      rw [hPC γ.source (sp 0)]
      have hpath : (sp 0).cast rfl γ.source.symm = Path.refl x := by
        ext u
        change (sp 0) u = x
        rw [hspfun 0 u]
        norm_num
      rw [hpath]
      rfl
    have hL1 : (⟨γ 1, Path.Homotopic.Quotient.mk (sp 1)⟩ : PathCover x) =
        ⟨w, Path.Homotopic.Quotient.mk γ⟩ := by
      rw [hPC γ.target (sp 1)]
      have hpath : (sp 1).cast rfl γ.target.symm = γ := by
        ext u
        change (sp 1) u = γ u
        rw [hspfun 1 u, show ((u : ℝ) * ((1 : unitInterval) : ℝ)) = (u : ℝ) by norm_num]
        exact γ.extend_extends' u
      rw [hpath]
    exact ⟨⟨⟨fun t => (⟨γ t, Path.Homotopic.Quotient.mk (sp t)⟩ : PathCover x), hLcont⟩, hL0, hL1⟩⟩
  -- A countable cover of the base by good opens.
  have hgoodAt : ∀ z : M, ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      (∀ a, a ∈ V → ∀ b, b ∈ V → ∃ η : Path a b, ∀ t, η t ∈ V) ∧
      (∀ (a b : M) (η₁ η₂ : Path a b), (∀ t, η₁ t ∈ V) → (∀ t, η₂ t ∈ V) →
        Path.Homotopic.Quotient.mk η₁ = Path.Homotopic.Quotient.mk η₂) := by
    intro z
    obtain ⟨V, -, hVo, hzV, hlin, hhomo⟩ := hdisc z Set.univ isOpen_univ (Set.mem_univ z)
    exact ⟨V, hVo, hzV, hlin, hhomo⟩
  choose Vf hVfo hVfmem hVflin hVfhomo using hgoodAt
  obtain ⟨tf, htfc, htfeq⟩ := TopologicalSpace.isOpen_iUnion_countable Vf hVfo
  have htf : Set.univ ⊆ ⋃ z ∈ tf, Vf z := by
    intro z _
    rw [htfeq]
    exact Set.mem_iUnion.mpr ⟨z, hVfmem z⟩
  obtain ⟨D, hDcnt, hDdense⟩ := TopologicalSpace.exists_countable_dense M
  -- The family of sheets over the countable good cover.
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮 : Set (Set (PathCover x)), ∀ S, S ∈ 𝒮 ↔
      ∃ pc : PathCover x, ∃ z ∈ tf, pc.pt ∈ Vf z ∧ S = pathCoverSheet x pc (Vf z) :=
    ⟨{S | ∃ pc : PathCover x, ∃ z ∈ tf, pc.pt ∈ Vf z ∧ S = pathCoverSheet x pc (Vf z)},
      fun _ => Iff.rfl⟩
  -- Each sheet of the family meets at most countably many members of the family.
  have hmeets : ∀ S ∈ 𝒮, Set.Countable {T | T ∈ 𝒮 ∧ (T ∩ S).Nonempty} := by
    intro S hS𝒮
    obtain ⟨pc, z, hztf, hpz, rfl⟩ := (h𝒮 S).mp hS𝒮
    have hD'cnt : Set.Countable
        {rc : PathCover x | rc ∈ pathCoverSheet x pc (Vf z) ∧ rc.pt ∈ D} := by
      rw [← Set.countable_coe_iff]
      have : Countable ↥D := hDcnt.to_subtype
      have hinj : Function.Injective fun rc :
          ↥{rc : PathCover x | rc ∈ pathCoverSheet x pc (Vf z) ∧ rc.pt ∈ D} =>
          (⟨rc.1.pt, rc.2.2⟩ : ↥D) := by
        intro rc rc' h
        have hpteq : rc.1.pt = rc'.1.pt := congrArg Subtype.val h
        exact Subtype.ext (hfiber1 pc (Vf z) (hVfhomo z) rc.1 rc'.1 rc.2.1 rc'.2.1 hpteq)
      exact hinj.countable
    have hper : ∀ rc : PathCover x, Set.Countable {T | T ∈ 𝒮 ∧ rc ∈ T} := by
      intro rc
      refine Set.Countable.mono ?_
        (htfc.image fun z' => pathCoverSheet x rc (Vf z'))
      rintro T ⟨hT𝒮, hrcT⟩
      obtain ⟨pc', z', hz'tf, hp'z', rfl⟩ := (h𝒮 T).mp hT𝒮
      exact ⟨z', hz'tf, hsheeteq pc' rc (Vf z') hrcT⟩
    refine Set.Countable.mono ?_ (hD'cnt.biUnion fun rc _ => hper rc)
    rintro T ⟨hT𝒮, qc, hqcT, hqcS⟩
    obtain ⟨pc', z', hz'tf, hp'z', rfl⟩ := (h𝒮 T).mp hT𝒮
    have hqp1 : qc.pt ∈ Vf z' := hpt pc' qc (Vf z') hqcT
    have hqp2 : qc.pt ∈ Vf z := hpt pc qc (Vf z) hqcS
    obtain ⟨V₃, hV₃sub, hV₃o, hqV₃, hlin₃, hhomo₃⟩ :=
      hdisc qc.pt (Vf z' ∩ Vf z) ((hVfo z').inter (hVfo z)) ⟨hqp1, hqp2⟩
    have hsheet₃T : pathCoverSheet x qc V₃ ⊆ pathCoverSheet x pc' (Vf z') :=
      Set.Subset.trans (hmono qc fun w hw => (hV₃sub hw).1) (htrans pc' qc (Vf z') hqcT)
    have hsheet₃S : pathCoverSheet x qc V₃ ⊆ pathCoverSheet x pc (Vf z) :=
      Set.Subset.trans (hmono qc fun w hw => (hV₃sub hw).2) (htrans pc qc (Vf z) hqcS)
    obtain ⟨d, hdV₃, hdD⟩ := hDdense.inter_open_nonempty V₃ hV₃o ⟨qc.pt, hqV₃⟩
    obtain ⟨rc, hrc₃, hrcpt⟩ := hsurj qc V₃ hlin₃ hqV₃ d hdV₃
    exact Set.mem_biUnion ⟨hsheet₃S hrc₃, hrcpt.symm ▸ hdD⟩ ⟨hT𝒮, hsheet₃T hrc₃⟩
  -- The chain-reachable sheets from the basepoint sheet.
  obtain ⟨zb, hzbtf, hxzb⟩ := Set.mem_iUnion₂.mp (htf (Set.mem_univ x))
  obtain ⟨C, hCzero, hCsucc⟩ : ∃ C : ℕ → Set (Set (PathCover x)),
      C 0 = {pathCoverSheet x (pathCoverBase x) (Vf zb)} ∧
      ∀ n, C (n + 1) = C n ∪ {T | T ∈ 𝒮 ∧ ∃ S ∈ C n, (T ∩ S).Nonempty} :=
    ⟨fun n => Nat.rec {pathCoverSheet x (pathCoverBase x) (Vf zb)}
      (fun _ Cn => Cn ∪ {T | T ∈ 𝒮 ∧ ∃ S ∈ Cn, (T ∩ S).Nonempty}) n, rfl, fun _ => rfl⟩
  have hbase𝒮 : pathCoverSheet x (pathCoverBase x) (Vf zb) ∈ 𝒮 :=
    (h𝒮 _).mpr ⟨pathCoverBase x, zb, hzbtf, hxzb, rfl⟩
  have hCsub : ∀ n, C n ⊆ 𝒮 := by
    intro n
    induction n with
    | zero =>
      rw [hCzero]
      intro S hS
      rw [Set.mem_singleton_iff.mp hS]
      exact hbase𝒮
    | succ n ih =>
      rw [hCsucc n]
      exact Set.union_subset ih fun T hT => hT.1
  have hCcnt : ∀ n, Set.Countable (C n) := by
    intro n
    induction n with
    | zero =>
      rw [hCzero]
      exact Set.countable_singleton _
    | succ n ih =>
      rw [hCsucc n]
      refine ih.union (Set.Countable.mono ?_ (ih.biUnion fun S hS => hmeets S (hCsub n hS)))
      rintro T ⟨hT𝒮, S, hSCn, hTS⟩
      exact Set.mem_biUnion hSCn ⟨hT𝒮, hTS⟩
  -- The union of the chained sheets is open, closed, and contains the basepoint class.
  obtain ⟨W, hWmem⟩ : ∃ W : Set (PathCover x), ∀ qc, qc ∈ W ↔ ∃ n, ∃ S ∈ C n, qc ∈ S :=
    ⟨{qc | ∃ n, ∃ S ∈ C n, qc ∈ S}, fun _ => Iff.rfl⟩
  have hWopen : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    intro qc hqc
    obtain ⟨n, S, hSn, hqcS⟩ := (hWmem qc).mp hqc
    obtain ⟨pc, z, hztf, hpz, hSeq⟩ := (h𝒮 S).mp (hCsub n hSn)
    refine ⟨S, fun rc hrc => (hWmem rc).mpr ⟨n, S, hSn, hrc⟩, ?_, hqcS⟩
    rw [hSeq]
    exact hopen pc (Vf z) (hVfo z) hpz
  have hbaseW : pathCoverBase x ∈ W := by
    refine (hWmem _).mpr ⟨0, pathCoverSheet x (pathCoverBase x) (Vf zb), ?_,
      hself (pathCoverBase x) (Vf zb) hxzb⟩
    rw [hCzero]
    exact rfl
  have hWclosed : IsClosed W := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro qc hqc
    rw [Set.mem_compl_iff] at hqc
    obtain ⟨z, hztf, hqz⟩ := Set.mem_iUnion₂.mp (htf (Set.mem_univ qc.pt))
    refine ⟨pathCoverSheet x qc (Vf z), fun rc hrc => ?_,
      hopen qc (Vf z) (hVfo z) hqz, hself qc (Vf z) hqz⟩
    rw [Set.mem_compl_iff]
    intro hrcW
    obtain ⟨n, S, hSn, hrcS⟩ := (hWmem rc).mp hrcW
    refine hqc ((hWmem qc).mpr ⟨n + 1, pathCoverSheet x qc (Vf z), ?_,
      hself qc (Vf z) hqz⟩)
    rw [hCsucc n]
    exact Or.inr ⟨(h𝒮 _).mpr ⟨qc, z, hztf, hqz, rfl⟩, S, hSn, rc, hrc, hrcS⟩
  -- Every fiber point over `y` joins to the basepoint class, hence lies in the union.
  have hfibW : ∀ c : Path.Homotopic.Quotient x y, (⟨y, c⟩ : PathCover x) ∈ W := by
    intro c
    obtain ⟨p⟩ := hjoin ⟨y, c⟩
    have hclop : IsClopen (⇑p ⁻¹' W) :=
      ⟨hWclosed.preimage p.continuous, hWopen.preimage p.continuous⟩
    have hne : (⇑p ⁻¹' W).Nonempty := ⟨0, by
      rw [Set.mem_preimage, p.source]
      exact hbaseW⟩
    have huniv := hclop.eq_univ hne
    have h1 : (1 : unitInterval) ∈ ⇑p ⁻¹' W := by
      rw [huniv]
      exact Set.mem_univ _
    rwa [Set.mem_preimage, p.target] at h1
  -- The path classes inject into the countable family of chained sheets.
  obtain ⟨F, hFmem⟩ : ∃ F : Set (Set (PathCover x)), ∀ S, S ∈ F ↔ ∃ n, S ∈ C n :=
    ⟨{S | ∃ n, S ∈ C n}, fun _ => Iff.rfl⟩
  have hFcnt : Set.Countable F := by
    have hFeq : F = ⋃ n, C n := Set.ext fun S => (hFmem S).trans Set.mem_iUnion.symm
    rw [hFeq]
    exact Set.countable_iUnion hCcnt
  have : Countable ↥F := hFcnt.to_subtype
  have hchoose : ∀ c : Path.Homotopic.Quotient x y,
      ∃ S, S ∈ F ∧ (⟨y, c⟩ : PathCover x) ∈ S := by
    intro c
    obtain ⟨n, S, hSn, hmem⟩ := (hWmem _).mp (hfibW c)
    exact ⟨S, (hFmem S).mpr ⟨n, hSn⟩, hmem⟩
  refine Function.Injective.countable (f := fun c : Path.Homotopic.Quotient x y =>
    (⟨(hchoose c).choose, ((hchoose c).choose_spec).1⟩ : ↥F)) ?_
  intro c c' hcc'
  have h1 := ((hchoose c).choose_spec).2
  have h2 := ((hchoose c').choose_spec).2
  have hSS : (hchoose c).choose = (hchoose c').choose := congrArg Subtype.val hcc'
  rw [hSS] at h1
  obtain ⟨n, hSn⟩ := (hFmem _).mp ((hchoose c').choose_spec).1
  obtain ⟨pc, z, hztf, hpz, hSdef⟩ := (h𝒮 _).mp (hCsub n hSn)
  rw [hSdef] at h1 h2
  have heq := hfiber1 pc (Vf z) (hVfhomo z) ⟨y, c⟩ ⟨y, c'⟩ h1 h2 rfl
  injection heq

/-- **Second countability of the path cover** of the genus surface: the sheets over a
countable base of chart balls through the countably many fiber points form a countable
cover by chart sources. -/
theorem secondCountableTopology_pathCover {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [T2Space M] [SecondCountableTopology M] (x₀ : M) :
    SecondCountableTopology (PathCover x₀) := by
  classical
  have hdisc : ∀ (ycen : M) (W : Set M), IsOpen W → ycen ∈ W →
      ∃ V : Set M, V ⊆ W ∧ IsOpen V ∧ ycen ∈ V ∧
        (∀ z, z ∈ V → ∀ w, w ∈ V → ∃ η : Path z w, ∀ t, η t ∈ V) ∧
        (∀ (a b : M) (η₁ η₂ : Path a b), (∀ t, η₁ t ∈ V) → (∀ t, η₂ t ∈ V) →
          Path.Homotopic.Quotient.mk η₁ = Path.Homotopic.Quotient.mk η₂) := by
    intro ycen W hW hyW
    set φ := chartAt ℂ ycen
    have hy : ycen ∈ φ.source := mem_chart_source ℂ ycen
    have hOopen : IsOpen (φ.target ∩ φ.symm ⁻¹' (W ∩ φ.source)) :=
      φ.continuousOn_symm.isOpen_inter_preimage φ.open_target (hW.inter φ.open_source)
    have hyO : φ ycen ∈ φ.target ∩ φ.symm ⁻¹' (W ∩ φ.source) := by
      refine ⟨φ.map_source hy, ?_⟩
      rw [Set.mem_preimage, φ.left_inv hy]
      exact ⟨hyW, hy⟩
    obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hOopen (φ ycen) hyO
    have hmemV : ∀ c ∈ Metric.ball (φ ycen) r,
        φ.symm c ∈ φ.source ∩ φ ⁻¹' Metric.ball (φ ycen) r := by
      intro c hc
      refine ⟨φ.map_target (hball hc).1, ?_⟩
      rw [Set.mem_preimage, φ.right_inv (hball hc).1]
      exact hc
    refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ ycen) r, ?_, ?_, ⟨hy, ?_⟩, ?_, ?_⟩
    · intro z hz
      have h3 : φ.symm (φ z) ∈ W ∩ φ.source := (hball hz.2).2
      rw [φ.left_inv hz.1] at h3
      exact h3.1
    · exact φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
    · exact Metric.mem_ball_self hr0
    · intro z hz w hw
      have hcm : ∀ t : unitInterval,
          (1 - (t : ℝ)) • φ z + (t : ℝ) • φ w ∈ Metric.ball (φ ycen) r := by
        intro t
        have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by
          have := t.2.2
          linarith
        exact (convex_ball (φ ycen) r) hz.2 hw.2 h1 t.2.1 (by ring)
      have hcombo : Continuous fun t : unitInterval => (1 - (t : ℝ)) • φ z + (t : ℝ) • φ w := by
        have hcoe : Continuous fun t : unitInterval => (t : ℝ) := continuous_subtype_val
        have h2 : Continuous fun t : unitInterval =>
            ((1 - (t : ℝ) : ℝ) : ℂ) * φ z + ((t : ℝ) : ℂ) * φ w :=
          ((Complex.continuous_ofReal.comp (continuous_const.sub hcoe)).mul
            continuous_const).add ((Complex.continuous_ofReal.comp hcoe).mul continuous_const)
        refine h2.congr fun t => ?_
        rw [Complex.real_smul, Complex.real_smul]
      refine ⟨⟨⟨fun t => φ.symm ((1 - (t : ℝ)) • φ z + (t : ℝ) • φ w), ?_⟩, ?_, ?_⟩, ?_⟩
      · exact φ.continuousOn_symm.comp_continuous hcombo fun t => (hball (hcm t)).1
      · change φ.symm ((1 - ((0 : unitInterval) : ℝ)) • φ z + ((0 : unitInterval) : ℝ) • φ w) = z
        norm_num
        exact φ.left_inv hz.1
      · change φ.symm ((1 - ((1 : unitInterval) : ℝ)) • φ z + ((1 : unitInterval) : ℝ) • φ w) = w
        norm_num
        exact φ.left_inv hw.1
      · intro t
        exact hmemV _ (hcm t)
    · intro a b η₁ η₂ hη₁ hη₂
      have hcm : ∀ st : unitInterval × unitInterval,
          (1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2) ∈
            Metric.ball (φ ycen) r := by
        intro st
        have h1 : (0 : ℝ) ≤ 1 - (st.1 : ℝ) := by
          have := st.1.2.2
          linarith
        exact (convex_ball (φ ycen) r) (hη₁ st.2).2 (hη₂ st.2).2 h1 st.1.2.1 (by ring)
      have hc1 : Continuous fun st : unitInterval × unitInterval => φ (η₁ st.2) :=
        φ.continuousOn.comp_continuous (η₁.continuous.comp continuous_snd)
          fun st => (hη₁ st.2).1
      have hc2 : Continuous fun st : unitInterval × unitInterval => φ (η₂ st.2) :=
        φ.continuousOn.comp_continuous (η₂.continuous.comp continuous_snd)
          fun st => (hη₂ st.2).1
      have hcombo : Continuous fun st : unitInterval × unitInterval =>
          (1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2) := by
        have hcoe : Continuous fun st : unitInterval × unitInterval => (st.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have h2 : Continuous fun st : unitInterval × unitInterval =>
            ((1 - (st.1 : ℝ) : ℝ) : ℂ) * φ (η₁ st.2) + ((st.1 : ℝ) : ℂ) * φ (η₂ st.2) :=
          ((Complex.continuous_ofReal.comp (continuous_const.sub hcoe)).mul hc1).add
            ((Complex.continuous_ofReal.comp hcoe).mul hc2)
        refine h2.congr fun st => ?_
        rw [Complex.real_smul, Complex.real_smul]
      refine Quotient.sound ⟨⟨⟨⟨fun st =>
        φ.symm ((1 - (st.1 : ℝ)) • φ (η₁ st.2) + (st.1 : ℝ) • φ (η₂ st.2)), ?_⟩, ?_, ?_⟩, ?_⟩⟩
      · exact φ.continuousOn_symm.comp_continuous hcombo fun st => (hball (hcm st)).1
      · intro t
        change φ.symm ((1 - ((0 : unitInterval) : ℝ)) • φ (η₁ t) +
          ((0 : unitInterval) : ℝ) • φ (η₂ t)) = η₁ t
        norm_num
        exact φ.left_inv (hη₁ t).1
      · intro t
        change φ.symm ((1 - ((1 : unitInterval) : ℝ)) • φ (η₁ t) +
          ((1 : unitInterval) : ℝ) • φ (η₂ t)) = η₂ t
        norm_num
        exact φ.left_inv (hη₂ t).1
      · intro s t ht
        have hcoinc : η₁ t = η₂ t := by
          rcases ht with h0 | h1
          · rw [h0, η₁.source, η₂.source]
          · rw [Set.mem_singleton_iff] at h1
            rw [h1, η₁.target, η₂.target]
        have hmemsrc : η₁ t ∈ φ.source := (hη₁ t).1
        change φ.symm ((1 - (s : ℝ)) • φ (η₁ t) + (s : ℝ) • φ (η₂ t)) = η₁ t
        rw [← hcoinc]
        have hone : (1 - (s : ℝ)) • φ (η₁ t) + (s : ℝ) • φ (η₁ t) = φ (η₁ t) := by
          module
        rw [hone]
        exact φ.left_inv hmemsrc
  -- Concatenations of paths inside a set stay inside the set.
  have htmem : ∀ (S : Set M) {a b c : M} (p : Path a b)
      (q : Path b c),
      (∀ t, p t ∈ S) → (∀ t, q t ∈ S) → ∀ t, (p.trans q) t ∈ S := by
    intro S a b c p q hp hq t
    have h := Set.mem_range_self (f := ⇑(p.trans q)) t
    rw [Path.trans_range] at h
    rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact hs ▸ hp s
    · exact hs ▸ hq s
  -- Concatenation of homotopy classes of paths.
  have hq1 : ∀ {a b c : M} (p : Path a b) (q : Path b c),
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q) =
        Path.Homotopic.Quotient.mk (p.trans q) := by
    intros
    rfl
  -- Reversals of paths inside a set stay inside the set.
  have hsymmem : ∀ (S : Set M) {a b : M} (p : Path a b),
      (∀ t, p t ∈ S) → ∀ t, p.symm t ∈ S := by
    intro S a b p hp t
    rw [Path.symm_apply]
    exact hp _
  -- Cancellation of a path class against its reverse.
  have hcancel : ∀ {a b : M} (cls : Path.Homotopic.Quotient x₀ a) (η : Path a b),
      (cls.trans (Path.Homotopic.Quotient.mk η)).trans (Path.Homotopic.Quotient.mk η.symm) =
        cls := by
    intro a b cls η
    rw [Path.Homotopic.Quotient.trans_assoc, hq1 η η.symm]
    have h2 : Path.Homotopic.Quotient.mk (η.trans η.symm) =
        Path.Homotopic.Quotient.refl a :=
      Quotient.sound (Path.Homotopic.trans_symm η)
    rw [h2, Path.Homotopic.Quotient.trans_refl]
  -- Sheets over open sets containing the endpoint are open.
  have hopen : ∀ (pc : PathCover x₀) (U : Set M), IsOpen U → pc.pt ∈ U →
      IsOpen (pathCoverSheet x₀ pc U) := fun pc U hU hpU =>
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨pc, U, hU, hpU, rfl⟩
  -- Every point lies on its own sheet.
  have hself : ∀ (pc : PathCover x₀) (U : Set M), pc.pt ∈ U →
      pc ∈ pathCoverSheet x₀ pc U := fun pc U hpU =>
    ⟨Path.refl pc.pt, fun _ => hpU, (Path.Homotopic.Quotient.trans_refl pc.cls).symm⟩
  -- Members of a sheet have endpoint inside the base open.
  have hpt : ∀ (pc qc : PathCover x₀) (U : Set M),
      qc ∈ pathCoverSheet x₀ pc U → qc.pt ∈ U := by
    intro pc qc U h
    obtain ⟨η, hη, -⟩ := h
    exact η.target ▸ hη 1
  -- Sheets are monotone in the base open.
  have hmono : ∀ (pc : PathCover x₀) {U U' : Set M}, U ⊆ U' →
      pathCoverSheet x₀ pc U ⊆ pathCoverSheet x₀ pc U' := by
    intro pc U U' hUU' qc hqc
    obtain ⟨η, hη, hcls⟩ := hqc
    exact ⟨η, fun t => hUU' (hη t), hcls⟩
  -- The sheet through a member of a sheet is inside that sheet.
  have htrans : ∀ (pc qc : PathCover x₀) (U : Set M), qc ∈ pathCoverSheet x₀ pc U →
      pathCoverSheet x₀ qc U ⊆ pathCoverSheet x₀ pc U := by
    intro pc qc U hqc rc hrc
    obtain ⟨η₀, hη₀, hcls₀⟩ := hqc
    obtain ⟨η₁, hη₁, hcls₁⟩ := hrc
    refine ⟨η₀.trans η₁, htmem U η₀ η₁ hη₀ hη₁, ?_⟩
    rw [hcls₁, hcls₀, Path.Homotopic.Quotient.trans_assoc, hq1 η₀ η₁]
  -- Sheet membership is symmetric.
  have hsymm : ∀ (pc qc : PathCover x₀) (U : Set M), qc ∈ pathCoverSheet x₀ pc U →
      pc ∈ pathCoverSheet x₀ qc U := by
    intro pc qc U hqc
    obtain ⟨η, hη, hcls⟩ := hqc
    refine ⟨η.symm, hsymmem U η hη, ?_⟩
    rw [hcls, hcancel pc.cls η]
  -- Two sheets over a common open sharing a point coincide.
  have hsheeteq : ∀ (pc rc : PathCover x₀) (U : Set M), rc ∈ pathCoverSheet x₀ pc U →
      pathCoverSheet x₀ rc U = pathCoverSheet x₀ pc U := fun pc rc U hrc =>
    Set.Subset.antisymm (htrans pc rc U hrc) (htrans rc pc U (hsymm pc rc U hrc))
  -- Sheets over chart-linearly connected opens surject onto the open.
  have hsurj : ∀ (pc : PathCover x₀) (V : Set M),
      (∀ a, a ∈ V → ∀ b, b ∈ V → ∃ η : Path a b, ∀ t, η t ∈ V) → pc.pt ∈ V →
      ∀ z ∈ V, ∃ rc, rc ∈ pathCoverSheet x₀ pc V ∧ rc.pt = z := by
    intro pc V hlinV hpV z hzV
    obtain ⟨η, hη⟩ := hlinV pc.pt hpV z hzV
    exact ⟨⟨z, pc.cls.trans (Path.Homotopic.Quotient.mk η)⟩, ⟨η, hη, rfl⟩, rfl⟩
  -- A countable basis of good opens.
  obtain ⟨𝒱, h𝒱cnt, h𝒱good, h𝒱basis⟩ : ∃ 𝒱 : Set (Set M), 𝒱.Countable ∧
      (∀ V ∈ 𝒱, IsOpen V ∧ V.Nonempty ∧
        ∀ a, a ∈ V → ∀ b, b ∈ V → ∃ η : Path a b, ∀ t, η t ∈ V) ∧
      ∀ (z : M) (u : Set M), IsOpen u → z ∈ u →
        ∃ V ∈ 𝒱, z ∈ V ∧ V ⊆ u := by
    have hb : ∀ b ∈ TopologicalSpace.countableBasis M,
        ∃ 𝒲 : Set (Set M), 𝒲.Countable ∧
          (∀ V ∈ 𝒲, (IsOpen V ∧ V.Nonempty ∧
            ∀ a, a ∈ V → ∀ b', b' ∈ V → ∃ η : Path a b', ∀ t, η t ∈ V) ∧ V ⊆ b) ∧
          ∀ z ∈ b, ∃ V ∈ 𝒲, z ∈ V := by
      intro b hbB
      have hbo : IsOpen b := TopologicalSpace.isOpen_of_mem_countableBasis hbB
      have hgood : ∀ z : ↥b, ∃ V : Set M,
          ((IsOpen V ∧ V.Nonempty ∧
            ∀ a, a ∈ V → ∀ b', b' ∈ V → ∃ η : Path a b', ∀ t, η t ∈ V) ∧ V ⊆ b) ∧
          z.1 ∈ V := by
        intro z
        obtain ⟨V, hVsub, hVo, hzV, hlin, -⟩ := hdisc z.1 b hbo z.2
        exact ⟨V, ⟨⟨hVo, ⟨z.1, hzV⟩, hlin⟩, hVsub⟩, hzV⟩
      choose Vb hVbgood hVbmem using hgood
      obtain ⟨T, hTcnt, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable Vb
        fun z => (hVbgood z).1.1
      refine ⟨Vb '' T, hTcnt.image Vb, ?_, ?_⟩
      · rintro V ⟨z, hzT, rfl⟩
        exact hVbgood z
      · intro z hz
        have hzmem : z ∈ ⋃ ww, Vb ww := Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hVbmem ⟨z, hz⟩⟩
        rw [← hTeq] at hzmem
        obtain ⟨ww, hwT, hzw⟩ := Set.mem_iUnion₂.mp hzmem
        exact ⟨Vb ww, ⟨ww, hwT, rfl⟩, hzw⟩
    choose 𝒲 h𝒲cnt h𝒲prop h𝒲cov using hb
    refine ⟨⋃ b, ⋃ hbB : b ∈ TopologicalSpace.countableBasis M, 𝒲 b hbB,
      Set.Countable.biUnion (TopologicalSpace.countable_countableBasis _) h𝒲cnt, ?_, ?_⟩
    · intro V hV
      obtain ⟨b, hbB, hV𝒲⟩ := Set.mem_iUnion₂.mp hV
      exact ((h𝒲prop b hbB) V hV𝒲).1
    · intro z u huo hzu
      obtain ⟨b, hbB, hzb, hbu⟩ :=
        (TopologicalSpace.isBasis_countableBasis M).exists_subset_of_mem_open
          hzu huo
      obtain ⟨V, hV𝒲, hzV⟩ := h𝒲cov b hbB z hzb
      exact ⟨V, Set.mem_iUnion₂.mpr ⟨b, hbB, hV𝒲⟩, hzV,
        Set.Subset.trans ((h𝒲prop b hbB) V hV𝒲).2 hbu⟩
  -- The fibers of the projection are countable.
  have hfib : ∀ z : M, Set.Countable {rc : PathCover x₀ | rc.pt = z} := by
    intro z
    have : Countable (Path.Homotopic.Quotient x₀ z) := countable_pathClasses _ x₀ z
    refine Set.Countable.mono ?_
      (Set.countable_range fun c : Path.Homotopic.Quotient x₀ z => (⟨z, c⟩ : PathCover x₀))
    rintro ⟨pt, cls⟩ hmem
    have hpteq : pt = z := hmem
    subst hpteq
    exact ⟨cls, rfl⟩
  -- The family of sheets over the countable basis of good opens.
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮 : Set (Set (PathCover x₀)), ∀ S, S ∈ 𝒮 ↔
      ∃ pc : PathCover x₀, ∃ V ∈ 𝒱, pc.pt ∈ V ∧ S = pathCoverSheet x₀ pc V :=
    ⟨{S | ∃ pc : PathCover x₀, ∃ V ∈ 𝒱, pc.pt ∈ V ∧ S = pathCoverSheet x₀ pc V},
      fun _ => Iff.rfl⟩
  -- The family is countable: sheets over a good open embed into a fiber.
  have h𝒮cnt : Set.Countable 𝒮 := by
    have hsub : 𝒮 ⊆ ⋃ V ∈ 𝒱,
        {S | ∃ pc : PathCover x₀, pc.pt ∈ V ∧ S = pathCoverSheet x₀ pc V} := by
      intro S hS
      obtain ⟨pc, V, hV𝒱, hpV, rfl⟩ := (h𝒮 S).mp hS
      exact Set.mem_biUnion hV𝒱 ⟨pc, hpV, rfl⟩
    refine Set.Countable.mono hsub (Set.Countable.biUnion h𝒱cnt fun V hV𝒱 => ?_)
    obtain ⟨hVo, ⟨z, hzV⟩, hlin⟩ := h𝒱good V hV𝒱
    have : Countable ↥{rc : PathCover x₀ | rc.pt = z} := (hfib z).to_subtype
    rw [← Set.countable_coe_iff]
    have hpick : ∀ S : ↥{S | ∃ pc : PathCover x₀, pc.pt ∈ V ∧ S = pathCoverSheet x₀ pc V},
        ∃ rc : PathCover x₀, rc ∈ S.1 ∧ rc.pt = z := by
      rintro ⟨S, pc, hpV, rfl⟩
      exact hsurj pc V hlin hpV z hzV
    choose pick hpickmem hpickpt using hpick
    refine Function.Injective.countable (f := fun S =>
      (⟨pick S, hpickpt S⟩ : ↥{rc : PathCover x₀ | rc.pt = z})) ?_
    rintro ⟨S, hS⟩ ⟨S', hS'⟩ hpe
    have hpp : pick ⟨S, hS⟩ = pick ⟨S', hS'⟩ := congrArg Subtype.val hpe
    have h1 := hpickmem ⟨S, hS⟩
    have h2 := hpickmem ⟨S', hS'⟩
    rw [hpp] at h1
    obtain ⟨rc, hrc1, hrc2⟩ : ∃ rc : PathCover x₀, rc ∈ S ∧ rc ∈ S' :=
      ⟨pick ⟨S', hS'⟩, h1, h2⟩
    have hSc := hS
    have hS'c := hS'
    obtain ⟨pc, hpV, hSeq⟩ := hSc
    obtain ⟨pc', hp'V, hS'eq⟩ := hS'c
    rw [hSeq] at hrc1
    rw [hS'eq] at hrc2
    refine Subtype.ext ?_
    change S = S'
    rw [hSeq, hS'eq, ← hsheeteq pc rc V hrc1, ← hsheeteq pc' rc V hrc2]
  -- Any open set shrinks, around each of its points, to a sheet over an open set.
  have hshrink : ∀ u : Set (PathCover x₀),
      TopologicalSpace.GenerateOpen {s | ∃ (pc : PathCover x₀)
        (U : Set M), IsOpen U ∧ pc.pt ∈ U ∧
        s = pathCoverSheet x₀ pc U} u →
      ∀ qc, qc ∈ u → ∃ V : Set M, IsOpen V ∧ qc.pt ∈ V ∧
        pathCoverSheet x₀ qc V ⊆ u := by
    intro u hu
    induction hu with
    | basic s hs =>
      obtain ⟨pc, U, hUo, hpU, rfl⟩ := hs
      intro qc hqc
      exact ⟨U, hUo, hpt pc qc U hqc, htrans pc qc U hqc⟩
    | univ =>
      intro qc _
      exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun rc _ => Set.mem_univ rc⟩
    | inter s t hs ht ihs iht =>
      intro qc hqc
      obtain ⟨V₁, hV₁o, hqV₁, hsub₁⟩ := ihs qc hqc.1
      obtain ⟨V₂, hV₂o, hqV₂, hsub₂⟩ := iht qc hqc.2
      refine ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, ⟨hqV₁, hqV₂⟩, fun rc hrc => ?_⟩
      exact ⟨hsub₁ (hmono qc Set.inter_subset_left hrc),
        hsub₂ (hmono qc Set.inter_subset_right hrc)⟩
    | sUnion S hS ih =>
      intro qc hqc
      obtain ⟨s, hsS, hqs⟩ := hqc
      obtain ⟨V, hVo, hqV, hsub⟩ := ih s hsS qc hqs
      exact ⟨V, hVo, hqV, hsub.trans (Set.subset_sUnion_of_mem hsS)⟩
  -- The countable family of sheets over the basis is a topological basis.
  have hbasis : TopologicalSpace.IsTopologicalBasis 𝒮 := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · intro S hS
      obtain ⟨pc, V, hV𝒱, hpV, rfl⟩ := (h𝒮 S).mp hS
      exact hopen pc V (h𝒱good V hV𝒱).1 hpV
    · intro qc u hqu huo
      have hu' : TopologicalSpace.GenerateOpen {s | ∃ (pc : PathCover x₀)
          (U : Set M), IsOpen U ∧ pc.pt ∈ U ∧
          s = pathCoverSheet x₀ pc U} u := huo
      obtain ⟨V', hV'o, hqV', hsub⟩ := hshrink u hu' qc hqu
      obtain ⟨V, hV𝒱, hqV, hVV'⟩ := h𝒱basis qc.pt V' hV'o hqV'
      exact ⟨pathCoverSheet x₀ qc V, (h𝒮 _).mpr ⟨qc, V, hV𝒱, hqV, rfl⟩, hself qc V hqV,
        Set.Subset.trans (hmono qc hVV') hsub⟩
  exact hbasis.secondCountableTopology h𝒮cnt

end RiemannDynamics
