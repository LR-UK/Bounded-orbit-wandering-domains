import FinitePunctureMetricInput
import UniformLocalLifting

open Set Metric Filter Function
open scoped Topology

namespace AreaDeficit.FinitePunctureMetricInput

/-- Uniform logarithmic comparison inside a proper local chart. The
radius and bound are chosen before the finite puncture set. -/
theorem uniform_chart_comparison (G : FinitePunctureMetricInput)
    {C : Set ℂ} (hC : IsCompact C) {a b : ℂ} (hab : a ≠ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : ℂ → ℂ) (K V : Set ℂ) (P E : Finset ℂ) (y : ℂ),
      a ∈ P → b ∈ P → y ∈ K → K ⊆ V → f y ∈ C → f y ∉ P ∪ E →
      (∀ w ∈ V, w ∈ P → f w ∈ P) → AnalyticOnNhd ℂ f K →
      IsCoveringMapOn (fun w : K => f w) (ball (f y) ε \ (↑(P ∪ E) : Set ℂ)) →
      (∀ w ∈ K, f w ∈ ball (f y) ε \ (↑(P ∪ E) : Set ℂ) → deriv f w ≠ 0) →
      max (Real.log (G.density P y) -
        Real.log (‖deriv f y‖ * G.density (P ∪ E) (f y))) 0 ≤ M := by
  classical
  obtain ⟨r, hr, hr1, H⟩ := exists_uniform_local_lifting_radius hC hab hε
  refine ⟨max (Real.log (1 / r)) 0, le_max_right _ _, ?_⟩
  intro f K V P E y ha hb hy hKV hfyC hfy hforward hf hcov hreg
  have hP : 2 ≤ P.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have hQ : 2 ≤ (P ∪ E).card := hP.trans (Finset.card_le_card Finset.subset_union_left)
  have hyP : y ∉ P := fun h => hfy (Finset.mem_union_left E (hforward y (hKV hy) h))
  obtain ⟨p, hp, hm, hp0, he⟩ := G.extremal_disc (P ∪ E) hQ (f y) hfy
  have hpC : p 0 ∈ C := hp0 ▸ hfyC
  have hcov' : IsCoveringMapOn (fun w : K => f w)
      (ball (p 0) ε \ (↑(P ∪ E) : Set ℂ)) := hp0 ▸ hcov
  obtain ⟨h, hh0, hmap, hcomp, hh, hhd⟩ := H f p K (↑(P ∪ E)) y
    (hp.analyticOnNhd isOpen_ball)
    (fun w hw heq => hm hw (heq ▸ Finset.mem_union_left E ha))
    (fun w hw heq => hm hw (heq ▸ Finset.mem_union_left E hb))
    (fun w hw => hm hw) hpC hy hp0.symm hf hcov'
    (by simpa only [hp0] using hreg)
  have hsub : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1.le
  have hmapP : MapsTo h (ball 0 r) ((↑P : Set ℂ)ᶜ) := by
    intro w hw hmem
    have hfp := hforward (h w) (hKV (hmap hw)) hmem
    have hcp : f (h w) = p w := hcomp hw
    rw [hcp] at hfp
    exact hm (hsub hw) (Finset.mem_union_left E hfp)
  have hdy : deriv f y ≠ 0 := hreg y hy ⟨mem_ball_self hε, hfy⟩
  have hn : 0 < ‖deriv f y‖ := norm_pos_iff.mpr hdy
  have hpos := G.positive (P ∪ E) hQ (f y) hfy
  have hposP := G.positive P hP y hyP
  have hs := G.schwarz_on_ball hP hr hh hmapP
  have hder : deriv h 0 = deriv p 0 / deriv f y := by
    simpa only [hh0] using (hhd 0 (mem_ball_self hr)).deriv
  rw [hh0, hder, norm_div] at hs
  have ha' : G.density P y * ‖deriv p 0‖ * r ≤ 2 * ‖deriv f y‖ := by
    have hh' := (le_div_iff₀ hr).mp hs
    have hmul := mul_le_mul_of_nonneg_right hh' hn.le
    have heq : (G.density P y * (‖deriv p 0‖ / ‖deriv f y‖) * r) * ‖deriv f y‖ =
        G.density P y * ‖deriv p 0‖ * r := by field_simp
    rwa [heq] at hmul
  have hscaled : G.density P y * r ≤ ‖deriv f y‖ * G.density (P ∪ E) (f y) := by
    have H' := mul_le_mul_of_nonneg_right ha' hpos.le
    have heq : (G.density P y * ‖deriv p 0‖ * r) * G.density (P ∪ E) (f y) =
        (G.density P y * r) * 2 := by
      rw [← he]
      ring
    rw [heq] at H'
    nlinarith
  have heta : 0 < ‖deriv f y‖ * G.density (P ∪ E) (f y) := mul_pos hn hpos
  have hratio : G.density P y / (‖deriv f y‖ * G.density (P ∪ E) (f y)) ≤ 1 / r := by
    apply (div_le_div_iff₀ heta hr).mpr
    simpa using hscaled
  have hlog := Real.log_le_log (div_pos hposP heta) hratio
  rw [Real.log_div (ne_of_gt hposP) (ne_of_gt heta)] at hlog
  exact max_le_max hlog le_rfl

/-- A compact family of source points has one logarithmic comparison
constant. Proper local charts are constructed from local analyticity. -/
theorem compact_log_comparison (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V L : Set ℂ} (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x))
    (hL : IsCompact L) (hLV : L ⊆ V)
    {a b : ℂ} (hab : a ≠ b) (E : Finset ℂ)
    (hE : ∀ w ∈ V, deriv f w = 0 → f w ∈ E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ P : Finset ℂ, a ∈ P → b ∈ P →
      (∀ w ∈ V, w ∈ P → f w ∈ P) → ∀ y ∈ L, f y ∉ P ∪ E →
      max (Real.log (G.density P y) -
        Real.log (‖deriv f y‖ * G.density (P ∪ E) (f y))) 0 ≤ M := by
  classical
  have hC : IsCompact (f '' L) := hL.image_of_continuousOn (hf.continuousOn.mono hLV)
  have hlocal : ∀ x : L, ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ P : Finset ℂ, a ∈ P → b ∈ P →
      (∀ w ∈ V, w ∈ P → f w ∈ P) →
      ∀ y ∈ L, y ∈ ball (x : ℂ) δ → f y ∉ P ∪ E →
      max (Real.log (G.density P y) -
        Real.log (‖deriv f y‖ * G.density (P ∪ E) (f y))) 0 ≤ M := by
    intro x
    obtain ⟨r, hr, s, hs, hKV, hfa, _, hdisj, _⟩ :=
      exists_local_disc_covering hV (hLV x.2) (hf x (hLV x.2)) (hn x (hLV x.2))
    have hnear : ∀ᶠ y in 𝓝 (x : ℂ), y ∈ ball (x : ℂ) r ∧
        f y ∈ ball (f x) (s / 2) :=
      Filter.inter_mem (ball_mem_nhds (x : ℂ) hr)
        ((hf x (hLV x.2)).continuousAt.preimage_mem_nhds
          (ball_mem_nhds (f x) (half_pos hs)))
    obtain ⟨δ, hδ, hδB⟩ := Metric.eventually_nhds_iff.mp hnear
    obtain ⟨M, hM, H⟩ := G.uniform_chart_comparison hC hab (half_pos hs)
    refine ⟨δ, hδ, M, hM, ?_⟩
    intro P ha hb hforward y hy hyB hyQ
    have hyK : y ∈ closedBall (x : ℂ) r := ball_subset_closedBall (hδB hyB).1
    have htarget : ball (f y) (s / 2) ⊆ ball (f x) s := by
      intro w hw
      have h1 := mem_ball.mp hw
      have h2 := mem_ball.mp (hδB hyB).2
      exact mem_ball.mpr ((dist_triangle w (f y) (f x)).trans_lt (by linarith))
    have hreg : ∀ w ∈ closedBall (x : ℂ) r,
        f w ∈ ball (f y) (s / 2) \ (↑(P ∪ E) : Set ℂ) → deriv f w ≠ 0 := by
      intro w hw hfw heq
      exact hfw.2 (Finset.mem_union_right P (hE w (hKV hw) heq))
    have hcov : IsCoveringMapOn (fun w : closedBall (x : ℂ) r => f w)
        (ball (f y) (s / 2) \ (↑(P ∪ E) : Set ℂ)) := by
      apply compact_analytic_covering (isCompact_closedBall (x : ℂ) r) hfa ?_ hreg
      intro w hw hfw
      rw [interior_closedBall (x : ℂ) hr.ne']
      have hns : w ∉ sphere (x : ℂ) r :=
        fun h => disjoint_left.mp hdisj (htarget hfw.1) ⟨w, h, rfl⟩
      exact lt_of_le_of_ne hw (fun he => hns he)
    exact H f (closedBall (x : ℂ) r) V P E y ha hb hyK hKV
      (mem_image_of_mem f hy) hyQ hforward hfa hcov hreg
  choose δ hδ M hM H using hlocal
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun x : L => ball (x : ℂ) (δ x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hδ ⟨x, hx⟩)⟩)
  refine ⟨∑ x ∈ t, M x, Finset.sum_nonneg (fun x _ => hM x), ?_⟩
  intro P ha hb hforward y hy hyQ
  obtain ⟨x, hxt, hyB⟩ := mem_iUnion₂.mp (ht hy)
  exact (H x P ha hb hforward y hy hyB hyQ).trans
    (Finset.single_le_sum (fun w _ => hM w) hxt)

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.compact_log_comparison
