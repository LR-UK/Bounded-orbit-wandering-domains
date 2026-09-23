import ComplexApproximation.CorrectedInterpolation
import ComplexApproximation.Topology.Filling
import Runge.Holomorphic

/-!
# The Rosay–Rudin extension step

Runge approximation and a compactly supported Cauchy–Riemann correction extend
a neighbourhood-holomorphic function across any specified compact set, with an
arbitrarily small uniform change on the original closed set. Iteration requires
the bounded-holes condition, which is separate from this analytic step.
-/

open Complex Set Function Filter Metric Bornology Runge
open scoped Topology ContDiff

namespace ComplexApproximation

/-- The neighbourhood-holomorphic extension step in the Rosay–Rudin proof. -/
theorem exists_holomorphic_neighbourhood_extension
    (E : Set ℂ) (hE : IsClosed E) (hholes : NoBoundedComplementComponents E)
    (U : Set ℂ) (hU : IsOpen U) (hEU : E ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (K : Set ℂ) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : ℂ → ℂ) (V : Set ℂ), IsOpen V ∧ E ∪ K ⊆ V ∧
      AnalyticOnNhd ℂ g V ∧ ∀ z ∈ E, ‖g z - f z‖ < ε := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  obtain ⟨φ, hφ, hcφ, hsφ, hrφ, h1φ⟩ :=
    exists_smooth_cutoff_controlled K (ball 0 R) hK isOpen_ball
      (fun z hz => mem_ball_zero_iff.mpr (hKR z hz))
  let φc : ℂ → ℂ := fun z => (φ z : ℂ)
  have hφc : ContDiff ℝ ∞ φc := Complex.ofRealCLM.contDiff.comp hφ
  have hsφc : support φc = support φ := by ext z; simp [φc, mem_support]
  have htφc : tsupport φc = tsupport φ := congrArg closure hsφc
  have hcφc : HasCompactSupport φc := by
    change IsCompact (tsupport φc)
    rw [htφc]
    exact hcφ
  have hD := contDiff_cauchyRiemannDefect hφc
  have hcD := hasCompactSupport_cauchyRiemannDefect hcφc
  have hsD : tsupport (cauchyRiemannDefect φc) ⊆ tsupport φ := by
    rw [← htφc]
    exact tsupport_cauchyRiemannDefect_subset φc
  obtain ⟨B₀, hB₀⟩ := hD.continuous.bounded_above_of_compact_support hcD
  let B := max B₀ 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right B₀ 0]
  have hBD (z : ℂ) : ‖cauchyRiemannDefect φc z‖ ≤ B :=
    (hB₀ z).trans (by dsimp [B]; linarith [le_max_left B₀ 0])
  obtain ⟨C, hC, hsolver⟩ := exists_bound_solveCauchyRiemann (tsupport φ) hcφ
  let δ := ε / (2 * (1 + C * B))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbudget : δ + C * (δ * B) < ε := by
    have hden : 2 * (1 + C * B) ≠ 0 := by positivity
    have heq : δ + C * (δ * B) = ε / 2 := by dsimp [δ]; field_simp
    rw [heq]
    linarith
  have hcompact : IsCompact (E ∩ closedBall 0 R) :=
    (isCompact_closedBall (0 : ℂ) R).inter_left hE
  obtain ⟨p, hp⟩ := polynomial_approximation (E ∩ closedBall 0 R) hcompact
    (isConnected_compl_inter_closedBall hholes hR) U hU
    (fun z hz => hEU hz.1) f hf δ hδ
  let T := E ∩ tsupport (cauchyRiemannDefect φc)
  have hT : IsCompact T := hcD.inter_left hE
  let W := U ∩ interior {z | ‖f z - p.eval z‖ < δ}
  have hW : IsOpen W := hU.inter isOpen_interior
  have hTW : T ⊆ W := by
    intro z hz
    have hzU := hEU hz.1
    refine ⟨hzU, mem_interior_iff_mem_nhds.mpr ?_⟩
    have hzR : z ∈ closedBall 0 R := ball_subset_closedBall (hsφ (hsD hz.2))
    have hc := ((hf z hzU).continuousAt.sub (p.continuous.continuousAt)).norm
    exact hc.eventually_lt_const (hp z ⟨hz.1, hzR⟩)
  obtain ⟨χ, hχ, hcχ, hsχ, hrχ, h1χ⟩ :=
    exists_smooth_cutoff_controlled T W hT hW hTW
  let χc : ℂ → ℂ := fun z => (χ z : ℂ)
  let q := interpolationDensity χc φc p.eval f
  have hq : ContDiff ℝ ∞ q := by
    apply contDiff_cutoff_mul hχ hsχ
    intro z hz
    exact (((hf z hz.1).contDiffAt.restrict_scalars ℝ).sub
      ((p.differentiable.differentiableOn.analyticOnNhd isOpen_univ z
        (mem_univ z)).contDiffAt.restrict_scalars ℝ)).mul hD.contDiffAt
  have hcq : HasCompactSupport q := hasCompactSupport_cutoff_mul hcχ _
  have hsq : support q ⊆ tsupport φ := by
    intro z hz
    apply hsD (subset_tsupport _ ?_)
    intro hzero
    exact hz (by simp [q, interpolationDensity, hzero])
  have hqbound (z : ℂ) : ‖q z‖ ≤ δ * B := by
    apply norm_cutoff_mul_le hrχ hsχ (mul_nonneg hδ.le hB.le)
    intro w hw
    rw [norm_mul]
    exact mul_le_mul ((interior_subset (s := {z | ‖f z - p.eval z‖ < δ}) hw.2).le)
      (hBD w) (norm_nonneg _) hδ.le
  have hχ1 : ∀ z ∈ E ∩ tsupport (cauchyRiemannDefect φc),
      χc =ᶠ[𝓝 z] (fun _ => 1) := by
    intro z hz
    filter_upwards [h1χ z hz] with w hw
    simp [χc, hw]
  let V := gluingOpen U φc χc
  let g : ℂ → ℂ := fun z => interpolate φc p.eval f z + solveCauchyRiemann q z
  refine ⟨g, V, isOpen_gluingOpen hU φc χc, ?_, ?_, ?_⟩
  · apply union_subset (subset_gluingOpen hEU hχ1)
    intro z hz
    left
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [h1φ z hz] with w hw
    simp [φc, hw]
  · exact analyticOnNhd_correctedInterpolation hU hφc p.differentiable hf hq hcq
  · intro z hz
    have hinterp : ‖interpolate φc p.eval f z - f z‖ ≤ δ := by
      apply norm_interpolate_sub_le hrφ hδ.le _ hz
      intro w hw
      exact (hp w ⟨hw.1, ball_subset_closedBall (hsφ hw.2)⟩).le
    have hcorr : ‖solveCauchyRiemann q z‖ ≤ C * (δ * B) :=
      hsolver q hq.continuous hcq hsq (δ * B) (mul_nonneg hδ.le hB.le) hqbound z
    calc
      ‖g z - f z‖ = ‖(interpolate φc p.eval f z - f z) + solveCauchyRiemann q z‖ := by
        congr 1
        dsimp [g]
        ring
      _ ≤ ‖interpolate φc p.eval f z - f z‖ + ‖solveCauchyRiemann q z‖ := norm_add_le _ _
      _ ≤ δ + C * (δ * B) := add_le_add hinterp hcorr
      _ < ε := hbudget

/-- Extend across a set whose portion outside the old approximation set is
bounded. This is the form applied to successive filled disks. -/
theorem exists_holomorphic_extension_of_bounded_difference
    (E F : Set ℂ) (hE : IsClosed E) (hholes : NoBoundedComplementComponents E)
    (hbounded : IsBounded (F \ E))
    (U : Set ℂ) (hU : IsOpen U) (hEU : E ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : ℂ → ℂ) (V : Set ℂ), IsOpen V ∧ F ⊆ V ∧
      AnalyticOnNhd ℂ g V ∧ ∀ z ∈ E, ‖g z - f z‖ < ε := by
  obtain ⟨R, _, hR⟩ := hbounded.exists_pos_norm_le
  obtain ⟨g, V, hV, hEV, hg, herr⟩ := exists_holomorphic_neighbourhood_extension
    E hE hholes U hU hEU f hf (closedBall 0 R) (isCompact_closedBall 0 R) ε hε
  refine ⟨g, V, hV, ?_, hg, herr⟩
  intro z hz
  by_cases hzE : z ∈ E
  · exact hEV (Or.inl hzE)
  · exact hEV (Or.inr (mem_closedBall_zero_iff.mpr (hR z ⟨hz, hzE⟩)))

end ComplexApproximation
