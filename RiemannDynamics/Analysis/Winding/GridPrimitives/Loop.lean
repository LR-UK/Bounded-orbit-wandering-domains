/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Winding.GridPrimitives.Join

/-!
# An essential grid loop from a bounded complementary component

An open set with a bounded complementary component carries a grid loop with
nonzero winding number about a point of that component.
-/

open Complex Set unitInterval

namespace RiemannDynamics

set_option maxHeartbeats 400000 in
-- This essential-loop separation proof elaborates as one large declaration whose
-- nested winding / complementary-component `have` chains exceed the default budget.
/-- **Essential loops around separated compact complementary pieces.** If a
compact piece `A` of the closed complement of an open set `T` is metrically
separated from the rest of the complement, then some closed curve in `T`
has nonzero winding number about any prescribed point of `A`: the boundary
of the union of small grid squares meeting `A` consists of grid edges lying
in `T`, and by the per-edge principal-logarithm increment linearity the
total winding of its boundary cycles about the point is one, so some cycle
is essential. -/
theorem exists_gridLoop_winding_ne_zero {T : Set ℂ} (hT : IsOpen T)
    {z₀ : ℂ} (A : Set ℂ) (ε : ℝ) (hε : 0 < ε) (hA : IsCompact A)
    (hzA : z₀ ∈ A) (hAT : A ⊆ Tᶜ)
    (hsep : ∀ w ∈ Tᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a) :
    ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧ (∀ t : unitInterval, γ t ∈ T) ∧
      windingNumber γ z₀ ≠ 0 := by
  classical
  -- ================================================================
  -- STAGE 0: translation invariance of the winding number, and the
  -- reduction to a configuration where the marked point is the center
  -- of the `(0,0)` grid square.
  -- ================================================================
  -- Winding is invariant under simultaneous translation of curve and point
  -- (the shifted curves are literally equal).
  have htw : ∀ (γ : C(unitInterval, ℂ)) (w q : ℂ),
      windingNumber (γ - ContinuousMap.const unitInterval w) (q - w) =
        windingNumber γ q := by
    intro γ w q
    have hsc : shiftedCurve (γ - ContinuousMap.const unitInterval w) (q - w) =
        shiftedCurve γ q := by
      ext t
      simp only [shiftedCurve, ContinuousMap.sub_apply,
        ContinuousMap.const_apply]
      ring
    unfold windingNumber
    rw [hsc]
  set δ : ℝ := ε / 100 with hδ_def
  have hδ : 0 < δ := by positivity
  set c₀ : ℂ := gridSquareCenter δ (0, 0) with hc₀_def
  set τ : ℂ := c₀ - z₀ with hτ_def
  set A' : Set ℂ := (fun w => w + τ) '' A with hA'_def
  set T' : Set ℂ := (fun w => w + τ) '' T with hT'_def
  have hT'open : IsOpen T' := isOpenMap_add_right τ T hT
  have hA'cpt : IsCompact A' := hA.image (continuous_add_const τ)
  have hc₀A' : c₀ ∈ A' := ⟨z₀, hzA, by rw [hτ_def]; ring⟩
  have hA'T' : A' ⊆ T'ᶜ := by
    rintro x ⟨a, haA, rfl⟩ ⟨t, htT, hteq⟩
    have hat : t = a := by
      have := add_right_cancel hteq
      exact this
    exact hAT haA (hat ▸ htT)
  have hsep' : ∀ w ∈ T'ᶜ, w ∉ A' → ∀ a ∈ A', ε ≤ dist w a := by
    intro w hw hwA a' ha'
    obtain ⟨a, haA, rfl⟩ := ha'
    have hw₀T : w - τ ∈ Tᶜ := by
      intro hmem
      exact hw ⟨w - τ, hmem, by ring⟩
    have hw₀A : w - τ ∉ A := by
      intro hmem
      exact hwA ⟨w - τ, hmem, by ring⟩
    have hd := hsep (w - τ) hw₀T hw₀A a haA
    calc ε ≤ dist (w - τ) a := hd
      _ = dist w (a + τ) := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          ring
  -- It suffices to find the loop in the translated configuration.
  suffices h : ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧
      (∀ t : unitInterval, γ t ∈ T') ∧ windingNumber γ c₀ ≠ 0 by
    obtain ⟨γ, hγcl, hγT', hγw⟩ := h
    refine ⟨γ - ContinuousMap.const unitInterval τ, ?_, ?_, ?_⟩
    · simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, hγcl]
    · intro t
      obtain ⟨s, hsT, hseq⟩ := hγT' t
      have hst : (γ - ContinuousMap.const unitInterval τ) t = s := by
        simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
        rw [← hseq]
        ring
      rw [hst]
      exact hsT
    · have h1 := htw γ τ c₀
      have h2 : c₀ - τ = z₀ := by rw [hτ_def]; ring
      rw [h2] at h1
      rw [h1]
      exact hγw
  -- ================================================================
  -- STAGE 1: the square complex `S` and its geometry.
  -- ================================================================
  -- A bounding box: `A'` is bounded, so its squares have indices in a box.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, A' ⊆ Metric.ball 0 (δ * N) := by
    obtain ⟨R, hR⟩ := hA'cpt.isBounded.subset_closedBall 0
    obtain ⟨N, hNgt⟩ := exists_nat_gt ((R + 1) / δ)
    rw [div_lt_iff₀ hδ] at hNgt
    refine ⟨N, fun x hx => ?_⟩
    have hxR : dist x 0 ≤ R := hR hx
    have hlt : R < δ * N := by nlinarith
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hxR hlt)
  set B₀ : Finset (ℤ × ℤ) :=
    Finset.Icc (-(N : ℤ) - 2, -(N : ℤ) - 2) ((N : ℤ) + 2, (N : ℤ) + 2)
    with hB₀_def
  set S : Finset (ℤ × ℤ) :=
    B₀.filter (fun p => (gridSquare δ p ∩ A').Nonempty) with hS_def
  -- Coordinate helpers.
  have hgre : ∀ q : ℤ × ℤ, (gridPoint δ q).re = δ * q.1 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hgim : ∀ q : ℤ × ℤ, (gridPoint δ q).im = δ * q.2 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hsegre : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).re = u * a.re + v * b.re := by
    intro a b u v
    simp [Complex.add_re]
  have hsegim : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).im = u * a.im + v * b.im := by
    intro a b u v
    simp [Complex.add_im]
  have hsq_mem : ∀ (p : ℤ × ℤ) (z : ℂ), z ∈ gridSquare δ p ↔
      (δ * p.1 ≤ z.re ∧ z.re ≤ δ * (p.1 + 1)) ∧
      (δ * p.2 ≤ z.im ∧ z.im ≤ δ * (p.2 + 1)) := by
    intro p z
    exact Iff.rfl
  have hKint : ∀ p : ℤ × ℤ, interior (gridSquare δ p) =
      Set.Ioo (δ * p.1) (δ * (p.1 + 1)) ×ℂ
        Set.Ioo (δ * p.2) (δ * (p.2 + 1)) := by
    intro p
    have hKeq : gridSquare δ p =
        Set.Icc (δ * p.1) (δ * (p.1 + 1)) ×ℂ
          Set.Icc (δ * p.2) (δ * (p.2 + 1)) := rfl
    rw [hKeq, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  have hgp00 : gridPoint δ (0, 0) = 0 := by
    simp [gridPoint]
  have hc₀eq : c₀ = ((δ / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
    rw [hc₀_def]
    simp only [gridSquareCenter, hgp00, zero_add]
    push_cast
    ring
  have hcre : c₀.re = δ / 2 := by
    rw [hc₀eq]
    simp [Complex.mul_re]
  have hcim : c₀.im = δ / 2 := by
    rw [hc₀eq]
    simp [Complex.mul_im]
  have hnorm_le : ∀ z : ℂ, ‖z‖ ≤ |z.re| + |z.im| := by
    intro z
    calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
          rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  -- Every point of the plane lies in the square of its floor indices;
  -- squares meeting `A'` have indices in the box.
  have hfloor : ∀ w : ℂ, w ∈ gridSquare δ (⌊w.re / δ⌋, ⌊w.im / δ⌋) := by
    intro w
    have hre1 : δ * (⌊w.re / δ⌋ : ℝ) ≤ w.re := by
      have h1 : (⌊w.re / δ⌋ : ℝ) ≤ w.re / δ := Int.floor_le _
      have h2 : δ * (⌊w.re / δ⌋ : ℝ) ≤ δ * (w.re / δ) := by nlinarith
      calc δ * (⌊w.re / δ⌋ : ℝ) ≤ δ * (w.re / δ) := h2
        _ = w.re := by field_simp
    have hre2 : w.re ≤ δ * ((⌊w.re / δ⌋ : ℝ) + 1) := by
      have h1 : w.re / δ < (⌊w.re / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : w.re < ((⌊w.re / δ⌋ : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h1
      nlinarith
    have him1 : δ * (⌊w.im / δ⌋ : ℝ) ≤ w.im := by
      have h1 : (⌊w.im / δ⌋ : ℝ) ≤ w.im / δ := Int.floor_le _
      have h2 : δ * (⌊w.im / δ⌋ : ℝ) ≤ δ * (w.im / δ) := by nlinarith
      calc δ * (⌊w.im / δ⌋ : ℝ) ≤ δ * (w.im / δ) := h2
        _ = w.im := by field_simp
    have him2 : w.im ≤ δ * ((⌊w.im / δ⌋ : ℝ) + 1) := by
      have h1 : w.im / δ < (⌊w.im / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : w.im < ((⌊w.im / δ⌋ : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h1
      nlinarith
    exact ⟨⟨hre1, hre2⟩, him1, him2⟩
  have hbox : ∀ p : ℤ × ℤ, (gridSquare δ p ∩ A').Nonempty → p ∈ B₀ := by
    rintro p ⟨x, hxsq, hxA⟩
    have hxball := hN hxA
    rw [Metric.mem_ball, dist_zero_right] at hxball
    have hre : |x.re| < δ * N :=
      lt_of_le_of_lt (Complex.abs_re_le_norm x) hxball
    have him : |x.im| < δ * N :=
      lt_of_le_of_lt (Complex.abs_im_le_norm x) hxball
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hsq_mem p x).mp hxsq
    rw [abs_lt] at hre him
    have hp1u : (p.1 : ℝ) < N := by nlinarith [hre.2, hre.1]
    have hp1l : -(N : ℝ) < (p.1 : ℝ) + 1 := by nlinarith [hre.1]
    have hp2u : (p.2 : ℝ) < N := by nlinarith [him.2]
    have hp2l : -(N : ℝ) < (p.2 : ℝ) + 1 := by nlinarith [him.1]
    have hi1 : p.1 < (N : ℤ) := by exact_mod_cast hp1u
    have hi2 : -(N : ℤ) < p.1 + 1 := by exact_mod_cast hp1l
    have hi3 : p.2 < (N : ℤ) := by exact_mod_cast hp2u
    have hi4 : -(N : ℤ) < p.2 + 1 := by exact_mod_cast hp2l
    rw [hB₀_def, Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hcoverA : A' ⊆ ⋃ p ∈ S, gridSquare δ p := by
    intro w hw
    have hwsq := hfloor w
    have hne : (gridSquare δ (⌊w.re / δ⌋, ⌊w.im / δ⌋) ∩ A').Nonempty :=
      ⟨w, hwsq, hw⟩
    have hpS : (⌊w.re / δ⌋, ⌊w.im / δ⌋) ∈ S := by
      rw [hS_def, Finset.mem_filter]
      exact ⟨hbox _ hne, hne⟩
    exact Set.mem_biUnion hpS hwsq
  -- Squares of `S` avoid the rest of the complement (diameter < ε), hence
  -- lie in `T' ∪ A'`.
  have hsq_diam : ∀ p : ℤ × ℤ, ∀ x y : ℂ, x ∈ gridSquare δ p →
      y ∈ gridSquare δ p → dist x y ≤ 2 * δ := by
    intro p x y hx hy
    obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := (hsq_mem p x).mp hx
    obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := (hsq_mem p y).mp hy
    have hexp1 : δ * ((p.1 : ℝ) + 1) = δ * p.1 + δ := by ring
    have hexp2 : δ * ((p.2 : ℝ) + 1) = δ * p.2 + δ := by ring
    rw [hexp1] at hx2 hy2
    rw [hexp2] at hx4 hy4
    rw [dist_eq_norm]
    calc ‖x - y‖ ≤ |(x - y).re| + |(x - y).im| := hnorm_le _
      _ ≤ δ + δ := by
          rw [Complex.sub_re, Complex.sub_im]
          have h1 : |x.re - y.re| ≤ δ := by
            rw [abs_le]
            constructor <;> linarith
          have h2 : |x.im - y.im| ≤ δ := by
            rw [abs_le]
            constructor <;> linarith
          linarith
      _ = 2 * δ := by ring
  have hSsub : ∀ p ∈ S, gridSquare δ p ⊆ T' ∪ A' := by
    intro p hp x hx
    by_contra hxn
    rw [Set.mem_union] at hxn
    push Not at hxn
    obtain ⟨hxT, hxA⟩ := hxn
    rw [hS_def, Finset.mem_filter] at hp
    obtain ⟨-, a, hasq, haA⟩ := hp
    have hd := hsep' x hxT hxA a haA
    have hdle := hsq_diam p x a hx hasq
    rw [hδ_def] at hdle
    linarith
  -- The marked square: `(0,0) ∈ S`, `c₀` interior to it and to no other.
  have hc₀sq : c₀ ∈ gridSquare δ (0, 0) := by
    rw [hsq_mem (0, 0) c₀]
    rw [hcre, hcim]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> push_cast <;> nlinarith
  have h00 : (0, 0) ∈ S := by
    rw [hS_def, Finset.mem_filter]
    refine ⟨?_, c₀, hc₀sq, hc₀A'⟩
    rw [hB₀_def, Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hc₀in : c₀ ∈ interior (gridSquare δ (0, 0)) := by
    rw [hKint, Complex.mem_reProdIm, hcre, hcim]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> push_cast <;> nlinarith
  have hc₀only : ∀ p : ℤ × ℤ, p ≠ (0, 0) → c₀ ∉ gridSquare δ p := by
    intro p hp hmem
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hsq_mem p c₀).mp hmem
    rw [hcre] at h1 h2
    rw [hcim] at h3 h4
    have hp1 : p.1 = 0 := by
      have ha : (p.1 : ℝ) < 1 := by
        by_contra hcon
        push Not at hcon
        have : δ * 1 ≤ δ * (p.1 : ℝ) := by nlinarith
        linarith
      have hb : (-1 : ℝ) < (p.1 : ℝ) := by
        by_contra hcon
        push Not at hcon
        have : δ * ((p.1 : ℝ) + 1) ≤ δ * 0 := by nlinarith
        linarith
      have ha' : p.1 < 1 := by exact_mod_cast ha
      have hb' : (-1 : ℤ) < p.1 := by exact_mod_cast hb
      omega
    have hp2 : p.2 = 0 := by
      have ha : (p.2 : ℝ) < 1 := by
        by_contra hcon
        push Not at hcon
        have : δ * 1 ≤ δ * (p.2 : ℝ) := by nlinarith
        linarith
      have hb : (-1 : ℝ) < (p.2 : ℝ) := by
        by_contra hcon
        push Not at hcon
        have : δ * ((p.2 : ℝ) + 1) ≤ δ * 0 := by nlinarith
        linarith
      have ha' : p.2 < 1 := by exact_mod_cast ha
      have hb' : (-1 : ℤ) < p.2 := by exact_mod_cast hb
      omega
    exact hp (Prod.ext_iff.mpr ⟨hp1, hp2⟩)
  -- `c₀` is off every grid line (both coordinates are half-integer
  -- multiples of `δ`), hence off every grid-path trace.
  have hhalf_ne : ∀ n : ℤ, δ / 2 ≠ δ * n := by
    intro n heq
    have h' : δ * (1 / 2 : ℝ) = δ * (n : ℝ) := by linarith
    have h2 : (1 / 2 : ℝ) = (n : ℝ) := mul_left_cancel₀ (ne_of_gt hδ) h'
    have h3 : (2 * n : ℝ) = 1 := by linarith
    have h4 : (2 * n : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hc₀line : ∀ q : ℤ × ℤ, ∀ w ∈ segment ℝ (gridPoint δ q)
      (gridPoint δ (q.1 + 1, q.2)), c₀ ≠ w := by
    intro q w hw heq
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have him : w.im = δ * q.2 := by
      rw [← hwe, hsegim, hgim, hgim]
      change u * (δ * (q.2 : ℝ)) + v * (δ * (q.2 : ℝ)) = δ * q.2
      have : u * (δ * (q.2 : ℝ)) + v * (δ * (q.2 : ℝ)) =
          (u + v) * (δ * q.2) := by ring
      rw [this, huv, one_mul]
    have : δ / 2 = δ * q.2 := by rw [← hcim, heq, him]
    exact hhalf_ne q.2 this
  have hc₀line' : ∀ q : ℤ × ℤ, ∀ w ∈ segment ℝ (gridPoint δ q)
      (gridPoint δ (q.1, q.2 + 1)), c₀ ≠ w := by
    intro q w hw heq
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have hre : w.re = δ * q.1 := by
      rw [← hwe, hsegre, hgre, hgre]
      change u * (δ * (q.1 : ℝ)) + v * (δ * (q.1 : ℝ)) = δ * q.1
      have : u * (δ * (q.1 : ℝ)) + v * (δ * (q.1 : ℝ)) =
          (u + v) * (δ * q.1) := by ring
      rw [this, huv, one_mul]
    have : δ / 2 = δ * q.1 := by rw [← hcre, heq, hre]
    exact hhalf_ne q.1 this
  -- ================================================================
  -- STAGE 2: the oriented boundary-edge set `E` (counterclockwise around
  -- `S`) and its vertex balance.
  -- ================================================================
  -- Oriented edges are ordered pairs of adjacent lattice indices; the
  -- boundary keeps an edge iff exactly one adjacent square is in `S`,
  -- oriented with the `S`-square on the left.
  set B₁ : Finset (ℤ × ℤ) :=
    Finset.Icc (-(N : ℤ) - 3, -(N : ℤ) - 3) ((N : ℤ) + 3, (N : ℤ) + 3)
    with hB₁_def
  set bdry : (ℤ × ℤ) × (ℤ × ℤ) → Prop := fun e =>
    -- rightward: from (i,j) to (i+1,j), square above (i,j) in S,
    -- square below (i,j-1) not in S
    (e.2 = (e.1.1 + 1, e.1.2) ∧ (e.1.1, e.1.2) ∈ S ∧ (e.1.1, e.1.2 - 1) ∉ S) ∨
    -- leftward: from (i+1,j) to (i,j)
    (e.1 = (e.2.1 + 1, e.2.2) ∧ (e.2.1, e.2.2 - 1) ∈ S ∧ (e.2.1, e.2.2) ∉ S) ∨
    -- upward: from (i,j) to (i,j+1), square left (i-1,j) in S,
    -- square right (i,j) not in S
    (e.2 = (e.1.1, e.1.2 + 1) ∧ (e.1.1 - 1, e.1.2) ∈ S ∧ (e.1.1, e.1.2) ∉ S) ∨
    -- downward: from (i,j+1) to (i,j)
    (e.1 = (e.2.1, e.2.2 + 1) ∧ (e.2.1, e.2.2) ∈ S ∧ (e.2.1 - 1, e.2.2) ∉ S)
    with hbdry_def
  set E : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := (B₁ ×ˢ B₁).filter bdry with hE_def
  -- Squares of `S` have box-bounded indices, so boundary-edge endpoints
  -- lie in the bigger box `B₁`; membership in `E` is exactly `bdry`.
  have hSbound : ∀ p ∈ S, -(N : ℤ) - 2 ≤ p.1 ∧ p.1 ≤ (N : ℤ) + 2 ∧
      -(N : ℤ) - 2 ≤ p.2 ∧ p.2 ≤ (N : ℤ) + 2 := by
    intro p hp
    rw [hS_def, Finset.mem_filter, hB₀_def, Finset.mem_Icc] at hp
    obtain ⟨⟨hlo, hhi⟩, -⟩ := hp
    rw [Prod.le_def] at hlo hhi
    exact ⟨hlo.1, hhi.1, hlo.2, hhi.2⟩
  have hB₁mem : ∀ a : ℤ × ℤ, -(N : ℤ) - 3 ≤ a.1 → a.1 ≤ (N : ℤ) + 3 →
      -(N : ℤ) - 3 ≤ a.2 → a.2 ≤ (N : ℤ) + 3 → a ∈ B₁ := by
    intro a h1 h2 h3 h4
    rw [hB₁_def, Finset.mem_Icc]
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  have hbdry_bound : ∀ e : (ℤ × ℤ) × (ℤ × ℤ), bdry e → e ∈ B₁ ×ˢ B₁ := by
    intro e h
    rw [hbdry_def] at h
    rw [Finset.mem_product]
    rcases h with ⟨he, hs, -⟩ | ⟨he, hs, -⟩ | ⟨he, hs, -⟩ | ⟨he, hs, -⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.1.1 := q1
      have b2 : e.1.1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.1.2 := q3
      have b4 : e.1.2 ≤ (N : ℤ) + 2 := q4
      have h21 : e.2.1 = e.1.1 + 1 := by rw [he]
      have h22 : e.2.2 = e.1.2 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.2.1 := q1
      have b2 : e.2.1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.2.2 - 1 := q3
      have b4 : e.2.2 - 1 ≤ (N : ℤ) + 2 := q4
      have h11 : e.1.1 = e.2.1 + 1 := by rw [he]
      have h12 : e.1.2 = e.2.2 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.1.1 - 1 := q1
      have b2 : e.1.1 - 1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.1.2 := q3
      have b4 : e.1.2 ≤ (N : ℤ) + 2 := q4
      have h21 : e.2.1 = e.1.1 := by rw [he]
      have h22 : e.2.2 = e.1.2 + 1 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.2.1 := q1
      have b2 : e.2.1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.2.2 := q3
      have b4 : e.2.2 ≤ (N : ℤ) + 2 := q4
      have h11 : e.1.1 = e.2.1 := by rw [he]
      have h12 : e.1.2 = e.2.2 + 1 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
  have hEmem : ∀ e : (ℤ × ℤ) × (ℤ × ℤ), e ∈ E ↔ bdry e := by
    intro e
    rw [hE_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hbdry_bound e h, h⟩⟩
  -- Vertex balance: at every lattice vertex, the number of `E`-edges
  -- entering equals the number leaving (case analysis on the membership
  -- pattern of the four squares at the vertex).
  have hbal : ∀ v : ℤ × ℤ,
      (E.filter (fun e => e.2 = v)).card =
        (E.filter (fun e => e.1 = v)).card := by
    intro v
    clear * - hEmem hbdry_def
    obtain ⟨v1, v2⟩ := v
    -- Membership characterizations for the eight candidate edges at `v`,
    -- in terms of the four squares at `v`.
    have hc1E : ((((v1 - 1, v2), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2) ∈ S ∧ (v1 - 1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inl ⟨?_, hs, hn⟩
        show ((v1, v2) : ℤ × ℤ) = (v1 - 1 + 1, v2)
        congr 1
        omega
    have hc2E : ((((v1 + 1, v2), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2 - 1) ∈ S ∧ (v1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inl ⟨?_, hs, hn⟩)
        exact trivial
    have hc3E : ((((v1, v2 - 1), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2 - 1) ∈ S ∧ (v1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inl ⟨?_, hs, hn⟩))
        show ((v1, v2) : ℤ × ℤ) = (v1, v2 - 1 + 1)
        congr 1
        omega
    have hc4E : ((((v1, v2 + 1), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2) ∈ S ∧ (v1 - 1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inr ⟨?_, hs, hn⟩))
        trivial
    have hd1E : ((((v1, v2), (v1 + 1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2) ∈ S ∧ (v1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inl ⟨?_, hs, hn⟩
        exact trivial
    have hd2E : ((((v1, v2), (v1 - 1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2 - 1) ∈ S ∧ (v1 - 1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inl ⟨?_, hs, hn⟩)
        show ((v1, v2) : ℤ × ℤ) = (v1 - 1 + 1, v2)
        congr 1
        omega
    have hd3E : ((((v1, v2), (v1, v2 + 1))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2) ∈ S ∧ (v1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inl ⟨?_, hs, hn⟩))
        trivial
    have hd4E : ((((v1, v2), (v1, v2 - 1))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2 - 1) ∈ S ∧ (v1 - 1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inr ⟨?_, hs, hn⟩))
        show ((v1, v2) : ℤ × ℤ) = (v1, v2 - 1 + 1)
        congr 1
        omega
    -- Every in-edge is one of the four candidates, and dually.
    have hin_eq : E.filter (fun e => e.2 = (v1, v2)) =
        ({((v1 - 1, v2), (v1, v2)), ((v1 + 1, v2), (v1, v2)),
          ((v1, v2 - 1), (v1, v2)), ((v1, v2 + 1), (v1, v2))} :
            Finset ((ℤ × ℤ) × (ℤ × ℤ))).filter (fun e => e ∈ E) := by
      ext e
      obtain ⟨⟨x, y⟩, s, t⟩ := e
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨heE, he2⟩
        refine ⟨?_, heE⟩
        injection he2 with hs1 hs2
        have hb := (hEmem ((x, y), s, t)).mp heE
        simp only [hbdry_def] at hb
        simp only [Prod.mk.injEq]
        rcases hb with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
          (injection h with h1 h2
           omega)
      · rintro ⟨h | h | h | h, heE⟩ <;>
          exact ⟨heE, congrArg Prod.snd h⟩
    have hout_eq : E.filter (fun e => e.1 = (v1, v2)) =
        ({((v1, v2), (v1 + 1, v2)), ((v1, v2), (v1 - 1, v2)),
          ((v1, v2), (v1, v2 + 1)), ((v1, v2), (v1, v2 - 1))} :
            Finset ((ℤ × ℤ) × (ℤ × ℤ))).filter (fun e => e ∈ E) := by
      ext e
      obtain ⟨⟨x, y⟩, s, t⟩ := e
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨heE, he1⟩
        refine ⟨?_, heE⟩
        injection he1 with hs1 hs2
        have hb := (hEmem ((x, y), s, t)).mp heE
        simp only [hbdry_def] at hb
        simp only [Prod.mk.injEq]
        rcases hb with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
          (injection h with h1 h2
           omega)
      · rintro ⟨h | h | h | h, heE⟩ <;>
          exact ⟨heE, congrArg Prod.fst h⟩
    -- Cards as indicator sums over the four candidates.
    have hin_card : (E.filter (fun e => e.2 = (v1, v2))).card =
        (if (((v1 - 1, v2), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1 + 1, v2), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1, v2 - 1), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        (if (((v1, v2 + 1), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0))) := by
      rw [hin_eq, Finset.card_filter]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_singleton]
    have hout_card : (E.filter (fun e => e.1 = (v1, v2))).card =
        (if (((v1, v2), (v1 + 1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1, v2), (v1 - 1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1, v2), (v1, v2 + 1)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        (if (((v1, v2), (v1, v2 - 1)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0))) := by
      rw [hout_eq, Finset.card_filter]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_singleton]
    rw [hin_card, hout_card]
    rw [if_congr hc1E rfl rfl, if_congr hc2E rfl rfl, if_congr hc3E rfl rfl,
      if_congr hc4E rfl rfl, if_congr hd1E rfl rfl, if_congr hd2E rfl rfl,
      if_congr hd3E rfl rfl, if_congr hd4E rfl rfl]
    -- telescoping indicator identity: [P ∧ ¬Q] + [Q] = [Q ∧ ¬P] + [P]
    have hf : ∀ P Q : Prop, ∀ (_ : Decidable P) (_ : Decidable Q),
        (if P ∧ ¬Q then (1 : ℕ) else 0) + (if Q then 1 else 0) =
          (if Q ∧ ¬P then 1 else 0) + (if P then 1 else 0) := by
      intro P Q dP dQ
      by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
    have h1 := hf ((v1 - 1, v2) ∈ S) ((v1 - 1, v2 - 1) ∈ S)
      inferInstance inferInstance
    have h2 := hf ((v1, v2 - 1) ∈ S) ((v1, v2) ∈ S)
      inferInstance inferInstance
    have h3 := hf ((v1 - 1, v2 - 1) ∈ S) ((v1, v2 - 1) ∈ S)
      inferInstance inferInstance
    have h4 := hf ((v1, v2) ∈ S) ((v1 - 1, v2) ∈ S)
      inferInstance inferInstance
    linarith [h1, h2, h3, h4]
  have hseg_h : ∀ (i j : ℤ), ∀ w ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i + 1, j)),
      w.im = δ * j ∧ δ * i ≤ w.re ∧ w.re ≤ δ * (i + 1) := by
    intro i j w hw
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have hv1 : v ≤ 1 := by linarith
    have hre : w.re = δ * i + v * δ := by
      rw [← hwe, hsegre, hgre, hgre]
      push_cast
      linear_combination (δ * (i : ℝ)) * huv
    have him : w.im = δ * j := by
      rw [← hwe, hsegim, hgim, hgim]
      change u * (δ * (j : ℝ)) + v * (δ * (j : ℝ)) = δ * j
      linear_combination (δ * (j : ℝ)) * huv
    refine ⟨him, ?_, ?_⟩
    · rw [hre]
      nlinarith
    · rw [hre]
      nlinarith
  have hseg_v : ∀ (i j : ℤ), ∀ w ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i, j + 1)),
      w.re = δ * i ∧ δ * j ≤ w.im ∧ w.im ≤ δ * (j + 1) := by
    intro i j w hw
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have hv1 : v ≤ 1 := by linarith
    have him : w.im = δ * j + v * δ := by
      rw [← hwe, hsegim, hgim, hgim]
      push_cast
      linear_combination (δ * (j : ℝ)) * huv
    have hre : w.re = δ * i := by
      rw [← hwe, hsegre, hgre, hgre]
      change u * (δ * (i : ℝ)) + v * (δ * (i : ℝ)) = δ * i
      linear_combination (δ * (i : ℝ)) * huv
    refine ⟨hre, ?_, ?_⟩
    · rw [him]
      nlinarith
    · rw [him]
      nlinarith
  have hkey : ∀ (pS pN : ℤ × ℤ) (w : ℂ), pS ∈ S → pN ∉ S →
      w ∈ gridSquare δ pS → w ∈ gridSquare δ pN → w ∈ T' := by
    intro pS pN w hpS hpN hwS hwN
    rcases hSsub pS hpS hwS with hwT | hwA
    · exact hwT
    · exact absurd (by
        rw [hS_def, Finset.mem_filter]
        exact ⟨hbox pN ⟨w, hwN, hwA⟩, ⟨w, hwN, hwA⟩⟩) hpN
  have hET : ∀ e ∈ E, segment ℝ (gridPoint δ e.1) (gridPoint δ e.2) ⊆ T' := by
    intro e he w hw
    clear * - hEmem hbdry_def hseg_h hseg_v hkey hsq_mem hδ he hw
    rw [hEmem, hbdry_def] at he
    obtain ⟨⟨i, j⟩, ⟨k, l⟩⟩ := e
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨⟨hk, hl⟩, hs, hn⟩ | ⟨⟨hi, hj⟩, hs, hn⟩ |
      ⟨⟨hk, hl⟩, hs, hn⟩ | ⟨⟨hi, hj⟩, hs, hn⟩
    · -- rightward from (i,j) to (i+1,j): S-square (i,j) above, (i,j-1) below
      rw [hk, hl] at hw
      obtain ⟨him, hre1, hre2⟩ := hseg_h i j w hw
      refine hkey (i, j) (i, j - 1) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him]
        push_cast
        nlinarith
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him] <;> push_cast <;> nlinarith
    · -- leftward: from (i,j) = (k+1,l) to (k,l);
      -- S-square (k, l-1) below, (k, l) above
      rw [hi, hj, segment_symm] at hw
      obtain ⟨him, hre1, hre2⟩ := hseg_h k l w hw
      refine hkey (k, l - 1) (k, l) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him] <;> push_cast <;> nlinarith
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him]
        push_cast
        nlinarith
    · -- upward from (i,j) to (i,j+1): S-square (i-1,j) left, (i,j) right
      rw [hk, hl] at hw
      obtain ⟨hre, him1, him2⟩ := hseg_v i j w hw
      refine hkey (i - 1, j) (i, j) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre] <;> push_cast <;> nlinarith
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre]
        push_cast
        nlinarith
    · -- downward: from (i,j) = (k,l+1) to (k,l);
      -- S-square (k,l) right, (k-1,l) left
      rw [hi, hj, segment_symm] at hw
      obtain ⟨hre, him1, him2⟩ := hseg_v k l w hw
      refine hkey (k, l) (k - 1, l) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre]
        push_cast
        nlinarith
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre] <;> push_cast <;> nlinarith
  -- ================================================================
  -- STAGE 3: per-edge principal-logarithm increments.
  -- ================================================================
  -- For `q` off a closed segment, the endpoint ratio avoids `ℝ≤0`.
  have hslit : ∀ a b q : ℂ, (∀ w ∈ segment ℝ a b, q ≠ w) →
      (b - q) / (a - q) ∈ Complex.slitPlane := by
    intro a b q hoff
    clear * - hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr fun h => hoff a (left_mem_segment ℝ a b) h.symm
    by_contra hns
    rw [Complex.mem_slitPlane_iff] at hns
    push Not at hns
    obtain ⟨hre, him⟩ := hns
    set r : ℝ := ((b - q) / (a - q)).re with hr_def
    have hratio : (b - q) / (a - q) = ((r : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im]
        exact him
    have hbq : b - q = ((r : ℝ) : ℂ) * (a - q) := by
      rw [← hratio, div_mul_cancel₀ _ haq]
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have hqseg : q ∈ segment ℝ a b := by
      refine ⟨-r / (1 - r), 1 / (1 - r), div_nonneg (by linarith) h1r.le,
        by positivity, ?_, ?_⟩
      · field_simp
        ring
      · rw [Complex.real_smul, Complex.real_smul]
        push_cast
        have hcne : ((1 : ℂ) - (r : ℂ)) ≠ 0 := by
          have : ((1 - r : ℝ) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (ne_of_gt h1r)
          push_cast at this
          exact this
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          div_eq_iff hcne]
        linear_combination hbq
    exact hoff q hqseg rfl
  -- The per-edge increment.
  set inc : (ℤ × ℤ) × (ℤ × ℤ) → ℂ → ℂ := fun e q =>
    Complex.log ((gridPoint δ e.2 - q) / (gridPoint δ e.1 - q)) with hinc_def
  -- Reversal negates the increment.
  have hincrev : ∀ (a b : ℤ × ℤ) (q : ℂ),
      (∀ w ∈ segment ℝ (gridPoint δ a) (gridPoint δ b), q ≠ w) →
      gridPoint δ a ≠ gridPoint δ b →
      inc (b, a) q = -inc (a, b) q := by
    intro a b q hoff _hab
    clear * - hslit hinc_def hoff
    have hx : (gridPoint δ b - q) / (gridPoint δ a - q) ∈ Complex.slitPlane :=
      hslit _ _ q hoff
    have harg : ((gridPoint δ b - q) / (gridPoint δ a - q)).arg ≠ Real.pi :=
      Complex.slitPlane_arg_ne_pi hx
    simp only [hinc_def]
    have hswap : (gridPoint δ a - q) / (gridPoint δ b - q) =
        ((gridPoint δ b - q) / (gridPoint δ a - q))⁻¹ := (inv_div _ _).symm
    rw [hswap, Complex.log_inv _ harg]
  -- Lift gluing: `2πi · wind = Σ inc` over the consecutive pairs of a
  -- closed grid path avoiding `q` (explicit piecewise principal-log lift
  -- glued with accumulated constants; `windingNumber_spec` pins the value).
  -- Points of a parametrized segment lie in the segment.
  have hsegmem : ∀ (a b : ℂ) (s : unitInterval),
      segmentPath a b s ∈ segment ℝ a b := by
    intro a b s
    clear * -
    refine ⟨1 - (s : ℝ), (s : ℝ), by linarith [s.2.2], s.2.1, by ring, ?_⟩
    change (1 - (s : ℝ)) • a + (s : ℝ) • b = a + ((s : ℝ) : ℂ) * (b - a)
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  -- The principal-log lift along one segment avoided by `q`.
  have hseglift : ∀ a b q : ℂ, (∀ w ∈ segment ℝ a b, q ≠ w) →
      ∃ f : C(unitInterval, ℂ),
        (∀ s : unitInterval, Complex.exp (f s) = segmentPath a b s - q) ∧
        f 1 - f 0 = Complex.log ((b - q) / (a - q)) ∧
        Complex.exp (f 1) = b - q := by
    intro a b q hoff
    clear * - hslit hsegmem hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hoff a (left_mem_segment ℝ a b)))
    have hgmem : ∀ s : unitInterval,
        (segmentPath a b s - q) / (a - q) ∈ Complex.slitPlane := by
      intro s
      refine hslit a (segmentPath a b s) q ?_
      intro w hw
      exact hoff w ((convex_segment a b).segment_subset
        (left_mem_segment ℝ a b) (hsegmem a b s) hw)
    have hgcont : Continuous fun s : unitInterval =>
        (segmentPath a b s - q) / (a - q) :=
      ((segmentPath a b).continuous.sub continuous_const).div_const _
    have hfcont : Continuous fun s : unitInterval =>
        Complex.log ((segmentPath a b s - q) / (a - q)) +
          Complex.log (a - q) := by
      refine Continuous.add ?_ continuous_const
      rw [continuous_iff_continuousAt]
      intro s
      exact hgcont.continuousAt.clog (hgmem s)
    refine ⟨⟨fun s => Complex.log ((segmentPath a b s - q) / (a - q)) +
      Complex.log (a - q), hfcont⟩, ?_, ?_, ?_⟩
    · intro s
      change Complex.exp (Complex.log ((segmentPath a b s - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [Complex.exp_add, Complex.exp_log haq,
        Complex.exp_log (Complex.slitPlane_ne_zero (hgmem s)),
        div_mul_cancel₀ _ haq]
    · change (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) - (Complex.log ((segmentPath a b 0 - q) /
          (a - q)) + Complex.log (a - q)) = _
      rw [(segmentPath a b).source, (segmentPath a b).target,
        div_self haq, Complex.log_one]
      ring
    · change Complex.exp (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [(segmentPath a b).target, Complex.exp_add, Complex.exp_log haq]
      have hbq : b - q ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (hoff b (right_mem_segment ℝ a b)))
      rw [Complex.exp_log (by
        exact div_ne_zero hbq haq), div_mul_cancel₀ _ haq]
  -- The glued lift along a grid path, by induction on the path.
  have hliftInd : ∀ (Lst : List (ℤ × ℤ)) (p : ℤ × ℤ),
      IsGridPath (p :: Lst) →
      ∀ q : ℂ, (∀ w ∈ gridPathTrace δ (p :: Lst), q ≠ w) →
      ∃ Lf : C(unitInterval, ℂ),
        IsLogLiftOf Lf
          (shiftedCurve (gridPathRealize δ p Lst).toContinuousMap q) ∧
        Lf 1 - Lf 0 = (((p :: Lst).zip Lst).map (fun e => inc e q)).sum := by
    intro Lst
    clear * - hseglift
    induction Lst with
    | nil =>
      intro p _ q hoff
      have hqp : q ≠ gridPoint δ p := hoff _ rfl
      refine ⟨ContinuousMap.const unitInterval
        (Complex.log (gridPoint δ p - q)), ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        rw [Complex.exp_log (sub_ne_zero.mpr (Ne.symm hqp))]
        change gridPoint δ p - q = (Path.refl (gridPoint δ p)) t - q
        simp
      · simp
    | cons r M ih =>
      intro p hpath q hoff
      have htail : IsGridPath (r :: M) :=
        (List.isChain_cons_cons.mp hpath).2
      have hofftrace : ∀ w ∈ gridPathTrace δ (r :: M), q ≠ w :=
        fun w hw => hoff w (Or.inr hw)
      have hoffseg : ∀ w ∈ segment ℝ (gridPoint δ p) (gridPoint δ r),
          q ≠ w := fun w hw => hoff w (Or.inl hw)
      obtain ⟨Lrest, hLrest, hLrest_inc⟩ := ih r htail q hofftrace
      obtain ⟨fseg, hfseg_lift, hfseg_inc, hfseg1⟩ :=
        hseglift (gridPoint δ p) (gridPoint δ r) q hoffseg
      have hbq : gridPoint δ r - q ≠ 0 := by
        rw [← hfseg1]
        exact Complex.exp_ne_zero _
      -- the rest lift starts at the seam value `gridPoint δ r − q`
      have hLrest0 : Complex.exp (Lrest 0) = gridPoint δ r - q := by
        have h := hLrest 0
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] at h
        rw [h, (gridPathRealize δ r M).source]
      have hexpc : Complex.exp (fseg 1 - Lrest 0) = 1 := by
        rw [Complex.exp_sub, hfseg1, hLrest0, div_self hbq]
      have hstart : (Lrest + ContinuousMap.const unitInterval
          (fseg 1 - Lrest 0)) 0 = fseg 1 := by
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        ring
      have hLrest'_lift : ∀ t, Complex.exp ((Lrest +
          ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) t) =
          (gridPathRealize δ r M) t - q := by
        intro t
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [Complex.exp_add, hexpc, mul_one]
        have h := hLrest t
        simpa only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] using h
      refine ⟨((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
        (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
          hstart, rfl⟩ : Path (fseg 1) ((Lrest +
            ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
          ).toContinuousMap, ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        change Complex.exp _ =
          ((segmentPath (gridPoint δ p) (gridPoint δ r)).trans
            (gridPathRealize δ r M)) t - q
        rw [Path.trans_apply, Path.trans_apply]
        split_ifs with ht
        · exact hfseg_lift _
        · exact hLrest'_lift _
      · have h0 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 0 = fseg 0 := by simp
        have h1 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 1 = (Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1 := by
          simp
        rw [h0, h1]
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [List.zip_cons_cons, List.map_cons, List.sum_cons, ← hLrest_inc]
        have hincpr : inc (p, r) q =
            Complex.log ((gridPoint δ r - q) / (gridPoint δ p - q)) := rfl
        rw [hincpr, ← hfseg_inc]
        ring
  have hlift : ∀ (L : List (ℤ × ℤ)), IsGridPath L → L ≠ [] →
      L.head? = L.getLast? →
      ∀ q : ℂ, (∀ w ∈ gridPathTrace δ L, q ≠ w) →
      (2 * Real.pi * Complex.I) * windingNumber (gridLoopCurve δ L) q =
        ((L.zip L.tail).map (fun e => inc e q)).sum := by
    intro L hL hne hcl q hoff
    clear * - hliftInd hδ hL hne hcl hoff
    obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨Lf, hLf, hLf_inc⟩ := hliftInd L' p hL q hoff
    have hclosed : gridLoopCurve δ (p :: L') 0 = gridLoopCurve δ (p :: L') 1 :=
      gridLoopCurve_closed (by simp) hcl
    have hrange : Set.range (gridLoopCurve δ (p :: L')) =
        gridPathTrace δ (p :: L') := range_gridLoopCurve hδ hL (by simp)
    have hq : ∀ t : unitInterval, gridLoopCurve δ (p :: L') t ≠ q := by
      intro t heq
      exact hoff _ (hrange ▸ Set.mem_range_self t) heq.symm
    have hspec := windingNumber_spec hclosed hq hLf
    rw [← hspec]
    exact hLf_inc
  -- ================================================================
  -- STAGE 4: square-boundary windings.
  -- ================================================================
  -- The counterclockwise boundary 5-cycle of the square at `p`.
  set sqB : ℤ × ℤ → List (ℤ × ℤ) := fun p =>
    [p, (p.1 + 1, p.2), (p.1 + 1, p.2 + 1), (p.1, p.2 + 1), p] with hsqB_def
  have hsqB_path : ∀ p, IsGridPath (sqB p) := by
    intro p
    change List.IsChain GridAdj _
    simp only [hsqB_def]
    refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
      List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
        List.isChain_singleton _⟩⟩⟩⟩
    · exact Or.inr ⟨by simp, rfl⟩
    · exact Or.inl ⟨rfl, by simp⟩
    · exact Or.inr ⟨by simp, rfl⟩
    · exact Or.inl ⟨rfl, by simp⟩
  have hsqB_closed : ∀ p, (sqB p).head? = (sqB p).getLast? := by
    intro p
    simp [hsqB_def]
  -- Interior points have winding one (four increments with positive-
  -- imaginary-part cross ratios summing into `(0, 4π)` ∩ `2πℤ` = `{2π}`,
  -- pinned by the telescoping product `exp (Σ inc) = 1`).
  have hratio_im : ∀ z w : ℂ, w ≠ 0 →
      0 < z.im * w.re - z.re * w.im → 0 < (z / w).im := by
    intro z w hw hcross
    rw [Complex.div_im]
    have hnormSq : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
    rw [div_sub_div_same]
    exact div_pos hcross hnormSq
  have hlog_im_bounds : ∀ z : ℂ, z ≠ 0 → 0 < z.im →
      0 < (Complex.log z).im ∧ (Complex.log z).im < Real.pi := by
    intro z hz him
    rw [Complex.log_im]
    constructor
    · rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr him.le) with h | h
      · exact h
      · exfalso
        have h0 := Complex.arg_eq_zero_iff.mp h.symm
        · linarith [h0.2]
    · rcases lt_or_eq_of_le (Complex.arg_le_pi z) with h | h
      · exact h
      · exfalso
        have h0 := Complex.arg_eq_pi_iff.mp h
        linarith [h0.2]
  have hsq_in : ∀ p : ℤ × ℤ, ∀ q ∈ interior (gridSquare δ p),
      windingNumber (gridLoopCurve δ (sqB p)) q = 1 := by
    intro p q hqint
    clear * - hKint hseg_h hseg_v hsqB_def hgre hgim hlog_im_bounds
      hratio_im hlift hsqB_path hsqB_closed hδ hqint
    rw [hKint, Complex.mem_reProdIm] at hqint
    obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hqint
    -- `q` avoids the boundary trace (strict interior coordinates).
    have hqoff : ∀ w ∈ gridPathTrace δ (sqB p), q ≠ w := by
      intro w hw heq
      simp only [hsqB_def, gridPathTrace] at hw
      rcases hw with h | h | h | h | h
      · obtain ⟨him, -, -⟩ := hseg_h p.1 p.2 w h
        rw [← heq] at him
        linarith
      · obtain ⟨hre, -, -⟩ := hseg_v (p.1 + 1) p.2 w h
        rw [← heq] at hre
        push_cast at hre
        linarith
      · rw [segment_symm] at h
        obtain ⟨him, -, -⟩ := hseg_h p.1 (p.2 + 1) w h
        rw [← heq] at him
        push_cast at him
        linarith
      · rw [segment_symm] at h
        obtain ⟨hre, -, -⟩ := hseg_v p.1 p.2 w h
        rw [← heq] at hre
        linarith
      · have hwp : w = gridPoint δ p := h
        have hqim : q.im = δ * p.2 := by rw [heq, hwp, hgim]
        linarith
    -- corner points are on the trace, hence differ from `q`
    have hmem1 : gridPoint δ p ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inl (left_mem_segment ℝ _ _)
    have hmem2 : gridPoint δ (p.1 + 1, p.2) ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inr (Or.inl (left_mem_segment ℝ _ _))
    have hmem3 : gridPoint δ (p.1 + 1, p.2 + 1) ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inr (Or.inr (Or.inl (left_mem_segment ℝ _ _)))
    have hmem4 : gridPoint δ (p.1, p.2 + 1) ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inr (Or.inr (Or.inr (Or.inl (left_mem_segment ℝ _ _))))
    have hne1 : gridPoint δ p - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem1))
    have hne2 : gridPoint δ (p.1 + 1, p.2) - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem2))
    have hne3 : gridPoint δ (p.1 + 1, p.2 + 1) - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem3))
    have hne4 : gridPoint δ (p.1, p.2 + 1) - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem4))
    -- the four increments have imaginary parts in `(0, π)`
    have hb1 : 0 < (inc (p, (p.1 + 1, p.2)) q).im ∧
        (inc (p, (p.1 + 1, p.2)) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne2 hne1) (hratio_im _ _ hne1 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    have hb2 : 0 < (inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) q).im ∧
        (inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne3 hne2) (hratio_im _ _ hne2 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    have hb3 : 0 < (inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) q).im ∧
        (inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne4 hne3) (hratio_im _ _ hne3 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    have hb4 : 0 < (inc ((p.1, p.2 + 1), p) q).im ∧
        (inc ((p.1, p.2 + 1), p) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne1 hne4) (hratio_im _ _ hne4 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    -- pin the winding by the total imaginary part
    have hli := hlift (sqB p) (hsqB_path p) (by simp [hsqB_def])
      (hsqB_closed p) q hqoff
    have hzip : ((sqB p).zip (sqB p).tail).map (fun e => inc e q) =
        [inc (p, (p.1 + 1, p.2)) q,
         inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) q,
         inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) q,
         inc ((p.1, p.2 + 1), p) q] := by
      simp only [hsqB_def, List.tail_cons, List.zip_cons_cons,
        List.zip_nil_right, List.map_cons, List.map_nil]
    rw [hzip] at hli
    have hW := congrArg Complex.im hli
    simp only [List.sum_cons, List.sum_nil, add_zero, Complex.add_im] at hW
    set W : ℤ := windingNumber (gridLoopCurve δ (sqB p)) q with hW_def
    have hLim : ((2 * (Real.pi : ℂ) * Complex.I) * ((W : ℤ) : ℂ)).im =
        2 * Real.pi * (W : ℝ) := by
      have h : (2 * (Real.pi : ℂ) * Complex.I) * ((W : ℤ) : ℂ) =
          (((2 * Real.pi * (W : ℝ)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h]
      simp [Complex.mul_im]
    rw [hLim] at hW
    have hWpos : (0 : ℝ) < 2 * Real.pi * (W : ℝ) := by
      rw [hW]
      linarith [hb1.1, hb2.1, hb3.1, hb4.1]
    have hWlt : 2 * Real.pi * (W : ℝ) < 4 * Real.pi := by
      rw [hW]
      linarith [hb1.2, hb2.2, hb3.2, hb4.2]
    have hπ := Real.pi_pos
    have hW1 : (0 : ℝ) < (W : ℝ) := by nlinarith
    have hW2 : (W : ℝ) < 2 := by nlinarith
    have hW1' : (0 : ℤ) < W := by exact_mod_cast hW1
    have hW2' : W < 2 := by exact_mod_cast hW2
    omega
  -- The trace of the square boundary is contained in the closed square.
  have hsqB_trace : ∀ p : ℤ × ℤ,
      gridPathTrace δ (sqB p) ⊆ gridSquare δ p := by
    intro p w hw
    clear * - hsqB_def hseg_h hseg_v hsq_mem hgre hgim hδ hw
    simp only [hsqB_def, gridPathTrace] at hw
    rw [hsq_mem]
    rcases hw with h | h | h | h | h
    · obtain ⟨him, h1, h2⟩ := hseg_h p.1 p.2 w h
      refine ⟨⟨h1, h2⟩, ?_, ?_⟩ <;> rw [him]
      nlinarith
    · obtain ⟨hre, h1, h2⟩ := hseg_v (p.1 + 1) p.2 w (by
        convert h using 2)
      refine ⟨⟨?_, ?_⟩, h1, h2⟩ <;> rw [hre] <;> push_cast <;> nlinarith
    · rw [segment_symm] at h
      obtain ⟨him, h1, h2⟩ := hseg_h p.1 (p.2 + 1) w (by
        convert h using 2)
      refine ⟨⟨h1, h2⟩, ?_, ?_⟩ <;> rw [him] <;> push_cast <;> nlinarith
    · rw [segment_symm] at h
      obtain ⟨hre, h1, h2⟩ := hseg_v p.1 p.2 w h
      refine ⟨⟨?_, ?_⟩, h1, h2⟩ <;> rw [hre]
      nlinarith
    · have hwp : w = gridPoint δ p := h
      rw [hwp]
      rw [hgre, hgim]  -- rewrites inside the goal via hsq_mem shape
      refine ⟨⟨le_refl _, ?_⟩, le_refl _, ?_⟩ <;> nlinarith
  -- Center coordinates of a square.
  have hcen_re : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).re = δ * p.1 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_re, hgre]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have : ((δ : ℂ) / 2 * (1 + Complex.I)).re = δ / 2 := by
      rw [hh]
      simp [Complex.mul_re]
    rw [this]
  have hcen_im : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).im = δ * p.2 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_im, hgim]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have : ((δ : ℂ) / 2 * (1 + Complex.I)).im = δ / 2 := by
      rw [hh]
      simp [Complex.mul_im]
    rw [this]
  have hcen_mem : ∀ p : ℤ × ℤ, gridSquareCenter δ p ∈ gridSquare δ p := by
    intro p
    rw [hsq_mem, hcen_re, hcen_im]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  -- Points outside the closed square have winding zero.
  have hsq_out : ∀ p : ℤ × ℤ, ∀ q : ℂ, q ∉ gridSquare δ p →
      windingNumber (gridLoopCurve δ (sqB p)) q = 0 := by
    intro p q hq
    clear * - hsqB_def hsqB_closed hsqB_path hsq_mem hδ hsq_diam
      hcen_mem hcen_re hsqB_trace hq
    have hclosed : gridLoopCurve δ (sqB p) 0 = gridLoopCurve δ (sqB p) 1 :=
      gridLoopCurve_closed (by simp [hsqB_def]) (hsqB_closed p)
    have hrange : Set.range (gridLoopCurve δ (sqB p)) =
        gridPathTrace δ (sqB p) :=
      range_gridLoopCurve hδ (hsqB_path p) (by simp [hsqB_def])
    -- The four open half-planes forming the complement of the square,
    -- grouped as two path-connected corner pairs.
    set U : Set ℂ :=
      ({z : ℂ | z.re < δ * p.1} ∪ {z : ℂ | z.im < δ * p.2}) ∪
      ({z : ℂ | δ * (p.1 + 1) < z.re} ∪ {z : ℂ | δ * (p.2 + 1) < z.im})
      with hU_def
    have hqU : q ∈ U := by
      by_contra hqn
      rw [hU_def] at hqn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hqn
      exact hq ((hsq_mem p q).mpr ⟨⟨hqn.1.1, hqn.2.1⟩, hqn.1.2, hqn.2.2⟩)
    have hdisjU : ∀ z ∈ U, z ∉ gridSquare δ p := by
      intro z hz hzsq
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hsq_mem p z).mp hzsq
      rw [hU_def] at hz
      simp only [Set.mem_union, Set.mem_ofPred_eq] at hz
      rcases hz with (h | h) | h | h <;> linarith
    -- A far reference point in `U`.
    set qf : ℂ := ((δ * p.1 - 3 * δ : ℝ) : ℂ) +
      ((δ * p.2 : ℝ) : ℂ) * Complex.I with hqf_def
    have hqf_re : qf.re = δ * p.1 - 3 * δ := by
      simp [hqf_def]
    have hqfU : qf ∈ U := by
      rw [hU_def]
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      left; left
      rw [hqf_re]
      linarith
    -- `U` is path-connected, hence preconnected.
    have hUconn : IsPreconnected U := by
      have hpc1 : IsPathConnected {z : ℂ | z.re < δ * p.1} := by
        refine (convex_halfSpace_lt (.mk Complex.add_re Complex.smul_re)
          _).isPathConnected ⟨((δ * p.1 - 1 : ℝ) : ℂ), ?_⟩
        simp [Set.mem_ofPred_eq]
      have hpc2 : IsPathConnected {z : ℂ | δ * (p.1 + 1) < z.re} := by
        refine (convex_halfSpace_gt (.mk Complex.add_re Complex.smul_re)
          _).isPathConnected ⟨((δ * (p.1 + 1) + 1 : ℝ) : ℂ), ?_⟩
        simp [Set.mem_ofPred_eq]
      have hpc3 : IsPathConnected {z : ℂ | z.im < δ * p.2} := by
        refine (convex_halfSpace_lt (.mk Complex.add_im Complex.smul_im)
          _).isPathConnected ⟨((δ * p.2 - 1 : ℝ) : ℂ) * Complex.I, ?_⟩
        simp [Set.mem_ofPred_eq]
      have hpc4 : IsPathConnected {z : ℂ | δ * (p.2 + 1) < z.im} := by
        refine (convex_halfSpace_gt (.mk Complex.add_im Complex.smul_im)
          _).isPathConnected ⟨((δ * (p.2 + 1) + 1 : ℝ) : ℂ) * Complex.I, ?_⟩
        simp [Set.mem_ofPred_eq]
      -- below-left corner joins piece 1 and piece 3
      have h13 : IsPathConnected
          ({z : ℂ | z.re < δ * p.1} ∪ {z : ℂ | z.im < δ * p.2}) := by
        refine hpc1.union hpc3
          ⟨((δ * p.1 - 1 : ℝ) : ℂ) + ((δ * p.2 - 1 : ℝ) : ℂ) * Complex.I,
            ?_, ?_⟩ <;> simp [Set.mem_ofPred_eq]
      -- above-right corner joins piece 2 and piece 4
      have h24 : IsPathConnected
          ({z : ℂ | δ * (p.1 + 1) < z.re} ∪
            {z : ℂ | δ * (p.2 + 1) < z.im}) := by
        refine hpc2.union hpc4
          ⟨((δ * (p.1 + 1) + 1 : ℝ) : ℂ) +
            ((δ * (p.2 + 1) + 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩ <;>
          simp [Set.mem_ofPred_eq]
      -- below-right corner joins the two pairs (below piece ∋ it, right
      -- piece ∋ it)
      have hU : IsPathConnected U := by
        rw [hU_def]
        refine h13.union h24
          ⟨((δ * (p.1 + 1) + 1 : ℝ) : ℂ) +
            ((δ * p.2 - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
        · right
          simp [Set.mem_ofPred_eq]
        · left
          simp [Set.mem_ofPred_eq]
      exact hU.isConnected.isPreconnected
    -- Winding at the far point is zero: trace inside a ball missing `qf`.
    have htrace_ball : ∀ t : unitInterval, gridLoopCurve δ (sqB p) t ∈
        Metric.ball (gridSquareCenter δ p) (3 * δ) := by
      intro t
      have hmem : gridLoopCurve δ (sqB p) t ∈ gridPathTrace δ (sqB p) := by
        rw [← hrange]
        exact Set.mem_range_self t
      have hd := hsq_diam p _ _ (hsqB_trace p hmem) (hcen_mem p)
      rw [Metric.mem_ball]
      linarith
    have hqf_far : qf ∉ Metric.ball (gridSquareCenter δ p) (3 * δ) := by
      rw [Metric.mem_ball, not_lt, dist_eq_norm]
      have h1 : |(qf - gridSquareCenter δ p).re| ≤
          ‖qf - gridSquareCenter δ p‖ := Complex.abs_re_le_norm _
      have h2 : (qf - gridSquareCenter δ p).re = -(3 * δ) - δ / 2 := by
        rw [Complex.sub_re, hqf_re, hcen_re]
        ring
      rw [h2] at h1
      have h3 : |(-(3 * δ) - δ / 2)| = 3 * δ + δ / 2 := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [h3] at h1
      linarith
    have hqf_wind : windingNumber (gridLoopCurve δ (sqB p)) qf = 0 :=
      windingNumber_eq_zero_of_ball hclosed htrace_ball hqf_far
    rw [← hqf_wind]
    exact windingNumber_eq_of_preconnected hclosed hUconn
      (fun t hmem => hdisjU _ hmem (hsqB_trace p (by
        rw [← hrange]; exact Set.mem_range_self t))) hqU hqfU
  -- ================================================================
  -- STAGE 5: cancellation — summing the square boundaries over `S`
  -- leaves exactly the `E`-edge increments.
  -- ================================================================
  -- Distinct adjacent grid points.
  have hgp_ne_h : ∀ v : ℤ × ℤ, gridPoint δ v ≠ gridPoint δ (v.1 + 1, v.2) := by
    intro v h
    clear * - hgre hδ h
    have h' := congrArg Complex.re h
    rw [hgre, hgre] at h'
    push_cast at h'
    nlinarith
  have hgp_ne_v : ∀ v : ℤ × ℤ, gridPoint δ v ≠ gridPoint δ (v.1, v.2 + 1) := by
    intro v h
    clear * - hgim hδ h
    have h' := congrArg Complex.im h
    rw [hgim, hgim] at h'
    push_cast at h'
    nlinarith
  -- Reversal identities for the two edge directions at `c₀`.
  have hRrev : ∀ v : ℤ × ℤ,
      inc ((v.1 + 1, v.2), v) c₀ = -inc (v, (v.1 + 1, v.2)) c₀ :=
    fun v => hincrev v (v.1 + 1, v.2) c₀ (hc₀line v) (hgp_ne_h v)
  have hUrev : ∀ v : ℤ × ℤ,
      inc ((v.1, v.2 + 1), v) c₀ = -inc (v, (v.1, v.2 + 1)) c₀ :=
    fun v => hincrev v (v.1, v.2 + 1) c₀ (hc₀line' v) (hgp_ne_v v)
  -- The square-boundary increment sum, reorganized into oriented
  -- rightward/upward edge contributions with signs.
  have hsq_rw : ∀ p : ℤ × ℤ,
      (((sqB p).zip (sqB p).tail).map (fun e => inc e c₀)).sum =
        (inc (p, (p.1 + 1, p.2)) c₀ -
          inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀) +
        (inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀ -
          inc (p, (p.1, p.2 + 1)) c₀) := by
    intro p
    clear * - hsqB_def hincrev hc₀line hc₀line' hgp_ne_h hgp_ne_v
    have hzip : ((sqB p).zip (sqB p).tail).map (fun e => inc e c₀) =
        [inc (p, (p.1 + 1, p.2)) c₀,
         inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀,
         inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) c₀,
         inc ((p.1, p.2 + 1), p) c₀] := by
      simp only [hsqB_def, List.tail_cons, List.zip_cons_cons,
        List.zip_nil_right, List.map_cons, List.map_nil]
    rw [hzip]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    have h3 : inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) c₀ =
        -inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀ :=
      hincrev (p.1, p.2 + 1) (p.1 + 1, p.2 + 1) c₀
        (hc₀line (p.1, p.2 + 1)) (hgp_ne_h (p.1, p.2 + 1))
    have h4 : inc ((p.1, p.2 + 1), p) c₀ = -inc (p, (p.1, p.2 + 1)) c₀ :=
      hincrev p (p.1, p.2 + 1) c₀ (hc₀line' p) (hgp_ne_v p)
    rw [h3, h4]
    ring
  -- Assemble the left side into four plain sums over `S`.
  have hLHS : (S.sum fun p => ((( sqB p).zip (sqB p).tail).map
      (fun e => inc e c₀)).sum) =
      ((S.sum fun p => inc (p, (p.1 + 1, p.2)) c₀) -
        (S.sum fun p => inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀)) +
      ((S.sum fun p => inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀) -
        (S.sum fun p => inc (p, (p.1, p.2 + 1)) c₀)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => hsq_rw p)
  -- Shifted-image membership characterizations.
  have himgUp : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1, p.2 + 1)) ↔ (v.1, v.2 - 1) ∈ S := by
    intro v
    clear * -
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have hp1 : p.1 = v.1 ∧ p.2 + 1 = v.2 := Prod.mk.injEq .. ▸ Prod.ext_iff.mp heq
      have : p = (v.1, v.2 - 1) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← this]
      exact hp
    · intro h
      exact ⟨(v.1, v.2 - 1), h, Prod.ext_iff.mpr ⟨rfl, by omega⟩⟩
  have himgRt : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1 + 1, p.2)) ↔ (v.1 - 1, v.2) ∈ S := by
    intro v
    clear * -
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have hp1 : p.1 + 1 = v.1 ∧ p.2 = v.2 := Prod.mk.injEq .. ▸ Prod.ext_iff.mp heq
      have : p = (v.1 - 1, v.2) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← this]
      exact hp
    · intro h
      exact ⟨(v.1 - 1, v.2), h, Prod.ext_iff.mpr ⟨by omega, rfl⟩⟩
  -- Reindex the shifted sums over the image Finsets.
  have hreidxUp : (S.sum fun p => inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀) =
      ((S.image fun p => (p.1, p.2 + 1)).sum
        fun v => inc (v, (v.1 + 1, v.2)) c₀) := by
    rw [Finset.sum_image (fun x _ y _ h => by
      have := Prod.ext_iff.mp h
      exact Prod.ext_iff.mpr ⟨this.1, by omega⟩)]
  have hreidxRt : (S.sum fun p => inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀) =
      ((S.image fun p => (p.1 + 1, p.2)).sum
        fun v => inc (v, (v.1, v.2 + 1)) c₀) := by
    rw [Finset.sum_image (fun x _ y _ h => by
      have := Prod.ext_iff.mp h
      exact Prod.ext_iff.mpr ⟨by omega, this.2⟩)]
  -- Difference-of-sums splitting helper.
  have hsplit : ∀ (s t : Finset (ℤ × ℤ)) (g : ℤ × ℤ → ℂ),
      s.sum g - t.sum g = (s.filter (fun v => v ∉ t)).sum g -
        (t.filter (fun v => v ∉ s)).sum g := by
    intro s t g
    clear * -
    have hs := Finset.sum_filter_add_sum_filter_not s (fun v => v ∈ t) g
    have ht := Finset.sum_filter_add_sum_filter_not t (fun v => v ∈ s) g
    have hst : s.filter (fun v => v ∈ t) = t.filter (fun v => v ∈ s) := by
      ext v
      simp only [Finset.mem_filter]
      exact and_comm
    rw [← hs, ← ht, hst]
    ring
  have hcancel :
      (S.sum fun p => ((( sqB p).zip (sqB p).tail).map
          (fun e => inc e c₀)).sum) =
        E.sum (fun e => inc e c₀) := by
    clear * - hEmem hbdry_def himgUp himgRt hreidxUp hreidxRt hsplit hLHS
      hRrev hUrev
    -- Four classes of boundary edges, indexed by lattice vertices.
    set HR : Finset (ℤ × ℤ) :=
      S.filter (fun v => v ∉ S.image (fun p => (p.1, p.2 + 1))) with hHR_def
    set HL : Finset (ℤ × ℤ) :=
      (S.image (fun p => (p.1, p.2 + 1))).filter (fun v => v ∉ S) with hHL_def
    set VU : Finset (ℤ × ℤ) :=
      (S.image (fun p => (p.1 + 1, p.2))).filter (fun v => v ∉ S) with hVU_def
    set VD : Finset (ℤ × ℤ) :=
      S.filter (fun v => v ∉ S.image (fun p => (p.1 + 1, p.2))) with hVD_def
    -- `E` is the disjoint union of the four edge images.
    have hE_eq : E = ((HR.image (fun v => (v, (v.1 + 1, v.2))) ∪
        HL.image (fun v => ((v.1 + 1, v.2), v))) ∪
        VU.image (fun v => (v, (v.1, v.2 + 1)))) ∪
        VD.image (fun v => ((v.1, v.2 + 1), v)) := by
      ext e
      rw [hEmem, hbdry_def]
      simp only [Finset.mem_union, Finset.mem_image, hHR_def, hHL_def,
        hVU_def, hVD_def, Finset.mem_filter, himgUp, himgRt]
      constructor
      · rintro (⟨he2, hs, hn⟩ | ⟨he1, hs, hn⟩ | ⟨he2, hs, hn⟩ | ⟨he1, hs, hn⟩)
        · refine Or.inl (Or.inl (Or.inl ⟨e.1, ⟨hs, ?_⟩, ?_⟩))
          · simpa using hn
          · rw [← he2]
        · refine Or.inl (Or.inl (Or.inr ⟨e.2, ⟨by simpa using hs,
            by simpa using hn⟩, ?_⟩))
          exact Prod.ext_iff.mpr ⟨he1.symm, rfl⟩
        · refine Or.inl (Or.inr ⟨e.1, ⟨by simpa using hs,
            by simpa using hn⟩, ?_⟩)
          rw [← he2]
        · refine Or.inr ⟨e.2, ⟨by simpa using hs, ?_⟩, ?_⟩
          · simpa using hn
          · exact Prod.ext_iff.mpr ⟨he1.symm, rfl⟩
      · rintro (((⟨v, ⟨hvS, hvn⟩, rfl⟩ | ⟨v, ⟨hvS, hvn⟩, rfl⟩) |
          ⟨v, ⟨hvS, hvn⟩, rfl⟩) | ⟨v, ⟨hvS, hvn⟩, rfl⟩)
        · exact Or.inl ⟨rfl, hvS, by simpa using hvn⟩
        · refine Or.inr (Or.inl ⟨rfl, ?_, ?_⟩) <;> simpa
        · refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)) <;> simpa
        · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)) <;> simpa
    -- Pairwise disjointness of the four images.
    have hd12 : Disjoint (HR.image (fun v => (v, (v.1 + 1, v.2))))
        (HL.image (fun v => ((v.1 + 1, v.2), v))) := by
      rw [Finset.disjoint_left]
      rintro e he1 he2
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp he1
      obtain ⟨w, -, hw⟩ := Finset.mem_image.mp he2
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hw
      obtain ⟨h11, -⟩ := Prod.ext_iff.mp h1
      obtain ⟨h21, -⟩ := Prod.ext_iff.mp h2
      simp only at h11 h21
      omega
    have hd3 : Disjoint (HR.image (fun v => (v, (v.1 + 1, v.2))) ∪
        HL.image (fun v => ((v.1 + 1, v.2), v)))
        (VU.image (fun v => (v, (v.1, v.2 + 1)))) := by
      rw [Finset.disjoint_left]
      rintro e he1 he2
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp he2
      rw [Finset.mem_union] at he1
      rcases he1 with h | h
      · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hv
        obtain ⟨h11, h12⟩ := Prod.ext_iff.mp h1
        obtain ⟨h21, h22⟩ := Prod.ext_iff.mp h2
        simp only at h11 h12 h21 h22
        omega
      · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hv
        obtain ⟨h11, h12⟩ := Prod.ext_iff.mp h1
        obtain ⟨h21, h22⟩ := Prod.ext_iff.mp h2
        simp only at h11 h12 h21 h22
        omega
    have hd4 : Disjoint ((HR.image (fun v => (v, (v.1 + 1, v.2))) ∪
        HL.image (fun v => ((v.1 + 1, v.2), v))) ∪
        VU.image (fun v => (v, (v.1, v.2 + 1))))
        (VD.image (fun v => ((v.1, v.2 + 1), v))) := by
      rw [Finset.disjoint_left]
      rintro e he1 he2
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp he2
      rw [Finset.mem_union, Finset.mem_union] at he1
      rcases he1 with (h | h) | h <;>
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp h <;>
        · obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hv
          obtain ⟨h11, h12⟩ := Prod.ext_iff.mp h1
          obtain ⟨h21, h22⟩ := Prod.ext_iff.mp h2
          simp only at h11 h12 h21 h22
          omega
    -- Sums over the four images.
    have hinj1 : ∀ x ∈ HR, ∀ y ∈ HR,
        (x, (x.1 + 1, x.2)) = (y, (y.1 + 1, y.2)) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).1
    have hinj2 : ∀ x ∈ HL, ∀ y ∈ HL,
        ((x.1 + 1, x.2), x) = ((y.1 + 1, y.2), y) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).2
    have hinj3 : ∀ x ∈ VU, ∀ y ∈ VU,
        (x, (x.1, x.2 + 1)) = (y, (y.1, y.2 + 1)) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).1
    have hinj4 : ∀ x ∈ VD, ∀ y ∈ VD,
        ((x.1, x.2 + 1), x) = ((y.1, y.2 + 1), y) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).2
    have hs1 : (HR.image (fun v => (v, (v.1 + 1, v.2)))).sum
        (fun e => inc e c₀) = HR.sum (fun v => inc (v, (v.1 + 1, v.2)) c₀) :=
      Finset.sum_image hinj1
    have hs2 : (HL.image (fun v => ((v.1 + 1, v.2), v))).sum
        (fun e => inc e c₀) =
        -(HL.sum (fun v => inc (v, (v.1 + 1, v.2)) c₀)) := by
      rw [Finset.sum_image hinj2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun v _ => hRrev v)
    have hs3 : (VU.image (fun v => (v, (v.1, v.2 + 1)))).sum
        (fun e => inc e c₀) = VU.sum (fun v => inc (v, (v.1, v.2 + 1)) c₀) :=
      Finset.sum_image hinj3
    have hs4 : (VD.image (fun v => ((v.1, v.2 + 1), v))).sum
        (fun e => inc e c₀) =
        -(VD.sum (fun v => inc (v, (v.1, v.2 + 1)) c₀)) := by
      rw [Finset.sum_image hinj4, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun v _ => hUrev v)
    -- Assemble.
    rw [hLHS, hreidxUp, hreidxRt, hE_eq,
      Finset.sum_union hd4, Finset.sum_union hd3, Finset.sum_union hd12,
      hs1, hs2, hs3, hs4,
      hsplit S (S.image (fun p => (p.1, p.2 + 1)))
        (fun v => inc (v, (v.1 + 1, v.2)) c₀),
      hsplit (S.image (fun p => (p.1 + 1, p.2))) S
        (fun v => inc (v, (v.1, v.2 + 1)) c₀)]
    simp only [← hHR_def, ← hHL_def, ← hVU_def, ← hVD_def]
    ring
  -- The left side equals `2πi` (exactly the `(0,0)` square contributes).
  -- First: `c₀` avoids every square-boundary trace (it is off grid lines).
  have hc₀offsq : ∀ p : ℤ × ℤ, ∀ w ∈ gridPathTrace δ (sqB p), c₀ ≠ w := by
    intro p w hw heq
    clear * - hsqB_def hseg_h hseg_v hcim hcre hhalf_ne hgim hw heq
    simp only [hsqB_def, gridPathTrace] at hw
    rcases hw with h | h | h | h | h
    · obtain ⟨him, -, -⟩ := hseg_h p.1 p.2 w h
      rw [← heq, hcim] at him
      exact hhalf_ne p.2 him
    · obtain ⟨hre, -, -⟩ := hseg_v (p.1 + 1) p.2 w h
      rw [← heq, hcre] at hre
      exact hhalf_ne (p.1 + 1) (by push_cast at hre ⊢; linarith)
    · rw [segment_symm] at h
      obtain ⟨him, -, -⟩ := hseg_h p.1 (p.2 + 1) w h
      rw [← heq, hcim] at him
      exact hhalf_ne (p.2 + 1) (by push_cast at him ⊢; linarith)
    · rw [segment_symm] at h
      obtain ⟨hre, -, -⟩ := hseg_v p.1 p.2 w h
      rw [← heq, hcre] at hre
      exact hhalf_ne p.1 hre
    · have hwp : w = gridPoint δ p := h
      have him : c₀.im = δ * p.2 := by rw [heq, hwp, hgim]
      rw [hcim] at him
      exact hhalf_ne p.2 him
  -- per-square increment sums via the lift identity
  have hsq_sum : ∀ p : ℤ × ℤ,
      (((sqB p).zip (sqB p).tail).map (fun e => inc e c₀)).sum =
        (2 * Real.pi * Complex.I) *
          (windingNumber (gridLoopCurve δ (sqB p)) c₀ : ℤ) := by
    intro p
    clear * - hlift hsqB_path hsqB_closed hsqB_def hc₀offsq
    rw [← hlift (sqB p) (hsqB_path p) (by simp [hsqB_def]) (hsqB_closed p)
      c₀ (hc₀offsq p)]
  have hsum_sq :
      (S.sum fun p => ((( sqB p).zip (sqB p).tail).map
          (fun e => inc e c₀)).sum) = 2 * Real.pi * Complex.I := by
    clear * - hsq_sum hsq_in hsq_out hc₀in hc₀only h00
    rw [Finset.sum_eq_single (0, 0)]
    · rw [hsq_sum (0, 0), hsq_in (0, 0) c₀ hc₀in]
      simp
    · intro p _ hp
      rw [hsq_sum p, hsq_out p c₀ (hc₀only p hp)]
      simp
    · intro h00'
      exact absurd h00 h00'
  -- ================================================================
  -- STAGE 6: cycle extraction and the essential cycle.
  -- ================================================================
  -- The balanced edge set decomposes into edge-disjoint closed grid
  -- cycles exhausting `E` (strong induction on `E.card`).
  -- Edges of `E` join distinct adjacent lattice points.
  have hEadj : ∀ e ∈ E, GridAdj e.1 e.2 := by
    intro e he
    clear * - hEmem hbdry_def he
    rw [hEmem, hbdry_def] at he
    rcases he with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  have hE_ne : ∀ e ∈ E, e.1 ≠ e.2 := by
    intro e he heq
    clear * - hEmem hbdry_def he heq
    rw [hEmem, hbdry_def] at he
    obtain ⟨hq1, hq2⟩ := Prod.ext_iff.mp heq
    rcases he with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h <;> omega
  -- Lists whose consecutive pairs are `E`-edges are grid paths.
  have hpathE : ∀ L : List (ℤ × ℤ),
      (∀ e ∈ L.zip L.tail, e ∈ E) → IsGridPath L := by
    clear * - hEadj
    intro L
    induction L with
    | nil => intro _; exact List.isChain_nil
    | cons a M ih =>
      intro hedges
      cases M with
      | nil => exact List.isChain_singleton _
      | cons b M' =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih ?_⟩
        · exact hEadj (a, b) (hedges (a, b) (List.mem_cons_self))
        · intro e he
          refine hedges e (List.mem_cons_of_mem _ ?_)
          exact he
  -- Nodup edge lists sum like their finsets.
  have hsum_nodup : ∀ ℓ : List ((ℤ × ℤ) × (ℤ × ℤ)), ℓ.Nodup →
      (ℓ.map (fun e => inc e c₀)).sum =
        ℓ.toFinset.sum (fun e => inc e c₀) := by
    clear * -
    intro ℓ
    induction ℓ with
    | nil => intro _; simp
    | cons e ℓ ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.sum_cons, List.toFinset_cons,
        Finset.sum_insert (by rw [List.mem_toFinset]; exact hnd.1), ih hnd.2]
  -- Degree bookkeeping under `erase`.
  have hdegInErase : ∀ (R : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (x y : ℤ × ℤ),
      (x, y) ∈ R → ∀ w : ℤ × ℤ,
      (R.filter (fun e => e.2 = w)).card =
        ((R.erase (x, y)).filter (fun e => e.2 = w)).card +
          (if w = y then 1 else 0) := by
    intro R x y hxy w
    clear * - hxy
    rw [Finset.filter_erase]
    by_cases h : w = y
    · subst h
      have hmem : (x, w) ∈ R.filter (fun e => e.2 = w) :=
        Finset.mem_filter.mpr ⟨hxy, rfl⟩
      rw [ite_eq_left rfl, Finset.card_erase_of_mem hmem]
      have hpos : 1 ≤ (R.filter (fun e => e.2 = w)).card :=
        Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · have hnot : (x, y) ∉ R.filter (fun e => e.2 = w) := by
        intro hmem
        rw [Finset.mem_filter] at hmem
        exact h hmem.2.symm
      rw [ite_eq_right h, add_zero, Finset.erase_eq_of_notMem hnot]
  have hdegOutErase : ∀ (R : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (x y : ℤ × ℤ),
      (x, y) ∈ R → ∀ w : ℤ × ℤ,
      (R.filter (fun e => e.1 = w)).card =
        ((R.erase (x, y)).filter (fun e => e.1 = w)).card +
          (if w = x then 1 else 0) := by
    intro R x y hxy w
    clear * - hxy
    rw [Finset.filter_erase]
    by_cases h : w = x
    · subst h
      have hmem : (w, y) ∈ R.filter (fun e => e.1 = w) :=
        Finset.mem_filter.mpr ⟨hxy, rfl⟩
      rw [ite_eq_left rfl, Finset.card_erase_of_mem hmem]
      have hpos : 1 ≤ (R.filter (fun e => e.1 = w)).card :=
        Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · have hnot : (x, y) ∉ R.filter (fun e => e.1 = w) := by
        intro hmem
        rw [Finset.mem_filter] at hmem
        exact h hmem.2.symm
      rw [ite_eq_right h, add_zero, Finset.erase_eq_of_notMem hnot]
  -- Trail extraction: from an imbalance `+1 at v, −1 at v₀`, walk from `v`
  -- back to `v₀` along unused edges.
  have hTRAIL : ∀ n : ℕ, ∀ (R : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (v₀ v : ℤ × ℤ),
      R.card ≤ n → R ⊆ E → v ≠ v₀ →
      (∀ w, (R.filter (fun e => e.2 = w)).card + (if w = v then 1 else 0) =
        (R.filter (fun e => e.1 = w)).card + (if w = v₀ then 1 else 0)) →
      ∃ M : List (ℤ × ℤ),
        (v :: M).getLast? = some v₀ ∧
        ((v :: M).zip M).Nodup ∧
        (∀ e ∈ (v :: M).zip M, e ∈ R) ∧
        (∀ w, ((R \ ((v :: M).zip M).toFinset).filter
            (fun e => e.2 = w)).card =
          ((R \ ((v :: M).zip M).toFinset).filter
            (fun e => e.1 = w)).card) := by
    clear * - hdegInErase hdegOutErase
    intro n
    induction n with
    | zero =>
      intro R v₀ v hcard hRE hne hinv
      exfalso
      have hR : R = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have h := hinv v
      rw [hR, ite_eq_left rfl, ite_eq_right hne] at h
      simp only [Finset.filter_empty, Finset.card_empty] at h
      omega
    | succ n ih =>
      intro R v₀ v hcard hRE hne hinv
      have h := hinv v
      rw [ite_eq_left rfl, ite_eq_right hne] at h
      have hpos : 0 < (R.filter (fun e => e.1 = v)).card := by omega
      obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at he
      obtain ⟨heR, he1⟩ := he
      obtain ⟨ea, eb⟩ := e
      have hea : v = ea := he1.symm
      subst hea
      have hcard' : (R.erase (v, eb)).card ≤ n := by
        have h1 := Finset.card_erase_of_mem heR
        have h2 : 1 ≤ R.card := Finset.card_pos.mpr ⟨_, heR⟩
        omega
      have hinv' : ∀ w, ((R.erase (v, eb)).filter
          (fun e => e.2 = w)).card + (if w = eb then 1 else 0) =
          ((R.erase (v, eb)).filter (fun e => e.1 = w)).card +
            (if w = v₀ then 1 else 0) := by
        intro w
        have h0 := hinv w
        rw [hdegInErase R v eb heR w, hdegOutErase R v eb heR w] at h0
        split_ifs at h0 ⊢ <;> omega
      by_cases heb : eb = v₀
      · have heb' : v₀ = eb := heb.symm
        subst heb'
        refine ⟨[v₀], by simp, by simp, ?_, ?_⟩
        · intro e he
          have hz : (v :: [v₀]).zip [v₀] = [(v, v₀)] := rfl
          rw [hz, List.mem_singleton] at he
          rw [he]
          exact heR
        · intro w
          have hz : ((v :: [v₀]).zip [v₀]).toFinset = {(v, v₀)} := by
            rfl
          rw [hz, Finset.sdiff_singleton_eq_erase]
          have h0 := hinv' w
          split_ifs at h0 <;> omega
      · have hR'E : R.erase (v, eb) ⊆ E :=
          (Finset.erase_subset _ _).trans hRE
        obtain ⟨M', hlast', hnodup', hmem', hbal'⟩ :=
          ih (R.erase (v, eb)) v₀ eb hcard' hR'E heb hinv'
        have hz : (v :: eb :: M').zip (eb :: M') =
            (v, eb) :: ((eb :: M').zip M') := rfl
        refine ⟨eb :: M', ?_, ?_, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]
          exact hlast'
        · rw [hz, List.nodup_cons]
          refine ⟨?_, hnodup'⟩
          intro hmem
          exact Finset.notMem_erase _ _ (hmem' _ hmem)
        · intro e he
          rw [hz] at he
          rcases List.mem_cons.mp he with rfl | he'
          · exact heR
          · exact Finset.mem_of_mem_erase (hmem' _ he')
        · intro w
          have hset : R \ ((v :: eb :: M').zip (eb :: M')).toFinset =
              (R.erase (v, eb)) \ ((eb :: M').zip M').toFinset := by
            rw [hz, List.toFinset_cons]
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert,
              Finset.mem_erase, List.mem_toFinset]
            constructor
            · rintro ⟨hxR, hxn⟩
              push Not at hxn
              exact ⟨⟨hxn.1, hxR⟩, hxn.2⟩
            · rintro ⟨⟨hx1, hxR⟩, hx2⟩
              refine ⟨hxR, ?_⟩
              push Not
              exact ⟨hx1, hx2⟩
          rw [hset]
          exact hbal' w
  -- Full decomposition by strong induction on the number of edges.
  have hMAIN : ∀ n : ℕ, ∀ F : Finset ((ℤ × ℤ) × (ℤ × ℤ)),
      F.card ≤ n → F ⊆ E →
      (∀ w, (F.filter (fun e => e.2 = w)).card =
        (F.filter (fun e => e.1 = w)).card) →
      ∃ cycles : List (List (ℤ × ℤ)),
        (∀ C ∈ cycles, IsGridPath C ∧ C ≠ [] ∧ C.head? = C.getLast? ∧
          ∀ e ∈ C.zip C.tail, e ∈ E) ∧
        ((cycles.map fun C =>
          ((C.zip C.tail).map (fun e => inc e c₀)).sum).sum
          = F.sum (fun e => inc e c₀)) := by
    clear * - hTRAIL hE_ne hpathE hsum_nodup hdegInErase hdegOutErase
    intro n
    induction n with
    | zero =>
      intro F hcard _ _
      have hF : F = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hF
      exact ⟨[], by simp, by simp⟩
    | succ n ih =>
      intro F hcard hFE hbalF
      rcases Finset.eq_empty_or_nonempty F with rfl | ⟨e₀, he₀⟩
      · exact ⟨[], by simp, by simp⟩
      obtain ⟨a, b⟩ := e₀
      have hba : b ≠ a := fun h => hE_ne (a, b) (hFE he₀) h.symm
      have hcard' : (F.erase (a, b)).card ≤ n := by
        have h1 := Finset.card_erase_of_mem he₀
        have h2 : 1 ≤ F.card := Finset.card_pos.mpr ⟨_, he₀⟩
        omega
      have hinv : ∀ w, ((F.erase (a, b)).filter
          (fun e => e.2 = w)).card + (if w = b then 1 else 0) =
          ((F.erase (a, b)).filter (fun e => e.1 = w)).card +
            (if w = a then 1 else 0) := by
        intro w
        have h0 := hbalF w
        rw [hdegInErase F a b he₀ w, hdegOutErase F a b he₀ w] at h0
        split_ifs at h0 ⊢ <;> omega
      obtain ⟨M, hM_last, hM_nodup, hM_mem, hM_bal⟩ :=
        hTRAIL n (F.erase (a, b)) a b hcard'
          ((Finset.erase_subset _ _).trans hFE) hba hinv
      have hz : (a :: b :: M).zip (b :: M) = (a, b) :: ((b :: M).zip M) := rfl
      have hW_sub : ((b :: M).zip M).toFinset ⊆ F.erase (a, b) :=
        fun x hx => hM_mem x (List.mem_toFinset.mp hx)
      have hF'card : ((F.erase (a, b)) \ ((b :: M).zip M).toFinset).card ≤ n :=
        le_trans (Finset.card_le_card Finset.sdiff_subset) hcard'
      have hF'E : (F.erase (a, b)) \ ((b :: M).zip M).toFinset ⊆ E :=
        Finset.sdiff_subset.trans ((Finset.erase_subset _ _).trans hFE)
      obtain ⟨cycles', hc'prop, hc'sum⟩ :=
        ih ((F.erase (a, b)) \ ((b :: M).zip M).toFinset) hF'card hF'E hM_bal
      refine ⟨(a :: b :: M) :: cycles', ?_, ?_⟩
      · intro C hC
        rcases List.mem_cons.mp hC with rfl | hC'
        · have hedges : ∀ e ∈ (a :: b :: M).zip (b :: M), e ∈ E := by
            intro e he
            rw [hz] at he
            rcases List.mem_cons.mp he with rfl | he'
            · exact hFE he₀
            · exact ((Finset.erase_subset _ _).trans hFE) (hM_mem e he')
          refine ⟨hpathE _ hedges, by simp, ?_, hedges⟩
          rw [List.head?_cons, List.getLast?_cons_cons, hM_last]
        · exact hc'prop C hC'
      · rw [List.map_cons, List.sum_cons, hc'sum]
        simp only [List.tail_cons]
        have h3 : (((a :: b :: M).zip (b :: M)).map
            (fun e => inc e c₀)).sum = inc (a, b) c₀ +
              (((b :: M).zip M).toFinset).sum (fun e => inc e c₀) := by
          rw [hz, List.map_cons, List.sum_cons, hsum_nodup _ hM_nodup]
        have h1 : (F.erase (a, b)).sum (fun e => inc e c₀) + inc (a, b) c₀ =
            F.sum (fun e => inc e c₀) :=
          Finset.sum_erase_add F _ he₀
        have h2 : ((F.erase (a, b)) \ ((b :: M).zip M).toFinset).sum
            (fun e => inc e c₀) +
            (((b :: M).zip M).toFinset).sum (fun e => inc e c₀) =
            (F.erase (a, b)).sum (fun e => inc e c₀) :=
          Finset.sum_sdiff hW_sub
        rw [h3]
        linear_combination h1 + h2
  have hcycles : ∃ cycles : List (List (ℤ × ℤ)),
      (∀ C ∈ cycles, IsGridPath C ∧ C ≠ [] ∧ C.head? = C.getLast? ∧
        ∀ e ∈ C.zip C.tail, e ∈ E) ∧
      ((cycles.map fun C => ((C.zip C.tail).map (fun e => inc e c₀)).sum).sum
        = E.sum (fun e => inc e c₀)) :=
    hMAIN E.card E le_rfl (fun _ h => h) hbal
  obtain ⟨cycles, hcycles_ok, hcycles_sum⟩ := hcycles
  clear * - hcancel hsum_sq hcycles_ok hcycles_sum hET hδ hA'T' hc₀A' hlift
  -- Some cycle has nonzero increment sum, hence nonzero winding.
  have hexists : ∃ C ∈ cycles, ((C.zip C.tail).map (fun e => inc e c₀)).sum ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : (cycles.map fun C =>
        ((C.zip C.tail).map (fun e => inc e c₀)).sum).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hx
      exact hall C hC
    rw [hzero, ← hcancel, hsum_sq] at hcycles_sum
    have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    exact hπ hcycles_sum.symm
  obtain ⟨C, hC_mem, hC_ne⟩ := hexists
  obtain ⟨hC_path, hC_nonempty, hC_closed, hC_edges⟩ := hcycles_ok C hC_mem
  -- The essential cycle has at least one edge.
  obtain ⟨a, b, M, rfl⟩ : ∃ a b M, C = a :: b :: M := by
    match C, hC_nonempty with
    | [_], _ => exact absurd (by simp) hC_ne
    | a :: b :: M, _ => exact ⟨a, b, M, rfl⟩
  -- Its trace lies in `T'` (all edges are boundary edges).
  have htraceT : ∀ (a b : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (∀ e ∈ (a :: b :: M).zip (b :: M), e ∈ E) →
      gridPathTrace δ (a :: b :: M) ⊆ T' := by
    intro a b M
    induction M generalizing a b with
    | nil =>
      intro hedge w hw
      have habE : (a, b) ∈ E := hedge (a, b) (by simp)
      rcases hw with hseg | hpt
      · exact hET (a, b) habE hseg
      · have hbw : w = gridPoint δ b := hpt
        exact hET (a, b) habE
          (hbw ▸ right_mem_segment ℝ (gridPoint δ a) (gridPoint δ b))
    | cons c M ih =>
      intro hedge w hw
      have habE : (a, b) ∈ E := hedge (a, b) (by simp)
      rcases hw with hseg | htr
      · exact hET (a, b) habE hseg
      · refine ih b c (fun e he => hedge e ?_) htr
        simp only [List.zip_cons_cons, List.mem_cons] at he ⊢
        tauto
  have hCtrace : gridPathTrace δ (a :: b :: M) ⊆ T' := htraceT a b M hC_edges
  -- `c₀` avoids the trace (it lies in the complement of `T'`).
  have hc₀off : ∀ w ∈ gridPathTrace δ (a :: b :: M), c₀ ≠ w := by
    intro w hw heq
    exact hA'T' hc₀A' (heq ▸ hCtrace hw)
  refine ⟨gridLoopCurve δ (a :: b :: M), ?_, ?_, ?_⟩
  · exact gridLoopCurve_closed (by simp) hC_closed
  · intro t
    have hrange : Set.range (gridLoopCurve δ (a :: b :: M)) =
        gridPathTrace δ (a :: b :: M) :=
      range_gridLoopCurve hδ hC_path (by simp)
    exact hCtrace (hrange ▸ Set.mem_range_self t)
  · intro hzero
    have hli := hlift (a :: b :: M) hC_path (by simp) hC_closed c₀ hc₀off
    rw [hzero] at hli
    simp only [Int.cast_zero, mul_zero] at hli
    exact hC_ne hli.symm

end RiemannDynamics
