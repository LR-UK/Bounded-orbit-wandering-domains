/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.GenusSurface.VertexChart

/-!
# The genus-`g` surface: the vertex chart image, the atlas, charted space

Openness of the vertex chart map on the chart disc
(`vertexChart_isOpen_image`), the packaged vertex chart, the atlas
`genusAtlas g` of `2g + 2` complex charts, the chart-at function
`genusChartAt`, and the `ChartedSpace ℂ (GenusSurface g)` instance. The
file closes with the pairing-root identity along the corner cycle, the key
arithmetic input to the transition analysis of the sibling file `Manifold`.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval
open scoped Manifold

namespace RiemannDynamics

set_option maxHeartbeats 400000 in
-- The saturation argument covers 4g corner charts with three kinds of ball
-- estimates; the resulting single proof term is large, so we raise the
-- heartbeat limit.
/-- Openness of the vertex chart inverse: the union of the log-polar corner
neighborhoods is saturated and open in the disc. -/
theorem vertexChart_isOpen_image (g : ℕ) [NeZero g] :
    ∀ W ⊆ Metric.ball (0 : ℂ) (vertexRadius g), IsOpen W →
      IsOpen (vertexChartFun g '' W) := by
  classical
  intro Wo hWsub hWopen
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hg1R : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := vertexRadius g with hδdef
  have hδ0 : 0 < δ := vertexRadius_pos g
  set h₀ : ℝ := Real.pi / (2 * g) with hh₀
  have hh0 : 0 < h₀ := by rw [hh₀]; positivity
  have hh2 : h₀ ≤ Real.pi / 2 := by
    rw [hh₀, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
    have h2g : (2 : ℝ) ≤ 2 * g := by linarith
    exact mul_le_mul_of_nonneg_left h2g hπ.le
  have h4gh : (4 * (g : ℝ)) * h₀ = 2 * Real.pi := by
    rw [hh₀]
    field_simp
    norm_num
  have hδ8 : δ ^ (2 * g) ≤ h₀ / 4 := by
    have h12 : δ ≤ 1 / 2 := min_le_left _ _
    have hq : δ ≤ Real.pi / (4 * g) := min_le_right _ _
    have h2 : δ ^ (2 * g) ≤ δ ^ 2 :=
      pow_le_pow_of_le_one hδ0.le (by linarith) (by omega)
    have h3 : δ ^ 2 ≤ (1 / 2) * (Real.pi / (4 * g)) := by
      rw [sq]
      exact mul_le_mul h12 hq hδ0.le (by norm_num)
    have h4 : (1 / 2) * (Real.pi / (4 * g)) = h₀ / 4 := by
      rw [hh₀]
      field_simp
    linarith
  -- the model closed disc
  set D : Set ℂ := Metric.closedBall (0 : ℂ) 1 with hD
  -- angle extraction
  have hexpI : ∀ Z₁ Z₂ : ℂ, Complex.exp (Complex.I * Z₁) = Complex.exp (Complex.I * Z₂) →
      ∃ n : ℤ, Z₁ = Z₂ + 2 * Real.pi * n := by
    intro Z₁ Z₂ hZ
    rw [Complex.exp_eq_exp_iff_exists_int] at hZ
    obtain ⟨n, hn⟩ := hZ
    refine ⟨n, ?_⟩
    have h2 : Complex.I * Z₁ = Complex.I * (Z₂ + 2 * Real.pi * n) := by
      rw [hn]
      ring
    exact mul_left_cancel₀ Complex.I_ne_zero h2
  have hkey : ∀ x₁ y₁ x₂ y₂ : ℝ,
      Complex.exp (Complex.I * (((x₁ : ℝ) : ℂ) + ((y₁ : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * (((x₂ : ℝ) : ℂ) + ((y₂ : ℝ) : ℂ) * Complex.I)) →
      ∃ n : ℤ, x₁ = x₂ + 2 * Real.pi * n ∧ y₁ = y₂ := by
    intro x₁ y₁ x₂ y₂ hx
    obtain ⟨n, hn⟩ := hexpI _ _ hx
    refine ⟨n, ?_, ?_⟩
    · have := congrArg Complex.re hn
      simpa using this
    · have := congrArg Complex.im hn
      simpa using this
  have hpv2 : ∀ p : ℤ, polyVertex g p =
      Complex.exp (Complex.I * (((h₀ * (p : ℝ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro p
    unfold polyVertex
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    field_simp
  have harc2 : ∀ (k : ℤ) (t : ℝ), arcPoint g k t =
      Complex.exp (Complex.I * (((h₀ * ((k : ℝ) + t) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro k t
    unfold arcPoint
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    field_simp
  have hnormz : ∀ x y : ℝ,
      ‖Complex.exp (Complex.I * (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        = Real.exp (-y) := by
    intro x y
    rw [Complex.norm_exp]
    congr 1
    simp
  have hsec0 : vertexSectorIndex g (0 : ℂ) = 0 := by
    unfold vertexSectorIndex
    rw [Complex.arg_zero]
    norm_num
  have hvert : ∀ c : ℤ, ‖polyVertex g c‖ = 1 := by
    intro c
    have hrw : polyVertex g c
        = Complex.exp (((Real.pi * (c : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hpvne : ∀ c : ℤ, polyVertex g c ≠ 0 := by
    intro c hc
    have := hvert c
    rw [hc, norm_zero] at this
    exact absurd this (by norm_num)
  -- normal form of the chart value at a point of the chart disc
  have hsetup : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
      ∃ (α φ W : ℝ) (c : ℤ),
        c = ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) ∧
        (0 ≤ c ∧ c < 4 * g) ∧ vertexSectorIndex g u < 4 * g ∧
        u = (‖u‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) ∧
        W = ‖u‖ ^ (2 * g) ∧ (0 ≤ W ∧ W < h₀ / 4) ∧
        (0 ≤ φ ∧ φ < Real.pi) ∧
        φ = 2 * g * α - (vertexSectorIndex g u : ℝ) * Real.pi ∧
        Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g)
          = Complex.I * ((((W * Real.cos φ : ℝ)) : ℂ) +
              (((W * Real.sin φ : ℝ)) : ℂ) * Complex.I) ∧
        polyVertex g c * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))
          = Complex.exp (Complex.I * (((h₀ * (c : ℝ) + W * Real.cos φ : ℝ) : ℂ) +
              ((W * Real.sin φ : ℝ) : ℂ) * Complex.I)) ∧
        ‖polyVertex g c *
          Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))‖ ≤ 1 ∧
        (W = 0 → u = 0) := by
    intro u hu
    have hρδ : ‖u‖ < δ := mem_ball_zero_iff.mp hu
    have hρ0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
    have hWlt : ‖u‖ ^ (2 * g) < h₀ / 4 :=
      lt_of_lt_of_le (pow_lt_pow_left₀ hρδ hρ0 (by omega)) hδ8
    have hW0 : (0 : ℝ) ≤ ‖u‖ ^ (2 * g) := pow_nonneg hρ0 _
    have hcval : (0 : ℤ) ≤ ((vertexSlot g ((vertexSectorIndex g u : ℕ) :
        ZMod (4 * g))).val : ℤ) ∧
        ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) < 4 * g := by
      constructor
      · positivity
      · exact_mod_cast ZMod.val_lt _
    by_cases hu0 : u = 0
    · subst hu0
      refine ⟨0, 0, ‖(0 : ℂ)‖ ^ (2 * g), _, rfl, hcval, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsec0]
        omega
      · simp
      · exact ⟨hW0, hWlt⟩
      · exact ⟨le_refl 0, hπ⟩
      · rw [hsec0]
        push_cast
        ring
      · rw [hsec0, norm_zero]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero]
        rw [zero_pow (by omega : 2 * g ≠ 0)]
        simp
      · rw [hsec0, norm_zero]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
        rw [hpv2]
        norm_num
        simp [zero_pow (show 2 * g ≠ 0 by omega)]
      · rw [hsec0]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
        rw [hvert]
      · intro _
        rfl
    · have harg1 : -Real.pi < Complex.arg u := Complex.neg_pi_lt_arg u
      have harg2 : Complex.arg u ≤ Real.pi := Complex.arg_le_pi u
      set α : ℝ := if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u
        with hα
      have hα0 : 0 ≤ α := by
        rw [hα]
        split_ifs with hc
        · linarith
        · linarith [not_lt.mp hc]
      have hα2 : α < 2 * Real.pi := by
        rw [hα]
        split_ifs with hc
        · linarith
        · linarith
      have hue : u = (‖u‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) := by
        have hbase : u = (‖u‖ : ℂ) * Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I) :=
          (Complex.norm_mul_exp_arg_mul_I u).symm
        rw [hα]
        split_ifs with hc
        · have h2π : Complex.exp (((Complex.arg u + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
              = Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.exp_eq_exp_iff_exists_int]
            refine ⟨1, ?_⟩
            push_cast
            ring
          rw [h2π]
          exact hbase
        · exact hbase
      have hsec : vertexSectorIndex g u = (⌊2 * (g : ℝ) / Real.pi * α⌋).toNat := by
        unfold vertexSectorIndex
        rw [hα]
      set x : ℝ := 2 * (g : ℝ) / Real.pi * α with hx
      have hx0 : 0 ≤ x := by
        rw [hx]
        exact mul_nonneg (by positivity) hα0
      have hfl0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
      have hsecZ : ((vertexSectorIndex g u : ℕ) : ℤ) = ⌊x⌋ := by
        rw [hsec]
        exact Int.toNat_of_nonneg hfl0
      have hsecR : ((vertexSectorIndex g u : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsecZ
      have hle : ((vertexSectorIndex g u : ℝ)) ≤ x := by
        rw [hsecR]
        exact Int.floor_le x
      have hlt : x < (vertexSectorIndex g u : ℝ) + 1 := by
        rw [hsecR]
        exact Int.lt_floor_add_one x
      have hm4 : vertexSectorIndex g u < 4 * g := by
        have hxlt : x < 4 * g := by
          rw [hx]
          calc 2 * (g : ℝ) / Real.pi * α < 2 * g / Real.pi * (2 * Real.pi) := by
                exact mul_lt_mul_of_pos_left hα2 (by positivity)
            _ = 4 * g := by field_simp; ring
        have hflt : ⌊x⌋ < ((4 * g : ℕ) : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hxlt)
        omega
      have hπx : Real.pi * x = 2 * g * α := by
        rw [hx]
        field_simp
      set msec : ℕ := vertexSectorIndex g u with hmsec
      set φ : ℝ := 2 * g * α - (msec : ℝ) * Real.pi with hφ
      have hφx : φ = Real.pi * (x - (msec : ℝ)) := by
        rw [hφ, ← hπx]
        ring
      have hφ0 : 0 ≤ φ := by
        rw [hφx]
        exact mul_nonneg hπ.le (by linarith)
      have hφπ : φ < Real.pi := by
        rw [hφx]
        calc Real.pi * (x - (msec : ℝ)) < Real.pi * 1 :=
              mul_lt_mul_of_pos_left (by linarith) hπ
          _ = Real.pi := mul_one _
      have hIarg : Complex.I * (-1) ^ msec * u ^ (2 * g)
          = Complex.I * ((((‖u‖ ^ (2 * g) * Real.cos φ : ℝ)) : ℂ) +
              (((‖u‖ ^ (2 * g) * Real.sin φ : ℝ)) : ℂ) * Complex.I) := by
        have hupow : u ^ (2 * g)
            = ((‖u‖ ^ (2 * g) : ℝ) : ℂ) * Complex.exp (((2 * g * α : ℝ) : ℂ) * Complex.I) := by
          have h1 : u ^ (2 * g)
              = ((‖u‖ : ℂ)) ^ (2 * g) * Complex.exp ((α : ℂ) * Complex.I) ^ (2 * g) := by
            rw [← mul_pow]
            exact congrArg (fun z : ℂ => z ^ (2 * g)) hue
          rw [h1, ← Complex.exp_nat_mul]
          congr 1
          · push_cast
            ring
          · congr 1
            push_cast
            ring
        have hsplit : Complex.exp (((2 * g * α : ℝ) : ℂ) * Complex.I)
            = (-1) ^ msec * Complex.exp (((φ : ℝ) : ℂ) * Complex.I) := by
          have h2 : (2 * g * α : ℝ) = (msec : ℝ) * Real.pi + φ := by
            rw [hφ]
            ring
          rw [h2]
          have h3 : ((((msec : ℝ) * Real.pi + φ : ℝ)) : ℂ) * Complex.I
              = ((msec : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) + ((φ : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [h3, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
        have hcs : Complex.exp (((φ : ℝ) : ℂ) * Complex.I)
            = ((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I := by
          rw [Complex.exp_mul_I]
          rw [Complex.ofReal_cos, Complex.ofReal_sin]
        have hm2 : ((-1 : ℂ)) ^ msec * (-1) ^ msec = 1 := by
          rw [← pow_add]
          exact Even.neg_one_pow ⟨msec, by ring⟩
        calc Complex.I * (-1) ^ msec * u ^ (2 * g)
            = Complex.I * (-1) ^ msec * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                ((-1) ^ msec * (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) *
                  Complex.I))) := by
              rw [hupow, hsplit, hcs]
          _ = Complex.I * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I)) *
                ((-1) ^ msec * (-1) ^ msec) := by ring
          _ = Complex.I * ((((‖u‖ ^ (2 * g) * Real.cos φ : ℝ)) : ℂ) +
                (((‖u‖ ^ (2 * g) * Real.sin φ : ℝ)) : ℂ) * Complex.I) := by
              rw [hm2]
              push_cast
              ring
      have hzid : polyVertex g ((vertexSlot g ((msec : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ msec * u ^ (2 * g))
          = Complex.exp (Complex.I *
              (((h₀ * (((vertexSlot g ((msec : ℕ) : ZMod (4 * g))).val : ℤ) : ℝ) +
                ‖u‖ ^ (2 * g) * Real.cos φ : ℝ) : ℂ) +
              ((‖u‖ ^ (2 * g) * Real.sin φ : ℝ) : ℂ) * Complex.I)) := by
        rw [hpv2, hIarg, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      refine ⟨α, φ, ‖u‖ ^ (2 * g), _, rfl, hcval, hm4, hue, rfl, ⟨hW0, hWlt⟩, ⟨hφ0, hφπ⟩,
        rfl, hIarg, hzid, ?_, ?_⟩
      · rw [hzid, hnormz]
        rw [Real.exp_le_one_iff]
        have : 0 ≤ ‖u‖ ^ (2 * g) * Real.sin φ :=
          mul_nonneg hW0 (Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ.le)
        linarith
      · intro hWz
        exact norm_eq_zero.mp ((pow_eq_zero_iff (by omega : 2 * g ≠ 0)).mp hWz)
  -- pinning helpers
  have hcollapse : ∀ W₁ φ₁ : ℝ, 0 < W₁ → 0 ≤ φ₁ → φ₁ < Real.pi → W₁ * Real.sin φ₁ = 0 →
      φ₁ = 0 := by
    intro W₁ φ₁ hW₁ h0 hπ₁ hs
    rcases mul_eq_zero.mp hs with hW | hsin
    · exact absurd hW (ne_of_gt hW₁)
    · by_contra hne
      have hpos : 0 < Real.sin φ₁ :=
        Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne h0 (Ne.symm hne)) hπ₁
      rw [hsin] at hpos
      exact absurd hpos (lt_irrefl 0)
  have hWpin : ∀ (W₁ : ℝ) (e : ℤ) (s : ℝ), 0 ≤ W₁ → W₁ < h₀ / 4 → 0 ≤ s → s ≤ 1 →
      W₁ = h₀ * (s - (e : ℝ)) → (e = 0 ∧ W₁ = h₀ * s) ∨ (s = 1 ∧ W₁ = 0) := by
    intro W₁ e s hW1 hW2 hs0 hs1 hWe
    have hse0 : 0 ≤ s - (e : ℝ) := by
      by_contra hcon
      push Not at hcon
      have : h₀ * (s - (e : ℝ)) < 0 := mul_neg_of_pos_of_neg hh0 hcon
      linarith
    have hse1 : s - (e : ℝ) < 1 / 4 := by
      by_contra hcon
      push Not at hcon
      have h5 : h₀ * (1 / 4) ≤ h₀ * (s - (e : ℝ)) := mul_le_mul_of_nonneg_left hcon hh0.le
      have h6 : h₀ * (1 / 4) = h₀ / 4 := by ring
      linarith
    have he1 : ((e : ℝ)) < 2 := by linarith
    have he2 : (-1 : ℝ) < ((e : ℝ)) := by linarith
    have hei : e < 2 ∧ -1 < e := ⟨by exact_mod_cast he1, by exact_mod_cast he2⟩
    have hcases : e = 0 ∨ e = 1 := by omega
    rcases hcases with he | he
    · left
      refine ⟨he, ?_⟩
      rw [hWe, he]
      norm_num
    · right
      have hs1' : s = 1 := by
        rw [he] at hse0
        push_cast at hse0
        linarith
      refine ⟨hs1', ?_⟩
      rw [hWe, he, hs1']
      norm_num
  -- ZMod plumbing
  have hcast : ∀ x : ZMod (4 * g), (((x.val : ℤ)) : ZMod (4 * g)) = x := by
    intro x
    rw [Int.cast_natCast]
    exact ZMod.natCast_rightInverse x
  have hplus2 : ∀ x : ZMod (4 * g), (x + 2).val % 4 = (x.val + 2) % 4 := by
    intro x
    have h1 : x + 2 = ((x.val + 2 : ℕ) : ZMod (4 * g)) := by
      push_cast
      rw [ZMod.natCast_rightInverse x]
    rw [h1, ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd _ ⟨g, rfl⟩
  have hminus2 : ∀ x : ZMod (4 * g), (x - 2).val % 4 = (x.val + 2) % 4 := by
    intro x
    have h0 : ((4 * g - 2 : ℕ) : ZMod (4 * g)) = -2 := by
      have h1 : ((4 * g - 2 : ℕ) : ZMod (4 * g)) + ((2 : ℕ) : ZMod (4 * g)) = 0 := by
        rw [← Nat.cast_add]
        have h2 : 4 * g - 2 + 2 = 4 * g := by omega
        rw [h2, ZMod.natCast_self]
      have h3 := eq_neg_of_add_eq_zero_left h1
      rwa [show ((2 : ℕ) : ZMod (4 * g)) = (2 : ZMod (4 * g)) from by push_cast; ring] at h3
    have h1 : x - 2 = ((x.val + (4 * g - 2) : ℕ) : ZMod (4 * g)) := by
      rw [Nat.cast_add, h0, ZMod.natCast_rightInverse x]
      ring
    rw [h1, ZMod.val_natCast]
    have h2 := Nat.mod_mod_of_dvd (x.val + (4 * g - 2)) (⟨g, rfl⟩ : (4 : ℕ) ∣ 4 * g)
    rw [h2]
    omega
  have hcornerexp : ∀ (a : ℤ) (θ : ℝ),
      polyVertex g a * Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))
        = Complex.exp (Complex.I * (((h₀ * (a : ℝ) - θ : ℝ)) : ℂ)) := by
    intro a θ
    rw [hpv2 a, Complex.ofReal_zero, zero_mul, add_zero, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the sector root: `RT j V` is the sector-`j` preimage of the corner point `v_{c_j} e^{iV}`.
  set RT : ℕ → ℂ → ℂ := fun j V =>
    Complex.exp ((Complex.log V + (j : ℕ) * Real.pi * Complex.I) / ((2 * (g : ℝ) : ℝ) : ℂ))
    with hRT
  have hRTnorm : ∀ (j : ℕ) (V : ℂ),
      ‖RT j V‖ = Real.exp ((Real.log ‖V‖ + 0) / (2 * (g : ℝ))) := by
    intro j V
    rw [hRT]
    simp only []
    rw [Complex.norm_exp]
    congr 1
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.re_ofReal_mul]
    rw [Complex.add_re, Complex.log_re]
    have him : ((j : ℕ) * Real.pi * Complex.I : ℂ).re = 0 := by
      simp [Complex.mul_re]
    rw [him]
    ring
  have hRTpow : ∀ (j : ℕ) (V : ℂ), V ≠ 0 → (RT j V) ^ (2 * g) = V * (-1) ^ j := by
    intro j V hV
    rw [hRT]
    simp only []
    rw [← Complex.exp_nat_mul]
    have harg : ((2 * g : ℕ) : ℂ) * ((Complex.log V + (j : ℕ) * Real.pi * Complex.I) /
        ((2 * (g : ℝ) : ℝ) : ℂ)) = Complex.log V + (j : ℕ) * Real.pi * Complex.I := by
      have hne : (((2 * (g : ℝ) : ℝ)) : ℂ) ≠ 0 := by
        push_cast
        intro hc
        have : (g : ℂ) = 0 := by linear_combination hc / 2
        exact hgC this
      field_simp
      push_cast
      ring
    have hexpj : Complex.exp (((j : ℕ) : ℂ) * Real.pi * Complex.I) = (-1) ^ j := by
      rw [mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    rw [harg, Complex.exp_add, Complex.exp_log hV, hexpj]
  -- the sector index of the root
  have hRTsec : ∀ (j : ℕ), j < 4 * g → ∀ V : ℂ, V ≠ 0 → 0 ≤ V.arg → V.arg < Real.pi →
      vertexSectorIndex g (RT j V) = j := by
    intro j hj V hV h0 hπV
    set w : ℂ := (Complex.log V + (j : ℕ) * Real.pi * Complex.I) / ((2 * (g : ℝ) : ℝ) : ℂ)
      with hw
    have hwim : w.im = (V.arg + j * Real.pi) / (2 * (g : ℝ)) := by
      rw [hw, div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.im_ofReal_mul]
      rw [Complex.add_im, Complex.log_im]
      have him : ((j : ℕ) * Real.pi * Complex.I : ℂ).im = j * Real.pi := by
        simp [Complex.mul_im]
      rw [him]
      ring
    set y : ℝ := (V.arg + j * Real.pi) / (2 * (g : ℝ)) with hy
    have hy0 : 0 ≤ y := by
      rw [hy]
      apply div_nonneg _ (by linarith)
      have : (0 : ℝ) ≤ j * Real.pi := by positivity
      linarith
    have hy2 : y < 2 * Real.pi := by
      rw [hy, div_lt_iff₀ (by linarith)]
      have hjR : (j : ℝ) ≤ 4 * g - 1 := by
        have : (j : ℝ) + 1 ≤ 4 * g := by exact_mod_cast hj
        linarith
      have : (j : ℝ) * Real.pi ≤ (4 * g - 1) * Real.pi :=
        mul_le_mul_of_nonneg_right hjR hπ.le
      nlinarith
    -- `RT j V = e^{w.re} · exp(y i)`
    have hsplit : RT j V = ((Real.exp w.re : ℝ) : ℂ) * Complex.exp ((y : ℝ) * Complex.I) := by
      rw [hRT]
      simp only []
      rw [← hw]
      calc Complex.exp w = Complex.exp (((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.re_add_im]
        _ = Complex.exp ((w.re : ℝ) : ℂ) * Complex.exp (((w.im : ℝ) : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
        _ = ((Real.exp w.re : ℝ) : ℂ) * Complex.exp ((y : ℝ) * Complex.I) := by
            rw [Complex.ofReal_exp, hwim]
    have hargRT : Complex.arg (RT j V) = if y ≤ Real.pi then y else y - 2 * Real.pi := by
      rw [hsplit]
      rw [Complex.arg_real_mul _ (Real.exp_pos _)]
      split_ifs with hcase
      · rw [Complex.exp_mul_I]
        exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, hcase⟩
      · have hper : Complex.exp ((y : ℝ) * Complex.I)
            = Complex.exp (((y - 2 * Real.pi : ℝ) : ℝ) * Complex.I) := by
          rw [Complex.exp_eq_exp_iff_exists_int]
          refine ⟨1, ?_⟩
          push_cast
          ring
        rw [hper, Complex.exp_mul_I]
        exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩
    -- normalized angle is `y` in both cases
    have hA : (if Complex.arg (RT j V) < 0 then Complex.arg (RT j V) + 2 * Real.pi
        else Complex.arg (RT j V)) = y := by
      rw [hargRT]
      rcases le_or_gt y Real.pi with hcase | hcase
      · rw [ite_eq_left hcase, ite_eq_right (not_lt.mpr hy0)]
      · rw [ite_eq_right (not_le.mpr hcase), ite_eq_left (by linarith : y - 2 * Real.pi < 0)]
        ring
    unfold vertexSectorIndex
    rw [hA]
    have hxval : 2 * (g : ℝ) / Real.pi * y = V.arg / Real.pi + (j : ℤ) := by
      rw [hy]
      push_cast
      field_simp
    rw [hxval, Int.floor_add_intCast]
    have hfl : ⌊V.arg / Real.pi⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · positivity
      · rw [div_lt_one hπ]
        exact hπV
    rw [hfl, zero_add]
    exact Int.toNat_natCast j
  -- the root hits the corner point
  have hroot : ∀ (j : ℕ), j < 4 * g → ∀ V : ℂ, V ≠ 0 → 0 ≤ V.arg → V.arg < Real.pi →
      vertexChartFun g (RT j V) = Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * V))) := by
    intro j hj V hV h0 hπV
    have hs := hRTsec j hj V hV h0 hπV
    have hp := hRTpow j V hV
    have h1 : vertexChartFun g (RT j V) = Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g
            ((vertexSlot g ((vertexSectorIndex g (RT j V) : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g (RT j V)) *
            (RT j V) ^ (2 * g)))) := rfl
    rw [h1, hs, hp]
    have h2 : Complex.I * (-1) ^ j * (V * (-1) ^ j) = Complex.I * V := by
      have hm2 : ((-1 : ℂ)) ^ j * (-1) ^ j = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨j, by ring⟩
      calc Complex.I * (-1) ^ j * (V * (-1) ^ j)
          = Complex.I * V * ((-1) ^ j * (-1) ^ j) := by ring
        _ = Complex.I * V := by rw [hm2]; ring
    rw [h2]
  -- glue across a shared ray, in the `θ`-parametrization
  have hglueθ : ∀ (n : ℕ) (θ : ℝ), 0 ≤ θ → θ < h₀ →
      (Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g ((n : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ))))) : GenusSurface g) =
      Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g (((n : ℕ) : ZMod (4 * g)) + 1)).val : ℤ) *
          Complex.exp (Complex.I * ((θ : ℝ) : ℂ)))) := by
    intro n θ hθ0 hθh
    set r : ℝ := if θ = 0 then 0 else Real.exp (Real.log θ / (2 * (g : ℝ))) with hr
    have hr0 : 0 ≤ r := by
      rw [hr]
      split_ifs
      · exact le_refl 0
      · exact (Real.exp_pos _).le
    have hrpow : r ^ (2 * g) = θ := by
      rw [hr]
      split_ifs with hθz
      · rw [hθz, zero_pow (by omega : 2 * g ≠ 0)]
      · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθz)
        rw [← Real.exp_nat_mul]
        have h2 : ((2 * g : ℕ) : ℝ) * (Real.log θ / (2 * (g : ℝ))) = Real.log θ := by
          push_cast
          field_simp
        rw [h2, Real.exp_log hθpos]
    have hrC : ((r : ℂ)) ^ (2 * g) = ((θ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hrpow]
    have hsmall : r ^ (2 * g) < Real.pi / (2 * g) := by
      rw [hrpow]
      rw [hh₀] at hθh
      exact hθh
    have hres := Quotient.sound (s := genusSetoid g) (vertexRay_glue g n hr0 hsmall)
    rw [hrC] at hres
    exact hres
  -- norm control for the root
  have hRTball : ∀ (η : ℝ), 0 < η → ∀ (i : ℕ) (V : ℂ), V ≠ 0 → ‖V‖ < η ^ (2 * g) →
      ‖RT i V‖ < η := by
    intro η hη i V hV hVη
    rw [hRTnorm, add_zero]
    have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
    have hlog : Real.log ‖V‖ < Real.log (η ^ (2 * g)) := Real.log_lt_log hVpos hVη
    rw [Real.log_pow] at hlog
    have h2 : Real.log ‖V‖ / (2 * (g : ℝ)) < Real.log η := by
      rw [div_lt_iff₀ (by linarith)]
      push_cast at hlog
      linarith
    calc Real.exp (Real.log ‖V‖ / (2 * (g : ℝ))) < Real.exp (Real.log η) :=
          Real.exp_lt_exp.mpr h2
      _ = η := Real.exp_log hη
  -- reduction to a ball criterion on the saturation
  apply isOpen_coinduced.mpr
  set T : Set ClosedDisc := Quotient.mk (genusSetoid g) ⁻¹' (vertexChartFun g '' Wo) with hT
  have hTmem : ∀ (z : ClosedDisc) (u : ℂ), u ∈ Wo →
      vertexChartFun g u = Quotient.mk (genusSetoid g) z → z ∈ T := by
    intro z u hu he
    exact ⟨u, hu, he⟩
  have hopen_of_balls : (∀ z₀ ∈ T, ∃ ε, 0 < ε ∧
      ∀ z : ClosedDisc, ‖z.1 - z₀.1‖ < ε → z ∈ T) → IsOpen T := by
    intro hTb
    rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨ε, hε0, hball⟩ := hTb z₀ hz₀
    refine ⟨Subtype.val ⁻¹' Metric.ball z₀.1 ε, ?_, ?_, ?_⟩
    · intro z hz
      apply hball z
      have hz' : z.1 ∈ Metric.ball z₀.1 ε := hz
      rwa [Metric.mem_ball, dist_eq_norm] at hz'
    · exact isOpen_ball.preimage continuous_subtype_val
    · change z₀.1 ∈ Metric.ball z₀.1 ε
      exact Metric.mem_ball_self hε0
  -- membership of a closed-disc point whose value is a known corner form
  have hzT : ∀ (z : ClosedDisc) (u : ℂ), u ∈ Wo →
      vertexChartFun g u = Quotient.mk (genusSetoid g) (projDisc z.1) → z ∈ T := by
    intro z u hu he
    apply hTmem z u hu
    rw [he]
    congr 1
    exact Subtype.ext (projDisc_eq (mem_closedBall_zero_iff.mp z.2))
  -- the vertex-ball lemma
  have hballB : (0 : ℂ) ∈ Wo → ∀ p : ℤ, ∃ ε, 0 < ε ∧
      ∀ z : ClosedDisc, ‖z.1 - polyVertex g p‖ < ε → z ∈ T := by
    intro h0W p
    obtain ⟨η, hη0, hηsub⟩ := Metric.isOpen_iff.mp hWopen 0 h0W
    -- normalize the vertex index
    set p' : ℤ := p % ((4 * g : ℕ) : ℤ) with hp'
    have h4gZ : (0 : ℤ) < ((4 * g : ℕ) : ℤ) := by positivity
    have hp'0 : 0 ≤ p' := Int.emod_nonneg p (by omega)
    have hp'lt : p' < ((4 * g : ℕ) : ℤ) := Int.emod_lt_of_pos p h4gZ
    have hmodeq : (p : ZMod (4 * g)) = ((p' : ℤ) : ZMod (4 * g)) := by
      rw [ZMod.intCast_eq_intCast_iff]
      exact (Int.emod_emod_of_dvd p dvd_rfl).symm
    have hpvcongr : ∀ x y : ℤ, ((x : ZMod (4 * g)) = (y : ZMod (4 * g))) →
        polyVertex g x = polyVertex g y := by
      intro x y hxy
      rw [ZMod.intCast_eq_intCast_iff] at hxy
      obtain ⟨q, hq⟩ := Int.ModEq.dvd hxy
      have hqZ : x - y = 4 * (g : ℤ) * (-q) := by push_cast at hq ⊢; linarith
      have hqC : (x : ℂ) - y = 4 * g * (-q : ℤ) := by exact_mod_cast hqZ
      unfold polyVertex
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-q, ?_⟩
      push_cast at hqC ⊢
      field_simp
      linear_combination hqC
    have hpvp : polyVertex g p = polyVertex g p' := hpvcongr p p' hmodeq
    -- the sector landing at this corner
    obtain ⟨jz, hjz⟩ := (vertexSlot_bijective g).surjective ((p' : ℤ) : ZMod (4 * g))
    set j : ℕ := jz.val with hjdef
    have hj4 : j < 4 * g := ZMod.val_lt jz
    have hslotj : vertexSlot g ((j : ℕ) : ZMod (4 * g)) = ((p' : ℤ) : ZMod (4 * g)) := by
      rw [hjdef, ZMod.natCast_rightInverse jz]
      exact hjz
    have hslotval : ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) = p' := by
      rw [hslotj]
      have h1 : ((p' : ℤ) : ZMod (4 * g)) = ((p'.toNat : ℕ) : ZMod (4 * g)) := by
        rw [← Int.toNat_of_nonneg hp'0]
        push_cast
        rw [Int.toNat_of_nonneg hp'0]
      rw [h1, ZMod.val_cast_of_lt (by omega)]
      omega
    -- the successor sector index
    set j₂ : ℕ := if j + 1 = 4 * g then 0 else j + 1 with hj₂
    have hj₂4 : j₂ < 4 * g := by
      rw [hj₂]
      split_ifs <;> omega
    have hj₂cast : ((j₂ : ℕ) : ZMod (4 * g)) = ((j : ℕ) : ZMod (4 * g)) + 1 := by
      rw [hj₂]
      split_ifs with hcase
      · rw [Nat.cast_zero]
        have : ((j + 1 : ℕ) : ZMod (4 * g)) = ((j : ℕ) : ZMod (4 * g)) + 1 := by push_cast; ring
        rw [← this, hcase, ZMod.natCast_self]
      · push_cast
        ring
    -- the eventual conditions near the vertex
    set b : ℝ := min (min (η ^ (2 * g)) (h₀ / 2)) 1 with hb
    have hb0 : 0 < b := by
      rw [hb]
      have : (0:ℝ) < η ^ (2*g) := by positivity
      simp only [lt_min_iff]
      exact ⟨⟨this, by linarith⟩, by norm_num⟩
    set U₁ : Set ℂ := {w : ℂ | 0 < (w / polyVertex g p').re} with hU₁
    have hU₁open : IsOpen U₁ := by
      have hcont : Continuous fun w : ℂ => (w / polyVertex g p').re :=
        Complex.continuous_re.comp (continuous_id.div_const _)
      exact isOpen_lt continuous_const hcont
    have hVmcont : ContinuousOn (fun w : ℂ => -Complex.I * Complex.log (w / polyVertex g p'))
        U₁ := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.clog (continuousOn_id.div_const _)
      intro w hw
      exact Complex.mem_slitPlane_iff.mpr (Or.inl hw)
    set C : Set ℂ := U₁ ∩ (fun w : ℂ => -Complex.I * Complex.log (w / polyVertex g p')) ⁻¹'
        (Metric.ball (0 : ℂ) b) with hC
    have hCopen : IsOpen C := hVmcont.isOpen_inter_preimage hU₁open isOpen_ball
    have hCmem : polyVertex g p' ∈ C := by
      constructor
      · change 0 < (polyVertex g p' / polyVertex g p').re
        rw [div_self (hpvne p')]
        norm_num
      · change -Complex.I * Complex.log (polyVertex g p' / polyVertex g p') ∈ Metric.ball 0 b
        rw [div_self (hpvne p'), Complex.log_one, mul_zero]
        exact Metric.mem_ball_self hb0
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp (hCopen.mem_nhds hCmem)
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    rw [hpvp] at hz
    have hwC : z.1 ∈ C := hεsub (by rwa [Metric.mem_ball, dist_eq_norm])
    obtain ⟨hw1, hw2⟩ := hwC
    set V : ℂ := -Complex.I * Complex.log (z.1 / polyVertex g p') with hV
    have hVb : ‖V‖ < b := by
      have := hw2
      rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at this
    have hzne : z.1 ≠ 0 := by
      intro hc
      have : (0 : ℝ) < ((z.1 / polyVertex g p').re) := hw1
      rw [hc, zero_div] at this
      simp at this
    have hζne : z.1 / polyVertex g p' ≠ 0 := div_ne_zero hzne (hpvne p')
    have hwexp : z.1 = polyVertex g p' * Complex.exp (Complex.I * V) := by
      have h1 : Complex.I * V = Complex.log (z.1 / polyVertex g p') := by
        rw [hV]
        calc Complex.I * (-Complex.I * Complex.log (z.1 / polyVertex g p'))
            = -(Complex.I * Complex.I) * Complex.log (z.1 / polyVertex g p') := by ring
          _ = Complex.log (z.1 / polyVertex g p') := by
              rw [Complex.I_mul_I]
              ring
      rw [h1, Complex.exp_log hζne, mul_comm]
      exact (div_mul_cancel₀ z.1 (hpvne p')).symm
    have hVim : 0 ≤ V.im := by
      have h1 : V.im = -(Complex.log (z.1 / polyVertex g p')).re := by
        rw [hV]
        have : (-Complex.I * Complex.log (z.1 / polyVertex g p')).im
            = -(Complex.log (z.1 / polyVertex g p')).re := by
          simp [Complex.mul_im]
        exact this
      rw [h1, Complex.log_re]
      have h2 : ‖z.1 / polyVertex g p'‖ = ‖z.1‖ := by
        rw [Complex.norm_div, hvert, div_one]
      rw [h2]
      have h3 : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have := Real.log_nonpos (norm_nonneg _) h3
      linarith
    by_cases hV0 : V = 0
    · -- the vertex itself
      have hzp : z.1 = polyVertex g p' := by
        rw [hwexp, hV0, mul_zero, Complex.exp_zero, mul_one]
      apply hzT z 0 h0W
      have hf0 : vertexChartFun g (0 : ℂ) = Quotient.mk (genusSetoid g)
          (projDisc (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g (0 : ℂ) : ℕ) : ZMod (4 * g))).val : ℤ) *
            Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g (0 : ℂ)) *
              (0 : ℂ) ^ (2 * g)))) := rfl
      rw [hf0]
      rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
      apply Quotient.sound
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [projDisc_eq (le_of_eq (hvert _))]
        exact ⟨_, rfl⟩
      · rw [projDisc_eq (by rw [hzp, hvert] : ‖z.1‖ ≤ 1), hzp]
        exact ⟨p', rfl⟩
    · have hargV0 : 0 ≤ V.arg := Complex.arg_nonneg_iff.mpr hVim
      have hVη : ‖V‖ < η ^ (2 * g) := by
        apply lt_of_lt_of_le hVb
        rw [hb]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      have hVh : ‖V‖ < h₀ / 2 := by
        apply lt_of_lt_of_le hVb
        rw [hb]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      by_cases hargVπ : V.arg = Real.pi
      · -- on the circle, clockwise side: jump to the paired sector
        obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hargVπ
        set θw : ℝ := -V.re with hθw
        have hθw0 : 0 < θw := by rw [hθw]; linarith
        have hVθ : V = ((-θw : ℝ) : ℂ) := by
          apply Complex.ext
          · rw [hθw]
            simp
          · rw [him]
            simp
        have hθwn : θw ≤ ‖V‖ := by
          have := Complex.abs_re_le_norm V
          rw [abs_of_nonpos (by linarith : V.re ≤ 0)] at this
          rw [hθw]
          exact this
        have hθC : ((θw : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast ne_of_gt hθw0
        have hargθ : Complex.arg ((θw : ℝ) : ℂ) = 0 := Complex.arg_ofReal_of_nonneg hθw0.le
        have hu := hroot j₂ hj₂4 ((θw : ℝ) : ℂ) hθC (by rw [hargθ]) (by rw [hargθ]; exact hπ)
        apply hzT z (RT j₂ ((θw : ℝ) : ℂ))
        · apply hηsub
          rw [Metric.mem_ball, dist_zero_right]
          apply hRTball η hη0
          · exact hθC
          · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθw0]
            linarith
        · rw [hu]
          have hslot2 : vertexSlot g ((j₂ : ℕ) : ZMod (4 * g))
              = vertexSlot g (((j : ℕ) : ZMod (4 * g)) + 1) := by
            rw [hj₂cast]
          rw [hslot2]
          rw [← hglueθ j θw hθw0.le (by linarith)]
          congr 2
          rw [hslotval]
          rw [hwexp, hVθ]
          congr 1
          push_cast
          ring_nf
      · -- interior or counterclockwise side: direct root
        have hargVπ' : V.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi V) hargVπ
        have hu := hroot j hj4 V hV0 hargV0 hargVπ'
        apply hzT z (RT j V)
        · apply hηsub
          rw [Metric.mem_ball, dist_zero_right]
          exact hRTball η hη0 j V hV0 hVη
        · rw [hu, hwexp]
          congr 3
          rw [hslotval]
  -- corner-ball lemma: coverage around a corner point with angle in `[0, π)`
  have hballA : ∀ (j : ℕ), j < 4 * g → ∀ V₀ : ℂ, V₀ ≠ 0 → 0 ≤ V₀.arg →
      V₀.arg < Real.pi → ‖V₀‖ < 1 → RT j V₀ ∈ Wo → ∃ ε, 0 < ε ∧
      ∀ z : ClosedDisc,
        ‖z.1 - polyVertex g ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * V₀)‖ < ε → z ∈ T := by
    intro j hj V₀ hV₀ne h0 hπV hV₀1 hRTW
    set c : ℤ := ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) with hc
    set z₀ : ℂ := polyVertex g c * Complex.exp (Complex.I * V₀) with hz₀d
    have hπ2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have hV₀im : 0 ≤ V₀.im := Complex.arg_nonneg_iff.mp h0
    have hV₀U : 0 < V₀.re ∨ 0 < V₀.im := by
      rcases lt_or_eq_of_le hV₀im with him | him
      · exact Or.inr him
      · left
        rcases lt_trichotomy V₀.re 0 with hre | hre | hre
        · exfalso
          have : V₀.arg = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hre, him.symm⟩
          linarith
        · exfalso
          apply hV₀ne
          apply Complex.ext
          · simpa using hre
          · simpa using him.symm
        · exact hre
    have hreV₀ : |V₀.re| ≤ ‖V₀‖ := Complex.abs_re_le_norm V₀
    have hζ₀ : z₀ / polyVertex g c = Complex.exp (Complex.I * V₀) := by
      rw [hz₀d, mul_comm, mul_div_assoc, div_self (hpvne c), mul_one]
    have hlogexp : Complex.log (Complex.exp (Complex.I * V₀)) = Complex.I * V₀ := by
      apply Complex.log_exp
      · have him : (Complex.I * V₀).im = V₀.re := by simp [Complex.mul_im]
        rw [him]
        have := abs_le.mp hreV₀
        linarith
      · have him : (Complex.I * V₀).im = V₀.re := by simp [Complex.mul_im]
        rw [him]
        have := abs_le.mp hreV₀
        linarith
    set Vm : ℂ → ℂ := fun w => -Complex.I * Complex.log (w / polyVertex g c) with hVm
    have hVmz₀ : Vm z₀ = V₀ := by
      rw [hVm]
      simp only []
      rw [hζ₀, hlogexp]
      calc -Complex.I * (Complex.I * V₀) = -(Complex.I * Complex.I) * V₀ := by ring
        _ = V₀ := by rw [Complex.I_mul_I]; ring
    set U₁ : Set ℂ := {w : ℂ | 0 < (w / polyVertex g c).re} with hU₁
    have hU₁open : IsOpen U₁ := by
      have hcont : Continuous fun w : ℂ => (w / polyVertex g c).re :=
        Complex.continuous_re.comp (continuous_id.div_const _)
      exact isOpen_lt continuous_const hcont
    have hz₀U₁ : z₀ ∈ U₁ := by
      change 0 < (z₀ / polyVertex g c).re
      rw [hζ₀]
      rw [Complex.exp_re]
      apply mul_pos (Real.exp_pos _)
      have him : (Complex.I * V₀).im = V₀.re := by simp [Complex.mul_im]
      rw [him]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have := abs_le.mp hreV₀
        linarith
      · have := abs_le.mp hreV₀
        linarith
    have hVmcont : ContinuousOn Vm U₁ := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.clog (continuousOn_id.div_const _)
      intro w hw
      exact Complex.mem_slitPlane_iff.mpr (Or.inl hw)
    set Up : Set ℂ := {v : ℂ | 0 < v.re ∨ 0 < v.im} with hUp
    have hUpopen : IsOpen Up := by
      have h1 : Up = {v : ℂ | 0 < v.re} ∪ {v : ℂ | 0 < v.im} := by
        rw [hUp]
        exact Set.ofPred_or
      rw [h1]
      exact (isOpen_lt continuous_const Complex.continuous_re).union
        (isOpen_lt continuous_const Complex.continuous_im)
    have hUpslit : Up ⊆ Complex.slitPlane := by
      intro v hv
      apply Complex.mem_slitPlane_iff.mpr
      rcases hv with h | h
      · exact Or.inl h
      · exact Or.inr (ne_of_gt h)
    set U₂ : Set ℂ := U₁ ∩ Vm ⁻¹' (Up ∩ Metric.ball 0 1) with hU₂
    have hU₂open : IsOpen U₂ :=
      hVmcont.isOpen_inter_preimage hU₁open (hUpopen.inter isOpen_ball)
    have hz₀U₂ : z₀ ∈ U₂ := by
      refine ⟨hz₀U₁, ?_⟩
      rw [Set.mem_preimage, hVmz₀]
      refine ⟨hV₀U, ?_⟩
      rw [Metric.mem_ball, dist_zero_right]
      exact hV₀1
    have hRTcont : ContinuousOn (fun w : ℂ => RT j (Vm w)) U₂ := by
      rw [hRT]
      simp only []
      apply Complex.continuous_exp.comp_continuousOn
      apply ContinuousOn.div_const
      apply ContinuousOn.add ?_ continuousOn_const
      apply ContinuousOn.clog ((hVmcont.mono Set.inter_subset_left))
      intro w hw
      have h2 : Vm w ∈ Up := (Set.mem_preimage.mp hw.2).1
      exact hUpslit h2
    set U₃ : Set ℂ := U₂ ∩ (fun w : ℂ => RT j (Vm w)) ⁻¹' Wo with hU₃
    have hU₃open : IsOpen U₃ := hRTcont.isOpen_inter_preimage hU₂open hWopen
    have hz₀U₃ : z₀ ∈ U₃ := by
      refine ⟨hz₀U₂, ?_⟩
      rw [Set.mem_preimage, hVmz₀]
      exact hRTW
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp (hU₃open.mem_nhds hz₀U₃)
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    have hwU₃ : z.1 ∈ U₃ := hεsub (by rw [Metric.mem_ball, dist_eq_norm]; exact hz)
    obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hwU₃
    set V : ℂ := Vm z.1 with hVdef
    have hVU : V ∈ Up := (Set.mem_preimage.mp hw2).1
    have hzne : z.1 ≠ 0 := by
      intro hcon
      have h2 : (0 : ℝ) < ((z.1 / polyVertex g c).re) := hw1
      rw [hcon, zero_div] at h2
      simp at h2
    have hζne : z.1 / polyVertex g c ≠ 0 := div_ne_zero hzne (hpvne c)
    have hwexp : z.1 = polyVertex g c * Complex.exp (Complex.I * V) := by
      have h1 : Complex.I * V = Complex.log (z.1 / polyVertex g c) := by
        rw [hVdef, hVm]
        simp only []
        calc Complex.I * (-Complex.I * Complex.log (z.1 / polyVertex g c))
            = -(Complex.I * Complex.I) * Complex.log (z.1 / polyVertex g c) := by ring
          _ = Complex.log (z.1 / polyVertex g c) := by
              rw [Complex.I_mul_I]
              ring
      rw [h1, Complex.exp_log hζne, mul_comm]
      exact (div_mul_cancel₀ z.1 (hpvne c)).symm
    have hVim : 0 ≤ V.im := by
      have h1 : V.im = -(Complex.log (z.1 / polyVertex g c)).re := by
        rw [hVdef, hVm]
        have h2 : (-Complex.I * Complex.log (z.1 / polyVertex g c)).im
            = -(Complex.log (z.1 / polyVertex g c)).re := by
          simp [Complex.mul_im]
        exact h2
      rw [h1, Complex.log_re]
      have h2 : ‖z.1 / polyVertex g c‖ = ‖z.1‖ := by
        rw [Complex.norm_div, hvert, div_one]
      rw [h2]
      have h3 : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have := Real.log_nonpos (norm_nonneg _) h3
      linarith
    have hVne : V ≠ 0 := by
      intro hcon
      rcases hVU with h | h <;> rw [hcon] at h <;> simp at h
    have hVarg0 : 0 ≤ V.arg := Complex.arg_nonneg_iff.mpr hVim
    have hVargπ : V.arg < Real.pi := by
      rcases lt_or_eq_of_le (Complex.arg_le_pi V) with h | h
      · exact h
      · exfalso
        obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp h
        rcases hVU with h2 | h2
        · linarith
        · linarith [him ▸ h2]
    have hu := hroot j hj V hVne hVarg0 hVargπ
    apply hzT z (RT j V) hw3
    rw [hu, hwexp]
  -- partner-ball lemma: coverage around a corner point on the clockwise ray
  have hballC : ∀ (n j₂ : ℕ), n < 4 * g → j₂ < 4 * g →
      (((j₂ : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1) →
      ∀ θ₀ : ℝ, 0 < θ₀ → θ₀ < h₀ / 2 → RT j₂ ((θ₀ : ℝ) : ℂ) ∈ Wo →
      ∃ ε, 0 < ε ∧ ∀ z : ClosedDisc,
        ‖z.1 - polyVertex g ((vertexSlot g ((n : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (-(Complex.I * ((θ₀ : ℝ) : ℂ)))‖ < ε → z ∈ T := by
    intro n j₂ hn hj₂4 hj₂c θ₀ hθ₀0 hθ₀h hRTW
    set c : ℤ := ((vertexSlot g ((n : ℕ) : ZMod (4 * g))).val : ℤ) with hc
    set z₀ : ℂ := polyVertex g c * Complex.exp (-(Complex.I * ((θ₀ : ℝ) : ℂ))) with hz₀d
    have hπ2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have hθ₀π : θ₀ < Real.pi / 2 := by
      have h1 : h₀ / 2 ≤ Real.pi / 4 := by linarith [hh2]
      linarith
    have hζ₀ : z₀ / polyVertex g c = Complex.exp (Complex.I * ((-θ₀ : ℝ) : ℂ)) := by
      rw [hz₀d, mul_comm, mul_div_assoc, div_self (hpvne c), mul_one]
      congr 1
      push_cast
      ring
    have hlogexp : Complex.log (Complex.exp (Complex.I * ((-θ₀ : ℝ) : ℂ)))
        = Complex.I * ((-θ₀ : ℝ) : ℂ) := by
      apply Complex.log_exp
      · have him : (Complex.I * ((-θ₀ : ℝ) : ℂ)).im = -θ₀ := by
          simp [Complex.mul_im]
        rw [him]
        linarith
      · have him : (Complex.I * ((-θ₀ : ℝ) : ℂ)).im = -θ₀ := by
          simp [Complex.mul_im]
        rw [him]
        linarith
    set Vm : ℂ → ℂ := fun w => -Complex.I * Complex.log (w / polyVertex g c) with hVm
    have hVmz₀ : Vm z₀ = ((-θ₀ : ℝ) : ℂ) := by
      rw [hVm]
      simp only []
      rw [hζ₀, hlogexp]
      calc -Complex.I * (Complex.I * ((-θ₀ : ℝ) : ℂ))
          = -(Complex.I * Complex.I) * ((-θ₀ : ℝ) : ℂ) := by ring
        _ = ((-θ₀ : ℝ) : ℂ) := by rw [Complex.I_mul_I]; ring
    set U₁ : Set ℂ := {w : ℂ | 0 < (w / polyVertex g c).re} with hU₁
    have hU₁open : IsOpen U₁ := by
      have hcont : Continuous fun w : ℂ => (w / polyVertex g c).re :=
        Complex.continuous_re.comp (continuous_id.div_const _)
      exact isOpen_lt continuous_const hcont
    have hz₀U₁ : z₀ ∈ U₁ := by
      change 0 < (z₀ / polyVertex g c).re
      rw [hζ₀, Complex.exp_re]
      apply mul_pos (Real.exp_pos _)
      have him : (Complex.I * ((-θ₀ : ℝ) : ℂ)).im = -θ₀ := by simp [Complex.mul_im]
      rw [him]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> [linarith; linarith]
    have hVmcont : ContinuousAt Vm z₀ := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.clog (continuousAt_id.div_const _)
      have h1 : z₀ / polyVertex g c ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl hz₀U₁)
      exact h1
    -- the two membership certificates
    have hIm_nonneg : ∀ w : ℂ, w ∈ D → 0 ≤ (Vm w).im := by
      intro w hw
      by_cases hw0 : w = 0
      · rw [hVm]
        simp only []
        rw [hw0, zero_div, Complex.log_zero, mul_zero]
        norm_num
      · have h1 : (Vm w).im = -(Complex.log (w / polyVertex g c)).re := by
          rw [hVm]
          have h2 : (-Complex.I * Complex.log (w / polyVertex g c)).im
              = -(Complex.log (w / polyVertex g c)).re := by
            simp [Complex.mul_im]
          exact h2
        rw [h1, Complex.log_re]
        have h2 : ‖w / polyVertex g c‖ = ‖w‖ := by
          rw [Complex.norm_div, hvert, div_one]
        rw [h2]
        have h3 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
        have := Real.log_nonpos (norm_nonneg _) h3
        linarith
    -- the interior root map, continuous within `D` at `z₀`
    have hΨ₁ : ContinuousWithinAt (fun w : ℂ => RT n (Vm w)) D z₀ := by
      have hlog : ContinuousWithinAt (fun w : ℂ => Complex.log (Vm w)) D z₀ := by
        have hbase : ContinuousWithinAt Complex.log {v : ℂ | 0 ≤ v.im} (Vm z₀) := by
          rw [hVmz₀]
          apply Complex.continuousWithinAt_log_of_re_neg_of_im_zero
          · simpa using hθ₀0
          · simp
        exact hbase.comp hVmcont.continuousWithinAt hIm_nonneg
      have haff : ContinuousWithinAt (fun w : ℂ =>
          (Complex.log (Vm w) + (n : ℕ) * Real.pi * Complex.I) / ((2 * (g : ℝ) : ℝ) : ℂ)) D
          z₀ := (hlog.add continuousWithinAt_const).div_const _
      rw [hRT]
      simp only []
      exact Complex.continuous_exp.continuousAt.comp_continuousWithinAt haff
    -- its boundary value is the paired root
    have hlogneg : Complex.log ((-θ₀ : ℝ) : ℂ)
        = ((Real.log θ₀ : ℝ) : ℂ) + Real.pi * Complex.I := by
      apply Complex.ext
      · rw [Complex.log_re]
        have h1 : ‖((-θ₀ : ℝ) : ℂ)‖ = θ₀ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : -θ₀ < 0)]
          ring
        rw [h1]
        simp
      · rw [Complex.log_im, Complex.arg_ofReal_of_neg (by linarith : -θ₀ < 0)]
        simp
    have hlim : RT n ((-θ₀ : ℝ) : ℂ) = RT j₂ ((θ₀ : ℝ) : ℂ) := by
      rw [hRT]
      simp only []
      rw [hlogneg, ← Complex.ofReal_log hθ₀0.le]
      -- exponents differ by an integer multiple of `2πi`
      rw [Complex.exp_eq_exp_iff_exists_int]
      have hj₂Z : ((j₂ : ℤ) : ZMod (4 * g)) = ((n + 1 : ℤ) : ZMod (4 * g)) := by
        push_cast
        rw [hj₂c]
      rw [ZMod.intCast_eq_intCast_iff] at hj₂Z
      obtain ⟨q, hq⟩ := Int.ModEq.dvd hj₂Z
      refine ⟨q, ?_⟩
      have hqR : ((n : ℝ) + 1) - (j₂ : ℝ) = 4 * g * q := by
        have : ((n + 1 : ℤ) : ℝ) - ((j₂ : ℤ) : ℝ) = ((4 * g : ℕ) : ℝ) * (q : ℝ) := by
          exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) hq
        push_cast at this
        linarith
      have hqC : ((n : ℂ) + 1) - (j₂ : ℂ) = 4 * g * q := by exact_mod_cast hqR
      have hne : (((2 * (g : ℝ) : ℝ)) : ℂ) ≠ 0 := by
        push_cast
        intro hcon
        exact hgC (by linear_combination hcon / 2)
      field_simp
      push_cast
      linear_combination (Real.pi : ℂ) * Complex.I * hqC
    -- the jump root map, continuous at `z₀`
    have hΨ₂ : ContinuousAt (fun w : ℂ => RT j₂ ((( -(Vm w).re : ℝ)) : ℂ)) z₀ := by
      have hre : ContinuousAt (fun w : ℂ => ((( -(Vm w).re : ℝ)) : ℂ)) z₀ := by
        apply Complex.continuous_ofReal.continuousAt.comp
        exact (Complex.continuous_re.continuousAt.comp hVmcont).neg
      have hval : ((( -(Vm z₀).re : ℝ)) : ℂ) = ((θ₀ : ℝ) : ℂ) := by
        rw [hVmz₀]
        simp
      have hlogc : ContinuousAt (fun w : ℂ => Complex.log ((( -(Vm w).re : ℝ)) : ℂ)) z₀ := by
        apply ContinuousAt.clog hre
        rw [hval]
        apply Complex.mem_slitPlane_iff.mpr
        left
        simpa using hθ₀0
      rw [hRT]
      simp only []
      apply Complex.continuous_exp.continuousAt.comp
      exact (hlogc.add continuousAt_const).div_const _
    -- assemble the eventual conditions within the closed disc
    have hev1 : ∀ᶠ w in nhdsWithin z₀ D, w ∈ U₁ :=
      mem_nhdsWithin_of_mem_nhds (hU₁open.mem_nhds hz₀U₁)
    have hev2 : ∀ᶠ w in nhdsWithin z₀ D,
        Vm w ∈ Metric.ball ((( -θ₀ : ℝ)) : ℂ) (θ₀ / 2) := by
      apply mem_nhdsWithin_of_mem_nhds
      apply hVmcont
      rw [hVmz₀]
      exact isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))
    have hev3 : ∀ᶠ w in nhdsWithin z₀ D,
        RT j₂ ((( -(Vm w).re : ℝ)) : ℂ) ∈ Wo := by
      apply mem_nhdsWithin_of_mem_nhds
      apply hΨ₂
      apply hWopen.mem_nhds
      have hval : ((( -(Vm z₀).re : ℝ)) : ℂ) = ((θ₀ : ℝ) : ℂ) := by
        rw [hVmz₀]
        simp
      change RT j₂ ((( -(Vm z₀).re : ℝ)) : ℂ) ∈ Wo
      rw [hval]
      exact hRTW
    have hev4 : ∀ᶠ w in nhdsWithin z₀ D, RT n (Vm w) ∈ Wo := by
      apply hΨ₁
      apply hWopen.mem_nhds
      change RT n (Vm z₀) ∈ Wo
      rw [hVmz₀, hlim]
      exact hRTW
    have hall := ((hev1.and hev2).and (hev3.and hev4))
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hall
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    have hzD : z.1 ∈ D := z.2
    have hcond := hεsub ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hz, hzD⟩
    obtain ⟨⟨hw1, hw2⟩, hw3, hw4⟩ := hcond
    set V : ℂ := Vm z.1 with hVdef
    have hVball : ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ < θ₀ / 2 := by
      have := hw2
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hVre : V.re < 0 := by
      have h1 : |V.re - (-θ₀)| ≤ ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ := by
        have h2 := Complex.abs_re_le_norm (V - ((( -θ₀ : ℝ)) : ℂ))
        have h3 : (V - ((( -θ₀ : ℝ)) : ℂ)).re = V.re - (-θ₀) := by
          simp
        rwa [h3] at h2
      obtain ⟨h4a, h4b⟩ := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hVball))
      linarith
    set θw : ℝ := -V.re with hθw
    have hθw1 : θ₀ / 2 < θw := by
      have h1 : |V.re - (-θ₀)| ≤ ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ := by
        have h2 := Complex.abs_re_le_norm (V - ((( -θ₀ : ℝ)) : ℂ))
        have h3 : (V - ((( -θ₀ : ℝ)) : ℂ)).re = V.re - (-θ₀) := by simp
        rwa [h3] at h2
      obtain ⟨h4a, h4b⟩ := abs_lt.mp (lt_of_le_of_lt h1 hVball)
      rw [hθw]
      linarith
    have hθw2 : θw < 3 * θ₀ / 2 := by
      have h1 : |V.re - (-θ₀)| ≤ ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ := by
        have h2 := Complex.abs_re_le_norm (V - ((( -θ₀ : ℝ)) : ℂ))
        have h3 : (V - ((( -θ₀ : ℝ)) : ℂ)).re = V.re - (-θ₀) := by simp
        rwa [h3] at h2
      obtain ⟨h4a, h4b⟩ := abs_lt.mp (lt_of_le_of_lt h1 hVball)
      rw [hθw]
      linarith
    have hzne : z.1 ≠ 0 := by
      intro hcon
      have h2 : (0 : ℝ) < ((z.1 / polyVertex g c).re) := hw1
      rw [hcon, zero_div] at h2
      simp at h2
    have hζne : z.1 / polyVertex g c ≠ 0 := div_ne_zero hzne (hpvne c)
    have hwexp : z.1 = polyVertex g c * Complex.exp (Complex.I * V) := by
      have h1 : Complex.I * V = Complex.log (z.1 / polyVertex g c) := by
        rw [hVdef, hVm]
        simp only []
        calc Complex.I * (-Complex.I * Complex.log (z.1 / polyVertex g c))
            = -(Complex.I * Complex.I) * Complex.log (z.1 / polyVertex g c) := by ring
          _ = Complex.log (z.1 / polyVertex g c) := by
              rw [Complex.I_mul_I]
              ring
      rw [h1, Complex.exp_log hζne, mul_comm]
      exact (div_mul_cancel₀ z.1 (hpvne c)).symm
    have hVim : 0 ≤ V.im := hIm_nonneg z.1 hzD
    rcases lt_or_eq_of_le hVim with hVim' | hVim'
    · -- interior side: direct root in sector `n`
      have hVne : V ≠ 0 := by
        intro hcon
        rw [hcon] at hVim'
        simp at hVim'
      have hVarg0 : 0 ≤ V.arg := Complex.arg_nonneg_iff.mpr hVim
      have hVargπ : V.arg < Real.pi := by
        rcases lt_or_eq_of_le (Complex.arg_le_pi V) with h | h
        · exact h
        · exfalso
          obtain ⟨-, him⟩ := Complex.arg_eq_pi_iff.mp h
          rw [him] at hVim'
          exact absurd hVim' (lt_irrefl 0)
      have hu := hroot n hn V hVne hVarg0 hVargπ
      apply hzT z (RT n V) hw4
      rw [hu, hwexp]
    · -- boundary: jump across the ray
      have hVreal : V = ((( -θw : ℝ)) : ℂ) := by
        apply Complex.ext
        · rw [hθw]
          simp
        · rw [← hVim']
          simp
      have hθC : ((θw : ℝ) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < θw := by linarith
        exact_mod_cast ne_of_gt this
      have hargθ : Complex.arg ((θw : ℝ) : ℂ) = 0 :=
        Complex.arg_ofReal_of_nonneg (by linarith)
      have hu := hroot j₂ hj₂4 ((θw : ℝ) : ℂ) hθC (by rw [hargθ]) (by rw [hargθ]; exact hπ)
      apply hzT z (RT j₂ ((θw : ℝ) : ℂ))
      · have hval : ((( -(Vm z.1).re : ℝ)) : ℂ) = ((θw : ℝ) : ℂ) := by
          rw [← hVdef, hθw]
        rw [← hval]
        exact hw3
      · rw [hu]
        have hslot2 : vertexSlot g ((j₂ : ℕ) : ZMod (4 * g))
            = vertexSlot g (((n : ℕ) : ZMod (4 * g)) + 1) := by
          rw [hj₂c]
        rw [hslot2]
        rw [← hglueθ n θw (by linarith) (by linarith)]
        congr 2
        rw [hwexp, hVreal]
        congr 1
        push_cast
        ring_nf
  -- main dispatch
  apply hopen_of_balls
  intro z₀ hz₀
  rw [hT] at hz₀
  obtain ⟨u₀, hu₀W, hfu₀⟩ := hz₀
  obtain ⟨α₀, φ₀, W₀, c, hcdef, ⟨hc0, hc4⟩, hm4, hue, hWdef, ⟨hW00, hWlt⟩, ⟨hφ0, hφπ⟩,
    hφdef, hIV, hz9, hnle, hzero⟩ := hsetup u₀ (hWsub hu₀W)
  have hrel : genusRel g
      (projDisc (polyVertex g
          ((vertexSlot g ((vertexSectorIndex g u₀ : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u₀) * u₀ ^ (2 * g)))) z₀ :=
    Quotient.exact hfu₀
  rw [← hcdef] at hrel
  set m : ℕ := vertexSectorIndex g u₀ with hmdef
  by_cases hW₀ : W₀ = 0
  · -- the value is the vertex class
    have hu₀0 : u₀ = 0 := hzero hW₀
    have h0W : (0 : ℂ) ∈ Wo := by
      rw [← hu₀0]
      exact hu₀W
    rw [hu₀0, zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one] at hrel
    have hpvdisc : (projDisc (polyVertex g c)).1 = polyVertex g c :=
      projDisc_eq (le_of_eq (hvert c))
    have hzvert : IsPolyVertex g z₀.1 := by
      rcases hrel with h1 | ⟨k, -, hpg | hpg⟩ | ⟨-, hv'⟩
      · have hval := congrArg Subtype.val h1
        rw [hpvdisc] at hval
        exact ⟨c, hval.symm⟩
      · exact (pairGraph_vertex_iff g k hpg).mp (by rw [hpvdisc]; exact ⟨c, rfl⟩)
      · exact (pairGraph_vertex_iff g k hpg).mpr (by rw [hpvdisc]; exact ⟨c, rfl⟩)
      · exact hv'
    obtain ⟨p, hp⟩ := hzvert
    obtain ⟨ε, hε0, hball⟩ := hballB h0W p
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    apply hball z
    rw [← hp]
    exact hz
  · -- positive radius
    have hW₀pos : 0 < W₀ := lt_of_le_of_ne hW00 (Ne.symm hW₀)
    set V₀ : ℂ := (((W₀ * Real.cos φ₀ : ℝ)) : ℂ) + (((W₀ * Real.sin φ₀ : ℝ)) : ℂ) * Complex.I
      with hV₀d
    have hV₀exp : V₀ = ((W₀ : ℝ) : ℂ) * Complex.exp (((φ₀ : ℝ) : ℂ) * Complex.I) := by
      rw [hV₀d, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    have hV₀norm : ‖V₀‖ = W₀ := by
      rw [hV₀exp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW₀pos]
      have h2 : ((φ₀ : ℝ) : ℂ) * Complex.I = ((φ₀ : ℝ) : ℂ) * Complex.I := rfl
      rw [Complex.norm_exp_ofReal_mul_I, mul_one]
    have hV₀ne : V₀ ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hV₀norm
      exact hW₀ hV₀norm.symm
    have hV₀arg : V₀.arg = φ₀ := by
      rw [hV₀exp, Complex.arg_real_mul _ hW₀pos, Complex.exp_mul_I]
      exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, hφπ.le⟩
    have hV₀arg0 : 0 ≤ V₀.arg := by
      rw [hV₀arg]
      exact hφ0
    have hV₀argπ : V₀.arg < Real.pi := by
      rw [hV₀arg]
      exact hφπ
    have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
    have hV₀1 : ‖V₀‖ < 1 := by
      rw [hV₀norm]
      have h1 : h₀ / 4 ≤ Real.pi / 8 := by linarith [hh2]
      linarith
    -- the root recovers `u₀`
    have hu₀ne : u₀ ≠ 0 := by
      intro hcon
      apply hW₀
      rw [hWdef, hcon, norm_zero]
      exact zero_pow (by omega)
    have hRTV₀ : RT m V₀ = u₀ := by
      have hlogV₀ : Complex.log V₀ = ((Real.log W₀ : ℝ) : ℂ) + ((φ₀ : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · rw [Complex.log_re, hV₀norm]
          simp
        · rw [Complex.log_im, hV₀arg]
          simp
      have hnormpos : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀ne
      have hueexp : u₀
          = Complex.exp (((Real.log ‖u₀‖ : ℝ) : ℂ) + ((α₀ : ℝ) : ℂ) * Complex.I) := by
        rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hnormpos]
        exact hue
      rw [hRT]
      simp only []
      rw [hlogV₀, hueexp]
      congr 1
      have hlogW : Real.log W₀ = 2 * g * Real.log ‖u₀‖ := by
        rw [hWdef, Real.log_pow]
        push_cast
        ring
      have hlogWC : ((Real.log W₀ : ℝ) : ℂ) = 2 * g * ((Real.log ‖u₀‖ : ℝ) : ℂ) := by
        exact_mod_cast hlogW
      have hφαR : φ₀ = 2 * g * α₀ - (m : ℝ) * Real.pi := hφdef
      have hφαC : ((φ₀ : ℝ) : ℂ) = 2 * g * ((α₀ : ℝ) : ℂ) - (m : ℂ) * Real.pi := by
        exact_mod_cast hφαR
      have hne2g : (((2 * (g : ℝ) : ℝ)) : ℂ) ≠ 0 := by
        push_cast
        intro hcon
        exact hgC (by linear_combination hcon / 2)
      field_simp
      push_cast
      linear_combination hlogWC + Complex.I * hφαC
    rcases hrel with h1 | ⟨k, hk4, hpg | hpg⟩ | ⟨hv, -⟩
    · -- clause 1: the point is the corner point itself
      have hval := congrArg Subtype.val h1
      rw [projDisc_eq hnle] at hval
      have hzform : z₀.1 = polyVertex g c * Complex.exp (Complex.I * V₀) := by
        rw [← hval, hIV]
      obtain ⟨ε, hε0, hball⟩ := hballA m hm4 V₀ hV₀ne hV₀arg0 hV₀argπ hV₀1
        (by rw [hRTV₀]; exact hu₀W)
      refine ⟨ε, hε0, ?_⟩
      intro z hz
      apply hball z
      rw [← hcdef, ← hzform]
      exact hz
    · -- pairing, order A: the corner point lies on the source arc `k`
      obtain ⟨t, -, hteq⟩ := hpg
      have ht1 := congrArg Prod.fst hteq
      have ht2 := congrArg Prod.snd hteq
      simp only at ht1 ht2
      rw [projDisc_eq hnle] at ht1
      rw [hz9] at ht1
      rw [harc2] at ht1
      obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ ht1
      have hφ00 : φ₀ = 0 := hcollapse W₀ φ₀ hW₀pos hφ0 hφπ hy₁.symm
      rw [hφ00, Real.cos_zero, mul_one] at hx₁
      have hW₀e : W₀ = h₀ * ((t : ℝ) - ((c - k + 4 * g * n₁ : ℤ) : ℝ)) := by
        push_cast
        linear_combination -hx₁ - (by rw [← h4gh] :
          2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁)
      rcases hWpin W₀ _ (t : ℝ) hW00 hWlt t.2.1 t.2.2 hW₀e with ⟨he₁, hW₀t⟩ | ⟨-, hW₀z⟩
      swap
      · exact absurd hW₀z hW₀
      -- source case: `c ≡ k`, partner corner is `c + 3`
      have hck : c - k + 4 * g * n₁ = 0 := he₁
      have hcmod : c % 4 = k % 4 := by
        have hdvd : (4 : ℤ) ∣ k - c := ⟨g * n₁, by linarith⟩
        have := Int.emod_emod_of_dvd c hdvd
        omega
      -- the predecessor sector
      set n : ℕ := if m = 0 then 4 * g - 1 else m - 1 with hn
      have hn4 : n < 4 * g := by
        rw [hn]
        split_ifs <;> omega
      have hncast : ((n : ℕ) : ZMod (4 * g)) = ((m : ℕ) : ZMod (4 * g)) - 1 := by
        rw [hn]
        split_ifs with hcase
        · rw [hcase, Nat.cast_zero, Nat.cast_sub (by omega : 1 ≤ 4 * g)]
          push_cast
          have h4g0 : (4 : ZMod (4 * g)) * (g : ZMod (4 * g)) = 0 := by
            have h5 := ZMod.natCast_self (4 * g)
            push_cast at h5
            exact h5
          rw [h4g0]
        · rw [Nat.cast_sub (by omega : 1 ≤ m)]
          push_cast
          ring
      have hj₂c : ((m : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1 := by
        rw [hncast]
        ring
      have hCm : ((c : ℤ) : ZMod (4 * g)) = vertexSlot g ((m : ℕ) : ZMod (4 * g)) := by
        rw [hcdef]
        exact hcast _
      have hsucc := vertexSlot_succ g ((n : ℕ) : ZMod (4 * g))
      rw [← hj₂c] at hsucc
      set s : ZMod (4 * g) := vertexSlot g ((n : ℕ) : ZMod (4 * g)) with hs
      have hCval : ((((c : ℤ) : ZMod (4 * g))).val : ℤ) = c := by
        rw [hCm, ← hcdef]
      have hsn : s = ((c + 3 : ℤ) : ZMod (4 * g)) := by
        by_cases hcond : ((s - 1).val % 4 = 0 ∨ (s - 1).val % 4 = 1)
        · exfalso
          have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s + 1 := by
            rw [hsucc]
            unfold pairInv
            rw [ite_eq_left hcond]
            ring
          have h2 : s - 1 = ((c : ℤ) : ZMod (4 * g)) - 2 := by
            rw [hCm, h1]
            ring
          rw [h2, hminus2] at hcond
          omega
        · have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s - 3 := by
            rw [hsucc]
            unfold pairInv
            rw [ite_eq_right hcond]
            ring
          have h2 : s = ((c : ℤ) : ZMod (4 * g)) + 3 := by
            rw [hCm, h1]
            ring
          rw [h2]
          push_cast
          ring
      obtain ⟨q₂, hq₂⟩ : ∃ q₂ : ℤ, ((s.val : ℤ)) = c + 3 + 4 * g * q₂ := by
        have h1 : ((s.val : ℤ) : ZMod (4 * g)) = ((c + 3 : ℤ) : ZMod (4 * g)) := by
          rw [hcast s, hsn]
        rw [ZMod.intCast_eq_intCast_iff] at h1
        obtain ⟨q₂, hq₂⟩ := Int.ModEq.dvd h1
        refine ⟨-q₂, ?_⟩
        push_cast at hq₂ ⊢
        linarith
      have hz₀form : z₀.1 = polyVertex g ((s.val : ℤ)) *
          Complex.exp (-(Complex.I * ((W₀ : ℝ) : ℂ))) := by
        rw [hcornerexp]
        rw [← ht2, harc2]
        rw [Complex.ofReal_zero, zero_mul, add_zero]
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨n₁ - q₂, ?_⟩
        have hq₂R : ((s.val : ℤ) : ℝ) = c + 3 + 4 * g * q₂ := by exact_mod_cast hq₂
        have hckR : (c : ℝ) - k + 4 * g * n₁ = 0 := by exact_mod_cast hck
        have h2πR : 2 * Real.pi = 4 * (g : ℝ) * h₀ := by linarith [h4gh]
        have hreal : h₀ * (((k : ℝ) + 2) + (1 - (t : ℝ)))
            = (h₀ * ((s.val : ℤ) : ℝ) - W₀) + 2 * Real.pi * ((n₁ : ℝ) - q₂) := by
          rw [hq₂R, hW₀t, h2πR]
          linear_combination (-h₀) * hckR
        have hC : ((h₀ * (((k : ℝ) + 2) + (1 - (t : ℝ))) : ℝ) : ℂ)
            = ((h₀ * ((s.val : ℤ) : ℝ) - W₀ : ℝ) : ℂ)
              + 2 * Real.pi * (((n₁ : ℝ) - q₂ : ℝ) : ℂ) := by
          exact_mod_cast hreal
        push_cast at hC ⊢
        linear_combination Complex.I * hC
      have hW₀h2 : W₀ < h₀ / 2 := by linarith
      have hRTW₀ : RT m ((W₀ : ℝ) : ℂ) ∈ Wo := by
        have hV₀W : V₀ = ((W₀ : ℝ) : ℂ) := by
          rw [hV₀d, hφ00]
          simp
        rw [← hV₀W, hRTV₀]
        exact hu₀W
      obtain ⟨ε, hε0, hball⟩ := hballC n m hn4 hm4 hj₂c W₀ hW₀pos hW₀h2 hRTW₀
      refine ⟨ε, hε0, ?_⟩
      intro z hz
      apply hball z
      rw [← hz₀form]
      exact hz
    · -- pairing, order B: the point lies on the source arc `k`
      obtain ⟨t, -, hteq⟩ := hpg
      have ht1 := congrArg Prod.fst hteq
      have ht2 := congrArg Prod.snd hteq
      simp only at ht1 ht2
      rw [projDisc_eq hnle] at ht2
      rw [hz9] at ht2
      rw [harc2] at ht2
      obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ ht2
      have hφ00 : φ₀ = 0 := hcollapse W₀ φ₀ hW₀pos hφ0 hφπ hy₁.symm
      rw [hφ00, Real.cos_zero, mul_one] at hx₁
      have hW₀e : W₀ = h₀ * ((1 - (t : ℝ)) - ((c - (k + 2) + 4 * g * n₁ : ℤ) : ℝ)) := by
        push_cast
        push_cast at hx₁
        linear_combination -hx₁ - (by rw [← h4gh] :
          2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁)
      rcases hWpin W₀ _ (1 - (t : ℝ)) hW00 hWlt (by linarith [t.2.2]) (by linarith [t.2.1])
        hW₀e with ⟨he₁, hW₀t⟩ | ⟨-, hW₀z⟩
      swap
      · exact absurd hW₀z hW₀
      have hck : c - (k + 2) + 4 * g * n₁ = 0 := he₁
      have hcmod : c % 4 = (k + 2) % 4 := by
        have hdvd : (4 : ℤ) ∣ (k + 2) - c := ⟨(g : ℤ) * n₁, by linarith⟩
        exact Int.modEq_iff_dvd.mpr hdvd
      set n : ℕ := if m = 0 then 4 * g - 1 else m - 1 with hn
      have hn4 : n < 4 * g := by
        rw [hn]
        split_ifs <;> omega
      have hncast : ((n : ℕ) : ZMod (4 * g)) = ((m : ℕ) : ZMod (4 * g)) - 1 := by
        rw [hn]
        split_ifs with hcase
        · rw [hcase, Nat.cast_zero, Nat.cast_sub (by omega : 1 ≤ 4 * g)]
          push_cast
          have h4g0 : (4 : ZMod (4 * g)) * (g : ZMod (4 * g)) = 0 := by
            have h5 := ZMod.natCast_self (4 * g)
            push_cast at h5
            exact h5
          rw [h4g0]
        · rw [Nat.cast_sub (by omega : 1 ≤ m)]
          push_cast
          ring
      have hj₂c : ((m : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1 := by
        rw [hncast]
        ring
      have hCm : ((c : ℤ) : ZMod (4 * g)) = vertexSlot g ((m : ℕ) : ZMod (4 * g)) := by
        rw [hcdef]
        exact hcast _
      have hsucc := vertexSlot_succ g ((n : ℕ) : ZMod (4 * g))
      rw [← hj₂c] at hsucc
      set s : ZMod (4 * g) := vertexSlot g ((n : ℕ) : ZMod (4 * g)) with hs
      have hCval : ((((c : ℤ) : ZMod (4 * g))).val : ℤ) = c := by
        rw [hCm, ← hcdef]
      have hsn : s = ((c - 1 : ℤ) : ZMod (4 * g)) := by
        by_cases hcond : ((s - 1).val % 4 = 0 ∨ (s - 1).val % 4 = 1)
        · have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s + 1 := by
            rw [hsucc]
            unfold pairInv
            rw [ite_eq_left hcond]
            ring
          have h2 : s = ((c : ℤ) : ZMod (4 * g)) - 1 := by
            rw [hCm, h1]
            ring
          rw [h2]
          push_cast
          ring
        · exfalso
          have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s - 3 := by
            rw [hsucc]
            unfold pairInv
            rw [ite_eq_right hcond]
            ring
          have h2 : s - 1 = ((c : ℤ) : ZMod (4 * g)) + 2 := by
            rw [hCm, h1]
            ring
          rw [h2, hplus2] at hcond
          omega
      obtain ⟨q₂, hq₂⟩ : ∃ q₂ : ℤ, ((s.val : ℤ)) = c - 1 + 4 * g * q₂ := by
        have h1 : ((s.val : ℤ) : ZMod (4 * g)) = ((c - 1 : ℤ) : ZMod (4 * g)) := by
          rw [hcast s, hsn]
        rw [ZMod.intCast_eq_intCast_iff] at h1
        obtain ⟨q₂, hq₂⟩ := Int.ModEq.dvd h1
        refine ⟨-q₂, ?_⟩
        push_cast at hq₂ ⊢
        linarith
      have hz₀form : z₀.1 = polyVertex g ((s.val : ℤ)) *
          Complex.exp (-(Complex.I * ((W₀ : ℝ) : ℂ))) := by
        rw [hcornerexp]
        rw [← ht1, harc2]
        rw [Complex.ofReal_zero, zero_mul, add_zero]
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨n₁ - q₂, ?_⟩
        have hq₂R : ((s.val : ℤ) : ℝ) = c - 1 + 4 * g * q₂ := by exact_mod_cast hq₂
        have hckR : (c : ℝ) - (k + 2) + 4 * g * n₁ = 0 := by exact_mod_cast hck
        have h2πR : 2 * Real.pi = 4 * (g : ℝ) * h₀ := by linarith [h4gh]
        have hreal : h₀ * ((k : ℝ) + (t : ℝ))
            = (h₀ * ((s.val : ℤ) : ℝ) - W₀) + 2 * Real.pi * ((n₁ : ℝ) - q₂) := by
          rw [hq₂R, hW₀t, h2πR]
          linear_combination (-h₀) * hckR
        have hC : ((h₀ * ((k : ℝ) + (t : ℝ)) : ℝ) : ℂ)
            = ((h₀ * ((s.val : ℤ) : ℝ) - W₀ : ℝ) : ℂ)
              + 2 * Real.pi * (((n₁ : ℝ) - q₂ : ℝ) : ℂ) := by
          exact_mod_cast hreal
        push_cast at hC ⊢
        linear_combination Complex.I * hC
      have hW₀h2 : W₀ < h₀ / 2 := by linarith
      have hRTW₀ : RT m ((W₀ : ℝ) : ℂ) ∈ Wo := by
        have hV₀W : V₀ = ((W₀ : ℝ) : ℂ) := by
          rw [hV₀d, hφ00]
          simp
        rw [← hV₀W, hRTV₀]
        exact hu₀W
      obtain ⟨ε, hε0, hball⟩ := hballC n m hn4 hm4 hj₂c W₀ hW₀pos hW₀h2 hRTW₀
      refine ⟨ε, hε0, ?_⟩
      intro z hz
      apply hball z
      rw [← hz₀form]
      exact hz
    · -- vertex clause is impossible at positive radius
      exfalso
      obtain ⟨p, hp⟩ := hv
      rw [projDisc_eq hnle, hz9, hpv2 p] at hp
      obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ hp
      have hφ00 : φ₀ = 0 := hcollapse W₀ φ₀ hW₀pos hφ0 hφπ hy₁
      rw [hφ00, Real.cos_zero, mul_one] at hx₁
      have hW₀e : W₀ = h₀ * ((0 : ℝ) - ((c - p - 4 * g * n₁ : ℤ) : ℝ)) := by
        push_cast
        linear_combination hx₁ + (by rw [← h4gh] :
          2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁)
      rcases hWpin W₀ _ 0 hW00 hWlt le_rfl (by norm_num) hW₀e with ⟨-, hW₀t⟩ | ⟨h01, -⟩
      · rw [mul_zero] at hW₀t
        exact hW₀ hW₀t
      · exact absurd h01 (by norm_num)

/-- The vertex chart at the single vertex class, compressing the `4g`
corners of angle `π` into `4g` sectors of angle `π/(2g)`. -/
noncomputable def vertexChart (g : ℕ) [NeZero g] :
    OpenPartialHomeomorph (GenusSurface g) ℂ :=
  OpenPartialHomeomorph.ofInvFunOn (vertexChartFun g)
    (Metric.ball 0 (vertexRadius g)) isOpen_ball (vertexChart_continuousOn g)
    (vertexChart_injOn g) (vertexChart_isOpen_image g)

/-! ## The atlas and the charted-space instance -/

/-- The atlas of the genus surface: the interior chart, the `2g` edge
charts, and the vertex chart. -/
noncomputable def genusAtlas (g : ℕ) [NeZero g] :
    Set (OpenPartialHomeomorph (GenusSurface g) ℂ) :=
  {interiorChart g} ∪ (Set.range fun jb : Fin g × Bool => edgeChart g jb.1 jb.2)
    ∪ {vertexChart g}

/-- Every class of the genus surface contains an interior point, an
edge-interior point, or is the vertex class, so the chart sources cover. -/
theorem chart_sources_cover (g : ℕ) [NeZero g] (p : GenusSurface g) :
    p ∈ (interiorChart g).source ∨
      (∃ jb : Fin g × Bool, p ∈ (edgeChart g jb.1 jb.2).source) ∨
      p ∈ (vertexChart g).source := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have : NeZero (4 * g) := ⟨by omega⟩
  have harc : ∀ (k : ℤ) (t : ℝ), ‖arcPoint g k t‖ = 1 := by
    intro k t
    have hrw : arcPoint g k t
        = Complex.exp (((Real.pi * ((k : ℝ) + t) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold arcPoint
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hvert : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    have hrw : polyVertex g m
        = Complex.exp (((Real.pi * (m : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  obtain ⟨z, rfl⟩ := Quotient.exists_rep p
  have hz1 : ‖z.1‖ ≤ 1 := by
    have hz2 := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at hz2
  rcases lt_or_eq_of_le hz1 with hlt | hcirc
  · -- Interior point: the interior chart.
    left
    rw [interiorChart_source]
    exact ⟨z, hlt, rfl⟩
  · -- Boundary point: write `z.1 = arcPoint g m t` with `t ∈ [0, 1)`.
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 2 * g * Complex.arg z.1 / Real.pi := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, m = ⌊x⌋ := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x - m := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by
      rw [ht, hm]
      exact sub_nonneg.mpr (Int.floor_le x)
    have ht1 : t < 1 := by
      rw [ht, hm]
      have := Int.lt_floor_add_one x
      linarith
    have h1exp := Complex.norm_mul_exp_arg_mul_I z.1
    rw [hcirc, Complex.ofReal_one, one_mul] at h1exp
    have harcz : arcPoint g m t = z.1 := by
      have hmt : (m : ℝ) + t = x := by rw [ht]; ring
      have hang : Real.pi * ((m : ℝ) + t) / (2 * g) = Complex.arg z.1 := by
        rw [hmt, hx]
        field_simp
      rw [← h1exp]
      unfold arcPoint
      congr 1
      have hangC := congrArg (fun r : ℝ => (r : ℂ)) hang
      push_cast at hangC
      linear_combination Complex.I * hangC
    rcases eq_or_lt_of_le ht0 with ht0' | htpos
    · -- Vertex: `t = 0`, so `z` is a vertex and lies in the vertex chart.
      right; right
      have hzv : z.1 = polyVertex g m := by
        rw [← harcz, ← ht0']
        exact arcPoint_zero g m
      have hsrc : (vertexChart g).source
          = vertexChartFun g '' Metric.ball 0 (vertexRadius g) := rfl
      rw [hsrc]
      refine ⟨0, Metric.mem_ball_self (vertexRadius_pos g), ?_⟩
      have hidx : vertexSectorIndex g 0 = 0 := by
        unfold vertexSectorIndex
        rw [Complex.arg_zero]
        simp
      have hfun0 : vertexChartFun g 0
          = Quotient.mk (genusSetoid g) (projDisc (polyVertex g 0)) := by
        unfold vertexChartFun
        rw [hidx]
        rw [Nat.cast_zero, vertexSlot_zero, ZMod.val_zero, Nat.cast_zero, pow_zero,
          mul_one, zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
      rw [hfun0]
      have hrel : genusRel g (projDisc (polyVertex g 0)) z :=
        Or.inr (Or.inr ⟨⟨0, projDisc_eq (hvert 0).le⟩, ⟨m, hzv⟩⟩)
      exact Quotient.sound hrel
    · -- Edge-interior: `0 < t < 1`, so `z` lies in an edge chart.
      right; left
      obtain ⟨m', hm'⟩ : ∃ m' : ℤ, m' = m % (4 * g) := ⟨_, rfl⟩
      have hgZ : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg1
      have h4g : (0 : ℤ) < 4 * (g : ℤ) := by linarith
      have hm'0 : 0 ≤ m' := hm' ▸ Int.emod_nonneg m (ne_of_gt h4g)
      have hm'lt : m' < 4 * g := hm' ▸ Int.emod_lt_of_pos m h4g
      have harcz' : arcPoint g m' t = z.1 := by
        rw [← harcz, arcPoint_eq_iff]
        refine ⟨-(m / (4 * g)), ?_⟩
        have hZ : m' - m = (4 * g : ℤ) * (-(m / (4 * g))) := by
          rw [hm', Int.emod_def]
          ring
        have hR : (m' : ℝ) - (m : ℝ) = (4 * (g : ℝ)) * (-(((m / (4 * g) : ℤ)) : ℝ)) := by
          exact_mod_cast hZ
        push_cast
        linarith [hR]
      have main : ∀ k : ℤ, 0 ≤ k → k < 4 * g → (k % 4 = 0 ∨ k % 4 = 1) →
          (∃ u ∈ edgeSector g k, edgeChartFun g k u = Quotient.mk (genusSetoid g) z) →
          ∃ jb : Fin g × Bool,
            Quotient.mk (genusSetoid g) z ∈ (edgeChart g jb.1 jb.2).source := by
        intro k hk0 hklt hk4 hex
        obtain ⟨u, hu, hfu⟩ := hex
        have hjlt : (k / 4).toNat < g := by omega
        obtain ⟨b, hb⟩ : ∃ b : Bool, (if b then (1 : ℤ) else 0) = k % 4 := by
          rcases hk4 with h | h
          · exact ⟨false, by rw [ite_eq_right Bool.false_ne_true, h]⟩
          · exact ⟨true, by rw [ite_eq_left rfl, h]⟩
        have hgoal : Quotient.mk (genusSetoid g) z
            ∈ (edgeChart g ⟨(k / 4).toNat, hjlt⟩ b).source := by
          have hidx : (4 * ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) + if b then 1 else 0)
              = k := by
            have h1 : ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) = ((k / 4).toNat : ℤ) := rfl
            rw [h1, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k / 4), hb]
            omega
          have hsrc : (edgeChart g ⟨(k / 4).toNat, hjlt⟩ b).source
              = edgeChartFun g
                  (4 * ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) + if b then 1 else 0) ''
                edgeSector g
                  (4 * ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) + if b then 1 else 0) := rfl
          rw [hsrc, hidx]
          exact ⟨u, hu, hfu⟩
        exact ⟨(⟨(k / 4).toNat, hjlt⟩, b), hgoal⟩
      have hdisj : (m' % 4 = 0 ∨ m' % 4 = 1) ∨
          ((m' - 2) % 4 = 0 ∨ (m' - 2) % 4 = 1) := by omega
      rcases hdisj with hA | hB
      · -- `z` lies on a source arc `m'`.
        refine main m' hm'0 hm'lt hA ⟨arcPoint g m' t, ?_, ?_⟩
        · exact ⟨1, (m' : ℝ) + t, by norm_num, by norm_num, by linarith, by linarith, by
            rw [Complex.ofReal_one, one_mul]
            unfold arcPoint
            congr 1
            push_cast
            ring⟩
        · unfold edgeChartFun
          refine (ite_eq_left (harc m' t).le).trans ?_
          exact congrArg (Quotient.mk (genusSetoid g)) (Subtype.ext (by
            rw [projDisc_eq (harc m' t).le]
            exact harcz'))
      · -- `z` lies on the target arc `m' = (m' - 2) + 2`: use the pairing.
        have hk0 : (0 : ℤ) ≤ m' - 2 := by omega
        have hklt : m' - 2 < 4 * g := by omega
        refine main (m' - 2) hk0 hklt hB ⟨arcPoint g (m' - 2) (1 - t), ?_, ?_⟩
        · exact ⟨1, ((m' - 2 : ℤ) : ℝ) + (1 - t), by norm_num, by norm_num, by linarith,
            by linarith, by
              rw [Complex.ofReal_one, one_mul]
              unfold arcPoint
              congr 1
              push_cast
              ring⟩
        · unfold edgeChartFun
          refine (ite_eq_left (harc (m' - 2) (1 - t)).le).trans ?_
          have hpair : ((projDisc (arcPoint g (m' - 2) (1 - t))).1, z.1)
              ∈ pairGraph g (m' - 2) := by
            refine ⟨⟨1 - t, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩,
              Set.mem_univ _, ?_⟩
            have hfst : arcPoint g (m' - 2) (1 - t)
                = (projDisc (arcPoint g (m' - 2) (1 - t))).1 :=
              (projDisc_eq (harc (m' - 2) (1 - t)).le).symm
            have hsnd : arcPoint g ((m' - 2) + 2) (1 - (1 - t)) = z.1 := by
              rw [(by ring : (m' - 2) + 2 = m'), (by ring : 1 - (1 - t) = t)]
              exact harcz'
            simp only [Prod.mk.injEq]
            exact ⟨hfst, hsnd⟩
          have hrel : genusRel g (projDisc (arcPoint g (m' - 2) (1 - t))) z :=
            Or.inr (Or.inl ⟨m' - 2, hB, Or.inl hpair⟩)
          exact Quotient.sound hrel

open Classical in
/-- The preferred chart at a point: the interior chart when possible, else
an edge chart, else the vertex chart. -/
noncomputable def genusChartAt (g : ℕ) [NeZero g] (p : GenusSurface g) :
    OpenPartialHomeomorph (GenusSurface g) ℂ :=
  if p ∈ (interiorChart g).source then interiorChart g
  else if h : ∃ jb : Fin g × Bool, p ∈ (edgeChart g jb.1 jb.2).source then
    edgeChart g h.choose.1 h.choose.2
  else vertexChart g

/-- Each point lies in the source of its preferred chart. -/
theorem mem_genusChartAt_source (g : ℕ) [NeZero g] (p : GenusSurface g) :
    p ∈ (genusChartAt g p).source := by
  unfold genusChartAt
  split_ifs with h1 h2
  · exact h1
  · exact h2.choose_spec
  · rcases chart_sources_cover g p with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h

/-- The preferred chart belongs to the atlas. -/
theorem genusChartAt_mem_atlas (g : ℕ) [NeZero g] (p : GenusSurface g) :
    genusChartAt g p ∈ genusAtlas g := by
  unfold genusChartAt genusAtlas
  split_ifs with h1 h2
  · exact Set.mem_union_left _ (Set.mem_union_left _ rfl)
  · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨h2.choose, rfl⟩)
  · exact Set.mem_union_right _ rfl

noncomputable instance instChartedSpaceGenusSurface (g : ℕ) [NeZero g] :
    ChartedSpace ℂ (GenusSurface g) where
  atlas := genusAtlas g
  chartAt := genusChartAt g
  mem_chart_source := mem_genusChartAt_source g
  chart_mem_atlas := genusChartAt_mem_atlas g

/-! ## The pairing-root identity -/

/-- The pairing-root identity along the corner cycle: with `n = c m - 1` a
source arc, the pairing root `exp (πi (2 c m + 1)/(2g))` of arc `n` divided
by the vertex `c (m+1)` is the vertex `c m`. -/
theorem pairingRoot_vertexSlot (g : ℕ) [NeZero g] (m : ℕ)
    (hsrc : (((vertexSlot g (m : ZMod (4 * g))).val : ℤ) - 1) % 4 = 0 ∨
      (((vertexSlot g (m : ZMod (4 * g))).val : ℤ) - 1) % 4 = 1) :
    Complex.exp (Real.pi * (2 * ((vertexSlot g (m : ZMod (4 * g))).val : ℤ) + 1) *
        Complex.I / (2 * g)) /
      polyVertex g ((vertexSlot g ((m : ZMod (4 * g)) + 1)).val : ℤ) =
      polyVertex g ((vertexSlot g (m : ZMod (4 * g))).val : ℤ) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have : NeZero (4 * g) := ⟨by omega⟩
  set c := vertexSlot g (m : ZMod (4 * g)) with hc
  set v := c.val with hv
  have hvlt : v < 4 * g := ZMod.val_lt c
  -- `v ≥ 1`: otherwise the source-arc hypothesis reads `(-1) % 4 ∈ {0, 1}`.
  have hv1 : 1 ≤ v := by
    by_contra hcon
    have hv0 : v = 0 := by omega
    rw [hv0] at hsrc
    omega
  -- `v ≠ 4g - 1`: otherwise the hypothesis reads `(4g - 2) % 4 = 2 ∈ {0, 1}`.
  have hvne : v ≠ 4 * g - 1 := by
    intro hcon
    have h2 : (((v : ℤ)) - 1) % 4 = 2 := by omega
    omega
  have hvsucc : v + 1 < 4 * g := by omega
  -- The successor slot is `c + 1`.
  have hsub1 : c - 1 = ((v - 1 : ℕ) : ZMod (4 * g)) := by
    have hcv : ((v : ℕ) : ZMod (4 * g)) = c := ZMod.natCast_rightInverse c
    rw [← hcv, Nat.cast_sub hv1, Nat.cast_one]
  have hpair : vertexSlot g ((m : ZMod (4 * g)) + 1) = c + 1 := by
    rw [vertexSlot_succ, ← hc, hsub1]
    unfold pairInv
    rw [ZMod.val_cast_of_lt (by omega : v - 1 < 4 * g)]
    rw [ite_eq_left (by omega : (v - 1) % 4 = 0 ∨ (v - 1) % 4 = 1)]
    have hcv : ((v : ℕ) : ZMod (4 * g)) = c := ZMod.natCast_rightInverse c
    rw [← hcv, Nat.cast_sub hv1, Nat.cast_one]
    ring
  have hval : (vertexSlot g ((m : ZMod (4 * g)) + 1)).val = v + 1 := by
    rw [hpair]
    have hcv : ((v : ℕ) : ZMod (4 * g)) = c := ZMod.natCast_rightInverse c
    rw [← hcv, ← Nat.cast_one, ← Nat.cast_add]
    exact ZMod.val_cast_of_lt hvsucc
  rw [hval]
  unfold polyVertex
  rw [div_eq_iff (Complex.exp_ne_zero _), ← Complex.exp_add]
  congr 1
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  push_cast
  ring

end RiemannDynamics
