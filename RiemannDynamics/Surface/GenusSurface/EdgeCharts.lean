/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.GenusSurface.Basic

/-!
# The genus-`g` surface: the edge charts

The `2g` edge charts of the `4g`-gon model. Over each source arc `k`
(`k % 4 ∈ {0, 1}`) the open annular sector `edgeSector g k` maps to the
surface by the two-piece gluing map `edgeChartFun g k`: points of the closed
disc project directly, and exterior points are first transported into the
disc by the side pairing. This file proves the map continuous, injective,
and open, and packages the inverse-first charts `edgeChart g j b`.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval
open scoped Manifold

namespace RiemannDynamics

/-! ### The edge charts -/

/-- The open annular sector over the open arc `k`: radii in `(1/2, 2)` and
angle parameter `θ' ∈ (k, k + 1)` in units of `π/(2g)`. -/
noncomputable def edgeSector (g : ℕ) (k : ℤ) : Set ℂ :=
  {u : ℂ | ∃ ρ θ' : ℝ, (1 / 2 : ℝ) < ρ ∧ ρ < 2 ∧ (k : ℝ) < θ' ∧ θ' < k + 1 ∧
    u = ρ * Complex.exp (Real.pi * θ' * Complex.I / (2 * g))}

/-- The annular sector over an open arc is open. -/
theorem isOpen_edgeSector (g : ℕ) [NeZero g] (k : ℤ) : IsOpen (edgeSector g k) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  rw [isOpen_iff_mem_nhds]
  intro u hu
  obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
  have hρ0 : (0 : ℝ) < ρ := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (θ' - k) (k + 1 - θ') := ⟨_, rfl⟩
  have hm1 : m ≤ θ' - k := by rw [hm]; exact min_le_left _ _
  have hm2 : m ≤ k + 1 - θ' := by rw [hm]; exact min_le_right _ _
  have hm0 : 0 < m := by rw [hm]; exact lt_min (by linarith) (by linarith)
  have h2g : (0 : ℝ) < 2 * g := by linarith
  have hb0 : 0 < Real.pi * m / (2 * g) := div_pos (mul_pos hπ hm0) h2g
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = Complex.exp (-(Real.pi * (θ' : ℂ) * Complex.I / (2 * g))) :=
    ⟨_, rfl⟩
  have hcnorm : ‖c‖ = 1 := by
    rw [hc]
    have h : (-(Real.pi * (θ' : ℂ) * Complex.I / (2 * g)))
        = ((-(Real.pi * θ' / (2 * g)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have huc : u * c = (ρ : ℂ) := by
    rw [hue, hc, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hunorm : ‖u‖ = ρ := by
    rw [hue, norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hmemA : ‖u‖ ∈ Set.Ioo (1 / 2 : ℝ) 2 := by
    rw [hunorm]
    exact ⟨hρ1, hρ2⟩
  have hA : (fun w : ℂ => ‖w‖) ⁻¹' Set.Ioo (1 / 2 : ℝ) 2 ∈ 𝓝 u :=
    ContinuousAt.preimage_mem_nhds continuous_norm.continuousAt (isOpen_Ioo.mem_nhds hmemA)
  have harg0 : Complex.arg (u * c) = 0 := by
    rw [huc]
    exact Complex.arg_ofReal_of_nonneg hρ0.le
  have hslit : u * c ∈ Complex.slitPlane := by
    rw [huc]
    exact Complex.ofReal_mem_slitPlane.mpr hρ0
  have hmemB : Complex.arg (u * c)
      ∈ Set.Ioo (-(Real.pi * m / (2 * g))) (Real.pi * m / (2 * g)) := by
    rw [harg0]
    exact ⟨by linarith, hb0⟩
  have hmulc : ContinuousAt (fun w : ℂ => w * c) u := continuousAt_id.mul continuousAt_const
  have hargc : ContinuousAt (fun w : ℂ => Complex.arg (w * c)) u := by
    exact ContinuousAt.comp (x := u) (f := fun w : ℂ => w * c)
      (Complex.continuousAt_arg hslit) hmulc
  have hB : (fun w : ℂ => Complex.arg (w * c)) ⁻¹'
      Set.Ioo (-(Real.pi * m / (2 * g))) (Real.pi * m / (2 * g)) ∈ 𝓝 u :=
    ContinuousAt.preimage_mem_nhds hargc (isOpen_Ioo.mem_nhds hmemB)
  filter_upwards [hA, hB] with w hw1 hw2
  simp only [Set.mem_preimage, Set.mem_Ioo] at hw1 hw2
  refine ⟨‖w‖, θ' + 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi, hw1.1, hw1.2, ?_, ?_, ?_⟩
  · have h1 : -(Real.pi * m) < Complex.arg (w * c) * (2 * g) := by
      have e1 : -(Real.pi * m / (2 * g)) * (2 * g) = -(Real.pi * m) := by field_simp
      rw [← e1]
      exact mul_lt_mul_of_pos_right hw2.1 h2g
    have h2 : -m < 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi := by
      rw [lt_div_iff₀ hπ]
      linarith
    linarith
  · have h1 : Complex.arg (w * c) * (2 * g) < Real.pi * m := by
      have e1 : Real.pi * m / (2 * g) * (2 * g) = Real.pi * m := by field_simp
      rw [← e1]
      exact mul_lt_mul_of_pos_right hw2.2 h2g
    have h2 : 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi < m := by
      rw [div_lt_iff₀ hπ]
      linarith
    linarith
  · have hwc := Complex.norm_mul_exp_arg_mul_I (w * c)
    have hnwc : ‖w * c‖ = ‖w‖ := by rw [norm_mul, hcnorm, mul_one]
    have hcc : c * Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) = 1 := by
      rw [hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
    calc w = w * (c * Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g))) := by
            rw [hcc, mul_one]
      _ = ↑‖w * c‖ * Complex.exp ((Complex.arg (w * c) : ℂ) * Complex.I) *
            Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
            rw [hwc, ← mul_assoc]
      _ = ↑‖w‖ * Complex.exp
            (Real.pi * ((θ' + 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi : ℝ) : ℂ) *
              Complex.I / (2 * g)) := by
            rw [hnwc, mul_assoc, ← Complex.exp_add]
            congr 2
            push_cast
            field_simp
            ring

/-- The edge chart inverse over the source arc `k`: the clamped quotient map
on the disc side, the side pairing followed by it on the exterior side. -/
noncomputable def edgeChartFun (g : ℕ) [NeZero g] (k : ℤ) (u : ℂ) : GenusSurface g :=
  if ‖u‖ ≤ 1 then Quotient.mk (genusSetoid g) (projDisc u)
  else Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u))

/-- Continuity of the edge chart inverse: the two closed pieces
`{‖u‖ ≤ 1}`, `{‖u‖ ≥ 1}` agree on the circle by the pairing clause. -/
theorem edgeChart_continuousOn (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    ContinuousOn (edgeChartFun g k) (edgeSector g k) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hne0 : ∀ u ∈ edgeSector g k, u ≠ 0 := by
    intro u hu
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    rw [hue]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) (Complex.exp_ne_zero _)
  have hq : Continuous (Quotient.mk (genusSetoid g)) := continuous_quot_mk
  have hσc : ContinuousOn (sidePairing g k) {u : ℂ | u ≠ 0} := by
    unfold sidePairing
    exact continuousOn_const.div continuousOn_id fun x hx => hx
  have hσq : ContinuousOn
      (fun u => Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u)))
      {u : ℂ | u ≠ 0} := by
    exact ((hq.comp continuous_projDisc).comp_continuousOn hσc)
  have hfr : frontier {a : ℂ | ‖a‖ ≤ 1} ⊆ {a : ℂ | ‖a‖ = 1} := by
    have hset : {a : ℂ | ‖a‖ ≤ 1} = Metric.closedBall (0 : ℂ) 1 := by
      ext a
      simp
    rw [hset, frontier_closedBall (0 : ℂ) one_ne_zero]
    intro a ha
    exact mem_sphere_zero_iff_norm.mp ha
  unfold edgeChartFun
  refine ContinuousOn.if ?_ ?_ ?_
  · rintro a ⟨haS, hafr⟩
    have hA1 : ‖a‖ = 1 := hfr hafr
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hae⟩ := haS
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hρval : ρ = 1 := by
      rw [hae, norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ0] at hA1
      exact hA1
    have hae1 : a = Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
      rw [hae, hρval, Complex.ofReal_one, one_mul]
    have haarc : a = arcPoint g k (θ' - k) := by
      rw [hae1]
      unfold arcPoint
      congr 1
      push_cast
      ring
    have hσarc : sidePairing g k a = arcPoint g (k + 2) (1 - (θ' - k)) := by
      rw [haarc, sidePairing_arcPoint]
    have ht0 : (0 : ℝ) ≤ θ' - k := by linarith
    have ht1 : θ' - (k : ℝ) ≤ 1 := by linarith
    have hva : (projDisc a).1 = a := projDisc_eq hA1.le
    have hσnorm : ‖sidePairing g k a‖ = 1 := norm_sidePairing g k hA1
    have hvσ : (projDisc (sidePairing g k a)).1 = sidePairing g k a := projDisc_eq hσnorm.le
    have hfst : arcPoint g k (θ' - k) = (projDisc a).1 := by
      rw [hva]
      exact haarc.symm
    have hsnd : arcPoint g (k + 2) (1 - (θ' - k)) = (projDisc (sidePairing g k a)).1 := by
      rw [hvσ]
      exact hσarc.symm
    have hrel : genusRel g (projDisc a) (projDisc (sidePairing g k a)) := by
      have hpair : ((projDisc a).1, (projDisc (sidePairing g k a)).1) ∈ pairGraph g k := by
        refine ⟨⟨θ' - k, ht0, ht1⟩, Set.mem_univ _, ?_⟩
        rw [← hfst, ← hsnd]
      exact Or.inr (Or.inl ⟨k, hk, Or.inl hpair⟩)
    exact Quotient.sound hrel
  · exact (hq.comp continuous_projDisc).continuousOn
  · exact hσq.mono fun x hx => hne0 x hx.1

/-- Injectivity of the edge chart inverse on its sector: the disc part has
angle parameter in `(k, k+1)`, the reflected exterior part in `(k+2, k+3)`,
and no vertices occur. -/
theorem edgeChart_injOn (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    Set.InjOn (edgeChartFun g k) (edgeSector g k) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hnormE : ∀ r s : ℝ, 0 ≤ r →
      ‖(r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = r := by
    intro r s hr
    rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have harc0 : ∀ s : ℝ,
      arcPoint g 0 s = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
    intro s
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hEeq : ∀ s s' : ℝ,
      Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
      ↔ ∃ n : ℤ, s - s' = 4 * g * n := by
    intro s s'
    rw [← harc0 s, ← harc0 s', arcPoint_eq_iff g 0 0 s s']
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast at hn
      linarith
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast
      linarith
  have harcE : ∀ (j : ℤ) (t : ℝ), arcPoint g j t
      = Complex.exp (Real.pi * (((j : ℝ) + t : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro j t
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hvertE : ∀ m : ℤ, polyVertex g m
      = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro m
    unfold polyVertex
    congr 1
  have hσE : ∀ r s : ℝ, r ≠ 0 →
      sidePairing g k ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))
        = ((r⁻¹ : ℝ) : ℂ) *
          Complex.exp (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro r s hr
    unfold sidePairing
    have hne : ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)
    rw [div_eq_iff hne, mul_mul_mul_comm, ← Complex.ofReal_mul, inv_mul_cancel₀ hr,
      Complex.ofReal_one, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have harc : ∀ (k₁ : ℤ) (t : ℝ), ‖arcPoint g k₁ t‖ = 1 := by
    intro k₁ t
    rw [harcE]
    exact hnorm1 _
  have hvert : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    rw [hvertE]
    exact hnorm1 _
  have hsingle : ∀ z w : ClosedDisc, ‖z.1‖ < 1 → genusRel g z w → z = w := by
    intro z w hz hrel
    have hrel' : z = w
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((z.1, w.1) ∈ pairGraph g k₁ ∨ (w.1, z.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hrel
    rcases hrel' with h | ⟨k₁, -, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · exact h
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g k₁ (s : ℝ) = z.1 := congrArg Prod.fst hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k₁ + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvert] at hz
      exact absurd hz (lt_irrefl 1)
  have hclass : ∀ (s : ℝ) (w z : ClosedDisc),
      ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) →
      w.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) →
      genusRel g w z →
      z.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) ∨
        z.1 = Complex.exp
          (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro s w z hs hw hrel
    have hrel' : w = z
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((w.1, z.1) ∈ pairGraph g k₁ ∨ (z.1, w.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g w.1 ∧ IsPolyVertex g z.1) := hrel
    rcases hrel' with h | ⟨k₁, hk₁, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · left
      rw [← h]
      exact hw
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = w.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = z.1 := congrArg Prod.snd ht
      rw [harcE, hw] at h1
      rw [harcE] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((4 * P + k - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ)) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k - k₁ ∧ 4 * P + k - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ0 : 4 * P + k - k₁ = 0 := by omega
        have htv : (t : ℝ) - (s - (k : ℝ)) = 0 := by
          have h0 : ((4 * P + k - k₁ : ℤ) : ℝ) = 0 := by
            rw [hJ0]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h2]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        push_cast
        linarith [hn, htv]
      · exfalso
        have hJr : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ) - 2) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k + 2 - k₁ ∧ 4 * P + k + 2 - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k + 2 - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = z.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = w.1 := congrArg Prod.snd ht
      rw [harcE] at h1
      rw [harcE, hw] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h2
      push_cast at hn
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · exfalso
        have hJr : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ)) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 3 - k - 4 * P ∧ k₁ + 3 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ) - 2) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 1 - k - 4 * P ∧ k₁ + 1 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ1 : k₁ + 1 - k - 4 * P = 1 := by omega
        have htv : (s - (k : ℝ) - 2) + (t : ℝ) = 1 := by
          have h0 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = 1 := by
            rw [hJ1]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h1]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        linarith [hn, htv]
    · exfalso
      have h1 : Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
          = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
        rw [← hw, ← hvertE]
        exact hm
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((m + 4 * P - k : ℤ) : ℝ) = s - (k : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k ∧ m + 4 * P - k < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((m + 4 * P - k - 2 : ℤ) : ℝ) = s - (k : ℝ) - 2 := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k - 2 ∧ m + 4 * P - k - 2 < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k - 2 : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k - 2 : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
  have hkey : ∀ r s r' s' : ℝ, 1 / 2 < r → r ≤ 1 → 1 / 2 < r' → r' ≤ 1 →
      ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) →
      ((k : ℝ) < s' ∧ s' < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s' ∧ s' < (k : ℝ) + 3) →
      Quotient.mk (genusSetoid g)
          (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))))
        = Quotient.mk (genusSetoid g)
          (projDisc ((r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))) →
      (r = r' ∧ ∃ n : ℤ, s - s' = 4 * g * n) ∨
        (r = 1 ∧ r' = 1 ∧ ∃ n : ℤ, s + s' - (2 * (k : ℝ) + 3) = 4 * g * n) := by
    intro r s r' s' hr1 hr2 hr1' hr2' hsA hsA' hquot
    have hr0 : (0 : ℝ) < r := by linarith
    have hr0' : (0 : ℝ) < r' := by linarith
    have hns : ‖(r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = r :=
      hnormE r s hr0.le
    have hns' : ‖(r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))‖ = r' :=
      hnormE r' s' hr0'.le
    have hv : (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))).1
        = (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) :=
      projDisc_eq (by rw [hns]; exact hr2)
    have hv' : (projDisc ((r' : ℂ) *
          Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))).1
        = (r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)) :=
      projDisc_eq (by rw [hns']; exact hr2')
    have hrel : genusRel g
        (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))))
        (projDisc ((r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))) :=
      Quotient.exact hquot
    rcases lt_or_eq_of_le hr2 with hlt | heq1
    · have hz : ‖(projDisc ((r : ℂ) *
          Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))).1‖ < 1 := by
        rw [hv, hns]
        exact hlt
      have heqd := hsingle _ _ hz hrel
      have hvals : (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
          = (r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)) := by
        rw [← hv, ← hv', heqd]
      have hrr : r = r' := by
        have h1 := hns
        rw [hvals, hns'] at h1
        exact h1.symm
      left
      refine ⟨hrr, (hEeq s s').mp ?_⟩
      have hcan : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0'.ne'
      rw [hrr] at hvals
      exact mul_left_cancel₀ hcan hvals
    · rcases lt_or_eq_of_le hr2' with hlt' | heq1'
      · exfalso
        have hrel2 : genusRel g
            (projDisc ((r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))))
            (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))) :=
          Quotient.exact hquot.symm
        have hz' : ‖(projDisc ((r' : ℂ) *
            Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))).1‖ < 1 := by
          rw [hv', hns']
          exact hlt'
        have heqd := hsingle _ _ hz' hrel2
        have hvals : (r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
            = (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
          rw [← hv', ← hv, heqd]
        have h1 := hns'
        rw [hvals, hns] at h1
        linarith
      · have hw1 : (projDisc ((r : ℂ) *
            Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))).1
            = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
          rw [hv, heq1, Complex.ofReal_one, one_mul]
        have hz1' : (projDisc ((r' : ℂ) *
            Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))).1
            = Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)) := by
          rw [hv', heq1', Complex.ofReal_one, one_mul]
        have hcls := hclass s _ _ hsA hw1 hrel
        rcases hcls with hcase | hcase
        · left
          refine ⟨by rw [heq1, heq1'], (hEeq s s').mp ?_⟩
          have h3 : Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
              = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
            rw [← hz1']
            exact hcase
          exact h3.symm
        · right
          refine ⟨heq1, heq1', ?_⟩
          have h3 : Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
              = Complex.exp
                (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
            rw [← hz1']
            exact hcase
          obtain ⟨n, hn⟩ := (hEeq _ _).mp h3
          exact ⟨n, by linarith [hn]⟩
  have hnf : ∀ u ∈ edgeSector g k, ∃ r s : ℝ, 1 / 2 < r ∧ r ≤ 1 ∧
      edgeChartFun g k u
        = Quotient.mk (genusSetoid g)
            (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))) ∧
      (((k : ℝ) < s ∧ s < (k : ℝ) + 1 ∧
          u = (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))) ∨
        ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3 ∧ r < 1 ∧
          u = ((r⁻¹ : ℝ) : ℂ) *
            Complex.exp
              (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)))) := by
    intro u hu
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hun : ‖u‖ = ρ := by
      rw [hue]
      exact hnormE ρ θ' hρ0.le
    by_cases hA : ‖u‖ ≤ 1
    · refine ⟨ρ, θ', hρ1, by rw [← hun]; exact hA, ?_, Or.inl ⟨hθ1, hθ2, hue⟩⟩
      have hval : edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc u) := ite_eq_left hA
      exact hval.trans (by rw [hue])
    · have hρgt : 1 < ρ := by
        rw [← hun]
        exact not_le.mp hA
      have hinv0 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
      have hcancel : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0.ne'
      have hinv1 : ρ⁻¹ < 1 := by nlinarith
      have hinvhalf : 1 / 2 < ρ⁻¹ := by nlinarith
      refine ⟨ρ⁻¹, 2 * (k : ℝ) + 3 - θ', hinvhalf, hinv1.le, ?_,
        Or.inr ⟨by linarith, by linarith, hinv1, ?_⟩⟩
      · have hval : edgeChartFun g k u
            = Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u)) := ite_eq_right hA
        exact hval.trans (by rw [hue, hσE ρ θ' hρ0.ne'])
      · have e1 : (ρ⁻¹)⁻¹ = ρ := inv_inv ρ
        have e2 : 2 * (k : ℝ) + 3 - (2 * (k : ℝ) + 3 - θ') = θ' := by ring
        rw [e1, e2]
        exact hue
  intro u hu u' hu' heq
  obtain ⟨r, s, hr1, hr2, hval, hcase⟩ := hnf u hu
  obtain ⟨r', s', hr1', hr2', hval', hcase'⟩ := hnf u' hu'
  rw [hval, hval'] at heq
  have hranges : ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) := by
    rcases hcase with ⟨h1, h2, -⟩ | ⟨h1, h2, -, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hranges' : ((k : ℝ) < s' ∧ s' < (k : ℝ) + 1) ∨
      ((k : ℝ) + 2 < s' ∧ s' < (k : ℝ) + 3) := by
    rcases hcase' with ⟨h1, h2, -⟩ | ⟨h1, h2, -, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  rcases hkey r s r' s' hr1 hr2 hr1' hr2' hranges hranges' heq with
    ⟨hrr, n, hn⟩ | ⟨hre1, hre1', n, hn⟩
  · obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
    have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
      rw [← hP]
      push_cast
      ring
    have hJr : ((4 * P : ℤ) : ℝ) = s - s' := by
      push_cast
      linarith [hn, hPr]
    rcases hcase with ⟨hs1, hs2, hueq⟩ | ⟨hs1, hs2, -, hueq⟩
    · rcases hcase' with ⟨hs1', hs2', hueq'⟩ | ⟨hs1', hs2', -, -⟩
      · have hss : s = s' := by
          have hJZ : (-1 : ℤ) < 4 * P ∧ 4 * P < 1 := by
            have hR1 : (-1 : ℝ) < ((4 * P : ℤ) : ℝ) := by
              rw [hJr]
              linarith
            have hR2 : ((4 * P : ℤ) : ℝ) < 1 := by
              rw [hJr]
              linarith
            exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
          have hP0 : (4 * P : ℤ) = 0 := by omega
          have h0 : ((4 * P : ℤ) : ℝ) = 0 := by
            rw [hP0]
            norm_num
          rw [hJr] at h0
          linarith
        rw [hueq, hueq', hrr, hss]
      · exfalso
        have hJZ : (-3 : ℤ) < 4 * P ∧ 4 * P < -1 := by
          have hR1 : (-3 : ℝ) < ((4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P : ℤ) : ℝ) < -1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
    · rcases hcase' with ⟨hs1', hs2', -⟩ | ⟨hs1', hs2', -, hueq'⟩
      · exfalso
        have hJZ : (1 : ℤ) < 4 * P ∧ 4 * P < 3 := by
          have hR1 : (1 : ℝ) < ((4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P : ℤ) : ℝ) < 3 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hss : s = s' := by
          have hJZ : (-1 : ℤ) < 4 * P ∧ 4 * P < 1 := by
            have hR1 : (-1 : ℝ) < ((4 * P : ℤ) : ℝ) := by
              rw [hJr]
              linarith
            have hR2 : ((4 * P : ℤ) : ℝ) < 1 := by
              rw [hJr]
              linarith
            exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
          have hP0 : (4 * P : ℤ) = 0 := by omega
          have h0 : ((4 * P : ℤ) : ℝ) = 0 := by
            rw [hP0]
            norm_num
          rw [hJr] at h0
          linarith
        rw [hueq, hueq', hrr, hss]
  · rcases hcase with ⟨hs1, hs2, -⟩ | ⟨-, -, hrlt, -⟩
    · rcases hcase' with ⟨hs1', hs2', -⟩ | ⟨-, -, hrlt', -⟩
      · exfalso
        obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
        have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
          rw [← hP]
          push_cast
          ring
        have hJr : ((4 * P : ℤ) : ℝ) = s + s' - (2 * (k : ℝ) + 3) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-3 : ℤ) < 4 * P ∧ 4 * P < -1 := by
          have hR1 : (-3 : ℝ) < ((4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P : ℤ) : ℝ) < -1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · exfalso
        rw [hre1'] at hrlt'
        exact lt_irrefl 1 hrlt'
    · exfalso
      rw [hre1] at hrlt
      exact lt_irrefl 1 hrlt

/-- Openness of the edge chart inverse: the saturation of the image of an
open subset adds the pairing mirror of its boundary trace, which is open in
the disc by the two-sided half-ball argument. -/
theorem edgeChart_isOpen_image (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    ∀ W ⊆ edgeSector g k, IsOpen W → IsOpen (edgeChartFun g k '' W) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hnormE : ∀ r s : ℝ, 0 ≤ r →
      ‖(r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = r := by
    intro r s hr
    rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have harc0 : ∀ s : ℝ,
      arcPoint g 0 s = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
    intro s
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hEeq : ∀ s s' : ℝ,
      Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
      ↔ ∃ n : ℤ, s - s' = 4 * g * n := by
    intro s s'
    rw [← harc0 s, ← harc0 s', arcPoint_eq_iff g 0 0 s s']
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast at hn
      linarith
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast
      linarith
  have harcE : ∀ (j : ℤ) (t : ℝ), arcPoint g j t
      = Complex.exp (Real.pi * (((j : ℝ) + t : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro j t
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hvertE : ∀ m : ℤ, polyVertex g m
      = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro m
    unfold polyVertex
    congr 1
  have hσE : ∀ r s : ℝ, r ≠ 0 →
      sidePairing g k ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))
        = ((r⁻¹ : ℝ) : ℂ) *
          Complex.exp (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro r s hr
    unfold sidePairing
    have hne : ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)
    rw [div_eq_iff hne, mul_mul_mul_comm, ← Complex.ofReal_mul, inv_mul_cancel₀ hr,
      Complex.ofReal_one, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have harc : ∀ (k₁ : ℤ) (t : ℝ), ‖arcPoint g k₁ t‖ = 1 := by
    intro k₁ t
    rw [harcE]
    exact hnorm1 _
  have hvert : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    rw [hvertE]
    exact hnorm1 _
  have hsingle : ∀ z w : ClosedDisc, ‖z.1‖ < 1 → genusRel g z w → z = w := by
    intro z w hz hrel
    have hrel' : z = w
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((z.1, w.1) ∈ pairGraph g k₁ ∨ (w.1, z.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hrel
    rcases hrel' with h | ⟨k₁, -, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · exact h
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g k₁ (s : ℝ) = z.1 := congrArg Prod.fst hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k₁ + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvert] at hz
      exact absurd hz (lt_irrefl 1)
  have hclass : ∀ (s : ℝ) (w z : ClosedDisc),
      ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) →
      w.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) →
      genusRel g w z →
      z.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) ∨
        z.1 = Complex.exp
          (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro s w z hs hw hrel
    have hrel' : w = z
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((w.1, z.1) ∈ pairGraph g k₁ ∨ (z.1, w.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g w.1 ∧ IsPolyVertex g z.1) := hrel
    rcases hrel' with h | ⟨k₁, hk₁, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · left
      rw [← h]
      exact hw
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = w.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = z.1 := congrArg Prod.snd ht
      rw [harcE, hw] at h1
      rw [harcE] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((4 * P + k - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ)) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k - k₁ ∧ 4 * P + k - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ0 : 4 * P + k - k₁ = 0 := by omega
        have htv : (t : ℝ) - (s - (k : ℝ)) = 0 := by
          have h0 : ((4 * P + k - k₁ : ℤ) : ℝ) = 0 := by
            rw [hJ0]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h2]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        push_cast
        linarith [hn, htv]
      · exfalso
        have hJr : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ) - 2) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k + 2 - k₁ ∧ 4 * P + k + 2 - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k + 2 - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = z.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = w.1 := congrArg Prod.snd ht
      rw [harcE] at h1
      rw [harcE, hw] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h2
      push_cast at hn
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · exfalso
        have hJr : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ)) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 3 - k - 4 * P ∧ k₁ + 3 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ) - 2) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 1 - k - 4 * P ∧ k₁ + 1 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ1 : k₁ + 1 - k - 4 * P = 1 := by omega
        have htv : (s - (k : ℝ) - 2) + (t : ℝ) = 1 := by
          have h0 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = 1 := by
            rw [hJ1]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h1]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        linarith [hn, htv]
    · exfalso
      have h1 : Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
          = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
        rw [← hw, ← hvertE]
        exact hm
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((m + 4 * P - k : ℤ) : ℝ) = s - (k : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k ∧ m + 4 * P - k < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((m + 4 * P - k - 2 : ℤ) : ℝ) = s - (k : ℝ) - 2 := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k - 2 ∧ m + 4 * P - k - 2 < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k - 2 : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k - 2 : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
  have hne0 : ∀ u ∈ edgeSector g k, u ≠ 0 := by
    intro u hu
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    rw [hue]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) (Complex.exp_ne_zero _)
  have hσc : ContinuousOn (sidePairing g k) {u : ℂ | u ≠ 0} := by
    unfold sidePairing
    exact continuousOn_const.div continuousOn_id fun x hx => hx
  have hωnorm : ‖Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))‖ = 1 := by
    have harg2 : (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))
        = Real.pi * ((2 * (k : ℝ) + 3 : ℝ) : ℂ) * Complex.I / (2 * g) := by
      push_cast
      ring
    rw [harg2]
    exact hnorm1 _
  have hσnorm : ∀ u : ℂ, ‖sidePairing g k u‖ = 1 / ‖u‖ := by
    intro u
    unfold sidePairing
    rw [norm_div, hωnorm]
  have hvalA : ∀ u : ℂ, ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc u) := by
    intro u h
    exact ite_eq_left h
  have hvalB : ∀ u : ℂ, ¬ ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u)) := by
    intro u h
    exact ite_eq_right h
  have hσimg : ∀ V : Set ℂ, V ⊆ edgeSector g k →
      sidePairing g k '' V = {z : ℂ | z ≠ 0} ∩ sidePairing g k ⁻¹' V := by
    intro V hVsec
    ext z
    constructor
    · rintro ⟨v, hvV, rfl⟩
      have hv0 : v ≠ 0 := hne0 v (hVsec hvV)
      refine ⟨?_, ?_⟩
      · have hne : sidePairing g k v ≠ 0 := by
          unfold sidePairing
          exact div_ne_zero (Complex.exp_ne_zero _) hv0
        exact hne
      · have hmem : sidePairing g k (sidePairing g k v) ∈ V := by
          rw [sidePairing_involutive g k hv0]
          exact hvV
        exact hmem
    · rintro ⟨hz0, hzV⟩
      exact ⟨sidePairing g k z, hzV, sidePairing_involutive g k hz0⟩
  have hσopen : ∀ V : Set ℂ, V ⊆ edgeSector g k → IsOpen V →
      IsOpen (sidePairing g k '' V) := by
    intro V hVsec hV
    rw [hσimg V hVsec]
    exact hσc.isOpen_inter_preimage isOpen_ne hV
  have hpairrel : ∀ a ∈ edgeSector g k, ‖a‖ = 1 →
      genusRel g (projDisc a) (projDisc (sidePairing g k a)) := by
    intro a haS hA1
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hae⟩ := haS
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hρval : ρ = 1 := by
      rw [hae, hnormE ρ θ' hρ0.le] at hA1
      exact hA1
    have haarc : a = arcPoint g k (θ' - k) := by
      rw [hae, hρval, Complex.ofReal_one, one_mul]
      unfold arcPoint
      congr 1
      push_cast
      ring
    have hσarc : sidePairing g k a = arcPoint g (k + 2) (1 - (θ' - k)) := by
      rw [haarc, sidePairing_arcPoint]
    have ht0 : (0 : ℝ) ≤ θ' - k := by linarith
    have ht1 : θ' - (k : ℝ) ≤ 1 := by linarith
    have hva : (projDisc a).1 = a := projDisc_eq hA1.le
    have hσn1 : ‖sidePairing g k a‖ = 1 := norm_sidePairing g k hA1
    have hvσ : (projDisc (sidePairing g k a)).1 = sidePairing g k a := projDisc_eq hσn1.le
    have hfst : arcPoint g k (θ' - k) = (projDisc a).1 := by
      rw [hva]
      exact haarc.symm
    have hsnd : arcPoint g (k + 2) (1 - (θ' - k)) = (projDisc (sidePairing g k a)).1 := by
      rw [hvσ]
      exact hσarc.symm
    have hpair : ((projDisc a).1, (projDisc (sidePairing g k a)).1) ∈ pairGraph g k := by
      refine ⟨⟨θ' - k, ht0, ht1⟩, Set.mem_univ _, ?_⟩
      rw [← hfst, ← hsnd]
    exact Or.inr (Or.inl ⟨k, hk, Or.inl hpair⟩)
  intro W hWsec hW
  have hqimg : edgeChartFun g k '' W
      = Quotient.mk (genusSetoid g) ''
        {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W} := by
    ext p
    constructor
    · rintro ⟨u, huW, rfl⟩
      by_cases hA : ‖u‖ ≤ 1
      · refine ⟨projDisc u, ?_, (hvalA u hA).symm⟩
        have hmem : (projDisc u).1 ∈ W := by
          rw [projDisc_eq hA]
          exact huW
        exact Or.inl hmem
      · have hu1 : 1 < ‖u‖ := not_le.mp hA
        have hlt : ‖sidePairing g k u‖ < 1 := by
          rw [hσnorm u]
          exact (div_lt_one (by linarith)).mpr hu1
        refine ⟨projDisc (sidePairing g k u), ?_, (hvalB u hA).symm⟩
        have hmem : (projDisc (sidePairing g k u)).1 ∈ sidePairing g k '' W := by
          rw [projDisc_eq hlt.le]
          exact ⟨u, huW, rfl⟩
        exact Or.inr hmem
    · rintro ⟨z, hz, rfl⟩
      have hz' : z.1 ∈ W ∨ z.1 ∈ sidePairing g k '' W := hz
      have hznorm : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      rcases hz' with hzW | ⟨v, hvW, hzv⟩
      · refine ⟨z.1, hzW, ?_⟩
        rw [hvalA z.1 hznorm]
        exact congrArg _ (Subtype.ext (projDisc_eq hznorm))
      · by_cases hv1 : ‖v‖ ≤ 1
        · have hv0 : v ≠ 0 := hne0 v (hWsec hvW)
          have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
          have hveq : ‖v‖ = 1 := by
            have h2 : (1 : ℝ) / ‖v‖ ≤ 1 := by
              rw [← hσnorm v, hzv]
              exact hznorm
            rw [div_le_one hvpos] at h2
            linarith
          have hσv1 : ‖sidePairing g k v‖ ≤ 1 := by
            rw [hσnorm v, hveq]
            norm_num
          have hz_eq : projDisc (sidePairing g k v) = z :=
            Subtype.ext ((projDisc_eq hσv1).trans hzv)
          refine ⟨v, hvW, ?_⟩
          rw [hvalA v hv1, ← hz_eq]
          exact Quotient.sound (hpairrel v (hWsec hvW) hveq)
        · have hu1 : 1 < ‖v‖ := not_le.mp hv1
          have hlt : ‖sidePairing g k v‖ < 1 := by
            rw [hσnorm v]
            exact (div_lt_one (by linarith)).mpr hu1
          refine ⟨v, hvW, ?_⟩
          rw [hvalB v hv1]
          exact congrArg _ (Subtype.ext ((projDisc_eq hlt.le).trans hzv))
  rw [hqimg]
  have hAopen : IsOpen (W ∪ sidePairing g k '' W) := hW.union (hσopen W hWsec hW)
  have hsat : Quotient.mk (genusSetoid g) ⁻¹'
      (Quotient.mk (genusSetoid g) '' {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W})
      = {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W} := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro p ⟨z, hz, hzp⟩
    have hrel : genusRel g z p := Quotient.exact hzp
    have hz' : z.1 ∈ W ∨ z.1 ∈ sidePairing g k '' W := hz
    rcases hz' with hzW | ⟨v, hvW, hzv⟩
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hze⟩ := hWsec hzW
      have hρ0 : (0 : ℝ) < ρ := by linarith
      have hznorm : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have hzρ : ‖z.1‖ = ρ := by
        rw [hze]
        exact hnormE ρ θ' hρ0.le
      have hρle : ρ ≤ 1 := by
        rw [← hzρ]
        exact hznorm
      rcases lt_or_eq_of_le hρle with hρlt | hρ1eq
      · have hzn : ‖z.1‖ < 1 := by
          rw [hzρ]
          exact hρlt
        have hzp' := hsingle z p hzn hrel
        rw [← hzp']
        exact Or.inl hzW
      · have hze1 : z.1 = Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
          rw [hze, hρ1eq, Complex.ofReal_one, one_mul]
        have hcls := hclass θ' z p (Or.inl ⟨hθ1, hθ2⟩) hze1 hrel
        rcases hcls with hp | hp
        · have hmem : p.1 ∈ W := by
            rw [hp, ← hze1]
            exact hzW
          exact Or.inl hmem
        · have hz1' : z.1 = ((1 : ℝ) : ℂ) *
              Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
            rw [hze1, Complex.ofReal_one, one_mul]
          have hσz := hσE 1 θ' one_ne_zero
          rw [← hz1'] at hσz
          have hσz' : sidePairing g k z.1 = Complex.exp
              (Real.pi * ((2 * (k : ℝ) + 3 - θ' : ℝ) : ℂ) * Complex.I / (2 * g)) := by
            rw [hσz, inv_one, Complex.ofReal_one, one_mul]
          have hmem : p.1 ∈ sidePairing g k '' W := by
            refine ⟨z.1, hzW, ?_⟩
            rw [hσz', ← hp]
          exact Or.inr hmem
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hve⟩ := hWsec hvW
      have hρ0 : (0 : ℝ) < ρ := by linarith
      have hσv : sidePairing g k v = ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp
          (Real.pi * ((2 * (k : ℝ) + 3 - θ' : ℝ) : ℂ) * Complex.I / (2 * g)) := by
        rw [hve]
        exact hσE ρ θ' hρ0.ne'
      have hznorm : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have hinv0 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
      have hzρ : ‖z.1‖ = ρ⁻¹ := by
        rw [← hzv, hσv]
        exact hnormE _ _ hinv0.le
      have hcancel : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0.ne'
      have hρge : 1 ≤ ρ := by
        have h2 : ρ⁻¹ ≤ 1 := by
          rw [← hzρ]
          exact hznorm
        nlinarith
      rcases lt_or_eq_of_le hρge with hρgt | hρeq1
      · have hzn : ‖z.1‖ < 1 := by
          rw [hzρ]
          nlinarith
        have hzp' := hsingle z p hzn hrel
        rw [← hzp']
        exact Or.inr ⟨v, hvW, hzv⟩
      · have hz1' : z.1 = Complex.exp
            (Real.pi * ((2 * (k : ℝ) + 3 - θ' : ℝ) : ℂ) * Complex.I / (2 * g)) := by
          rw [← hzv, hσv, ← hρeq1, inv_one, Complex.ofReal_one, one_mul]
        have hcls := hclass (2 * (k : ℝ) + 3 - θ') z p
          (Or.inr ⟨by linarith, by linarith⟩) hz1' hrel
        rcases hcls with hp | hp
        · have hmem : p.1 ∈ sidePairing g k '' W := by
            refine ⟨v, hvW, ?_⟩
            rw [hzv, hz1', hp]
          exact Or.inr hmem
        · have he2 : 2 * (k : ℝ) + 3 - (2 * (k : ℝ) + 3 - θ') = θ' := by ring
          rw [he2] at hp
          have hveq1 : v = Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
            rw [hve, ← hρeq1, Complex.ofReal_one, one_mul]
          have hmem : p.1 ∈ W := by
            rw [hp, ← hveq1]
            exact hvW
          exact Or.inl hmem
  have hpre : IsOpen (Quotient.mk (genusSetoid g) ⁻¹'
      (Quotient.mk (genusSetoid g) ''
        {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W})) := by
    rw [hsat]
    exact hAopen.preimage continuous_subtype_val
  exact isOpen_coinduced.mpr hpre

/-- The source-arc index of the edge chart labelled by `j : Fin g` and
`b : Bool` is `≡ 0` or `1 (mod 4)`. -/
theorem edgeIndex_mod (g : ℕ) (j : Fin g) (b : Bool) :
    (4 * (j : ℤ) + if b then 1 else 0) % 4 = 0 ∨
      (4 * (j : ℤ) + if b then 1 else 0) % 4 = 1 := by
  cases b
  · rw [ite_eq_right Bool.false_ne_true]
    omega
  · rw [ite_eq_left rfl]
    omega

/-- The edge chart over the source arc `4j` (for `b = false`, carrying
`a_{j+1}`) or `4j + 1` (for `b = true`, carrying `b_{j+1}`). Its source is a
neighborhood of the glued open edge, its target the open annular sector. -/
noncomputable def edgeChart (g : ℕ) [NeZero g] (j : Fin g) (b : Bool) :
    OpenPartialHomeomorph (GenusSurface g) ℂ :=
  OpenPartialHomeomorph.ofInvFunOn (edgeChartFun g (4 * j + if b then 1 else 0))
    (edgeSector g (4 * j + if b then 1 else 0))
    (isOpen_edgeSector g _)
    (edgeChart_continuousOn g _ (edgeIndex_mod g j b))
    (edgeChart_injOn g _ (edgeIndex_mod g j b))
    (edgeChart_isOpen_image g _ (edgeIndex_mod g j b))

/-- The inverse of an edge chart is the two-piece gluing map. -/
theorem edgeChart_symm_apply (g : ℕ) [NeZero g] (j : Fin g) (b : Bool) (u : ℂ) :
    (edgeChart g j b).symm u = edgeChartFun g (4 * j + if b then 1 else 0) u := by
  rfl

end RiemannDynamics
