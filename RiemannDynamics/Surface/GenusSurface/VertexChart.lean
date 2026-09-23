/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.GenusSurface.EdgeCharts

/-!
# The genus-`g` surface: the vertex chart, continuity and injectivity

The single vertex class of the `4g`-gon model requires one final chart. The
chart disc of radius `vertexRadius g` is cut into `4g` angular sectors;
sector `m` is laid down at the polygon corner `vertexSlot g m` by a power
map, giving `vertexChartFun g`. This file develops the corner-slot
combinatorics (`pairInv`, `vertexSlot`), proves the ray-gluing identity
`vertexRay_glue`, and shows `vertexChartFun` is continuous and injective on
the chart disc.

Openness of the image is proved in the sibling file `Atlas`.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval
open scoped Manifold

namespace RiemannDynamics

/-! ### The vertex chart -/

/-- The arc involution `π̂` on indices mod `4g`: source arcs (`n % 4 ∈
{0, 1}`) go to `n + 2`, target arcs to `n - 2`. -/
def pairInv (g : ℕ) (n : ZMod (4 * g)) : ZMod (4 * g) :=
  if n.val % 4 = 0 ∨ n.val % 4 = 1 then n + 2 else n - 2

/-- The corner-slot map of the vertex chart: sector `m` of the chart disc is
laid down at the corner `vertexSlot g m`. Closed form: `c 0 = 0`, and for
`m ≥ 1` with `m - 1 = 4i + s`, `c m = 4(g - 1 - i) + [1, 2, 3, 0]ₛ`. -/
def vertexSlot (g : ℕ) (m : ZMod (4 * g)) : ZMod (4 * g) :=
  if m = 0 then 0
  else
    ((4 * (g - 1 - (m.val - 1) / 4) +
      (if (m.val - 1) % 4 = 3 then 0 else (m.val - 1) % 4 + 1) : ℕ) : ZMod (4 * g))

/-- The slot map fixes `0`. -/
theorem vertexSlot_zero (g : ℕ) : vertexSlot g 0 = 0 := by
  unfold vertexSlot
  rw [ite_eq_left rfl]

/-- The slot recurrence: the successor slot is the arc involution of the
predecessor arc, `c (m+1) = π̂ (c m - 1)`. -/
theorem vertexSlot_succ (g : ℕ) [NeZero g] (m : ZMod (4 * g)) :
    vertexSlot g (m + 1) = pairInv g (vertexSlot g m - 1) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have : NeZero (4 * g) := ⟨by omega⟩
  have hval : ∀ a : ℕ, a < 4 * g → ((a : ZMod (4 * g))).val = a := fun a ha =>
    ZMod.val_cast_of_lt ha
  have hslot : ∀ v : ℕ, 1 ≤ v → v < 4 * g →
      vertexSlot g ((v : ℕ) : ZMod (4 * g)) =
        ((4 * (g - 1 - (v - 1) / 4) +
          (if (v - 1) % 4 = 3 then 0 else (v - 1) % 4 + 1) : ℕ) : ZMod (4 * g)) := by
    intro v hv1 hvlt
    have hne : ((v : ℕ) : ZMod (4 * g)) ≠ 0 := by
      intro hcontra
      have hv := hval v hvlt
      rw [hcontra, ZMod.val_zero] at hv
      omega
    unfold vertexSlot
    rw [ite_eq_right hne, hval v hvlt]
  have hpair : ∀ b : ℕ, b < 4 * g →
      pairInv g ((b : ℕ) : ZMod (4 * g)) =
        if b % 4 = 0 ∨ b % 4 = 1 then ((b + 2 : ℕ) : ZMod (4 * g))
        else ((b - 2 : ℕ) : ZMod (4 * g)) := by
    intro b hb
    unfold pairInv
    rw [hval b hb]
    split_ifs with hcond
    · push_cast
      ring
    · have hb2 : 2 ≤ b := by omega
      rw [Nat.cast_sub hb2]
      push_cast
      ring
  have hsub1 : ∀ a : ℕ, 1 ≤ a →
      ((a : ℕ) : ZMod (4 * g)) - 1 = ((a - 1 : ℕ) : ZMod (4 * g)) := by
    intro a ha
    rw [Nat.cast_sub ha, Nat.cast_one]
  by_cases hm0 : m = 0
  · subst hm0
    rw [zero_add, vertexSlot_zero]
    have hneg : (0 : ZMod (4 * g)) - 1 = ((4 * g - 1 : ℕ) : ZMod (4 * g)) := by
      rw [← ZMod.natCast_self (4 * g)]
      exact hsub1 (4 * g) (by omega)
    rw [hneg, hpair (4 * g - 1) (by omega), ite_eq_right (by omega)]
    rw [show (1 : ZMod (4 * g)) = ((1 : ℕ) : ZMod (4 * g)) from Nat.cast_one.symm]
    rw [hslot 1 le_rfl (by omega), ite_eq_right (by omega : ¬(1 - 1) % 4 = 3)]
    congr 1
    omega
  · obtain ⟨v, hvlt, hv1, hmc⟩ :
        ∃ v : ℕ, v < 4 * g ∧ 1 ≤ v ∧ ((v : ℕ) : ZMod (4 * g)) = m :=
      ⟨m.val, ZMod.val_lt m,
        Nat.one_le_iff_ne_zero.mpr (fun hc => hm0 ((ZMod.val_eq_zero m).mp hc)),
        ZMod.natCast_rightInverse m⟩
    rw [← hmc, hslot v hv1 hvlt]
    rcases Nat.lt_or_ge (v + 1) (4 * g) with hlt | hge
    · have hm1 : ((v : ℕ) : ZMod (4 * g)) + 1 = ((v + 1 : ℕ) : ZMod (4 * g)) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hm1, hslot (v + 1) (by omega) hlt]
      simp only [Nat.add_sub_cancel]
      have hs4 : (v - 1) % 4 = 0 ∨ (v - 1) % 4 = 1 ∨ (v - 1) % 4 = 2 ∨
          (v - 1) % 4 = 3 := by omega
      rcases hs4 with hs | hs | hs | hs
      · rw [ite_eq_right (by omega : ¬v % 4 = 3), ite_eq_right (by omega : ¬(v - 1) % 4 = 3)]
        rw [hsub1 _ (by omega), hpair _ (by omega), ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_right (by omega : ¬v % 4 = 3), ite_eq_right (by omega : ¬(v - 1) % 4 = 3)]
        rw [hsub1 _ (by omega), hpair _ (by omega), ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_left (by omega : v % 4 = 3), ite_eq_right (by omega : ¬(v - 1) % 4 = 3)]
        rw [hsub1 _ (by omega), hpair _ (by omega), ite_eq_right (by omega)]
        congr 1
        omega
      · rw [ite_eq_right (by omega : ¬v % 4 = 3), ite_eq_left hs]
        rw [hsub1 _ (by omega), hpair _ (by omega), ite_eq_right (by omega)]
        congr 1
        omega
    · have hveq : v = 4 * g - 1 := by omega
      have hm1 : ((v : ℕ) : ZMod (4 * g)) + 1 = 0 := by
        have h2 : ((v : ℕ) : ZMod (4 * g)) + 1 = ((v + 1 : ℕ) : ZMod (4 * g)) := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [h2, show v + 1 = 4 * g from by omega, ZMod.natCast_self]
      rw [hm1, vertexSlot_zero]
      have hS : 4 * (g - 1 - (v - 1) / 4) +
          (if (v - 1) % 4 = 3 then 0 else (v - 1) % 4 + 1) = 3 := by
        rw [ite_eq_right (by omega)]
        omega
      rw [hS, hsub1 3 (by omega), hpair (3 - 1) (by omega), ite_eq_right (by omega)]
      have h32 : (3 - 1 - 2 : ℕ) = 0 := by omega
      rw [h32, Nat.cast_zero]

/-- The slot map is a bijection of `ZMod (4g)` (a single `4g`-cycle). -/
theorem vertexSlot_bijective (g : ℕ) [NeZero g] :
    Function.Bijective (vertexSlot g) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have : NeZero (4 * g) := ⟨by omega⟩
  rw [← Finite.injective_iff_bijective]
  intro a b hab
  have hval : ∀ c : ℕ, c < 4 * g → ((c : ZMod (4 * g))).val = c := fun c hc =>
    ZMod.val_cast_of_lt hc
  have hslotval : ∀ x : ZMod (4 * g), x ≠ 0 →
      (vertexSlot g x).val =
        4 * (g - 1 - (x.val - 1) / 4) +
          (if (x.val - 1) % 4 = 3 then 0 else (x.val - 1) % 4 + 1) := by
    intro x hx
    have hxlt : x.val < 4 * g := ZMod.val_lt x
    have hx1 : 1 ≤ x.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hx ((ZMod.val_eq_zero x).mp hc))
    unfold vertexSlot
    rw [ite_eq_right hx]
    exact hval _ (by split_ifs <;> omega)
  by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
  · rw [ha0, hb0]
  · exfalso
    rw [ha0, vertexSlot_zero] at hab
    have h0 : (vertexSlot g b).val = 0 := by
      rw [← hab, ZMod.val_zero]
    rw [hslotval b hb0] at h0
    have hblt : b.val < 4 * g := ZMod.val_lt b
    have hb1 : 1 ≤ b.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hb0 ((ZMod.val_eq_zero b).mp hc))
    split_ifs at h0
    all_goals omega
  · exfalso
    rw [hb0, vertexSlot_zero] at hab
    have h0 : (vertexSlot g a).val = 0 := by
      rw [hab, ZMod.val_zero]
    rw [hslotval a ha0] at h0
    have halt : a.val < 4 * g := ZMod.val_lt a
    have ha1 : 1 ≤ a.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => ha0 ((ZMod.val_eq_zero a).mp hc))
    split_ifs at h0
    all_goals omega
  · have hv : (vertexSlot g a).val = (vertexSlot g b).val := by rw [hab]
    rw [hslotval a ha0, hslotval b hb0] at hv
    have halt : a.val < 4 * g := ZMod.val_lt a
    have hblt : b.val < 4 * g := ZMod.val_lt b
    have ha1 : 1 ≤ a.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => ha0 ((ZMod.val_eq_zero a).mp hc))
    have hb1 : 1 ≤ b.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hb0 ((ZMod.val_eq_zero b).mp hc))
    have hveq : a.val = b.val := by
      split_ifs at hv <;> omega
    exact ZMod.val_injective (4 * g) hveq

/-- The radius of the vertex chart: small enough that
`vertexRadius g ^ (2g) < π/(2g)`, keeping each compressed corner inside its
adjacent arcs. -/
noncomputable def vertexRadius (g : ℕ) : ℝ :=
  min (1 / 2) (Real.pi / (4 * g))

/-- The vertex chart radius is positive. -/
theorem vertexRadius_pos (g : ℕ) [NeZero g] : 0 < vertexRadius g := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hg : (0 : ℝ) < g := by exact_mod_cast hg1
  unfold vertexRadius
  exact lt_min (by norm_num) (div_pos Real.pi_pos (by linarith))

/-- The compressed corner scale is below the arc scale:
`vertexRadius g ^ (2g) < π/(2g)`. -/
theorem vertexRadius_pow_lt (g : ℕ) [NeZero g] :
    vertexRadius g ^ (2 * g) < Real.pi / (2 * g) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hg : (0 : ℝ) < g := by exact_mod_cast hg1
  have hpos : 0 < vertexRadius g := vertexRadius_pos g
  have h12 : vertexRadius g ≤ 1 / 2 := min_le_left _ _
  have hpow : vertexRadius g ^ (2 * g) ≤ vertexRadius g :=
    pow_le_of_le_one hpos.le (by linarith) (by omega)
  have hquarter : vertexRadius g ≤ Real.pi / (4 * g) := min_le_right _ _
  have hlt : Real.pi / (4 * g) < Real.pi / (2 * g) := by
    apply div_lt_div_of_pos_left Real.pi_pos (by linarith)
    linarith
  linarith

/-- The sector index of a chart-disc point: the integer part of its angle in
units of `π/(2g)`, with the angle normalized to `[0, 2π)`. -/
noncomputable def vertexSectorIndex (g : ℕ) (u : ℂ) : ℕ :=
  (⌊(2 * g / Real.pi) *
    (if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u)⌋).toNat

/-- The vertex chart inverse: on sector `m` of the chart disc, the class of
`polyVertex (c m) · exp (i · (-1)^m · u^(2g))`; the integer power `u^(2g)`
compresses each corner angle `π` to `π/(2g)`. -/
noncomputable def vertexChartFun (g : ℕ) [NeZero g] (u : ℂ) : GenusSurface g :=
  Quotient.mk (genusSetoid g)
    (projDisc (polyVertex g ((vertexSlot g (vertexSectorIndex g u)).val : ℤ) *
      Complex.exp (Complex.I * (-1) ^ vertexSectorIndex g u * u ^ (2 * g))))

/-- Ray consistency of the vertex chart: on the ray shared by sectors `m`
and `m + 1` the two sector formulas give `genusRel`-equal points — the side
pairing of arc `c m - 1` carries `polyVertex (c m) · e^{-iθ}` to
`polyVertex (π̂ (c m - 1)) · e^{+iθ}` and `π̂ (c m - 1) = c (m + 1)`. -/
theorem vertexRay_glue (g : ℕ) [NeZero g] (m : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : r ^ (2 * g) < Real.pi / (2 * g)) :
    genusRel g
      (projDisc (polyVertex g ((vertexSlot g (m : ZMod (4 * g))).val : ℤ) *
        Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g)))))
      (projDisc (polyVertex g ((vertexSlot g ((m : ZMod (4 * g)) + 1)).val : ℤ) *
        Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)))) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set θ : ℝ := r ^ (2 * g) with hθ
  have hθ0 : 0 ≤ θ := pow_nonneg hr _
  set w : ℝ := 2 * g * θ / Real.pi with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w < 1 := by
    rw [hw, div_lt_one hπ]
    calc 2 * g * θ < 2 * g * (Real.pi / (2 * g)) := by
          exact mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = Real.pi := by field_simp
  have hwθ : Real.pi * w / (2 * g) = θ := by
    rw [hw]
    field_simp
  have hθC : ((r : ℂ)) ^ (2 * g) = ((θ : ℝ) : ℂ) := by
    rw [hθ]
    push_cast
    ring
  -- Norms: both sides are on the unit circle.
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
  set a := vertexSlot g ((m : ℕ) : ZMod (4 * g)) with ha
  set b := vertexSlot g (((m : ℕ) : ZMod (4 * g)) + 1) with hb
  have hnorm1 : ‖polyVertex g ((a.val : ℤ)) *
      Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g)))‖ = 1 := by
    rw [norm_mul, hvert]
    have hre : -(Complex.I * (r : ℂ) ^ (2 * g)) = ((-θ : ℝ) : ℂ) * Complex.I := by
      rw [hθC]
      push_cast
      ring
    rw [hre, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnorm2 : ‖polyVertex g ((b.val : ℤ)) *
      Complex.exp (Complex.I * (r : ℂ) ^ (2 * g))‖ = 1 := by
    rw [norm_mul, hvert]
    have hre : Complex.I * (r : ℂ) ^ (2 * g) = ((θ : ℝ) : ℂ) * Complex.I := by
      rw [hθC]
      ring
    rw [hre, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hp1 : (projDisc (polyVertex g ((a.val : ℤ)) *
      Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g))))).1
      = polyVertex g ((a.val : ℤ)) * Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g))) :=
    projDisc_eq (le_of_eq hnorm1)
  have hp2 : (projDisc (polyVertex g ((b.val : ℤ)) *
      Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)))).1
      = polyVertex g ((b.val : ℤ)) * Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)) :=
    projDisc_eq (le_of_eq hnorm2)
  -- ZMod plumbing.
  have hcast : ∀ x : ZMod (4 * g), (((x.val : ℤ)) : ZMod (4 * g)) = x := by
    intro x
    rw [Int.cast_natCast]
    exact ZMod.natCast_rightInverse x
  have hpv : ∀ x y : ℤ, ((x : ZMod (4 * g)) = (y : ZMod (4 * g))) →
      polyVertex g x = polyVertex g y := by
    intro x y hxy
    rw [ZMod.intCast_eq_intCast_iff] at hxy
    obtain ⟨j, hj⟩ := Int.ModEq.dvd hxy
    have hjZ : x - y = 4 * (g : ℤ) * (-j) := by push_cast at hj ⊢; linarith
    have hjC : (x : ℂ) - y = 4 * g * (-j : ℤ) := by exact_mod_cast hjZ
    unfold polyVertex
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-j, ?_⟩
    push_cast at hjC ⊢
    field_simp
    linear_combination hjC
  have hsub1val : ∀ x : ZMod (4 * g), x ≠ 0 → (x - 1).val = x.val - 1 := by
    intro x hx
    have hx1 : 1 ≤ x.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hx ((ZMod.val_eq_zero x).mp hc))
    have hxlt : x.val < 4 * g := ZMod.val_lt x
    have hxe : x - 1 = ((x.val - 1 : ℕ) : ZMod (4 * g)) := by
      rw [Nat.cast_sub hx1, Nat.cast_one, ZMod.natCast_rightInverse x]
    rw [hxe, ZMod.val_cast_of_lt (by omega)]
  have hneg1val : (0 - 1 : ZMod (4 * g)).val = 4 * g - 1 := by
    have h1 : (0 - 1 : ZMod (4 * g)) = ((4 * g - 1 : ℕ) : ZMod (4 * g)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self]
    rw [h1, ZMod.val_cast_of_lt (by omega)]
  have hsucc : b = pairInv g (a - 1) := vertexSlot_succ g _
  have hπw : Real.pi * w = 2 * g * θ := by
    rw [hw]
    field_simp
  -- The two component identities, one per sign of the exponent.
  have harcM : ∀ (k : ℤ) (t : ℝ) (c : ℤ), ((k : ℝ) + t) = (c : ℝ) - w →
      arcPoint g k t = polyVertex g c * Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g))) := by
    intro k t c hkt
    unfold arcPoint polyVertex
    rw [hθC, ← Complex.exp_add]
    congr 1
    have key : Real.pi * ((k : ℝ) + t) = Real.pi * c - 2 * g * θ := by
      rw [hkt]
      linear_combination -hπw
    have keyC : (Real.pi : ℂ) * ((k : ℂ) + t) = (Real.pi : ℂ) * c - 2 * g * θ := by
      exact_mod_cast key
    field_simp
    linear_combination keyC
  have harcP : ∀ (k : ℤ) (t : ℝ) (c : ℤ), ((k : ℝ) + t) = (c : ℝ) + w →
      arcPoint g k t = polyVertex g c * Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)) := by
    intro k t c hkt
    unfold arcPoint polyVertex
    rw [hθC, ← Complex.exp_add]
    congr 1
    have key : Real.pi * ((k : ℝ) + t) = Real.pi * c + 2 * g * θ := by
      rw [hkt]
      linear_combination hπw
    have keyC : (Real.pi : ℂ) * ((k : ℂ) + t) = (Real.pi : ℂ) * c + 2 * g * θ := by
      exact_mod_cast key
    field_simp
    linear_combination keyC
  by_cases hs : (a - 1).val % 4 = 0 ∨ (a - 1).val % 4 = 1
  · -- Source case: `b = a + 1`, pairing arc `k = a.val - 1`.
    have hane : a ≠ 0 := by
      intro ha0
      rw [ha0, hneg1val] at hs
      omega
    have haval : (a - 1).val = a.val - 1 := hsub1val a hane
    have ha1 : 1 ≤ a.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hane ((ZMod.val_eq_zero a).mp hc))
    have hbval : b = a + 1 := by
      rw [hsucc]
      unfold pairInv
      rw [ite_eq_left hs]
      ring
    have hpvb : polyVertex g ((b.val : ℤ)) = polyVertex g ((a.val : ℤ) + 1) := by
      apply hpv
      rw [hcast]
      push_cast
      rw [ZMod.natCast_rightInverse a, hbval]
    refine Or.inr (Or.inl ⟨(a.val : ℤ) - 1, by omega, Or.inl ?_⟩)
    unfold pairGraph
    refine ⟨⟨1 - w, by constructor <;> [linarith; linarith]⟩, Set.mem_univ _, ?_⟩
    rw [Prod.ext_iff]
    constructor
    · change arcPoint g ((a.val : ℤ) - 1) (1 - w) = _
      rw [hp1]
      exact harcM ((a.val : ℤ) - 1) (1 - w) (a.val : ℤ) (by push_cast; ring)
    · change arcPoint g ((a.val : ℤ) - 1 + 2) (1 - (1 - w)) = _
      rw [hp2, hpvb]
      exact harcP ((a.val : ℤ) - 1 + 2) (1 - (1 - w)) ((a.val : ℤ) + 1) (by push_cast; ring)
  · -- Target case: `b = a - 3`, pairing arc `k = a.val - 3`.
    have hbval : b = a - 3 := by
      rw [hsucc]
      unfold pairInv
      rw [ite_eq_right hs]
      ring
    have hmod4 : (((a - 1).val : ℤ)) % 4 = ((a.val : ℤ) - 1) % 4 := by
      by_cases ha0 : a = 0
      · simp only [ha0, hneg1val, ZMod.val_zero]
        omega
      · rw [hsub1val a ha0]
        have ha1 : 1 ≤ a.val :=
          Nat.one_le_iff_ne_zero.mpr (fun hc => ha0 ((ZMod.val_eq_zero a).mp hc))
        omega
    have hs' : ((a.val : ℤ) - 1) % 4 = 2 ∨ ((a.val : ℤ) - 1) % 4 = 3 := by omega
    have hpvb : polyVertex g ((b.val : ℤ)) = polyVertex g ((a.val : ℤ) - 3) := by
      apply hpv
      rw [hcast]
      push_cast
      rw [ZMod.natCast_rightInverse a, hbval]
    refine Or.inr (Or.inl ⟨(a.val : ℤ) - 3, by omega, Or.inr ?_⟩)
    unfold pairGraph
    refine ⟨⟨w, by constructor <;> [linarith; linarith]⟩, Set.mem_univ _, ?_⟩
    rw [Prod.ext_iff]
    constructor
    · change arcPoint g ((a.val : ℤ) - 3) w = _
      rw [hp2, hpvb]
      exact harcP ((a.val : ℤ) - 3) w ((a.val : ℤ) - 3) (by push_cast; ring)
    · change arcPoint g ((a.val : ℤ) - 3 + 2) (1 - w) = _
      rw [hp1]
      exact harcM ((a.val : ℤ) - 3 + 2) (1 - w) (a.val : ℤ) (by push_cast; ring)

/-- Continuity of the vertex chart inverse on the chart disc: `4g` closed
sectors glued along consistent rays, with all formulas tending to the vertex
class at `0`. -/
theorem vertexChart_continuousOn (g : ℕ) [NeZero g] :
    ContinuousOn (vertexChartFun g) (Metric.ball (0 : ℂ) (vertexRadius g)) := by
  classical
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := vertexRadius g with hδdef
  have hδ0 : 0 < δ := vertexRadius_pos g
  have hδp : δ ^ (2 * g) < Real.pi / (2 * g) := vertexRadius_pow_lt g
  set h₀ : ℝ := Real.pi / (2 * g) with hh₀
  have hh0 : 0 < h₀ := by rw [hh₀]; positivity
  have hg1R : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hh2 : h₀ ≤ Real.pi / 2 := by
    rw [hh₀, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
    have h2g : (2 : ℝ) ≤ 2 * g := by linarith
    exact mul_le_mul_of_nonneg_left h2g hπ.le
  have h4gh : (4 * (g : ℝ)) * h₀ = 2 * Real.pi := by
    rw [hh₀]
    field_simp
    norm_num
  -- The unit-circle exponential and the closed sectors.
  set E : ℝ → ℂ := fun x => Complex.exp ((x : ℂ) * Complex.I) with hEdef
  have hE : ∀ x y : ℝ, E x * E y = E (x + y) := by
    intro x y
    simp only [hEdef]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEim : ∀ x : ℝ, (E x).im = Real.sin x := by
    intro x
    simp only [hEdef]
    exact Complex.exp_ofReal_mul_I_im x
  have hSim : ∀ ρ x θ : ℝ, (((ρ : ℂ) * E x) * E (-θ)).im = ρ * Real.sin (x - θ) := by
    intro ρ x θ
    rw [mul_assoc, hE, Complex.im_ofReal_mul, hEim, ← sub_eq_add_neg]
  set S : ℕ → Set ℂ := fun n =>
    {u : ℂ | 0 ≤ (u * E (-((n : ℝ) * h₀))).im ∧ (u * E (-(((n : ℝ) + 1) * h₀))).im ≤ 0}
    with hS
  have hSclosed : ∀ n : ℕ, IsClosed (S n) := by
    intro n
    have h1 : Continuous fun u : ℂ => (u * E (-((n : ℝ) * h₀))).im :=
      Complex.continuous_im.comp (continuous_mul_const _)
    have h2 : Continuous fun u : ℂ => (u * E (-(((n : ℝ) + 1) * h₀))).im :=
      Complex.continuous_im.comp (continuous_mul_const _)
    have hrw : S n = {u : ℂ | 0 ≤ (u * E (-((n : ℝ) * h₀))).im} ∩
        {u : ℂ | (u * E (-(((n : ℝ) + 1) * h₀))).im ≤ 0} := by
      simp only [hS]
      exact Set.ofPred_and
    rw [hrw]
    exact (isClosed_le continuous_const h1).inter (isClosed_le h2 continuous_const)
  -- Sector index basics.
  have hsec0 : vertexSectorIndex g (0 : ℂ) = 0 := by
    unfold vertexSectorIndex
    rw [Complex.arg_zero]
    norm_num
  have hpolar : ∀ u : ℂ, u ≠ 0 →
      ∃ α : ℝ, 0 ≤ α ∧ α < 2 * Real.pi ∧ u = (‖u‖ : ℂ) * E α ∧
        (vertexSectorIndex g u : ℝ) * h₀ ≤ α ∧
        α < ((vertexSectorIndex g u : ℝ) + 1) * h₀ ∧ vertexSectorIndex g u < 4 * g := by
    intro u hu
    have harg1 : -Real.pi < Complex.arg u := Complex.neg_pi_lt_arg u
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
    have hue : u = (‖u‖ : ℂ) * E α := by
      have hbase : u = (‖u‖ : ℂ) * E (Complex.arg u) := by
        simp only [hEdef]
        exact (Complex.norm_mul_exp_arg_mul_I u).symm
      rw [hα]
      split_ifs with hc
      · have h2π : E (2 * Real.pi) = 1 := by
          simp only [hEdef]
          have harg : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg, Complex.exp_two_pi_mul_I]
        calc u = (‖u‖ : ℂ) * E (Complex.arg u) := hbase
          _ = (‖u‖ : ℂ) * (E (Complex.arg u) * E (2 * Real.pi)) := by rw [h2π, mul_one]
          _ = (‖u‖ : ℂ) * E (Complex.arg u + 2 * Real.pi) := by rw [hE]
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
    have hle : ((vertexSectorIndex g u : ℝ)) ≤ x := by
      have h1 := Int.floor_le x
      have h2 : ((vertexSectorIndex g u : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsecZ
      rw [h2]
      exact h1
    have hlt : x < (vertexSectorIndex g u : ℝ) + 1 := by
      have h1 := Int.lt_floor_add_one x
      have h2 : ((vertexSectorIndex g u : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsecZ
      rw [h2]
      exact h1
    have hxα : x * h₀ = α := by
      rw [hx, hh₀]
      field_simp
    have hb1 : (vertexSectorIndex g u : ℝ) * h₀ ≤ α := by
      rw [← hxα]
      exact mul_le_mul_of_nonneg_right hle hh0.le
    have hb2 : α < ((vertexSectorIndex g u : ℝ) + 1) * h₀ := by
      rw [← hxα]
      exact (mul_lt_mul_of_pos_right hlt hh0)
    have hm4 : vertexSectorIndex g u < 4 * g := by
      have hxlt : x < 4 * g := by
        rw [hx]
        calc 2 * (g : ℝ) / Real.pi * α < 2 * g / Real.pi * (2 * Real.pi) := by
              exact mul_lt_mul_of_pos_left hα2 (by positivity)
          _ = 4 * g := by field_simp; ring
      have hflt : ⌊x⌋ < ((4 * g : ℕ) : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hxlt)
      omega
    exact ⟨α, hα0, hα2, hue, hb1, hb2, hm4⟩
  have hcover : ∀ u : ℂ, u ∈ S (vertexSectorIndex g u) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      refine ⟨?_, ?_⟩ <;> simp
    · obtain ⟨α, hα0, hα2, hue, hb1, hb2, hm4⟩ := hpolar u hu
      set msec := vertexSectorIndex g u with hmsecdef
      refine ⟨?_, ?_⟩
      · rw [hue, hSim]
        apply mul_nonneg (norm_nonneg u)
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith
        · linarith [hh2, hπ]
      · rw [hue, hSim]
        have hsin : Real.sin (α - ((msec : ℝ) + 1) * h₀) ≤ 0 := by
          have hneg : 0 ≤ Real.sin (-(α - ((msec : ℝ) + 1) * h₀)) := by
            apply Real.sin_nonneg_of_nonneg_of_le_pi
            · linarith
            · linarith [hh2, hπ]
          rw [Real.sin_neg] at hneg
          linarith
        have hp := mul_nonneg (norm_nonneg u) (neg_nonneg.mpr hsin)
        linarith [hp]
  -- Interval extraction from the sign of sin.
  have hsinA : ∀ x : ℝ, -(2 * Real.pi) < x → x < 2 * Real.pi → 0 ≤ Real.sin x →
      (0 ≤ x ∧ x ≤ Real.pi) ∨ x ≤ -Real.pi := by
    intro x hx1 hx2 hs
    rcases le_or_gt x (-Real.pi) with hc | hc
    · exact Or.inr hc
    rcases lt_or_ge x 0 with h0 | h0
    · exact absurd hs (not_le.mpr (Real.sin_neg_of_neg_of_neg_pi_lt h0 hc))
    rcases le_or_gt x Real.pi with h1 | h1
    · exact Or.inl ⟨h0, h1⟩
    exfalso
    have h2 : 0 < Real.sin (x - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h2
    linarith
  have hsinB : ∀ y : ℝ, -(2 * Real.pi) - Real.pi / 2 < y → y < 2 * Real.pi →
      Real.sin y ≤ 0 → (-Real.pi ≤ y ∧ y ≤ 0) ∨ Real.pi ≤ y ∨ y ≤ -(2 * Real.pi) := by
    intro y hy1 hy2 hs
    rcases le_or_gt y 0 with h0 | h0
    · rcases le_or_gt (-Real.pi) y with h1 | h1
      · exact Or.inl ⟨h1, h0⟩
      rcases le_or_gt y (-(2 * Real.pi)) with h2 | h2
      · exact Or.inr (Or.inr h2)
      exfalso
      have h3 : 0 < Real.sin (y + 2 * Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_add_two_pi] at h3
      linarith
    rcases le_or_gt Real.pi y with h1 | h1
    · exact Or.inr (Or.inl h1)
    exact absurd hs (not_le.mpr (Real.sin_pos_of_pos_of_lt_pi h0 h1))
  have hchar : ∀ n : ℕ, n < 4 * g → ∀ u : ℂ, u ≠ 0 → u ∈ S n → ∀ α : ℝ,
      0 ≤ α → α < 2 * Real.pi → u = (‖u‖ : ℂ) * E α →
      ((n : ℝ) * h₀ ≤ α ∧ α ≤ ((n : ℝ) + 1) * h₀) ∨ (α = 0 ∧ n = 4 * g - 1) := by
    intro n hn u hu hmem α hα0 hα2 hue
    have hr0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    obtain ⟨hm1, hm2⟩ := hmem
    rw [hue, hSim] at hm1 hm2
    have hs1 : 0 ≤ Real.sin (α - (n : ℝ) * h₀) := (mul_nonneg_iff_of_pos_left hr0).mp hm1
    have hs2 : Real.sin (α - ((n : ℝ) + 1) * h₀) ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have := mul_pos hr0 hcon
      linarith
    have hn' : (n : ℝ) < 4 * g := by exact_mod_cast hn
    have hnh0 : 0 ≤ (n : ℝ) * h₀ := mul_nonneg (Nat.cast_nonneg n) hh0.le
    have hnh : (n : ℝ) * h₀ < 2 * Real.pi := by
      have := mul_lt_mul_of_pos_right hn' hh0
      linarith
    have hx1 : -(2 * Real.pi) < α - (n : ℝ) * h₀ := by linarith
    have hx2 : α - (n : ℝ) * h₀ < 2 * Real.pi := by linarith
    have hy1 : -(2 * Real.pi) - Real.pi / 2 < α - ((n : ℝ) + 1) * h₀ := by linarith
    have hy2 : α - ((n : ℝ) + 1) * h₀ < 2 * Real.pi := by linarith
    rcases hsinA _ hx1 hx2 hs1 with ⟨hA1, hA2⟩ | hA
    · rcases hsinB _ hy1 hy2 hs2 with ⟨hB1, hB2⟩ | hB | hB
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exfalso; linarith
      · exfalso; linarith [hh2, hπ]
    · rcases hsinB _ hy1 hy2 hs2 with ⟨hB1, hB2⟩ | hB | hB
      · exfalso; linarith
      · exfalso; linarith
      · have hle' : ((n : ℝ) + 1) ≤ 4 * g := by exact_mod_cast hn
        have hn1 : ((n : ℝ) + 1) * h₀ ≤ 4 * g * h₀ :=
          mul_le_mul_of_nonneg_right hle' hh0.le
        have hα0' : α = 0 := le_antisymm (by linarith) hα0
        have hnge : 4 * g ≤ n + 1 := by
          by_contra hcon
          push Not at hcon
          have hlt' : ((n : ℝ) + 1) < 4 * g := by exact_mod_cast hcon
          have := mul_lt_mul_of_pos_right hlt' hh0
          linarith
        exact Or.inr ⟨hα0', by omega⟩
  -- The per-sector continuous formulas.
  set F : ℕ → ℂ → GenusSurface g := fun n u =>
    Quotient.mk (genusSetoid g)
      (projDisc (polyVertex g ((vertexSlot g (n : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ n * u ^ (2 * g)))) with hF
  have hfF : ∀ u : ℂ, vertexChartFun g u = F (vertexSectorIndex g u) u := by
    intro u
    rw [hF]
    rfl
  have hFc : ∀ n : ℕ, Continuous (F n) := by
    intro n
    rw [hF]
    have h1 : Continuous fun u : ℂ => Complex.I * (-1) ^ n * u ^ (2 * g) :=
      continuous_const.mul (continuous_pow (2 * g))
    have h2 : Continuous fun u : ℂ =>
        polyVertex g ((vertexSlot g (n : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ n * u ^ (2 * g)) :=
      continuous_const.mul (Complex.continuous_exp.comp h1)
    exact continuous_quot_mk.comp (continuous_projDisc.comp h2)
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
  -- The glue across shared rays, in quotient form.
  have hglue : ∀ n : ℕ, ∀ ρ : ℝ, 0 ≤ ρ → ρ < δ →
      (Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g (n : ZMod (4 * g))).val : ℤ) *
          Complex.exp (-(Complex.I * (ρ : ℂ) ^ (2 * g))))) : GenusSurface g) =
      Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g ((n : ZMod (4 * g)) + 1)).val : ℤ) *
          Complex.exp (Complex.I * (ρ : ℂ) ^ (2 * g)))) := by
    intro n ρ hρ0 hρδ
    apply Quotient.sound
    apply vertexRay_glue g n hρ0
    calc ρ ^ (2 * g) ≤ δ ^ (2 * g) :=
          pow_le_pow_left₀ hρ0 hρδ.le (2 * g)
      _ < Real.pi / (2 * g) := hδp
  -- The function agrees with the fixed-sector formula on each closed sector.
  have hEqOn : ∀ n : ℕ, n < 4 * g → ∀ u : ℂ, u ∈ S n → u ∈ Metric.ball (0 : ℂ) δ →
      vertexChartFun g u = F n u := by
    intro n hn u hmem hball
    by_cases hu : u = 0
    · subst hu
      rw [hfF 0, hsec0]
      have hzero : ∀ k : ℕ, F k 0 = Quotient.mk (genusSetoid g)
          (projDisc (polyVertex g ((vertexSlot g (k : ZMod (4 * g))).val : ℤ))) := by
        intro k
        rw [hF]
        simp only []
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
      rw [hzero 0, hzero n]
      apply Quotient.sound
      refine Or.inr (Or.inr ⟨?_, ?_⟩) <;>
        · rw [projDisc_eq (le_of_eq (hvert _))]
          exact ⟨_, rfl⟩
    · obtain ⟨α, hα0, hα2, hue, hb1, hb2, hm4⟩ := hpolar u hu
      rcases hchar n hn u hu hmem α hα0 hα2 hue with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · -- interior-or-shared-ray case
        have hnm1 : n ≤ vertexSectorIndex g u := by
          by_contra hcon
          push Not at hcon
          have hle' : (vertexSectorIndex g u : ℝ) + 1 ≤ (n : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hcon
          have := mul_le_mul_of_nonneg_right hle' hh0.le
          linarith
        have hnm2 : vertexSectorIndex g u ≤ n + 1 := by
          by_contra hcon
          push Not at hcon
          have hle' : (n : ℝ) + 2 ≤ (vertexSectorIndex g u : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hcon
          have := mul_le_mul_of_nonneg_right hle' hh0.le
          linarith
        rcases Nat.eq_or_lt_of_le hnm1 with heq | hlt
        · rw [hfF u, ← heq]
        · have hmeq : vertexSectorIndex g u = n + 1 := by omega
          have hαeq : α = ((n : ℝ) + 1) * h₀ := by
            rw [hmeq] at hb1
            push_cast at hb1
            linarith
          have hρ0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
          have hρδ : ‖u‖ < δ := mem_ball_zero_iff.mp hball
          have hupow : u ^ (2 * g) = ((‖u‖ : ℂ)) ^ (2 * g) * (-1) ^ (n + 1) := by
            have h1 : u ^ (2 * g) = ((‖u‖ : ℂ)) ^ (2 * g) * (E α) ^ (2 * g) := by
              rw [← mul_pow]
              exact congrArg (fun z : ℂ => z ^ (2 * g)) hue
            rw [h1, hαeq]
            congr 1
            simp only [hEdef]
            rw [← Complex.exp_nat_mul]
            have hexp : ((2 * g : ℕ) : ℂ) * (((((n : ℝ) + 1) * h₀ : ℝ) : ℂ) * Complex.I)
                = ((n + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
              rw [hh₀]
              push_cast
              have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
              field_simp
            rw [hexp, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
          have hodd : ((-1 : ℂ)) ^ n * (-1) ^ (n + 1) = -1 := by
            rw [← pow_add]
            exact Odd.neg_one_pow ⟨n, by ring⟩
          have heven : ((-1 : ℂ)) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow ⟨n + 1, by ring⟩
          have idA : Complex.I * (-1) ^ n * u ^ (2 * g)
              = -(Complex.I * (‖u‖ : ℂ) ^ (2 * g)) := by
            rw [hupow]
            calc Complex.I * (-1) ^ n * ((‖u‖ : ℂ) ^ (2 * g) * (-1) ^ (n + 1))
                = Complex.I * (‖u‖ : ℂ) ^ (2 * g) * ((-1) ^ n * (-1) ^ (n + 1)) := by ring
              _ = -(Complex.I * (‖u‖ : ℂ) ^ (2 * g)) := by rw [hodd]; ring
          have idB : Complex.I * (-1) ^ (n + 1) * u ^ (2 * g)
              = Complex.I * (‖u‖ : ℂ) ^ (2 * g) := by
            rw [hupow]
            calc Complex.I * (-1) ^ (n + 1) * ((‖u‖ : ℂ) ^ (2 * g) * (-1) ^ (n + 1))
                = Complex.I * (‖u‖ : ℂ) ^ (2 * g) * ((-1) ^ (n + 1) * (-1) ^ (n + 1)) := by
                  ring
              _ = Complex.I * (‖u‖ : ℂ) ^ (2 * g) := by rw [heven]; ring
          have hslot : ((n + 1 : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1 := by
            push_cast
            ring
          rw [hfF u, hmeq, hF]
          simp only []
          rw [idA, idB, hslot]
          exact (hglue n ‖u‖ hρ0 hρδ).symm
      · -- wrap-around case: `α = 0`, `n = 4g - 1`.
        have hmsec0 : vertexSectorIndex g u = 0 := by
          by_contra hcon
          have h1 : (1 : ℝ) ≤ (vertexSectorIndex g u : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcon
          have h2 := mul_le_mul_of_nonneg_right h1 hh0.le
          rw [hc1] at hb1
          linarith
        have hρ0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
        have hρδ : ‖u‖ < δ := mem_ball_zero_iff.mp hball
        have hE0 : E 0 = 1 := by
          simp only [hEdef]
          norm_num
        have hueρ : u = ((‖u‖ : ℝ) : ℂ) := by
          calc u = (‖u‖ : ℂ) * E α := hue
            _ = (‖u‖ : ℂ) * E 0 := by rw [hc1]
            _ = (‖u‖ : ℂ) := by rw [hE0, mul_one]
        have hupow : u ^ (2 * g) = ((‖u‖ : ℂ)) ^ (2 * g) :=
          congrArg (fun z : ℂ => z ^ (2 * g)) hueρ
        have idB : Complex.I * (-1) ^ (0 : ℕ) * u ^ (2 * g)
            = Complex.I * (‖u‖ : ℂ) ^ (2 * g) := by
          rw [hupow, pow_zero, mul_one]
        have idA : Complex.I * (-1) ^ (4 * g - 1) * u ^ (2 * g)
            = -(Complex.I * (‖u‖ : ℂ) ^ (2 * g)) := by
          rw [hupow]
          have hodd : ((-1 : ℂ)) ^ (4 * g - 1) = -1 :=
            Odd.neg_one_pow ⟨2 * g - 1, by omega⟩
          rw [hodd]
          ring
        have hslot : ((0 : ℕ) : ZMod (4 * g)) = (((4 * g - 1 : ℕ)) : ZMod (4 * g)) + 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 4 * g), Nat.cast_one, ZMod.natCast_self,
            Nat.cast_zero]
          ring
        rw [hfF u, hmsec0, hc2, hF]
        simp only []
        rw [idA, idB, hslot]
        exact (hglue (4 * g - 1) ‖u‖ hρ0 hρδ).symm
  -- Assembly: pasting over the finitely many closed sectors through the point.
  intro u₀ hu₀
  have hunionT : ∀ t : Finset ℕ,
      (∀ n ∈ t, ContinuousWithinAt (vertexChartFun g) (S n ∩ Metric.ball 0 δ) u₀) →
      ContinuousWithinAt (vertexChartFun g) (⋃ n ∈ t, S n ∩ Metric.ball 0 δ) u₀ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have hempty : (⋃ n ∈ (∅ : Finset ℕ), S n ∩ Metric.ball 0 δ) = (∅ : Set ℂ) := by
        simp
      rw [hempty]
      change Filter.Tendsto _ _ _
      rw [nhdsWithin_empty]
      exact tendsto_bot
    | insert a s ha ih =>
      intro hall
      rw [Finset.set_biUnion_insert]
      exact (hall a (Finset.mem_insert_self a s)).union
        (ih fun n hn => hall n (Finset.mem_insert_of_mem hn))
  set Bad : Finset ℕ := (Finset.range (4 * g)).filter (fun n => u₀ ∉ S n) with hBad
  set V : Set ℂ := Metric.ball (0 : ℂ) δ ∩ ⋂ n ∈ Bad, (S n)ᶜ with hV
  have hVopen : IsOpen V := by
    rw [hV]
    apply IsOpen.inter isOpen_ball
    apply isOpen_biInter_finset
    intro n _
    exact (hSclosed n).isOpen_compl
  have hu₀V : u₀ ∈ V := by
    rw [hV]
    refine ⟨hu₀, ?_⟩
    apply Set.mem_iInter₂.mpr
    intro n hn
    rw [hBad, Finset.mem_filter] at hn
    exact hn.2
  set Good : Finset ℕ := (Finset.range (4 * g)).filter (fun n => u₀ ∈ S n) with hGood
  have hVsub : V ⊆ ⋃ n ∈ Good, S n ∩ Metric.ball 0 δ := by
    intro u hu
    rw [hV] at hu
    have hsub4 : vertexSectorIndex g u < 4 * g := by
      by_cases hu0 : u = 0
      · rw [hu0, hsec0]
        omega
      · exact (hpolar u hu0).choose_spec.2.2.2.2.2
    have hgood : vertexSectorIndex g u ∈ Good := by
      rw [hGood, Finset.mem_filter, Finset.mem_range]
      refine ⟨hsub4, ?_⟩
      by_contra hcon
      have hbad : vertexSectorIndex g u ∈ Bad := by
        rw [hBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨hsub4, hcon⟩
      have hcompl := Set.mem_iInter₂.mp hu.2
      exact (hcompl _ hbad) (hcover u)
    exact Set.mem_biUnion hgood ⟨hcover u, hu.1⟩
  have hpiece : ∀ n ∈ Good, ContinuousWithinAt (vertexChartFun g)
      (S n ∩ Metric.ball 0 δ) u₀ := by
    intro n hnG
    rw [hGood, Finset.mem_filter, Finset.mem_range] at hnG
    have hcw : ContinuousWithinAt (F n) (S n ∩ Metric.ball 0 δ) u₀ :=
      (hFc n).continuousAt.continuousWithinAt
    apply hcw.congr
    · intro y hy
      exact hEqOn n hnG.1 y hy.1 hy.2
    · exact hEqOn n hnG.1 u₀ hnG.2 hu₀
  have hCW : ContinuousWithinAt (vertexChartFun g) V u₀ :=
    (hunionT Good hpiece).mono hVsub
  exact (hCW.continuousAt (hVopen.mem_nhds hu₀V)).continuousWithinAt

/-- Injectivity of the vertex chart inverse on the chart disc: same-sector
collisions force `u^(2g) = u'^(2g)` within one closed angular sector, and
cross-sector collisions occur only on the shared rays, where the formulas
agree; uses injectivity of the slot map. -/
theorem vertexChart_injOn (g : ℕ) [NeZero g] :
    Set.InjOn (vertexChartFun g) (Metric.ball (0 : ℂ) (vertexRadius g)) := by
  classical
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hg1R : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := vertexRadius g with hδdef
  have hδ0 : 0 < δ := vertexRadius_pos g
  set h₀ : ℝ := Real.pi / (2 * g) with hh₀
  have hh0 : 0 < h₀ := by rw [hh₀]; positivity
  have h4gh : (4 * (g : ℝ)) * h₀ = 2 * Real.pi := by
    rw [hh₀]
    field_simp
    norm_num
  -- `δ ^ (2g) ≤ h₀ / 4`.
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
  -- Angle extraction from equality of unit exponentials.
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
  -- Exponential forms of vertices and arc points.
  have hpv2 : ∀ p : ℤ, polyVertex g p =
      Complex.exp (Complex.I * (((h₀ * (p : ℝ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro p
    unfold polyVertex
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
    field_simp
  have harc2 : ∀ (k : ℤ) (t : ℝ), arcPoint g k t =
      Complex.exp (Complex.I * (((h₀ * ((k : ℝ) + t) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro k t
    unfold arcPoint
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
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
  -- Normal form of the chart formula at any point of the chart disc.
  have hsetup : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
      ∃ (α φ W : ℝ) (c : ℤ),
        c = ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) ∧
        (0 ≤ c ∧ c < 4 * g) ∧ vertexSectorIndex g u < 4 * g ∧
        u = (‖u‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) ∧
        W = ‖u‖ ^ (2 * g) ∧ (0 ≤ W ∧ W < h₀ / 4) ∧
        (0 ≤ φ ∧ φ < Real.pi) ∧
        φ = 2 * g * α - (vertexSectorIndex g u : ℝ) * Real.pi ∧
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
      refine ⟨0, 0, ‖(0 : ℂ)‖ ^ (2 * g), _, rfl, hcval, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsec0]
        omega
      · simp
      · exact ⟨hW0, hWlt⟩
      · exact ⟨le_refl 0, hπ⟩
      · rw [hsec0]
        push_cast
        ring
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
    · -- polar decomposition
      have harg1 : -Real.pi < Complex.arg u := Complex.neg_pi_lt_arg u
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
      set m : ℕ := vertexSectorIndex g u with hm
      set φ : ℝ := 2 * g * α - (m : ℝ) * Real.pi with hφ
      have hφx : φ = Real.pi * (x - (m : ℝ)) := by
        rw [hφ, ← hπx]
        ring
      have hφ0 : 0 ≤ φ := by
        rw [hφx]
        exact mul_nonneg hπ.le (by linarith)
      have hφπ : φ < Real.pi := by
        rw [hφx]
        calc Real.pi * (x - (m : ℝ)) < Real.pi * 1 :=
              mul_lt_mul_of_pos_left (by linarith) hπ
          _ = Real.pi := mul_one _
      -- the exponential identity
      have hIarg : Complex.I * (-1) ^ m * u ^ (2 * g)
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
            = (-1) ^ m * Complex.exp (((φ : ℝ) : ℂ) * Complex.I) := by
          have h2 : (2 * g * α : ℝ) = (m : ℝ) * Real.pi + φ := by
            rw [hφ]
            ring
          rw [h2]
          have h3 : ((((m : ℝ) * Real.pi + φ : ℝ)) : ℂ) * Complex.I
              = ((m : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) + ((φ : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [h3, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
        have hcs : Complex.exp (((φ : ℝ) : ℂ) * Complex.I)
            = ((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I := by
          rw [Complex.exp_mul_I]
          rw [Complex.ofReal_cos, Complex.ofReal_sin]
        have hm2 : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
          rw [← pow_add]
          exact Even.neg_one_pow ⟨m, by ring⟩
        calc Complex.I * (-1) ^ m * u ^ (2 * g)
            = Complex.I * (-1) ^ m * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                ((-1) ^ m * (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I))) := by
              rw [hupow, hsplit, hcs]
          _ = Complex.I * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I)) *
                ((-1) ^ m * (-1) ^ m) := by ring
          _ = Complex.I * ((((‖u‖ ^ (2 * g) * Real.cos φ : ℝ)) : ℂ) +
                (((‖u‖ ^ (2 * g) * Real.sin φ : ℝ)) : ℂ) * Complex.I) := by
              rw [hm2]
              push_cast
              ring
      have hzid : polyVertex g ((vertexSlot g ((m : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ m * u ^ (2 * g))
          = Complex.exp (Complex.I *
              (((h₀ * (((vertexSlot g ((m : ℕ) : ZMod (4 * g))).val : ℤ) : ℝ) +
                ‖u‖ ^ (2 * g) * Real.cos φ : ℝ) : ℂ) +
              ((‖u‖ ^ (2 * g) * Real.sin φ : ℝ) : ℂ) * Complex.I)) := by
        rw [hpv2, hIarg, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      refine ⟨α, φ, ‖u‖ ^ (2 * g), _, rfl, hcval, hm4, hue, rfl, ⟨hW0, hWlt⟩, ⟨hφ0, hφπ⟩,
        rfl, hzid, ?_, ?_⟩
      · rw [hzid, hnormz]
        rw [Real.exp_le_one_iff]
        have : 0 ≤ ‖u‖ ^ (2 * g) * Real.sin φ :=
          mul_nonneg hW0 (Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ.le)
        linarith
      · intro hWz
        exact norm_eq_zero.mp ((pow_eq_zero_iff (by omega : 2 * g ≠ 0)).mp hWz)
  -- pinning and collapse helpers
  have hcollapse : ∀ W₁ φ₁ : ℝ, 0 ≤ φ₁ → φ₁ < Real.pi → W₁ * Real.sin φ₁ = 0 →
      W₁ * Real.cos φ₁ = W₁ := by
    intro W₁ φ₁ h0 hπ₁ hs
    rcases mul_eq_zero.mp hs with hW | hsin
    · rw [hW, zero_mul]
    · have hφz : φ₁ = 0 := by
        by_contra hne
        have hpos : 0 < Real.sin φ₁ :=
          Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne h0 (Ne.symm hne)) hπ₁
        rw [hsin] at hpos
        exact absurd hpos (lt_irrefl 0)
      rw [hφz, Real.cos_zero, mul_one]
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
      have : h₀ * (1 / 4) ≤ h₀ * (s - (e : ℝ)) := mul_le_mul_of_nonneg_left hcon hh0.le
      have h4 : h₀ * (1 / 4) = h₀ / 4 := by ring
      linarith
    have he1 : ((e : ℝ)) < 2 := by linarith
    have he2 : (-1 : ℝ) < ((e : ℝ)) := by linarith
    have hei : e < 2 ∧ -1 < e := ⟨by exact_mod_cast he1, by exact_mod_cast he2⟩
    have : e = 0 ∨ e = 1 := by omega
    rcases this with he | he
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
  have hslotinj : ∀ m m' : ℕ, m < 4 * g → m' < 4 * g →
      (vertexSlot g ((m : ℕ) : ZMod (4 * g))).val
        = (vertexSlot g ((m' : ℕ) : ZMod (4 * g))).val → m = m' := by
    intro m m' hm hm' hval
    have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = vertexSlot g ((m' : ℕ) : ZMod (4 * g)) :=
      ZMod.val_injective _ hval
    have h2 : ((m : ℕ) : ZMod (4 * g)) = ((m' : ℕ) : ZMod (4 * g)) :=
      (vertexSlot_bijective g).injective h1
    have h3 := congrArg ZMod.val h2
    rwa [ZMod.val_cast_of_lt hm, ZMod.val_cast_of_lt hm'] at h3
  -- Main argument.
  intro u hu u' hu' heqf
  obtain ⟨α, φ, W, c, hcdef, ⟨hc0, hc4⟩, hm4, hue, hWdef, ⟨hW0, hWlt⟩, ⟨hφ0, hφπ⟩,
    hφdef, hz, hn1, hzero⟩ := hsetup u hu
  obtain ⟨α', φ', W', c', hcdef', ⟨hc0', hc4'⟩, hm4', hue', hWdef', ⟨hW0', hWlt'⟩,
    ⟨hφ0', hφπ'⟩, hφdef', hz', hn1', hzero'⟩ := hsetup u' hu'
  have hrel : genusRel g
      (projDisc (polyVertex g
          ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))))
      (projDisc (polyVertex g
          ((vertexSlot g ((vertexSectorIndex g u' : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)))) :=
    Quotient.exact heqf
  rw [← hcdef, ← hcdef'] at hrel
  have hpd : (projDisc (polyVertex g c *
      Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g)))).1
      = polyVertex g c *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g)) :=
    projDisc_eq hn1
  have hpd' : (projDisc (polyVertex g c' *
      Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)))).1
      = polyVertex g c' *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)) :=
    projDisc_eq hn1'
  -- endgame from matched data
  have hfinish : W = W' → φ = φ' → c = c' → u = u' := by
    intro hWeq hφeq hceq
    by_cases hWz : W = 0
    · rw [hzero hWz, hzero' (by rw [← hWeq]; exact hWz)]
    · have hmm : vertexSectorIndex g u = vertexSectorIndex g u' := by
        apply hslotinj _ _ hm4 hm4'
        have h1 : ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ)
            = ((vertexSlot g ((vertexSectorIndex g u' : ℕ) : ZMod (4 * g))).val : ℤ) := by
          rw [← hcdef, ← hcdef', hceq]
        exact_mod_cast h1
      have hαeq : α = α' := by
        have h2 : 2 * (g : ℝ) * α = 2 * g * α' := by
          have e1 : φ = 2 * g * α - (vertexSectorIndex g u : ℝ) * Real.pi := hφdef
          have e2 : φ' = 2 * g * α' - (vertexSectorIndex g u' : ℝ) * Real.pi := hφdef'
          have e3 : ((vertexSectorIndex g u : ℕ) : ℝ)
              = ((vertexSectorIndex g u' : ℕ) : ℝ) := by
            exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hmm
          rw [e1, e2, e3] at hφeq
          linarith
        have h2g0 : (2 * (g : ℝ)) ≠ 0 := by positivity
        have h3 : 2 * (g : ℝ) * α = 2 * (g : ℝ) * α' := by linarith
        exact mul_left_cancel₀ h2g0 h3
      have hρeq : ‖u‖ = ‖u'‖ := by
        have hpow : ‖u‖ ^ (2 * g) = ‖u'‖ ^ (2 * g) := by
          rw [← hWdef, ← hWdef', hWeq]
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := pow_lt_pow_left₀ hlt (norm_nonneg u) (by omega : 2 * g ≠ 0)
          linarith
        · have := pow_lt_pow_left₀ hlt (norm_nonneg u') (by omega : 2 * g ≠ 0)
          linarith
      rw [hue, hue', hρeq, hαeq]
  -- shared pairing analysis
  have hpaircase : ∀ (c₁ c₂ : ℤ) (W₁ W₂ φ₁ φ₂ : ℝ), 0 ≤ W₁ → W₁ < h₀ / 4 →
      0 ≤ W₂ → W₂ < h₀ / 4 → 0 ≤ φ₁ → φ₁ < Real.pi → 0 ≤ φ₂ → φ₂ < Real.pi →
      ∀ (k : ℤ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      arcPoint g k t = Complex.exp (Complex.I *
        (((h₀ * (c₁ : ℝ) + W₁ * Real.cos φ₁ : ℝ) : ℂ) +
          ((W₁ * Real.sin φ₁ : ℝ) : ℂ) * Complex.I)) →
      arcPoint g (k + 2) (1 - t) = Complex.exp (Complex.I *
        (((h₀ * (c₂ : ℝ) + W₂ * Real.cos φ₂ : ℝ) : ℂ) +
          ((W₂ * Real.sin φ₂ : ℝ) : ℂ) * Complex.I)) →
      W₁ = 0 ∧ W₂ = 0 := by
    intro c₁ c₂ W₁ W₂ φ₁ φ₂ hW₁0 hW₁lt hW₂0 hW₂lt hφ₁0 hφ₁π hφ₂0 hφ₂π k t ht0 ht1 harc harc'
    rw [harc2] at harc harc'
    obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ harc
    obtain ⟨n₂, hx₂, hy₂⟩ := hkey _ _ _ _ harc'
    have hc₁ : W₁ * Real.cos φ₁ = W₁ := hcollapse W₁ φ₁ hφ₁0 hφ₁π hy₁.symm
    have hc₂ : W₂ * Real.cos φ₂ = W₂ := hcollapse W₂ φ₂ hφ₂0 hφ₂π hy₂.symm
    rw [hc₁] at hx₁
    rw [hc₂] at hx₂
    -- W₁ = h₀ (t - e₁), W₂ = h₀ ((1 - t) - e₂)
    have h2πn₁ : 2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁ := by rw [← h4gh]
    have h2πn₂ : 2 * Real.pi * (n₂ : ℝ) = 4 * g * h₀ * n₂ := by rw [← h4gh]
    have hW₁e : W₁ = h₀ * (t - ((c₁ - k + 4 * g * n₁ : ℤ) : ℝ)) := by
      push_cast
      linear_combination -hx₁ - h2πn₁
    have hW₂e : W₂ = h₀ * ((1 - t) - ((c₂ - (k + 2) + 4 * g * n₂ : ℤ) : ℝ)) := by
      push_cast
      push_cast at hx₂
      linear_combination -hx₂ - h2πn₂
    rcases hWpin W₁ _ t hW₁0 hW₁lt ht0 ht1 hW₁e with ⟨he₁, hW₁t⟩ | ⟨ht1', hW₁z⟩
    · rcases hWpin W₂ _ (1 - t) hW₂0 hW₂lt (by linarith) (by linarith) hW₂e with
        ⟨he₂, hW₂t⟩ | ⟨ht0', hW₂z⟩
      · -- W₁ = h₀ t, W₂ = h₀ (1 - t): sum is h₀, too large
        exfalso
        have hsum : W₁ + W₂ = h₀ := by
          rw [hW₁t, hW₂t]
          ring
        linarith
      · -- 1 - t = 1: t = 0 hence W₁ = 0 too
        have ht0'' : t = 0 := by linarith
        constructor
        · rw [hW₁t, ht0'', mul_zero]
        · exact hW₂z
    · rcases hWpin W₂ _ (1 - t) hW₂0 hW₂lt (by linarith) (by linarith) hW₂e with
        ⟨he₂, hW₂t⟩ | ⟨ht0', hW₂z⟩
      · have : W₂ = 0 := by
          rw [hW₂t, ht1']
          norm_num
        exact ⟨hW₁z, this⟩
      · exfalso
        linarith
  -- shared vertex analysis
  have hvertcase : ∀ (c₁ : ℤ) (W₁ φ₁ : ℝ), 0 ≤ W₁ → W₁ < h₀ / 4 →
      0 ≤ φ₁ → φ₁ < Real.pi → ∀ p : ℤ,
      Complex.exp (Complex.I * (((h₀ * (c₁ : ℝ) + W₁ * Real.cos φ₁ : ℝ) : ℂ) +
        ((W₁ * Real.sin φ₁ : ℝ) : ℂ) * Complex.I)) = polyVertex g p →
      W₁ = 0 := by
    intro c₁ W₁ φ₁ hW₁0 hW₁lt hφ₁0 hφ₁π p hpe
    rw [hpv2] at hpe
    obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ hpe
    have hcc : W₁ * Real.cos φ₁ = W₁ := hcollapse W₁ φ₁ hφ₁0 hφ₁π hy₁
    rw [hcc] at hx₁
    have h2πn₁ : 2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁ := by rw [← h4gh]
    have hW₁e : W₁ = h₀ * ((0 : ℝ) - ((c₁ - p - 4 * g * n₁ : ℤ) : ℝ)) := by
      push_cast
      linear_combination hx₁ + h2πn₁
    rcases hWpin W₁ _ 0 hW₁0 hW₁lt le_rfl (by norm_num) hW₁e with ⟨_, hW₁t⟩ | ⟨h01, _⟩
    · rw [hW₁t, mul_zero]
    · exact absurd h01 (by norm_num)
  -- case analysis on the gluing relation
  rcases hrel with h1 | ⟨k, -, hpg | hpg⟩ | ⟨hv, hv'⟩
  · -- equality clause
    have hZZ : polyVertex g c *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))
        = polyVertex g c' *
          Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)) := by
      have hval := congrArg Subtype.val h1
      rwa [hpd, hpd'] at hval
    rw [hz, hz'] at hZZ
    obtain ⟨n, hxeq, hyeq⟩ := hkey _ _ _ _ hZZ
    have h2πn : 2 * Real.pi * (n : ℝ) = 4 * g * h₀ * n := by rw [← h4gh]
    have hdh : ((c - c' - 4 * g * n : ℤ) : ℝ) * h₀ = W' * Real.cos φ' - W * Real.cos φ := by
      push_cast
      linear_combination hxeq + h2πn
    have habs : |W * Real.cos φ| ≤ W := by
      rw [abs_mul, abs_of_nonneg hW0]
      calc W * |Real.cos φ| ≤ W * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one φ) hW0
        _ = W := mul_one W
    have habs' : |W' * Real.cos φ'| ≤ W' := by
      rw [abs_mul, abs_of_nonneg hW0']
      calc W' * |Real.cos φ'| ≤ W' * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one φ') hW0'
        _ = W' := mul_one W'
    have hbd : |W' * Real.cos φ' - W * Real.cos φ| < h₀ / 2 := by
      have h1 := abs_le.mp habs
      have h2 := abs_le.mp habs'
      rw [abs_lt]
      constructor <;> linarith
    have hd0 : (c - c' - 4 * g * n : ℤ) = 0 := by
      have h1 : ((c - c' - 4 * g * n : ℤ) : ℝ) < 1 := by
        by_contra hcon
        push Not at hcon
        have h2 : 1 * h₀ ≤ ((c - c' - 4 * g * n : ℤ) : ℝ) * h₀ :=
          mul_le_mul_of_nonneg_right hcon hh0.le
        rw [one_mul, hdh] at h2
        have := (abs_lt.mp hbd).2
        linarith
      have h2 : (-1 : ℝ) < ((c - c' - 4 * g * n : ℤ) : ℝ) := by
        by_contra hcon
        push Not at hcon
        have h3 : ((c - c' - 4 * g * n : ℤ) : ℝ) * h₀ ≤ (-1) * h₀ :=
          mul_le_mul_of_nonneg_right hcon hh0.le
        rw [hdh] at h3
        have := (abs_lt.mp hbd).1
        linarith
      have hz1 : (c - c' - 4 * g * n : ℤ) < 1 := by exact_mod_cast h1
      have hz2 : (-1 : ℤ) < (c - c' - 4 * g * n : ℤ) := by exact_mod_cast h2
      omega
    have hn0 : n = 0 := by
      have hce : c - c' = 4 * (g : ℤ) * n := by omega
      rcases lt_trichotomy n 0 with hlt | h0 | hgt
      · exfalso
        have h1 : n ≤ -1 := by omega
        have h2 : 4 * (g : ℤ) * n ≤ 4 * (g : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : (4 : ℤ) * g * (-1) = -(4 * g) := by ring
        rw [h3] at h2
        omega
      · exact h0
      · exfalso
        have h1 : (1 : ℤ) ≤ n := by omega
        have h2 : 4 * (g : ℤ) * 1 ≤ 4 * (g : ℤ) * n :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        rw [mul_one] at h2
        omega
    have hcc : c = c' := by
      have := hd0
      rw [hn0] at this
      omega
    have hcos : W * Real.cos φ = W' * Real.cos φ' := by
      have h1 : ((c - c' - 4 * g * n : ℤ) : ℝ) = 0 := by
        rw [hd0]
        norm_num
      rw [h1, zero_mul] at hdh
      linarith
    have hsin : W * Real.sin φ = W' * Real.sin φ' := hyeq
    have hWW : W = W' := by
      have e1 : (W * Real.sin φ) ^ 2 + (W * Real.cos φ) ^ 2 = W ^ 2 := by
        have hpyth := Real.sin_sq_add_cos_sq φ
        linear_combination (W ^ 2) * hpyth
      have e2 : (W' * Real.sin φ') ^ 2 + (W' * Real.cos φ') ^ 2 = W' ^ 2 := by
        have hpyth := Real.sin_sq_add_cos_sq φ'
        linear_combination (W' ^ 2) * hpyth
      have hsq : W ^ 2 = W' ^ 2 := by
        rw [← e1, ← e2, hsin, hcos]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hp2 := pow_lt_pow_left₀ hlt hW0 (by norm_num : (2 : ℕ) ≠ 0)
        linarith only [hp2, hsq]
      · have hp2 := pow_lt_pow_left₀ hlt hW0' (by norm_num : (2 : ℕ) ≠ 0)
        linarith only [hp2, hsq]
    by_cases hWz : W = 0
    · rw [hzero hWz, hzero' (by rw [← hWW]; exact hWz)]
    · have hWne : W ≠ 0 := hWz
      have hcosφ : Real.cos φ = Real.cos φ' := by
        apply mul_left_cancel₀ hWne
        rw [hcos, hWW]
      have hφφ : φ = φ' :=
        Real.injOn_cos ⟨hφ0, hφπ.le⟩ ⟨hφ0', hφπ'.le⟩ hcosφ
      exact hfinish hWW hφφ hcc
  · -- pairing clause, (z, z') order
    obtain ⟨t, -, hteq⟩ := hpg
    have ht1 := congrArg Prod.fst hteq
    have ht2 := congrArg Prod.snd hteq
    simp only at ht1 ht2
    rw [hpd] at ht1
    rw [hpd'] at ht2
    rw [hz] at ht1
    rw [hz'] at ht2
    obtain ⟨hWzz, hWzz'⟩ := hpaircase c c' W W' φ φ' hW0 hWlt hW0' hWlt' hφ0 hφπ hφ0' hφπ'
      k (t : ℝ) t.2.1 t.2.2 ht1 ht2
    rw [hzero hWzz, hzero' hWzz']
  · -- pairing clause, (z', z) order
    obtain ⟨t, -, hteq⟩ := hpg
    have ht1 := congrArg Prod.fst hteq
    have ht2 := congrArg Prod.snd hteq
    simp only at ht1 ht2
    rw [hpd'] at ht1
    rw [hpd] at ht2
    rw [hz'] at ht1
    rw [hz] at ht2
    obtain ⟨hWzz', hWzz⟩ := hpaircase c' c W' W φ' φ hW0' hWlt' hW0 hWlt hφ0' hφπ' hφ0 hφπ
      k (t : ℝ) t.2.1 t.2.2 ht1 ht2
    rw [hzero hWzz, hzero' hWzz']
  · -- vertex clause
    obtain ⟨p, hp⟩ := hv
    obtain ⟨p', hp'⟩ := hv'
    rw [hpd, hz] at hp
    rw [hpd', hz'] at hp'
    have hWz : W = 0 := hvertcase c W φ hW0 hWlt hφ0 hφπ p hp
    have hWz' : W' = 0 := hvertcase c' W' φ' hW0' hWlt' hφ0' hφπ' p' hp'
    rw [hzero hWz, hzero' hWz']

end RiemannDynamics
