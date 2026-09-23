/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.GenusSurface.Atlas

/-!
# The genus-`g` surface: analytic transitions and the manifold instance

Every transition map of the genus-surface atlas is analytic with
nonvanishing derivative on its source: each overlap component carries a
single formula `id`, `u ↦ ω/u`, or `u ↦ A · exp (± i u^(2g))`. This yields
`isManifold_genusSurface` and the `IsManifold 𝓘(ℂ) ω (GenusSurface g)`
instance, so `GenusSurface g` is an analytic one-dimensional complex
manifold. The file ends with the base point, the vertex point, and the
quotient-map lemmas.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval
open scoped Manifold

namespace RiemannDynamics

/-! ## Analytic transitions and the manifold instance -/

set_option maxHeartbeats 400000 in
-- The single proof elaborates the full 3-family × 3-family transition case analysis
-- (interior/edge/vertex charts, with the two-sided ray analysis of the vertex chart);
-- the default 200000 heartbeats are exhausted during the final case dispatch.
/-- Every transition map of the genus-surface atlas is analytic with
nonvanishing derivative on its source: each overlap component carries a
single formula `id`, `u ↦ ω/u`, or `u ↦ A · exp (± i u^(2g))`. -/
theorem transition_analyticAt (g : ℕ) [NeZero g] :
    ∀ e ∈ atlas ℂ (GenusSurface g), ∀ e' ∈ atlas ℂ (GenusSurface g),
      ∀ z ∈ (e.symm.trans e').source,
        AnalyticAt ℂ (e.symm.trans e') z ∧ deriv (e.symm.trans e') z ≠ 0 := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have : NeZero (4 * g) := ⟨by omega⟩
  -- ## Norm facts
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hvertnorm : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    have hrw : polyVertex g m
        = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
      unfold polyVertex
      norm_num
    rw [hrw, hnorm1]
  have harcnorm : ∀ (k : ℤ) (t : ℝ), ‖arcPoint g k t‖ = 1 := by
    intro k t
    have hrw : arcPoint g k t
        = Complex.exp (Real.pi * (((k : ℝ) + t : ℝ) : ℂ) * Complex.I / (2 * g)) := by
      unfold arcPoint
      norm_num
    rw [hrw, hnorm1]
  have hωnorm : ∀ k : ℤ,
      ‖Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))‖ = 1 := by
    intro k
    have hrw : (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))
        = Real.pi * (((2 * (k : ℝ) + 3 : ℝ)) : ℂ) * Complex.I / (2 * g) := by
      push_cast
      ring
    rw [hrw, hnorm1]
  have hσnorm : ∀ (k : ℤ) (u : ℂ), ‖sidePairing g k u‖ = 1 / ‖u‖ := by
    intro k u
    unfold sidePairing
    rw [norm_div, hωnorm]
  -- ## Interior classes are singletons
  have hsingle : ∀ z w : ClosedDisc, ‖z.1‖ < 1 → genusRel g z w → z = w := by
    intro z w hz hrel
    have hrel' : z = w
        ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
            ((z.1, w.1) ∈ pairGraph g k ∨ (w.1, z.1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hrel
    rcases hrel' with h | ⟨k, -, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · exact h
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g k (s : ℝ) = z.1 := congrArg Prod.fst hs
      rw [← h1, harcnorm] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harcnorm] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvertnorm] at hz
      exact absurd hz (lt_irrefl 1)
  -- ## Interior representative extraction
  have hintRep : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ ≤ 1 →
      Quotient.mk (genusSetoid g) (projDisc y) = Quotient.mk (genusSetoid g) (projDisc x) →
      y = x := by
    intro x y hx hy h
    have hrel : genusRel g (projDisc x) (projDisc y) :=
      (genusRel_equivalence g).symm (Quotient.exact h)
    have heq := hsingle (projDisc x) (projDisc y)
      (by rw [projDisc_eq hx.le]; exact hx) hrel
    have hval := congrArg Subtype.val heq
    rw [projDisc_eq hx.le, projDisc_eq hy] at hval
    exact hval.symm
  -- ## Edge chart pieces
  have hEFin : ∀ (k : ℤ) (u : ℂ), ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc u) := by
    intro k u h
    unfold edgeChartFun
    exact ite_eq_left h
  have hEFout : ∀ (k : ℤ) (u : ℂ), ¬ ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u)) := by
    intro k u h
    unfold edgeChartFun
    exact ite_eq_right h
  -- Identify the preimage of an interior class under an edge-chart inverse.
  have hedgeW : ∀ (k : ℤ) (x w : ℂ), ‖x‖ < 1 →
      edgeChartFun g k w = Quotient.mk (genusSetoid g) (projDisc x) →
      (‖w‖ ≤ 1 ∧ w = x) ∨ (1 < ‖w‖ ∧ x ≠ 0 ∧ w = sidePairing g k x) := by
    intro k x w hx h
    by_cases hcase : ‖w‖ ≤ 1
    · rw [hEFin k w hcase] at h
      exact Or.inl ⟨hcase, hintRep x w hx hcase h⟩
    · rw [hEFout k w hcase] at h
      push Not at hcase
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hcase
        linarith
      have hσle : ‖sidePairing g k w‖ ≤ 1 := by
        rw [hσnorm]
        rw [div_le_one (lt_trans one_pos hcase)]
        linarith
      have hσw : sidePairing g k w = x := hintRep x _ hx hσle h
      have hx0 : x ≠ 0 := by
        intro h0
        have hn : ‖sidePairing g k w‖ = 0 := by rw [hσw, h0, norm_zero]
        rw [hσnorm k w] at hn
        have hwpos : (0 : ℝ) < ‖w‖ := lt_trans one_pos hcase
        rw [div_eq_zero_iff] at hn
        rcases hn with h1 | h1
        · exact one_ne_zero h1
        · linarith
      have hww : w = sidePairing g k x := by
        rw [← hσw, sidePairing_involutive g k hw0]
      exact Or.inr ⟨hcase, hx0, hww⟩
  -- ## Arc separation bricks
  have harc_eq : ∀ (a b : ℤ) (t s : ℝ), -1 < t - s → t - s < 1 →
      arcPoint g a t = arcPoint g b s →
      t = s ∧ (a : ZMod (4 * g)) = (b : ZMod (4 * g)) := by
    intro a b t s h1 h2 heq
    obtain ⟨n, hn⟩ := (arcPoint_eq_iff g a b t s).mp heq
    push_cast at hn
    have hts : t - s = ((4 * g * n - a + b : ℤ) : ℝ) := by
      push_cast
      linarith
    have hJ0 : (4 * (g : ℤ) * n - a + b) = 0 := by
      have hlb : (-1 : ℝ) < ((4 * g * n - a + b : ℤ) : ℝ) := by
        rw [← hts]
        exact h1
      have hub : ((4 * g * n - a + b : ℤ) : ℝ) < 1 := by
        rw [← hts]
        exact h2
      have hlb' : (-1 : ℤ) < 4 * (g : ℤ) * n - a + b := by exact_mod_cast hlb
      have hub' : 4 * (g : ℤ) * n - a + b < 1 := by exact_mod_cast hub
      omega
    have hts0 : t - s = 0 := by
      rw [hts, hJ0]
      norm_num
    refine ⟨by linarith, ?_⟩
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    push_cast
    linear_combination hJ0
  have hnotvert : ∀ (a : ℤ) (t : ℝ), 0 < t → t < 1 → ¬ IsPolyVertex g (arcPoint g a t) := by
    intro a t ht0 ht1 ⟨mv, hmv⟩
    rw [← arcPoint_zero g mv] at hmv
    obtain ⟨ht, -⟩ := harc_eq a mv t 0 (by linarith) (by linarith) hmv
    linarith
  -- The class of an open-arc point never meets the vertex class.
  have hvert_rel : ∀ (a : ℤ) (t : ℝ), 0 < t → t < 1 → ∀ mv : ℤ,
      ¬ genusRel g (projDisc (arcPoint g a t)) (projDisc (polyVertex g mv)) := by
    intro a t ht0 ht1 mv hrel
    have hva : (projDisc (arcPoint g a t)).1 = arcPoint g a t :=
      projDisc_eq (harcnorm a t).le
    have hvv : (projDisc (polyVertex g mv)).1 = polyVertex g mv :=
      projDisc_eq (hvertnorm mv).le
    have hrel' : projDisc (arcPoint g a t) = projDisc (polyVertex g mv)
        ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
            (((projDisc (arcPoint g a t)).1, (projDisc (polyVertex g mv)).1) ∈ pairGraph g k ∨
             ((projDisc (polyVertex g mv)).1, (projDisc (arcPoint g a t)).1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g (projDisc (arcPoint g a t)).1
            ∧ IsPolyVertex g (projDisc (polyVertex g mv)).1) := hrel
    rcases hrel' with h | ⟨k, -, h | h⟩ | ⟨h, -⟩
    · have := congrArg Subtype.val h
      rw [hva, hvv] at this
      exact hnotvert a t ht0 ht1 ⟨mv, this⟩
    · rw [hva, hvv] at h
      have hiff := pairGraph_vertex_iff g k h
      exact hnotvert a t ht0 ht1 (hiff.mpr ⟨mv, rfl⟩)
    · rw [hva, hvv] at h
      have hiff := pairGraph_vertex_iff g k h
      exact hnotvert a t ht0 ht1 (hiff.mp ⟨mv, rfl⟩)
    · rw [hva] at h
      exact hnotvert a t ht0 ht1 h
  -- Full relation analysis between two open-arc points.
  have harc_rel : ∀ (a b : ℤ) (t s : ℝ), 0 < t → t < 1 → 0 < s → s < 1 →
      genusRel g (projDisc (arcPoint g a t)) (projDisc (arcPoint g b s)) →
      ((b : ZMod (4 * g)) = (a : ZMod (4 * g)) ∧ s = t) ∨
      (∃ k₀ : ℤ, (k₀ % 4 = 0 ∨ k₀ % 4 = 1) ∧
        (((a : ZMod (4 * g)) = (k₀ : ZMod (4 * g)) ∧
            (b : ZMod (4 * g)) = ((k₀ + 2 : ℤ) : ZMod (4 * g)) ∧ s = 1 - t) ∨
         ((b : ZMod (4 * g)) = (k₀ : ZMod (4 * g)) ∧
            (a : ZMod (4 * g)) = ((k₀ + 2 : ℤ) : ZMod (4 * g)) ∧ s = 1 - t))) := by
    intro a b t s ht0 ht1 hs0 hs1 hrel
    have hva : (projDisc (arcPoint g a t)).1 = arcPoint g a t :=
      projDisc_eq (harcnorm a t).le
    have hvb : (projDisc (arcPoint g b s)).1 = arcPoint g b s :=
      projDisc_eq (harcnorm b s).le
    have hrel' : projDisc (arcPoint g a t) = projDisc (arcPoint g b s)
        ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
            (((projDisc (arcPoint g a t)).1, (projDisc (arcPoint g b s)).1) ∈ pairGraph g k ∨
             ((projDisc (arcPoint g b s)).1, (projDisc (arcPoint g a t)).1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g (projDisc (arcPoint g a t)).1
            ∧ IsPolyVertex g (projDisc (arcPoint g b s)).1) := hrel
    rcases hrel' with h | ⟨k, hk, h | h⟩ | ⟨h, -⟩
    · have hval := congrArg Subtype.val h
      rw [hva, hvb] at hval
      obtain ⟨hts, hab⟩ := harc_eq a b t s (by linarith) (by linarith) hval
      exact Or.inl ⟨hab.symm, hts.symm⟩
    · -- (arc a, arc b) matched by pairGraph k: a ≡ k, b ≡ k+2, s = 1 - t.
      obtain ⟨τ, -, hτ⟩ := h
      have h1 : arcPoint g k (τ : ℝ) = arcPoint g a t := by
        rw [← hva]
        exact congrArg Prod.fst hτ
      have h2 : arcPoint g (k + 2) (1 - (τ : ℝ)) = arcPoint g b s := by
        rw [← hvb]
        exact congrArg Prod.snd hτ
      obtain ⟨hτt, hka⟩ := harc_eq k a (τ : ℝ) t
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h1
      obtain ⟨hτs, hkb⟩ := harc_eq (k + 2) b (1 - (τ : ℝ)) s
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h2
      refine Or.inr ⟨k, hk, Or.inl ⟨hka.symm, hkb.symm, ?_⟩⟩
      rw [← hτs, hτt]
    · obtain ⟨τ, -, hτ⟩ := h
      have h1 : arcPoint g k (τ : ℝ) = arcPoint g b s := by
        rw [← hvb]
        exact congrArg Prod.fst hτ
      have h2 : arcPoint g (k + 2) (1 - (τ : ℝ)) = arcPoint g a t := by
        rw [← hva]
        exact congrArg Prod.snd hτ
      obtain ⟨hτs, hkb⟩ := harc_eq k b (τ : ℝ) s
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h1
      obtain ⟨hτt, hka⟩ := harc_eq (k + 2) a (1 - (τ : ℝ)) t
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h2
      refine Or.inr ⟨k, hk, Or.inr ⟨hkb.symm, hka.symm, ?_⟩⟩
      rw [← hτs]
      linarith [hτt]
    · rw [hva] at h
      exact absurd h (hnotvert a t ht0 ht1)
  -- ## ZMod-to-exponential bridges
  have hzmodDvd : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      ∃ q : ℤ, a - b = 4 * g * q := by
    intro a b hab
    rw [ZMod.intCast_eq_intCast_iff] at hab
    obtain ⟨q, hq⟩ := Int.ModEq.dvd hab
    refine ⟨-q, ?_⟩
    push_cast at hq ⊢
    linarith
  have hpvEq : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      polyVertex g a = polyVertex g b := by
    intro a b hab
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    unfold polyVertex
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨q, ?_⟩
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqC : (a : ℂ) - b = 4 * g * q := by exact_mod_cast hq
    field_simp
    linear_combination hqC
  have harcEqZ : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) → ∀ t : ℝ,
      arcPoint g a t = arcPoint g b t := by
    intro a b hab t
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    unfold arcPoint
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨q, ?_⟩
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqC : (a : ℂ) - b = 4 * g * q := by exact_mod_cast hq
    field_simp
    linear_combination hqC
  have hσEq : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      sidePairing g a = sidePairing g b := by
    intro a b hab
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    funext u
    unfold sidePairing
    congr 1
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨2 * q, ?_⟩
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqC : (a : ℂ) - b = 4 * g * q := by exact_mod_cast hq
    field_simp
    push_cast
    linear_combination 2 * hqC
  have hsectorEq : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      edgeSector g a = edgeSector g b := by
    intro a b hab
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    ext u
    constructor <;> intro hu
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
      refine ⟨ρ, θ' - 4 * g * q, hρ1, hρ2, ?_, ?_, ?_⟩
      · have : (b : ℝ) = a - 4 * g * q := by exact_mod_cast (by linarith [hq] : (b:ℤ) = a - 4*g*q)
        rw [this]
        linarith
      · have : (b : ℝ) = a - 4 * g * q := by exact_mod_cast (by linarith [hq] : (b:ℤ) = a - 4*g*q)
        rw [this]
        linarith
      · rw [hue]
        congr 1
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨q, ?_⟩
        have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp
        ring
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
      refine ⟨ρ, θ' + 4 * g * q, hρ1, hρ2, ?_, ?_, ?_⟩
      · have : (a : ℝ) = b + 4 * g * q := by exact_mod_cast (by linarith [hq] : (a:ℤ) = b + 4*g*q)
        rw [this]
        linarith
      · have : (a : ℝ) = b + 4 * g * q := by exact_mod_cast (by linarith [hq] : (a:ℤ) = b + 4*g*q)
        rw [this]
        linarith
      · rw [hue]
        congr 1
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨-q, ?_⟩
        have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp
        ring
  -- ## Sector-index machinery for the vertex chart
  set N : ℂ → ℝ :=
    fun u => if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u with hN
  have hidx : ∀ u : ℂ, vertexSectorIndex g u = (⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat := by
    intro u
    simp only [hN]
    rfl
  have hN0 : ∀ u : ℂ, 0 ≤ N u := by
    intro u
    simp only [hN]
    split_ifs with h
    · have := Complex.neg_pi_lt_arg u
      linarith
    · linarith [not_lt.mp h]
  have hNlt : ∀ u : ℂ, N u < 2 * Real.pi := by
    intro u
    simp only [hN]
    split_ifs with h
    · linarith
    · linarith [Complex.arg_le_pi u]
  have hNrep : ∀ u : ℂ, u = (‖u‖ : ℂ) * Complex.exp (((N u : ℝ) : ℂ) * Complex.I) := by
    intro u
    simp only [hN]
    split_ifs with h
    · have hcast : (((Complex.arg u + 2 * Real.pi : ℝ) : ℂ)) * Complex.I
          = ((Complex.arg u : ℝ) : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by
        push_cast
        ring
      rw [hcast, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one,
        Complex.norm_mul_exp_arg_mul_I]
    · rw [Complex.norm_mul_exp_arg_mul_I]
  have him : ∀ u : ℂ, (u ^ (2 * g)).im = ‖u‖ ^ (2 * g) * Real.sin (2 * g * N u) := by
    intro u
    conv_lhs => rw [hNrep u]
    rw [mul_pow, ← Complex.exp_nat_mul]
    have h1 : ((2 * g : ℕ) : ℂ) * (((N u : ℝ) : ℂ) * Complex.I)
        = ((2 * g * N u : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have h2 : ((‖u‖ : ℂ)) ^ (2 * g) = ((‖u‖ ^ (2 * g) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, h2, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hpix : ∀ u : ℂ, 2 * (g : ℝ) * N u = Real.pi * ((2 * (g : ℝ) / Real.pi) * N u) := by
    intro u
    field_simp
  have hsin_sign : ∀ u : ℂ,
      0 ≤ (-1 : ℝ) ^ (vertexSectorIndex g u) * Real.sin (2 * g * N u) := by
    intro u
    rw [hidx u, hpix u]
    have hx0 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N u := mul_nonneg (by positivity) (hN0 u)
    have hfl0 : 0 ≤ ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ := Int.floor_nonneg.mpr hx0
    have hfl : (⌊(2 * (g : ℝ) / Real.pi) * N u⌋ : ℝ) ≤ (2 * (g : ℝ) / Real.pi) * N u :=
      Int.floor_le _
    have hfl1 : (2 * (g : ℝ) / Real.pi) * N u < ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ + 1 :=
      Int.lt_floor_add_one _
    have hdecomp : Real.pi * ((2 * (g : ℝ) / Real.pi) * N u)
        = Real.pi * ((2 * (g : ℝ) / Real.pi) * N u - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋)
          + ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ * Real.pi := by
      ring
    rw [hdecomp, Real.sin_add_int_mul_pi]
    have hpow : ((-1 : ℝ) ^ ((⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat))
        * ((-1 : ℝ) ^ (⌊(2 * (g : ℝ) / Real.pi) * N u⌋) : ℝ) = 1 := by
      rw [← Int.toNat_of_nonneg hfl0, zpow_natCast, ← pow_add]
      exact Even.neg_one_pow ⟨(⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat, rfl⟩
    have hs0 : 0 ≤ Real.sin (Real.pi *
        ((2 * (g : ℝ) / Real.pi) * N u - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋)) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have hd : (0 : ℝ) ≤ (2 * (g : ℝ) / Real.pi) * N u
            - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ := by
          linarith
        positivity
      · nlinarith
    calc (0 : ℝ) ≤ (((-1 : ℝ) ^ ((⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat))
          * ((-1 : ℝ) ^ (⌊(2 * (g : ℝ) / Real.pi) * N u⌋) : ℝ))
          * Real.sin (Real.pi *
            ((2 * (g : ℝ) / Real.pi) * N u - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋)) := by
            rw [hpow, one_mul]
            exact hs0
      _ = _ := by ring
  have hidx_lt : ∀ u : ℂ, vertexSectorIndex g u < 4 * g := by
    intro u
    rw [hidx u]
    have h2 : (2 * (g : ℝ) / Real.pi) * N u < (2 * (g : ℝ) / Real.pi) * (2 * Real.pi) :=
      mul_lt_mul_of_pos_left (hNlt u) (by positivity)
    have h3 : (2 * (g : ℝ) / Real.pi) * (2 * Real.pi) = 4 * g := by
      field_simp
      ring
    rw [h3] at h2
    have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ < (4 * g : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast h2
    omega
  have hNoff : ∀ u : ℂ, ¬(u.im = 0 ∧ 0 ≤ u.re) → N u = Real.pi + Complex.arg (-u) := by
    intro u hu
    rcases lt_trichotomy u.im 0 with h | h | h
    · simp only [hN]
      rw [ite_eq_left (Complex.arg_neg_iff.mpr h), Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
      ring
    · have hre : u.re < 0 := by
        by_contra hcon
        exact hu ⟨h, not_lt.mp hcon⟩
      have h1 : Complex.arg u = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hre, h⟩
      have h2 : Complex.arg (-u) = 0 := by
        rw [Complex.arg_eq_zero_iff]
        constructor
        · rw [Complex.neg_re]
          linarith
        · rw [Complex.neg_im, h, neg_zero]
      simp only [hN]
      rw [ite_eq_right (by rw [h1]; linarith), h1, h2]
      ring
    · have hnneg : ¬ Complex.arg u < 0 := by
        rw [not_lt]
        exact Complex.arg_nonneg_iff.mpr h.le
      simp only [hN]
      rw [ite_eq_right hnneg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
      ring
  have hNcont : ∀ u : ℂ, ¬(u.im = 0 ∧ 0 ≤ u.re) → ContinuousAt N u := by
    intro u hu
    have hcl : IsClosed {v : ℂ | v.im = 0 ∧ 0 ≤ v.re} :=
      (isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_re)
    have hopen : IsOpen {v : ℂ | ¬(v.im = 0 ∧ 0 ≤ v.re)} := hcl.isOpen_compl
    have hslit : -u ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases him0 : u.im = 0
      · left
        rw [Complex.neg_re]
        have hre : u.re < 0 := by
          by_contra hcon
          exact hu ⟨him0, not_lt.mp hcon⟩
        linarith
      · right
        rw [Complex.neg_im]
        exact neg_ne_zero.mpr him0
    have hc : ContinuousAt (fun v : ℂ => Real.pi + Complex.arg (-v)) u :=
      continuousAt_const.add
        ((Complex.continuousAt_arg hslit).comp continuous_neg.continuousAt)
    apply hc.congr
    filter_upwards [hopen.eventually_mem hu] with v hv
    exact (hNoff v hv).symm
  -- Local constancy of the sector index off the rays.
  have hidx_const : ∀ z : ℂ, Real.sin (2 * g * N z) ≠ 0 →
      ∀ᶠ u in 𝓝 z, vertexSectorIndex g u = vertexSectorIndex g z := by
    intro z hsin
    have hnp : ¬(z.im = 0 ∧ 0 ≤ z.re) := by
      intro hcon
      have harg : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hcon.2, hcon.1⟩
      have hNz : N z = 0 := by
        simp only [hN]
        rw [ite_eq_right (by rw [harg]; exact lt_irrefl 0), harg]
      rw [hNz] at hsin
      simp at hsin
    have hcont : ContinuousAt (fun u : ℂ => (2 * (g : ℝ) / Real.pi) * N u) z :=
      continuousAt_const.mul (hNcont z hnp)
    have hxm : ((⌊(2 * (g : ℝ) / Real.pi) * N z⌋ : ℝ)) ≤ (2 * (g : ℝ) / Real.pi) * N z :=
      Int.floor_le _
    have hxm1 : (2 * (g : ℝ) / Real.pi) * N z < ⌊(2 * (g : ℝ) / Real.pi) * N z⌋ + 1 :=
      Int.lt_floor_add_one _
    have hxne : (2 * (g : ℝ) / Real.pi) * N z
        ≠ ((⌊(2 * (g : ℝ) / Real.pi) * N z⌋ : ℝ)) := by
      intro hcon
      apply hsin
      rw [hpix z, hcon, mul_comm]
      exact Real.sin_int_mul_pi _
    have hlt : ((⌊(2 * (g : ℝ) / Real.pi) * N z⌋ : ℝ)) < (2 * (g : ℝ) / Real.pi) * N z :=
      lt_of_le_of_ne hxm (Ne.symm hxne)
    have hev := hcont.eventually_mem (Ioo_mem_nhds hlt hxm1)
    filter_upwards [hev] with u hu
    rw [hidx u, hidx z]
    congr 1
    rw [Int.floor_eq_iff]
    exact ⟨hu.1.le, hu.2⟩
  -- The two-sided dichotomy at a ray point.
  have hray : ∀ z : ℂ, z ≠ 0 → Real.sin (2 * g * N z) = 0 →
      ((2 * (g : ℝ) / Real.pi) * N z = (vertexSectorIndex g z : ℝ)) ∧
      (∀ᶠ u in 𝓝 z, vertexSectorIndex g u = vertexSectorIndex g z ∨
        (vertexSectorIndex g u
            = (if vertexSectorIndex g z = 0 then 4 * g - 1 else vertexSectorIndex g z - 1) ∧
          Real.sin (2 * g * N u) ≠ 0)) := by
    intro z hz0 hsin
    have hx0 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N z := mul_nonneg (by positivity) (hN0 z)
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) * Real.pi = 2 * g * N z := by
      rw [← Real.sin_eq_zero_iff]
      exact hsin
    have hxn : (2 * (g : ℝ) / Real.pi) * N z = (n : ℝ) := by
      field_simp
      linarith [hn]
    have hn0 : 0 ≤ n := by
      have hc : (0 : ℝ) ≤ (n : ℝ) := by
        rw [← hxn]
        exact hx0
      exact_mod_cast hc
    have hidxz : vertexSectorIndex g z = n.toNat := by
      rw [hidx z, hxn, Int.floor_intCast]
    have hfst : (2 * (g : ℝ) / Real.pi) * N z = (vertexSectorIndex g z : ℝ) := by
      rw [hidxz, hxn]
      congr 1
      omega
    refine ⟨hfst, ?_⟩
    by_cases hm0 : vertexSectorIndex g z = 0
    · -- ray along the positive real axis
      have hNz : N z = 0 := by
        have hz' : (2 * (g : ℝ) / Real.pi) * N z = 0 := by
          rw [hfst, hm0]
          norm_num
        rcases mul_eq_zero.mp hz' with h | h
        · exact absurd h (by positivity)
        · exact h
      have harg : Complex.arg z = 0 := by
        simp only [hN] at hNz
        by_cases h : Complex.arg z < 0
        · rw [ite_eq_left h] at hNz
          have := Complex.neg_pi_lt_arg z
          linarith
        · rw [ite_eq_right h] at hNz
          exact hNz
      have hslit : z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        left
        obtain ⟨hre, him0⟩ := Complex.arg_eq_zero_iff.mp harg
        rcases lt_or_eq_of_le hre with h | h
        · exact h
        · exact absurd (Complex.ext h.symm him0) hz0
      have hargc : ContinuousAt Complex.arg z := Complex.continuousAt_arg hslit
      have hwin : ∀ᶠ u in 𝓝 z,
          Complex.arg u ∈ Set.Ioo (-(Real.pi / (4 * g))) (Real.pi / (4 * g)) := by
        apply hargc.eventually_mem
        rw [harg]
        have hq : (0 : ℝ) < Real.pi / (4 * g) := by positivity
        exact Ioo_mem_nhds (by linarith) hq
      filter_upwards [hwin] with u hu
      by_cases hcase : Complex.arg u < 0
      · right
        have hNu : N u = Complex.arg u + 2 * Real.pi := by
          simp only [hN]
          rw [ite_eq_left hcase]
        have hsplit : (2 * (g : ℝ) / Real.pi) * N u
            = (2 * (g : ℝ) / Real.pi) * Complex.arg u + 4 * g := by
          rw [hNu]
          field_simp
          ring
        have hb1 : (2 * (g : ℝ) / Real.pi) * (-(Real.pi / (4 * g)))
            < (2 * (g : ℝ) / Real.pi) * Complex.arg u :=
          mul_lt_mul_of_pos_left hu.1 (by positivity)
        have hc1 : (2 * (g : ℝ) / Real.pi) * (-(Real.pi / (4 * g))) = -(1 / 2) := by
          field_simp
          norm_num
        have hb2 : (2 * (g : ℝ) / Real.pi) * Complex.arg u < 0 :=
          mul_neg_of_pos_of_neg (by positivity) hcase
        rw [hc1] at hb1
        have hy1 : 4 * (g : ℝ) - 1 / 2 < (2 * (g : ℝ) / Real.pi) * N u := by
          rw [hsplit]
          linarith
        have hy2 : (2 * (g : ℝ) / Real.pi) * N u < 4 * g := by
          rw [hsplit]
          linarith
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = 4 * g - 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · push_cast
            linarith
          · push_cast
            linarith
        constructor
        · rw [hidx u, hfl, ite_eq_left hm0]
          omega
        · intro hcon
          obtain ⟨n', hn'⟩ : ∃ n' : ℤ, (n' : ℝ) * Real.pi = 2 * g * N u := by
            rw [← Real.sin_eq_zero_iff]
            exact hcon
          have hxn' : (2 * (g : ℝ) / Real.pi) * N u = (n' : ℝ) := by
            field_simp
            linarith [hn']
          rw [hxn'] at hy1 hy2
          have h1 : 4 * (g : ℤ) - 1 < n' := by
            have hr : (4 * (g : ℝ) - 1 : ℝ) < n' := by linarith
            exact_mod_cast hr
          have h2 : n' < 4 * (g : ℤ) := by exact_mod_cast hy2
          omega
      · left
        have hNu : N u = Complex.arg u := by
          simp only [hN]
          rw [ite_eq_right hcase]
        have hy1 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N u := mul_nonneg (by positivity) (hN0 u)
        have hb1 : (2 * (g : ℝ) / Real.pi) * Complex.arg u
            < (2 * (g : ℝ) / Real.pi) * (Real.pi / (4 * g)) :=
          mul_lt_mul_of_pos_left hu.2 (by positivity)
        have hc1 : (2 * (g : ℝ) / Real.pi) * (Real.pi / (4 * g)) = 1 / 2 := by
          field_simp
          norm_num
        rw [hc1] at hb1
        have hy2 : (2 * (g : ℝ) / Real.pi) * N u < 1 / 2 := by
          rw [hNu]
          linarith
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = 0 := by
          rw [Int.floor_eq_iff]
          constructor
          · push_cast
            linarith
          · push_cast
            linarith
        rw [hidx u, hfl, hm0]
        rfl
    · -- interior ray: the normalized angle is continuous at `z`
      have hm1 : 1 ≤ vertexSectorIndex g z := Nat.one_le_iff_ne_zero.mpr hm0
      have hNzpos : 0 < N z := by
        rcases lt_or_eq_of_le (hN0 z) with h | h
        · exact h
        · exfalso
          apply hm0
          rw [hidx z, ← h, mul_zero, Int.floor_zero]
          rfl
      have hnp : ¬(z.im = 0 ∧ 0 ≤ z.re) := by
        intro hcon
        have harg : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hcon.2, hcon.1⟩
        have hNz : N z = 0 := by
          simp only [hN]
          rw [ite_eq_right (by rw [harg]; exact lt_irrefl 0), harg]
        linarith
      have hcont : ContinuousAt (fun u : ℂ => (2 * (g : ℝ) / Real.pi) * N u) z :=
        continuousAt_const.mul (hNcont z hnp)
      have hwin : ∀ᶠ u in 𝓝 z, (2 * (g : ℝ) / Real.pi) * N u ∈
          Set.Ioo ((vertexSectorIndex g z : ℝ) - 1 / 2)
            ((vertexSectorIndex g z : ℝ) + 1 / 2) := by
        apply hcont.eventually_mem
        rw [hfst]
        exact Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [hwin] with u hu
      by_cases hcase : (vertexSectorIndex g z : ℝ) ≤ (2 * (g : ℝ) / Real.pi) * N u
      · left
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = (vertexSectorIndex g z : ℤ) := by
          rw [Int.floor_eq_iff]
          constructor
          · exact_mod_cast hcase
          · have := hu.2
            push_cast
            linarith
        rw [hidx u, hfl]
        omega
      · right
        push Not at hcase
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = (vertexSectorIndex g z : ℤ) - 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · have := hu.1
            push_cast
            linarith
          · push_cast
            linarith
        constructor
        · rw [hidx u, hfl, ite_eq_right hm0]
          omega
        · intro hcon
          obtain ⟨n', hn'⟩ : ∃ n' : ℤ, (n' : ℝ) * Real.pi = 2 * g * N u := by
            rw [← Real.sin_eq_zero_iff]
            exact hcon
          have hxn' : (2 * (g : ℝ) / Real.pi) * N u = (n' : ℝ) := by
            field_simp
            linarith [hn']
          rw [hxn'] at hu hcase
          have h1 : (vertexSectorIndex g z : ℤ) - 1 < n' := by
            have hr : ((vertexSectorIndex g z : ℝ)) - 1 < (n' : ℝ) := by
              have := hu.1
              linarith
            exact_mod_cast hr
          have h2 : n' < (vertexSectorIndex g z : ℤ) := by exact_mod_cast hcase
          omega
    -- ## Vertex-chart formula bricks
  have hAne : ∀ a : ℤ, polyVertex g a ≠ 0 := by
    intro a h
    have hn := hvertnorm a
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hPnorm : ∀ (a : ℤ) (mm : ℕ) (u : ℂ),
      ‖polyVertex g a * Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g))‖
        = Real.exp (-((-1 : ℝ) ^ mm * (u ^ (2 * g)).im)) := by
    intro a mm u
    rw [norm_mul, hvertnorm, one_mul, Complex.norm_exp]
    congr 1
    have h1 : Complex.I * (-1 : ℂ) ^ mm * u ^ (2 * g)
        = (((-1 : ℝ) ^ mm : ℝ) : ℂ) * (u ^ (2 * g) * Complex.I) := by
      push_cast
      ring
    rw [h1, Complex.re_ofReal_mul, Complex.mul_I_re]
    ring
  have hψv : ∀ (mm : ℕ) (u : ℂ), vertexSectorIndex g u = mm →
      vertexChartFun g u = Quotient.mk (genusSetoid g) (projDisc (polyVertex g
        ((vertexSlot g ((mm : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g)))) := by
    intro mm u h
    unfold vertexChartFun
    rw [h]
  have hparityR : ∀ m₀ : ℕ,
      ((-1 : ℝ) ^ (if m₀ = 0 then 4 * g - 1 else m₀ - 1)) = -((-1 : ℝ)) ^ m₀ := by
    intro m₀
    by_cases h : m₀ = 0
    · rw [ite_eq_left h, h, pow_zero]
      exact Odd.neg_one_pow ⟨2 * g - 1, by omega⟩
    · rw [ite_eq_right h]
      have h1 : m₀ = (m₀ - 1) + 1 := by omega
      conv_rhs => rw [h1]
      rw [pow_succ]
      ring
  have hparityC : ∀ m₀ : ℕ,
      ((-1 : ℂ) ^ (if m₀ = 0 then 4 * g - 1 else m₀ - 1)) = -((-1 : ℂ)) ^ m₀ := by
    intro m₀
    by_cases h : m₀ = 0
    · rw [ite_eq_left h, h, pow_zero]
      exact Odd.neg_one_pow ⟨2 * g - 1, by omega⟩
    · rw [ite_eq_right h]
      have h1 : m₀ = (m₀ - 1) + 1 := by omega
      conv_rhs => rw [h1]
      rw [pow_succ]
      ring
  have hzslot : ∀ m₀ : ℕ,
      (((if m₀ = 0 then 4 * g - 1 else m₀ - 1 : ℕ) : ZMod (4 * g)) + 1)
        = ((m₀ : ℕ) : ZMod (4 * g)) := by
    intro m₀
    by_cases h : m₀ = 0
    · rw [ite_eq_left h, h]
      have h1 : ((4 * g - 1 : ℕ) : ZMod (4 * g)) + 1 = ((4 * g - 1 + 1 : ℕ) : ZMod (4 * g)) := by
        push_cast
        ring
      have h2 : 4 * g - 1 + 1 = 4 * g := by omega
      rw [h1, h2, ZMod.natCast_self]
      exact Nat.cast_zero.symm
    · rw [ite_eq_right h]
      have h1 : ((m₀ - 1 : ℕ) : ZMod (4 * g)) + 1 = ((m₀ - 1 + 1 : ℕ) : ZMod (4 * g)) := by
        push_cast
        ring
      rw [h1]
      congr 1
      omega
  -- ## The reduction of a transition to a local analytic model
  have hred : ∀ (E E' : OpenPartialHomeomorph (GenusSurface g) ℂ) (z : ℂ) (F : ℂ → ℂ),
      AnalyticAt ℂ F z → deriv F z ≠ 0 →
      (∀ᶠ u in 𝓝 z, F u ∈ E'.target ∧ E'.symm (F u) = E.symm u) →
      AnalyticAt ℂ (E.symm.trans E') z ∧ deriv (E.symm.trans E') z ≠ 0 := by
    intro E E' z F hF hdF hev
    have hEq : (⇑(E.symm.trans E') : ℂ → ℂ) =ᶠ[𝓝 z] F := by
      filter_upwards [hev] with u hu
      rw [OpenPartialHomeomorph.trans_apply, ← hu.2, E'.right_inv hu.1]
    refine ⟨hF.congr hEq.symm, ?_⟩
    rw [hEq.deriv_eq]
    exact hdF
  -- ## Diagonal transitions are the identity
  have hdiag : ∀ E : OpenPartialHomeomorph (GenusSurface g) ℂ, ∀ z ∈ (E.symm.trans E).source,
      AnalyticAt ℂ (E.symm.trans E) z ∧ deriv (E.symm.trans E) z ≠ 0 := by
    intro E z hz
    have hzt : z ∈ E.target := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
      exact hz.1
    refine hred E E z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
    filter_upwards [E.open_target.eventually_mem hzt] with u hu
    exact ⟨hu, rfl⟩
  -- ## The inverse bootstrap: a transition inverse to an analytic one is analytic
  have hsymm : ∀ E E' : OpenPartialHomeomorph (GenusSurface g) ℂ,
      (∀ w ∈ (E.symm.trans E').source,
        AnalyticAt ℂ (E.symm.trans E') w ∧ deriv (E.symm.trans E') w ≠ 0) →
      ∀ z ∈ (E'.symm.trans E).source,
        AnalyticAt ℂ (E'.symm.trans E) z ∧ deriv (E'.symm.trans E) z ≠ 0 := by
    intro E E' hfwd z hz
    have hTsymm : E'.symm.trans E = (E.symm.trans E').symm := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    rw [hTsymm] at hz ⊢
    have hzt : z ∈ (E.symm.trans E').target := by
      rwa [OpenPartialHomeomorph.symm_source] at hz
    have hdiff : DifferentiableOn ℂ (⇑(E.symm.trans E').symm) (E.symm.trans E').target := by
      intro y hy
      have hwy : (E.symm.trans E').symm y ∈ (E.symm.trans E').source :=
        (E.symm.trans E').map_target hy
      obtain ⟨hAy, hdy⟩ := hfwd _ hwy
      have hev : ∀ᶠ y' in 𝓝 y, (E.symm.trans E') ((E.symm.trans E').symm y') = y' := by
        filter_upwards [(E.symm.trans E').open_target.eventually_mem hy] with y' hy'
        exact (E.symm.trans E').right_inv hy'
      exact (HasDerivAt.of_local_left_inverse
        ((E.symm.trans E').continuousAt_symm hy)
        hAy.differentiableAt.hasDerivAt hdy hev).differentiableAt.differentiableWithinAt
    have hAz : AnalyticAt ℂ (⇑(E.symm.trans E').symm) z :=
      hdiff.analyticAt ((E.symm.trans E').open_target.mem_nhds hzt)
    refine ⟨hAz, ?_⟩
    have hws : (E.symm.trans E').symm z ∈ (E.symm.trans E').source :=
      (E.symm.trans E').map_target hzt
    obtain ⟨hAw, hdw⟩ := hfwd _ hws
    have hTz : (E.symm.trans E') ((E.symm.trans E').symm z) = z :=
      (E.symm.trans E').right_inv hzt
    have hd2 : DifferentiableAt ℂ (⇑(E.symm.trans E').symm)
        ((E.symm.trans E') ((E.symm.trans E').symm z)) := by
      rw [hTz]
      exact hAz.differentiableAt
    have hder := deriv_comp ((E.symm.trans E').symm z) hd2 hAw.differentiableAt
    have hidEq : (⇑(E.symm.trans E').symm ∘ ⇑(E.symm.trans E') : ℂ → ℂ)
        =ᶠ[𝓝 ((E.symm.trans E').symm z)] id := by
      filter_upwards [(E.symm.trans E').open_source.eventually_mem hws] with u hu
      exact (E.symm.trans E').left_inv hu
    have hder1 : deriv (⇑(E.symm.trans E').symm ∘ ⇑(E.symm.trans E'))
        ((E.symm.trans E').symm z) = 1 := by
      rw [hidEq.deriv_eq, deriv_id]
    rw [hder1, hTz] at hder
    intro h0
    rw [h0, zero_mul] at hder
    exact one_ne_zero hder
  -- ## Source membership decomposition
  have hsrc_mem : ∀ (E E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      ∀ z ∈ (E.symm.trans E').source, z ∈ E.target ∧ E.symm z ∈ E'.source := by
    intro E E' z hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    exact ⟨hz.1, hz.2⟩
    -- ## Side-pairing analytic bricks
  have hσmulinv : ∀ k : ℤ, sidePairing g k
      = fun u : ℂ => Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) * u⁻¹ := by
    intro k
    funext u
    unfold sidePairing
    rw [div_eq_mul_inv]
  have hσana : ∀ (k : ℤ) (z : ℂ), z ≠ 0 → AnalyticAt ℂ (sidePairing g k) z := by
    intro k z hz
    rw [hσmulinv k]
    exact analyticAt_const.mul (analyticAt_id.inv hz)
  have hσderiv : ∀ (k : ℤ) (z : ℂ), z ≠ 0 →
      HasDerivAt (sidePairing g k)
        (Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) * (-(z ^ 2)⁻¹)) z := by
    intro k z hz
    rw [hσmulinv k]
    exact (hasDerivAt_inv hz).const_mul _
  have hσdne : ∀ (k : ℤ) (z : ℂ), z ≠ 0 →
      Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) * (-(z ^ 2)⁻¹) ≠ 0 := by
    intro k z hz
    apply mul_ne_zero (Complex.exp_ne_zero _)
    rw [neg_ne_zero]
    exact inv_ne_zero (pow_ne_zero 2 hz)
  have hopen_gt : IsOpen {u : ℂ | 1 < ‖u‖} := isOpen_lt continuous_const continuous_norm
  -- Boundary points of an edge sector are open-arc points.
  have hsector_arc : ∀ (k : ℤ) (u : ℂ), u ∈ edgeSector g k → ‖u‖ = 1 →
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ u = arcPoint g k t := by
    intro k u hu hu1
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    have hρpos : (0 : ℝ) < ρ := by linarith
    have hρval : ρ = 1 := by
      have hn : ‖u‖ = ρ := by
        rw [hue, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos, hnorm1,
          mul_one]
      rw [hn] at hu1
      exact hu1
    refine ⟨θ' - k, by linarith, by linarith, ?_⟩
    rw [hue, hρval, Complex.ofReal_one, one_mul]
    unfold arcPoint
    congr 1
    push_cast
    ring
  -- Open-arc points lie in their edge sector.
  have harc_mem : ∀ (k : ℤ) (t : ℝ), 0 < t → t < 1 → arcPoint g k t ∈ edgeSector g k := by
    intro k t ht0 ht1
    refine ⟨1, k + t, by norm_num, by norm_num, by linarith, by linarith, ?_⟩
    rw [Complex.ofReal_one, one_mul]
    unfold arcPoint
    congr 1
    push_cast
    ring
  -- ## Interior chart data
  have hIsymm : ∀ u : ℂ, (interiorChart g).symm u
      = Quotient.mk (genusSetoid g) (projDisc u) := interiorChart_symm_apply g
  -- ## Core: interior source to edge target
  have hIEcore : ∀ (k' : ℤ) (E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E'.source = edgeChartFun g k' '' edgeSector g k' →
      E'.target = edgeSector g k' →
      (∀ u, E'.symm u = edgeChartFun g k' u) →
      ∀ z ∈ ((interiorChart g).symm.trans E').source,
        AnalyticAt ℂ ((interiorChart g).symm.trans E') z ∧
          deriv ((interiorChart g).symm.trans E') z ≠ 0 := by
    intro k' E' hsrc' htgt' hsym' z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    have hzt1 : z ∈ Metric.ball (0 : ℂ) 1 := hzt
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzt1
    rw [hIsymm z, hsrc'] at hzs
    obtain ⟨w, hwV, hww⟩ := hzs
    rcases hedgeW k' z w hz1 hww with ⟨-, hwz⟩ | ⟨hw2, hz0, hwσ⟩
    · -- the identity branch
      rw [hwz] at hwV
      refine hred _ E' z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
      filter_upwards [(isOpen_edgeSector g k').eventually_mem hwV,
        Metric.isOpen_ball.eventually_mem hzt1] with u hu1 hu2
      have hu2' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu2
      simp only [id_eq]
      constructor
      · rw [htgt']
        exact hu1
      · rw [hsym', hIsymm, hEFin k' u hu2'.le]
    · -- the side-pairing branch
      have hFz : sidePairing g k' z = w := hwσ.symm
      refine hred _ E' z (sidePairing g k') (hσana k' z hz0)
        (by rw [(hσderiv k' z hz0).deriv]; exact hσdne k' z hz0) ?_
      have hσc : ContinuousAt (sidePairing g k') z := (hσana k' z hz0).continuousAt
      have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ edgeSector g k' := by
        apply hσc.eventually_mem
        rw [hFz]
        exact (isOpen_edgeSector g k').mem_nhds hwV
      have hev2 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ {v : ℂ | 1 < ‖v‖} := by
        apply hσc.eventually_mem
        rw [hFz]
        exact hopen_gt.mem_nhds hw2
      have hev3 : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
      filter_upwards [hev1, hev2, hev3] with u hu1 hu2 hu3
      refine ⟨by rw [htgt']; exact hu1, ?_⟩
      rw [hsym', hIsymm, hEFout k' _ (not_le.mpr hu2), sidePairing_involutive g k' hu3]
  -- ## Core: edge source to interior target
  have hEIcore : ∀ (k : ℤ) (E : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E.target = edgeSector g k →
      (∀ u, E.symm u = edgeChartFun g k u) →
      ∀ z ∈ (E.symm.trans (interiorChart g)).source,
        AnalyticAt ℂ (E.symm.trans (interiorChart g)) z ∧
          deriv (E.symm.trans (interiorChart g)) z ≠ 0 := by
    intro k E htgt hsymE z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    rw [htgt] at hzt
    have hzs1 : E.symm z ∈ (fun u => Quotient.mk (genusSetoid g) (projDisc u))
        '' Metric.ball (0 : ℂ) 1 := hzs
    obtain ⟨w, hwV, hww⟩ := hzs1
    have hww' : Quotient.mk (genusSetoid g) (projDisc w) = E.symm z := hww
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hwV
    rcases lt_trichotomy ‖z‖ 1 with hz1 | hz1 | hz1
    · -- interior branch: identity
      refine hred E _ z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
      filter_upwards [Metric.isOpen_ball.eventually_mem
        (mem_ball_zero_iff.mpr hz1)] with u hu
      have hu' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
      simp only [id_eq]
      refine ⟨hu, ?_⟩
      rw [hIsymm, hsymE, hEFin k u hu'.le]
    · -- boundary: impossible
      exfalso
      rw [hsymE, hEFin k z (le_of_eq hz1)] at hww'
      have hzw : z = w := hintRep w z hw1 (le_of_eq hz1) hww'.symm
      rw [hzw] at hz1
      linarith
    · -- exterior branch: the side pairing
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz1
        linarith
      refine hred E _ z (sidePairing g k) (hσana k z hz0)
        (by rw [(hσderiv k z hz0).deriv]; exact hσdne k z hz0) ?_
      filter_upwards [hopen_gt.eventually_mem hz1] with u hu
      have hu1 : (1 : ℝ) < ‖u‖ := hu
      have hσlt : ‖sidePairing g k u‖ < 1 := by
        rw [hσnorm, div_lt_one (lt_trans one_pos hu1)]
        linarith
      refine ⟨mem_ball_zero_iff.mpr hσlt, ?_⟩
      rw [hIsymm, hsymE, hEFout k u (not_le.mpr hu1)]
  -- ## Core: edge source to a distinct edge target
  have hEEcore : ∀ (k k' : ℤ) (E E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E.target = edgeSector g k →
      (∀ u, E.symm u = edgeChartFun g k u) →
      E'.source = edgeChartFun g k' '' edgeSector g k' →
      E'.target = edgeSector g k' →
      (∀ u, E'.symm u = edgeChartFun g k' u) →
      ¬(k : ZMod (4 * g)) = (k' : ZMod (4 * g)) →
      ¬(k : ZMod (4 * g)) = ((k' + 2 : ℤ) : ZMod (4 * g)) →
      ¬((k + 2 : ℤ) : ZMod (4 * g)) = (k' : ZMod (4 * g)) →
      ∀ z ∈ (E.symm.trans E').source,
        AnalyticAt ℂ (E.symm.trans E') z ∧ deriv (E.symm.trans E') z ≠ 0 := by
    intro k k' E E' htgt hsymE hsrc' htgt' hsym' hne hne2 hne2' z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    rw [htgt] at hzt
    rw [hsrc'] at hzs
    obtain ⟨w, hwV, hww⟩ := hzs
    rw [hsymE] at hww
    rcases lt_trichotomy ‖z‖ 1 with hz1 | hz1 | hz1
    · -- z interior
      rw [hEFin k z hz1.le] at hww
      rcases hedgeW k' z w hz1 hww with ⟨-, hwz⟩ | ⟨hw2, hz0, hwσ⟩
      · rw [hwz] at hwV
        refine hred E E' z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
        filter_upwards [(isOpen_edgeSector g k').eventually_mem hwV,
          Metric.isOpen_ball.eventually_mem (mem_ball_zero_iff.mpr hz1)] with u hu1 hu2
        have hu2' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu2
        simp only [id_eq]
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rw [hsym', hsymE, hEFin k' u hu2'.le, hEFin k u hu2'.le]
      · have hFz : sidePairing g k' z = w := hwσ.symm
        refine hred E E' z (sidePairing g k') (hσana k' z hz0)
          (by rw [(hσderiv k' z hz0).deriv]; exact hσdne k' z hz0) ?_
        have hσc : ContinuousAt (sidePairing g k') z := (hσana k' z hz0).continuousAt
        have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ edgeSector g k' := by
          apply hσc.eventually_mem
          rw [hFz]
          exact (isOpen_edgeSector g k').mem_nhds hwV
        have hev2 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ {v : ℂ | 1 < ‖v‖} := by
          apply hσc.eventually_mem
          rw [hFz]
          exact hopen_gt.mem_nhds hw2
        have hev3 : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
        have hev4 : ∀ᶠ u in 𝓝 z, u ∈ Metric.ball (0 : ℂ) 1 :=
          Metric.isOpen_ball.eventually_mem (mem_ball_zero_iff.mpr hz1)
        filter_upwards [hev1, hev2, hev3, hev4] with u hu1 hu2 hu3 hu4
        have hu4' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu4
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rw [hsym', hsymE, hEFout k' _ (not_le.mpr hu2), sidePairing_involutive g k' hu3,
          hEFin k u hu4'.le]
    · -- z on the open arc: impossible for distinct charts
      exfalso
      rw [hEFin k z (le_of_eq hz1)] at hww
      obtain ⟨t, ht0, ht1, hzarc⟩ := hsector_arc k z hzt hz1
      rcases lt_trichotomy ‖w‖ 1 with hw1 | hw1 | hw1
      · rw [hEFin k' w hw1.le] at hww
        have hzw : z = w := hintRep w z hw1 (le_of_eq hz1) hww.symm
        rw [hzw] at hz1
        linarith
      · rw [hEFin k' w (le_of_eq hw1)] at hww
        obtain ⟨t', ht'0, ht'1, hwarc⟩ := hsector_arc k' w hwV hw1
        have hrel : genusRel g (projDisc (arcPoint g k' t')) (projDisc (arcPoint g k t)) := by
          rw [← hwarc, ← hzarc]
          exact Quotient.exact hww
        rcases harc_rel k' k t' t ht'0 ht'1 ht0 ht1 hrel with
          ⟨hab, -⟩ | ⟨k₀, -, ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩⟩
        · exact hne hab
        · apply hne2
          rw [h2]
          push_cast
          rw [h1]
        · apply hne2'
          rw [h2]
          push_cast
          rw [h1]
      · rw [hEFout k' w (not_le.mpr hw1)] at hww
        have hσw1 : ‖sidePairing g k' w‖ < 1 := by
          rw [hσnorm, div_lt_one (lt_trans one_pos hw1)]
          linarith
        have hzw : z = sidePairing g k' w :=
          hintRep (sidePairing g k' w) z hσw1 (le_of_eq hz1) hww.symm
        rw [hzw] at hz1
        linarith
    · -- z exterior
      rw [hEFout k z (not_le.mpr hz1)] at hww
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz1
        linarith
      have hσz1 : ‖sidePairing g k z‖ < 1 := by
        rw [hσnorm, div_lt_one (lt_trans one_pos hz1)]
        linarith
      rcases hedgeW k' (sidePairing g k z) w hσz1 hww with ⟨-, hwz⟩ | ⟨hw2, -, hwσ⟩
      · -- w = σ_k z
        rw [hwz] at hwV
        refine hred E E' z (sidePairing g k) (hσana k z hz0)
          (by rw [(hσderiv k z hz0).deriv]; exact hσdne k z hz0) ?_
        have hσc : ContinuousAt (sidePairing g k) z := (hσana k z hz0).continuousAt
        have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k u ∈ edgeSector g k' := by
          apply hσc.eventually_mem
          exact (isOpen_edgeSector g k').mem_nhds hwV
        filter_upwards [hev1, hopen_gt.eventually_mem hz1] with u hu1 hu2
        have hu2' : (1 : ℝ) < ‖u‖ := hu2
        have hσu : ‖sidePairing g k u‖ < 1 := by
          rw [hσnorm, div_lt_one (lt_trans one_pos hu2')]
          linarith
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rw [hsym', hsymE, hEFin k' _ hσu.le, hEFout k u (not_le.mpr hu2')]
      · -- w = σ_{k'} (σ_k z): the transition is the linear map (ω'/ω) · u
        have hcomp : ∀ u : ℂ, u ≠ 0 → sidePairing g k' (sidePairing g k u)
            = (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u := by
          intro u hu
          unfold sidePairing
          have h1 : Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) ≠ 0 :=
            Complex.exp_ne_zero _
          have h2 : Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g)) ≠ 0 :=
            Complex.exp_ne_zero _
          field_simp
        have hcne : Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
            / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) ≠ 0 :=
          div_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
        have hFz : (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
            / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * z = w := by
          rw [← hcomp z hz0]
          exact hwσ.symm
        have hnormF : ∀ u : ℂ,
            ‖(Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
              / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u‖
              = ‖u‖ := by
          intro u
          rw [norm_mul, norm_div, hωnorm, hωnorm]
          norm_num
        refine hred E E' z (fun u : ℂ =>
          (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
            / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u)
          (analyticAt_const.mul analyticAt_id) ?_ ?_
        · have hd : HasDerivAt (fun u : ℂ =>
              (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u)
              ((Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * 1) z :=
            (hasDerivAt_id z).const_mul _
          rw [hd.deriv, mul_one]
          exact hcne
        · have hFc : ContinuousAt (fun u : ℂ =>
              (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u) z :=
            (continuous_const.mul continuous_id).continuousAt
          have hev1 : ∀ᶠ u in 𝓝 z,
              (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u
                ∈ edgeSector g k' := by
            apply hFc.eventually_mem
            rw [hFz]
            exact (isOpen_edgeSector g k').mem_nhds hwV
          have hev3 : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
          filter_upwards [hev1, hopen_gt.eventually_mem hz1, hev3] with u hu1 hu2 hu3
          have hu2' : (1 : ℝ) < ‖u‖ := hu2
          have hσku0 : sidePairing g k u ≠ 0 := by
            rw [hσmulinv k]
            exact mul_ne_zero (Complex.exp_ne_zero _) (inv_ne_zero hu3)
          have hgtF : ¬ ‖(Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
              / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u‖ ≤ 1 := by
            rw [hnormF]
            exact not_le.mpr hu2'
          refine ⟨by rw [htgt']; exact hu1, ?_⟩
          rw [hsym', hsymE, hEFout k' _ hgtF, hEFout k u (not_le.mpr hu2'), ← hcomp u hu3,
            sidePairing_involutive g k' hσku0]
    -- ## Vertex-chart bricks
  have hVsym : ∀ u : ℂ, (vertexChart g).symm u = vertexChartFun g u := fun _ => rfl
  have hccast : ∀ x : ZMod (4 * g), ((x.val : ℤ) : ZMod (4 * g)) = x := by
    intro x
    rw [Int.cast_natCast]
    exact ZMod.natCast_rightInverse x
  have hncastN : ∀ x : ZMod (4 * g), ((x.val : ℕ) : ZMod (4 * g)) = x := fun x =>
    ZMod.natCast_rightInverse x
  have hzmod4 : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) → a % 4 = b % 4 := by
    intro a b h
    obtain ⟨q, hq⟩ := hzmodDvd a b h
    have hdvd : (4 : ℤ) ∣ b - a := ⟨-(g * q), by linarith⟩
    exact Int.modEq_iff_dvd.mpr hdvd
  have hpvMul : ∀ a b : ℤ, polyVertex g a * polyVertex g b = polyVertex g (a + b) := by
    intro a b
    unfold polyVertex
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hωpv : ∀ kk : ℤ,
      Complex.exp (Real.pi * (2 * (kk : ℂ) + 3) * Complex.I / (2 * g))
        = polyVertex g (2 * kk + 3) := by
    intro kk
    unfold polyVertex
    congr 1
    push_cast
    ring
  have hsign_at : ∀ (mm : ℕ) (u : ℂ), vertexSectorIndex g u = mm →
      0 ≤ (-1 : ℝ) ^ mm * (u ^ (2 * g)).im := by
    intro mm u hu
    rw [him u]
    have hs := hsin_sign u
    rw [hu] at hs
    calc (0 : ℝ) ≤ ‖u‖ ^ (2 * g) * ((-1 : ℝ) ^ mm * Real.sin (2 * g * N u)) :=
          mul_nonneg (pow_nonneg (norm_nonneg u) _) hs
      _ = (-1 : ℝ) ^ mm * (‖u‖ ^ (2 * g) * Real.sin (2 * g * N u)) := by ring
  have hsign_lt : ∀ (mm : ℕ) (u : ℂ), vertexSectorIndex g u = mm → u ≠ 0 →
      Real.sin (2 * g * N u) ≠ 0 → 0 < (-1 : ℝ) ^ mm * (u ^ (2 * g)).im := by
    intro mm u hu hu0 hsin
    rcases lt_or_eq_of_le (hsign_at mm u hu) with h | h
    · exact h
    · exfalso
      have hIm : (u ^ (2 * g)).im = 0 := by
        have hpm : ((-1 : ℝ) ^ mm) ≠ 0 := pow_ne_zero _ (by norm_num)
        rcases mul_eq_zero.mp h.symm with h1 | h1
        · exact absurd h1 hpm
        · exact h1
      rw [him u] at hIm
      rcases mul_eq_zero.mp hIm with h1 | h1
      · exact absurd h1 (pow_ne_zero _ (norm_ne_zero_iff.mpr hu0))
      · exact hsin h1
  have hPana : ∀ (a : ℤ) (mm : ℕ) (z : ℂ),
      AnalyticAt ℂ (fun u : ℂ => polyVertex g a
        * Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g))) z := by
    intro a mm z
    exact analyticAt_const.mul
      (analyticAt_cexp.comp (analyticAt_const.mul (analyticAt_id.pow _)))
  have hPderivne : ∀ (a : ℤ) (mm : ℕ) (z : ℂ), z ≠ 0 →
      deriv (fun u : ℂ => polyVertex g a
        * Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g))) z ≠ 0 := by
    intro a mm z hz0
    have hd := (((hasDerivAt_pow (2 * g) z).const_mul
      (Complex.I * (-1) ^ mm)).cexp).const_mul (polyVertex g a)
    rw [hd.deriv]
    apply mul_ne_zero (hAne a)
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero
    · exact mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (by norm_num))
    · apply mul_ne_zero
      · have h2g : ((2 * g : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        exact_mod_cast h2g
      · exact pow_ne_zero _ hz0
  have hraypow : ∀ (u : ℂ) (mm : ℕ), vertexSectorIndex g u = mm →
      Real.sin (2 * g * N u) = 0 →
      u ^ (2 * g) = ((-1 : ℂ)) ^ mm * ((‖u‖ ^ (2 * g) : ℝ) : ℂ) := by
    intro u mm hidxu hsinu
    have hx0 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N u := mul_nonneg (by positivity) (hN0 u)
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) * Real.pi = 2 * g * N u := by
      rw [← Real.sin_eq_zero_iff]
      exact hsinu
    have hxn : (2 * (g : ℝ) / Real.pi) * N u = (n : ℝ) := by
      field_simp
      linarith [hn]
    have hn0 : 0 ≤ n := by
      have hc : (0 : ℝ) ≤ (n : ℝ) := by
        rw [← hxn]
        exact hx0
      exact_mod_cast hc
    have hmm : (mm : ℤ) = n := by
      rw [← hidxu, hidx u, hxn, Int.floor_intCast]
      omega
    have hreal : 2 * (g : ℝ) * N u = (mm : ℝ) * Real.pi := by
      rw [← hn]
      congr 1
      exact_mod_cast hmm.symm
    conv_lhs => rw [hNrep u]
    rw [mul_pow, ← Complex.exp_nat_mul]
    have hexp : ((2 * g : ℕ) : ℂ) * (((N u : ℝ) : ℂ) * Complex.I)
        = ((mm : ℕ) : ℂ) * (Real.pi * Complex.I) := by
      have hC := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hreal
      push_cast at hC ⊢
      linear_combination Complex.I * hC
    rw [hexp, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    push_cast
    ring
  -- ## Core: vertex source to interior target
  have hVI : ∀ z ∈ ((vertexChart g).symm.trans (interiorChart g)).source,
      AnalyticAt ℂ ((vertexChart g).symm.trans (interiorChart g)) z ∧
        deriv ((vertexChart g).symm.trans (interiorChart g)) z ≠ 0 := by
    intro z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    have hzs1 : (vertexChart g).symm z ∈ (fun u => Quotient.mk (genusSetoid g) (projDisc u))
        '' Metric.ball (0 : ℂ) 1 := hzs
    obtain ⟨w, hwV, hww⟩ := hzs1
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hwV
    have hww' : Quotient.mk (genusSetoid g) (projDisc w) = vertexChartFun g z := hww
    rw [hψv (vertexSectorIndex g z) z rfl] at hww'
    have hPle1 : ‖polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))‖ ≤ 1 := by
      rw [hPnorm, Real.exp_le_one_iff]
      linarith [hsign_at (vertexSectorIndex g z) z rfl]
    have hwP : polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g)) = w :=
      hintRep w _ hw1 hPle1 hww'.symm
    have hPlt : ‖polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))‖ < 1 := by
      rw [hwP]
      exact hw1
    have hsin_ne : Real.sin (2 * g * N z) ≠ 0 := by
      intro hcon
      have hIm : (z ^ (2 * g)).im = 0 := by
        rw [him z, hcon, mul_zero]
      rw [hPnorm, hIm, mul_zero, neg_zero, Real.exp_zero] at hPlt
      exact lt_irrefl 1 hPlt
    have hz0 : z ≠ 0 := by
      intro hcon
      apply hsin_ne
      have hN0z : N z = 0 := by
        simp only [hN, hcon, Complex.arg_zero]
        norm_num
      rw [hN0z, mul_zero, Real.sin_zero]
    refine hred _ _ z (fun u : ℂ => polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
      (hPana _ _ z) (hPderivne _ _ z hz0) ?_
    have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
        ∈ Metric.ball (0 : ℂ) 1 := by
      apply (hPana _ _ z).continuousAt.eventually_mem
      exact Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hPlt)
    filter_upwards [hev1, hidx_const z hsin_ne] with u hu1 hu2
    refine ⟨hu1, ?_⟩
    rw [hIsymm, hVsym, hψv (vertexSectorIndex g z) u hu2]
  have hPdval : ∀ (a : ℤ) (mm : ℕ) (z : ℂ), z ≠ 0 →
      polyVertex g a * (Complex.exp (Complex.I * (-1) ^ mm * z ^ (2 * g))
        * (Complex.I * (-1) ^ mm * (((2 * g : ℕ) : ℂ) * z ^ (2 * g - 1)))) ≠ 0 := by
    intro a mm z hz0
    apply mul_ne_zero (hAne a)
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero
    · exact mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (by norm_num))
    · apply mul_ne_zero
      · have h2g : ((2 * g : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        exact h2g
      · exact pow_ne_zero _ hz0
  -- ## Core: vertex source to edge target
  have hVEcore : ∀ (k' : ℤ) (E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E'.source = edgeChartFun g k' '' edgeSector g k' →
      E'.target = edgeSector g k' →
      (∀ u, E'.symm u = edgeChartFun g k' u) →
      (k' % 4 = 0 ∨ k' % 4 = 1) →
      ∀ z ∈ ((vertexChart g).symm.trans E').source,
        AnalyticAt ℂ ((vertexChart g).symm.trans E') z ∧
          deriv ((vertexChart g).symm.trans E') z ≠ 0 := by
    intro k' E' hsrc' htgt' hsym' hk'4 z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    have hztb : z ∈ Metric.ball (0 : ℂ) (vertexRadius g) := hzt
    rw [hsrc'] at hzs
    obtain ⟨w, hwV, hww⟩ := hzs
    have hww' : edgeChartFun g k' w = vertexChartFun g z := hww
    rw [hψv (vertexSectorIndex g z) z rfl] at hww'
    -- `z = 0` is impossible: the vertex class does not meet an edge-chart source.
    have hz0 : z ≠ 0 := by
      intro hcon
      rw [hcon] at hww'
      rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one] at hww'
      rcases lt_trichotomy ‖w‖ 1 with hw1 | hw1 | hw1
      · rw [hEFin k' w hw1.le] at hww'
        have h1 := hintRep w _ hw1 (hvertnorm _).le hww'.symm
        rw [← h1, hvertnorm] at hw1
        exact lt_irrefl 1 hw1
      · obtain ⟨t', ht'0, ht'1, hwarc⟩ := hsector_arc k' w hwV hw1
        rw [hEFin k' w (le_of_eq hw1), hwarc] at hww'
        exact hvert_rel k' t' ht'0 ht'1 _ (Quotient.exact hww')
      · rw [hEFout k' w (not_le.mpr hw1)] at hww'
        have hσw1 : ‖sidePairing g k' w‖ < 1 := by
          rw [hσnorm, div_lt_one (lt_trans one_pos hw1)]
          linarith
        have h1 := hintRep (sidePairing g k' w) _ hσw1 (hvertnorm _).le hww'.symm
        rw [← h1, hvertnorm] at hσw1
        exact lt_irrefl 1 hσw1
    by_cases hsin : Real.sin (2 * g * N z) = 0
    · -- ray case
      set mv := vertexSectorIndex g z with hmv
      set cv := ((vertexSlot g ((mv : ℕ) : ZMod (4 * g))).val : ℤ) with hcvdef
      set jv := (if mv = 0 then 4 * g - 1 else mv - 1 : ℕ) with hjv
      set cj := ((vertexSlot g ((jv : ℕ) : ZMod (4 * g))).val : ℤ) with hcjdef
      have hdich := (hray z hz0 hsin).2
      have hzpow : z ^ (2 * g) = ((-1 : ℂ)) ^ mv * ((‖z‖ ^ (2 * g) : ℝ) : ℂ) :=
        hraypow z mv hmv.symm hsin
      have hsq : ((-1 : ℂ)) ^ mv * ((-1 : ℂ)) ^ mv = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨mv, rfl⟩
      have hIm0 : (z ^ (2 * g)).im = 0 := by
        rw [him z, hsin, mul_zero]
      have hPz1 : ‖polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * z ^ (2 * g))‖
          = 1 := by
        rw [hPnorm, hIm0, mul_zero, neg_zero, Real.exp_zero]
      have hnz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
      have hrlt : ‖z‖ ^ (2 * g) < Real.pi / (2 * g) := by
        have h1 : ‖z‖ < vertexRadius g := mem_ball_zero_iff.mp hztb
        have h2 : ‖z‖ ^ (2 * g) < vertexRadius g ^ (2 * g) :=
          pow_lt_pow_left₀ h1 (norm_nonneg z) (by omega)
        exact lt_trans h2 (vertexRadius_pow_lt g)
      have hs₀pos : 0 < (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g) := by positivity
      have hs₀lt : (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g) < 1 := by
        have h1 : (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)
            < (2 * (g : ℝ) / Real.pi) * (Real.pi / (2 * g)) :=
          mul_lt_mul_of_pos_left hrlt (by positivity)
        have h2 : (2 * (g : ℝ) / Real.pi) * (Real.pi / (2 * g)) = 1 := by
          field_simp
        linarith
      have hPzarc : polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * z ^ (2 * g))
          = arcPoint g cv ((2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)) := by
        rw [hzpow]
        unfold polyVertex arcPoint
        rw [← Complex.exp_add]
        congr 1
        have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp
        ring_nf
        linear_combination (2 * (g : ℂ) * ((‖z‖ : ℂ)) ^ (2 * g)) * hsq
      -- identify the target arc of the chart from `w`
      have hwid : ((cv : ZMod (4 * g)) = (k' : ZMod (4 * g)))
          ∨ ((cv : ZMod (4 * g)) = ((k' + 2 : ℤ) : ZMod (4 * g))) := by
        rcases lt_trichotomy ‖w‖ 1 with hw1 | hw1 | hw1
        · exfalso
          rw [hEFin k' w hw1.le] at hww'
          have h1 := hintRep w _ hw1 (le_of_eq hPz1) hww'.symm
          rw [h1] at hPz1
          rw [hPz1] at hw1
          exact lt_irrefl 1 hw1
        · rw [hEFin k' w (le_of_eq hw1)] at hww'
          obtain ⟨t', ht'0, ht'1, hwarc⟩ := hsector_arc k' w hwV hw1
          rw [hwarc, hPzarc] at hww'
          have hrel := Quotient.exact hww'
          rcases harc_rel k' cv t' ((2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)) ht'0 ht'1
            hs₀pos hs₀lt hrel with
            ⟨hab, -⟩ | ⟨k₀, hk₀4, ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩⟩
          · exact Or.inl hab
          · refine Or.inr ?_
            rw [h2]
            push_cast
            rw [h1]
          · exfalso
            have h4 := hzmod4 k' (k₀ + 2) h2
            omega
        · exfalso
          rw [hEFout k' w (not_le.mpr hw1)] at hww'
          have hσw1 : ‖sidePairing g k' w‖ < 1 := by
            rw [hσnorm, div_lt_one (lt_trans one_pos hw1)]
            linarith
          have h1 := hintRep (sidePairing g k' w) _ hσw1 (le_of_eq hPz1) hww'.symm
          rw [h1] at hPz1
          rw [hPz1] at hσw1
          exact lt_irrefl 1 hσw1
      -- the slot recurrence at the ray
      have hsuccrel := vertexSlot_succ g ((jv : ℕ) : ZMod (4 * g))
      rw [hjv] at hsuccrel
      rw [hzslot mv] at hsuccrel
      rw [← hjv] at hsuccrel
      -- hsuccrel : vertexSlot g (mv-cast) = pairInv g (vertexSlot g (jv-cast) - 1)
      have hncast : (((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) : ZMod (4 * g))
          = ((cj - 1 : ℤ) : ZMod (4 * g)) := by
        rw [hccast]
        push_cast
        rw [hccast]
      -- the two sides of the key identity
      have hkey2 : ((2 * k' + 3 : ℤ) : ZMod (4 * g)) = ((cj + cv : ℤ) : ZMod (4 * g)) ∧
          (((cv : ZMod (4 * g)) = (k' : ZMod (4 * g))) ∨
            (((cj - 1 : ℤ) : ZMod (4 * g)) = (k' : ZMod (4 * g)))) := by
        have hcvelt : ((cv : ℤ) : ZMod (4 * g)) = vertexSlot g ((mv : ℕ) : ZMod (4 * g)) :=
          hccast _
        have hcjelt : ((cj : ℤ) : ZMod (4 * g)) = vertexSlot g ((jv : ℕ) : ZMod (4 * g)) :=
          hccast _
        by_cases hcond : ((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 0 ∨
            (vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 1)
        · -- source-arc branch: `c mv = n + 2 = c jv + 1`
          unfold pairInv at hsuccrel
          rw [ite_eq_left hcond] at hsuccrel
          have hcv1 : ((cv : ℤ) : ZMod (4 * g)) = ((cj + 1 : ℤ) : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hcjelt, hsuccrel]
            ring
          have hcvn : ((cv : ℤ) : ZMod (4 * g))
              = ((((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) + 2 : ℤ)
                : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hsuccrel, hncastN]
          rcases hwid with hB | hA
          · -- `cv ≡ k'` is impossible on the source branch (mod 4)
            exfalso
            have e1 := hzmod4 cv k' hB
            have e2 := hzmod4 cv
              (((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) + 2) hcvn
            have e3 : (0 : ℤ) ≤ ((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) := by
              positivity
            omega
          · -- main source case: `k' ≡ c jv - 1`
            have hk'n : ((k' : ℤ) : ZMod (4 * g)) = ((cj - 1 : ℤ) : ZMod (4 * g)) := by
              have h5 : ((k' + 2 : ℤ) : ZMod (4 * g)) = ((cj + 1 : ℤ) : ZMod (4 * g)) := by
                rw [← hA]
                exact hcv1
              push_cast at h5 ⊢
              linear_combination h5
            refine ⟨?_, Or.inr hk'n.symm⟩
            have h6 := hk'n
            have h7 := hcv1
            push_cast at h6 h7 ⊢
            linear_combination 2 * h6 - h7
        · -- target-arc branch: `c mv = n - 2 = c jv - 3`
          unfold pairInv at hsuccrel
          rw [ite_eq_right hcond] at hsuccrel
          have hcv3 : ((cv : ℤ) : ZMod (4 * g)) = ((cj - 3 : ℤ) : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hcjelt, hsuccrel]
            ring
          have hcvn : ((cv : ℤ) : ZMod (4 * g))
              = ((((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) - 2 : ℤ)
                : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hsuccrel, hncastN]
          have hcond' : (vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 2 ∨
              (vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 3 := by
            omega
          rcases hwid with hB | hA
          · -- main target case: `k' ≡ cv`
            refine ⟨?_, Or.inl hB⟩
            have h6 := hB
            have h7 := hcv3
            push_cast at h6 h7 ⊢
            linear_combination (-2 : ZMod (4 * g)) * h6 + h7
          · -- `cv ≡ k' + 2` is impossible on the target branch (mod 4)
            exfalso
            have e1 := hzmod4 cv (k' + 2) hA
            have e2 := hzmod4 cv
              (((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) - 2) hcvn
            have e3 : (0 : ℤ) ≤ ((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) := by
              positivity
            omega
      have hkey : Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
          = polyVertex g cj * polyVertex g cv := by
        rw [hωpv k', hpvMul, hpvEq (2 * k' + 3) (cj + cv) hkey2.1]
      rw [← hmv] at hdich
      rw [← hjv] at hdich
      have hjv1 : ((jv : ℕ) : ZMod (4 * g)) + 1 = ((mv : ℕ) : ZMod (4 * g)) := by
        rw [hjv]
        exact hzslot mv
      have hparR : ((-1 : ℝ) ^ jv) = -((-1 : ℝ)) ^ mv := by
        rw [hjv]
        exact hparityR mv
      have hparC : ((-1 : ℂ) ^ jv) = -((-1 : ℂ)) ^ mv := by
        rw [hjv]
        exact hparityC mv
      have hψvz : ∀ u : ℂ, vertexSectorIndex g u = mv → vertexChartFun g u
          = Quotient.mk (genusSetoid g) (projDisc (polyVertex g cv
            * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)))) := by
        intro u hu
        rw [hψv mv u hu, hcvdef]
      have hψvj : ∀ u : ℂ, vertexSectorIndex g u = jv → vertexChartFun g u
          = Quotient.mk (genusSetoid g) (projDisc (polyVertex g cj
            * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)))) := by
        intro u hu
        rw [hψv jv u hu, hcjdef]
      have hσP : ∀ u : ℂ, sidePairing g k'
          (polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)))
          = polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)) := by
        intro u
        unfold sidePairing
        rw [div_eq_iff (mul_ne_zero (hAne cv) (Complex.exp_ne_zero _)), hkey]
        have hst : Complex.I * (-1 : ℂ) ^ jv * u ^ (2 * g)
            + Complex.I * (-1 : ℂ) ^ mv * u ^ (2 * g) = 0 := by
          rw [hparC]
          ring
        rw [mul_mul_mul_comm, ← Complex.exp_add, hst, Complex.exp_zero, mul_one]
      have hσP' : ∀ u : ℂ, sidePairing g k'
          (polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)))
          = polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)) := by
        intro u
        unfold sidePairing
        rw [div_eq_iff (mul_ne_zero (hAne cj) (Complex.exp_ne_zero _)), hkey]
        have hst : Complex.I * (-1 : ℂ) ^ mv * u ^ (2 * g)
            + Complex.I * (-1 : ℂ) ^ jv * u ^ (2 * g) = 0 := by
          rw [hparC]
          ring
        rw [mul_mul_mul_comm, ← Complex.exp_add, hst, Complex.exp_zero, mul_one]
        exact mul_comm _ _
      have hballz : ∀ᶠ u in 𝓝 z, u ∈ Metric.ball (0 : ℂ) (vertexRadius g) :=
        Metric.isOpen_ball.eventually_mem hztb
      have hne0ev : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
      rcases hkey2.2 with hB | hA
      · -- the chart carries the sector arc: use the `mv`-side formula
        have hsecEq : edgeSector g cv = edgeSector g k' := hsectorEq cv k' hB
        have hFmem : polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * z ^ (2 * g))
            ∈ edgeSector g k' := by
          rw [hPzarc, ← hsecEq]
          exact harc_mem cv _ hs₀pos hs₀lt
        refine hred _ E' z (fun u : ℂ => polyVertex g cv
            * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)))
          (hPana _ _ z) (hPderivne _ _ z hz0) ?_
        have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g cv
            * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)) ∈ edgeSector g k' :=
          (hPana cv mv z).continuousAt.eventually_mem
            ((isOpen_edgeSector g k').mem_nhds hFmem)
        filter_upwards [hev1, hne0ev, hdich] with u hu1 hu2 hu3
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rcases hu3 with hidxu | ⟨hidxu, hsinu⟩
        · have hle : ‖polyVertex g cv
              * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g))‖ ≤ 1 := by
            rw [hPnorm, Real.exp_le_one_iff]
            linarith [hsign_at mv u hidxu]
          rw [hsym', hEFin k' _ hle, hVsym, hψvz u hidxu]
        · have hgt : ¬ ‖polyVertex g cv
              * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g))‖ ≤ 1 := by
            rw [hPnorm, not_le, Real.one_lt_exp_iff]
            have h1 := hsign_lt jv u hidxu hu2 hsinu
            rw [hparR] at h1
            linarith
          rw [hsym', hEFout k' _ hgt, hσP u, hVsym, hψvj u hidxu]
      · -- the chart carries the paired arc: use the `jv`-side formula
        have hsecEq : edgeSector g (cj - 1) = edgeSector g k' := hsectorEq (cj - 1) k' hA
        have hPsarc : polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * z ^ (2 * g))
            = arcPoint g (cj - 1) (1 - (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)) := by
          rw [hzpow, hparC]
          unfold polyVertex arcPoint
          rw [← Complex.exp_add]
          congr 1
          have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast
          field_simp
          ring_nf
          linear_combination (-(2 * (g : ℂ) * ((‖z‖ : ℂ)) ^ (2 * g))) * hsq
        have hFmem : polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * z ^ (2 * g))
            ∈ edgeSector g k' := by
          rw [hPsarc, ← hsecEq]
          exact harc_mem (cj - 1) _ (by linarith) (by linarith)
        refine hred _ E' z (fun u : ℂ => polyVertex g cj
            * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)))
          (hPana _ _ z) (hPderivne _ _ z hz0) ?_
        have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g cj
            * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)) ∈ edgeSector g k' :=
          (hPana cj jv z).continuousAt.eventually_mem
            ((isOpen_edgeSector g k').mem_nhds hFmem)
        filter_upwards [hev1, hne0ev, hdich, hballz] with u hu1 hu2 hu3 hu4
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rcases hu3 with hidxu | ⟨hidxu, hsinu⟩
        · -- the `mv` side, including the shared ray
          by_cases hsinu : Real.sin (2 * g * N u) = 0
          · -- on the ray: the two sector formulas are glued
            have hupow := hraypow u mv hidxu hsinu
            have hIm0u : (u ^ (2 * g)).im = 0 := by
              rw [him u, hsinu, mul_zero]
            have hle : ‖polyVertex g cj
                * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))‖ ≤ 1 := by
              rw [hPnorm, hIm0u, mul_zero, neg_zero, Real.exp_zero]
            have hsu : ‖u‖ ^ (2 * g) < Real.pi / (2 * g) :=
              lt_trans (pow_lt_pow_left₀ (mem_ball_zero_iff.mp hu4) (norm_nonneg u)
                (by omega)) (vertexRadius_pow_lt g)
            have hglue := vertexRay_glue g jv (norm_nonneg u) hsu
            rw [hjv1] at hglue
            have hQ : Quotient.mk (genusSetoid g) (projDisc (polyVertex g
                ((vertexSlot g ((jv : ℕ) : ZMod (4 * g))).val : ℤ)
                * Complex.exp (-(Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)))))
                = Quotient.mk (genusSetoid g) (projDisc (polyVertex g
                  ((vertexSlot g ((mv : ℕ) : ZMod (4 * g))).val : ℤ)
                  * Complex.exp (Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)))) :=
              Quotient.sound hglue
            have hform1 : polyVertex g cj
                * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))
                = polyVertex g ((vertexSlot g ((jv : ℕ) : ZMod (4 * g))).val : ℤ)
                  * Complex.exp (-(Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g))) := by
              rw [hcjdef, hupow, hparC]
              have harg : Complex.I * -(-1 : ℂ) ^ mv
                  * ((-1 : ℂ) ^ mv * ((‖u‖ ^ (2 * g) : ℝ) : ℂ))
                  = -(Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)) := by
                push_cast
                linear_combination (-(Complex.I) * ((‖u‖ : ℂ)) ^ (2 * g)) * hsq
              rw [harg]
            have hform2 : polyVertex g cv
                * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g))
                = polyVertex g ((vertexSlot g ((mv : ℕ) : ZMod (4 * g))).val : ℤ)
                  * Complex.exp (Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)) := by
              rw [hcvdef, hupow]
              have harg : Complex.I * (-1 : ℂ) ^ mv
                  * ((-1 : ℂ) ^ mv * ((‖u‖ ^ (2 * g) : ℝ) : ℂ))
                  = Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g) := by
                push_cast
                linear_combination (Complex.I * ((‖u‖ : ℂ)) ^ (2 * g)) * hsq
              rw [harg]
            rw [hsym', hEFin k' _ hle, hVsym, hψvz u hidxu, hform1, hform2]
            exact hQ
          · -- off the ray on the `mv` side: pair back
            have hgt : ¬ ‖polyVertex g cj
                * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))‖ ≤ 1 := by
              rw [hPnorm, not_le, Real.one_lt_exp_iff, hparR]
              have h1 := hsign_lt mv u hidxu hu2 hsinu
              linarith
            rw [hsym', hEFout k' _ hgt, hσP' u, hVsym, hψvz u hidxu]
        · -- the `jv` side: direct
          have hle : ‖polyVertex g cj
              * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))‖ ≤ 1 := by
            rw [hPnorm, Real.exp_le_one_iff]
            linarith [hsign_at jv u hidxu]
          rw [hsym', hEFin k' _ hle, hVsym, hψvj u hidxu]
    · -- off the rays: the sector formula, possibly post-composed with the pairing
      have hPlt : ‖polyVertex g
          ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
          * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))‖ < 1 := by
        rw [hPnorm, Real.exp_lt_one_iff]
        linarith [hsign_lt (vertexSectorIndex g z) z rfl hz0 hsin]
      rcases hedgeW k' _ w hPlt hww' with ⟨-, hwz⟩ | ⟨hw2, hPz0, hwσ⟩
      · -- direct branch
        rw [hwz] at hwV
        refine hred _ E' z (fun u : ℂ => polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
          (hPana _ _ z) (hPderivne _ _ z hz0) ?_
        have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
            ∈ edgeSector g k' :=
          (hPana _ _ z).continuousAt.eventually_mem ((isOpen_edgeSector g k').mem_nhds hwV)
        have hev2 : ∀ᶠ u in 𝓝 z, polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
            ∈ Metric.ball (0 : ℂ) 1 :=
          (hPana _ _ z).continuousAt.eventually_mem
            (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hPlt))
        filter_upwards [hev1, hev2, hidx_const z hsin] with u h1 h2 h3
        refine ⟨by rw [htgt']; exact h1, ?_⟩
        rw [hsym', hEFin k' _ (mem_ball_zero_iff.mp h2).le, hVsym,
          hψv (vertexSectorIndex g z) u h3]
      · -- pairing branch
        have hPz0' : polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g)) ≠ 0 :=
          mul_ne_zero (hAne _) (Complex.exp_ne_zero _)
        refine hred _ E' z (fun u : ℂ => sidePairing g k' (polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))))
          ?_ ?_ ?_
        · exact AnalyticAt.comp (g := sidePairing g k') (f := fun u : ℂ => polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
            (x := z) (hσana k' _ hPz0') (hPana _ _ z)
        · have hPhd := (((hasDerivAt_pow (2 * g) z).const_mul
            (Complex.I * (-1) ^ (vertexSectorIndex g z))).cexp).const_mul (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ))
          have hchain := HasDerivAt.comp z (hσderiv k' _ hPz0') hPhd
          have hd2 : deriv (fun u : ℂ => sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))) z
              = Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                  * (-((polyVertex g
                    ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
                    * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z)
                      * z ^ (2 * g))) ^ 2)⁻¹)
                * (polyVertex g
                    ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
                  * (Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))
                    * (Complex.I * (-1) ^ (vertexSectorIndex g z)
                      * (((2 * g : ℕ) : ℂ) * z ^ (2 * g - 1))))) := hchain.deriv
          rw [hd2]
          exact mul_ne_zero (hσdne k' _ hPz0') (hPdval _ _ z hz0)
        · have hFz : sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))) = w :=
            hwσ.symm
          have hσPc : ContinuousAt (fun u : ℂ => sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))) z :=
            (AnalyticAt.comp (g := sidePairing g k') (f := fun u : ℂ => polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
              (x := z) (hσana k' _ hPz0') (hPana _ _ z)).continuousAt
          have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
              ∈ edgeSector g k' := by
            apply hσPc.eventually_mem
            rw [hFz]
            exact (isOpen_edgeSector g k').mem_nhds hwV
          have hev2 : ∀ᶠ u in 𝓝 z, polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
              ∈ Metric.ball (0 : ℂ) 1 :=
            (hPana _ _ z).continuousAt.eventually_mem
              (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hPlt))
          filter_upwards [hev1, hev2, hidx_const z hsin] with u h1 h2 h3
          have hPu0 : polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)) ≠ 0 :=
            mul_ne_zero (hAne _) (Complex.exp_ne_zero _)
          have hPu1 : ‖polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))‖ < 1 :=
            mem_ball_zero_iff.mp h2
          have hPupos : 0 < ‖polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))‖ :=
            norm_pos_iff.mpr hPu0
          have hgt : ¬ ‖sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))‖
              ≤ 1 := by
            rw [hσnorm, not_le, lt_div_iff₀ hPupos, one_mul]
            exact hPu1
          refine ⟨by rw [htgt']; exact h1, ?_⟩
          rw [hsym', hEFout k' _ hgt, sidePairing_involutive g k' hPu0, hVsym,
            hψv (vertexSectorIndex g z) u h3]
    -- ## Assembly over the atlas
  have hcases : ∀ f ∈ atlas ℂ (GenusSurface g), f = interiorChart g ∨
      (∃ jb : Fin g × Bool, f = edgeChart g jb.1 jb.2) ∨ f = vertexChart g := by
    intro f hf
    have hf' : f ∈ ({interiorChart g}
        ∪ Set.range (fun jb : Fin g × Bool => edgeChart g jb.1 jb.2)
        ∪ {vertexChart g} : Set (OpenPartialHomeomorph (GenusSurface g) ℂ)) := hf
    rcases hf' with (hf1 | hf1) | hf1
    · exact Or.inl hf1
    · obtain ⟨jb, hjb⟩ := hf1
      exact Or.inr (Or.inl ⟨jb, hjb.symm⟩)
    · exact Or.inr (Or.inr hf1)
  have hedgeIdxNe : ∀ (j j' : Fin g) (b b' : Bool),
      ((4 * (j : ℤ) + if b then 1 else 0 : ℤ) : ZMod (4 * g))
        = ((4 * (j' : ℤ) + if b' then 1 else 0 : ℤ) : ZMod (4 * g)) →
      j = j' ∧ b = b' := by
    intro j j' b b' hcon
    obtain ⟨q, hq⟩ := hzmodDvd _ _ hcon
    have hgZ : (1 : ℤ) ≤ g := by exact_mod_cast hg1
    have hjZ : (j : ℤ) < g := by exact_mod_cast j.2
    have hj'Z : (j' : ℤ) < g := by exact_mod_cast j'.2
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le _
    have hj'0 : (0 : ℤ) ≤ (j' : ℤ) := by exact_mod_cast Nat.zero_le _
    have hifb : ∀ c : Bool, (0 : ℤ) ≤ (if c then (1 : ℤ) else 0) ∧
        (if c then (1 : ℤ) else 0) ≤ 1 := by
      intro c
      cases c
      · rw [ite_eq_right Bool.false_ne_true]
        norm_num
      · rw [ite_eq_left rfl]
        norm_num
    have hgq : 4 * (g : ℤ) * q = 4 * ((g : ℤ) * q) := by ring
    rw [hgq] at hq
    have hq0 : (g : ℤ) * q = 0 := by
      rcases lt_trichotomy q 0 with h | h | h
      · exfalso
        have h1 : (g : ℤ) * q ≤ -g := by nlinarith
        linarith [(hifb b).1, (hifb b).2, (hifb b').1, (hifb b').2]
      · rw [h, mul_zero]
      · exfalso
        have h1 : (g : ℤ) ≤ g * q := by nlinarith
        linarith [(hifb b).1, (hifb b).2, (hifb b').1, (hifb b').2]
    rw [hq0, mul_zero] at hq
    cases b <;> cases b' <;> (try simp only [Bool.false_eq_true, if_false, if_true] at hq)
    · refine ⟨Fin.ext ?_, rfl⟩
      omega
    · exfalso
      omega
    · exfalso
      omega
    · refine ⟨Fin.ext ?_, rfl⟩
      omega
  intro e he e' he'
  rcases hcases e he with he1 | ⟨⟨j, b⟩, he1⟩ | he1
  · subst he1
    rcases hcases e' he' with he2 | ⟨⟨j', b'⟩, he2⟩ | he2
    · subst he2
      exact hdiag _
    · subst he2
      exact hIEcore (4 * (j' : ℤ) + if b' then 1 else 0) (edgeChart g j' b') rfl rfl
        (fun u => rfl)
    · subst he2
      exact hsymm (vertexChart g) (interiorChart g) hVI
  · subst he1
    rcases hcases e' he' with he2 | ⟨⟨j', b'⟩, he2⟩ | he2
    · subst he2
      exact hEIcore (4 * (j : ℤ) + if b then 1 else 0) (edgeChart g j b) rfl (fun u => rfl)
    · subst he2
      by_cases hsame : j = j' ∧ b = b'
      · obtain ⟨rfl, rfl⟩ := hsame
        exact hdiag _
      · refine hEEcore (4 * (j : ℤ) + if b then 1 else 0)
          (4 * (j' : ℤ) + if b' then 1 else 0) (edgeChart g j b) (edgeChart g j' b')
          rfl (fun u => rfl) rfl rfl (fun u => rfl) ?_ ?_ ?_
        · intro hcon
          exact hsame (hedgeIdxNe j j' b b' hcon)
        · intro hcon
          have h4 := hzmod4 _ _ hcon
          have e1 := edgeIndex_mod g j b
          have e2 := edgeIndex_mod g j' b'
          omega
        · intro hcon
          have h4 := hzmod4 _ _ hcon
          have e1 := edgeIndex_mod g j b
          have e2 := edgeIndex_mod g j' b'
          omega
    · subst he2
      exact hsymm (vertexChart g) (edgeChart g j b)
        (hVEcore (4 * (j : ℤ) + if b then 1 else 0) (edgeChart g j b) rfl rfl
          (fun u => rfl) (edgeIndex_mod g j b))
  · subst he1
    rcases hcases e' he' with he2 | ⟨⟨j', b'⟩, he2⟩ | he2
    · subst he2
      exact hVI
    · subst he2
      exact hVEcore (4 * (j' : ℤ) + if b' then 1 else 0) (edgeChart g j' b') rfl rfl
        (fun u => rfl) (edgeIndex_mod g j' b')
    · subst he2
      exact hdiag _

open scoped ContDiff in
/-- The genus surface is an analytic complex manifold: all atlas transitions
are analytic. -/
theorem isManifold_genusSurface (g : ℕ) [NeZero g] :
    IsManifold 𝓘(ℂ) ω (GenusSurface g) := by
  have hana : ∀ e ∈ atlas ℂ (GenusSurface g), ∀ e' ∈ atlas ℂ (GenusSurface g),
      ContDiffOn ℂ ω (e.symm.trans e') (e.symm.trans e').source := by
    intro e he e' he'
    have h : AnalyticOnNhd ℂ (e.symm.trans e') (e.symm.trans e').source :=
      fun z hz => (transition_analyticAt g e he e' he' z hz).1
    exact h.contDiffOn (e.symm.trans e').open_source.uniqueDiffOn
  have hgr : HasGroupoid (GenusSurface g) (contDiffGroupoid ω 𝓘(ℂ)) := by
    constructor
    intro e e' he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    have hsymmEq : (e.symm.trans e').symm = e'.symm.trans e := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    constructor
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
        Set.preimage_id, Set.range_id, Set.inter_univ]
      exact hana e he e' he'
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
        Set.preimage_id, Set.range_id, Set.inter_univ]
      have hset : (e.symm.trans e').target = (e'.symm.trans e).source := by
        rw [← hsymmEq, OpenPartialHomeomorph.symm_source]
      rw [hsymmEq, hset]
      exact hana e' he' e he
  exact IsManifold.mk' 𝓘(ℂ) ω (GenusSurface g) (gr := hgr)

open scoped ContDiff in
instance (g : ℕ) [NeZero g] : IsManifold 𝓘(ℂ) ω (GenusSurface g) :=
  isManifold_genusSurface g

/-! ## Base points and the quotient map -/

/-- The base point of the genus surface: the class of the center of the
disc. -/
noncomputable def basePoint (g : ℕ) [NeZero g] : GenusSurface g :=
  Quotient.mk (genusSetoid g) ⟨0, Metric.mem_closedBall_self zero_le_one⟩

/-- The vertex of the `4g`-gon lies on the closed unit disc. -/
theorem polyVertex_mem_closedBall (g : ℕ) (m : ℤ) :
    polyVertex g m ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  unfold polyVertex
  have h : (Real.pi * m * Complex.I / (2 * g) : ℂ)
      = ((Real.pi * m / (2 * g) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The vertex class of the genus surface. -/
noncomputable def vertexPoint (g : ℕ) [NeZero g] : GenusSurface g :=
  Quotient.mk (genusSetoid g) ⟨polyVertex g 0, polyVertex_mem_closedBall g 0⟩

/-- The projection to the genus surface is a quotient map. -/
theorem quotientMap_genus (g : ℕ) [NeZero g] :
    IsQuotientMap (Quotient.mk (genusSetoid g)) := isQuotientMap_quot_mk

/-- Openness in the genus surface is openness of the saturation in the
disc. -/
theorem isOpen_saturated_iff (g : ℕ) [NeZero g] (A : Set (GenusSurface g)) :
    IsOpen A ↔ IsOpen (Quotient.mk (genusSetoid g) ⁻¹' A) :=
  (quotientMap_genus g).isOpen_preimage.symm

end RiemannDynamics
