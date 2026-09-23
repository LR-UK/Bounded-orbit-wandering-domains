import Runge.PoleTopology
import Mathlib.Analysis.Complex.Polynomial.Basic

open Polynomial Set

namespace Runge

/-- Rational functions with a nonzero denominator whose zeros are confined to
the prescribed set of allowed poles. -/
def poleAlgebra (K P : Set ℂ) : Subalgebra ℂ C(K, ℂ) where
  carrier := {f | ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
    (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧ ∀ z : K, f z = p.eval (z : ℂ) / q.eval (z : ℂ)}
  zero_mem' := ⟨0, 1, by simp, by simp, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp, by simp, by simp⟩
  add_mem' := by
    rintro f g ⟨p, q, hq0, hq, hqP, hf⟩ ⟨r, s, hs0, hs, hsP, hg⟩
    refine ⟨p*s+q*r, q*s, mul_ne_zero hq0 hs0, ?_, ?_, ?_⟩
    · intro z
      simpa using mul_ne_zero (hq z) (hs z)
    · intro a ha
      simp only [Polynomial.eval_mul, mul_eq_zero] at ha
      exact ha.elim (hqP a) (hsP a)
    · intro z
      simp only [ContinuousMap.add_apply, Polynomial.eval_add, Polynomial.eval_mul]
      rw [hf, hg]
      exact div_add_div _ _ (hq z) (hs z)
  mul_mem' := by
    rintro f g ⟨p, q, hq0, hq, hqP, hf⟩ ⟨r, s, hs0, hs, hsP, hg⟩
    refine ⟨p*r, q*s, mul_ne_zero hq0 hs0, ?_, ?_, ?_⟩
    · intro z
      simpa using mul_ne_zero (hq z) (hs z)
    · intro a ha
      simp only [Polynomial.eval_mul, mul_eq_zero] at ha
      exact ha.elim (hqP a) (hsP a)
    · intro z
      simp only [ContinuousMap.mul_apply, Polynomial.eval_mul]
      rw [hf, hg]
      exact div_mul_div_comm _ _ _ _
  algebraMap_mem' c := ⟨C c, 1, by simp, by simp, by simp, by simp⟩

noncomputable def poleClosure (K P : Set ℂ) [CompactSpace K] : Subalgebra ℂ C(K, ℂ) :=
  (poleAlgebra K P).topologicalClosure

theorem polynomialMap_mem_poleAlgebra (K P : Set ℂ) (p : ℂ[X]) :
    polynomialMap K p ∈ poleAlgebra K P :=
  ⟨p, 1, by simp, by simp, by simp, by simp⟩

theorem poleKernel_mem_poleAlgebra (K P : Set ℂ) (a : ℂ) (ha : a ∉ K) (haP : a ∈ P) :
    poleKernel K a ha ∈ poleAlgebra K P := by
  refine ⟨1, X-C a, ?_, ?_, ?_, ?_⟩
  · intro he
    have h := congrArg (fun p : ℂ[X] => p.coeff 1) he
    simp at h
  · intro z
    simpa using sub_ne_zero.mpr (fun h : (z : ℂ) = a => ha (h ▸ z.property))
  · intro z hz
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hz
    exact hz ▸ haP
  · intro z
    simp [one_div]

theorem mem_poleClosure_iff (K P : Set ℂ) [CompactSpace K] (f : C(K, ℂ)) :
    f ∈ poleClosure K P ↔ ∀ ε : ℝ, 0 < ε →
      ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
        (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
        ∀ z : K, ‖f z - p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε := by
  change f ∈ closure (poleAlgebra K P : Set C(K, ℂ)) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro hf ε hε
    obtain ⟨g, ⟨p, q, hq0, hq, hqP, hg⟩, hfg⟩ := hf ε hε
    refine ⟨p, q, hq0, hq, hqP, fun z => ?_⟩
    rw [← hg z]
    exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (f-g) z)
      (by simpa only [dist_eq_norm] using hfg)
  · intro hf ε hε
    obtain ⟨p, q, hq0, hq, hqP, hpq⟩ := hf ε hε
    refine ⟨rationalMap K p q hq, ⟨p, q, hq0, hq, hqP, fun _ => rfl⟩, ?_⟩
    rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
    exact hpq

theorem poleAlgebra_empty_polynomial (K : Set ℂ) (f : C(K, ℂ))
    (hf : f ∈ poleAlgebra K ∅) : ∃ p : ℂ[X], f = polynomialMap K p := by
  obtain ⟨p, q, _, _, hqP, hpq⟩ := hf
  have hd : q.degree ≤ 0 := le_of_not_gt fun h => by
    obtain ⟨a, ha⟩ := Complex.exists_root h
    exact hqP a ha
  have hq := Polynomial.eq_C_of_degree_le_zero hd
  refine ⟨p * C (q.coeff 0)⁻¹, ?_⟩
  apply ContinuousMap.ext
  intro z
  rw [hpq z, hq]
  simp [polynomialMap, div_eq_mul_inv]

theorem mem_poleClosure_empty_iff (K : Set ℂ) [CompactSpace K] (f : C(K, ℂ)) :
    f ∈ poleClosure K ∅ ↔ ∀ ε : ℝ, 0 < ε →
      ∃ p : ℂ[X], ∀ z : K, ‖f z - p.eval (z : ℂ)‖ < ε := by
  change f ∈ closure (poleAlgebra K ∅ : Set C(K, ℂ)) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro hf ε hε
    obtain ⟨g, hg, hfg⟩ := hf ε hε
    obtain ⟨p, rfl⟩ := poleAlgebra_empty_polynomial K g hg
    refine ⟨p, fun z => ?_⟩
    exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (f-polynomialMap K p) z)
      (by simpa only [dist_eq_norm] using hfg)
  · intro hf ε hε
    obtain ⟨p, hp⟩ := hf ε hε
    refine ⟨polynomialMap K p, polynomialMap_mem_poleAlgebra K ∅ p, ?_⟩
    rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
    exact hp

end Runge
