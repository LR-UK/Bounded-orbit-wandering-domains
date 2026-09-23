import FunctionTheory.Analytic.FiniteComposition
import FunctionTheory.Conformal.CompactConformalInverse

open Set Function
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Exact images along a non-autonomous finite orbit. -/
theorem image_finiteComposition (g : ℕ → ℂ → ℂ) (K : ℕ → Set ℂ) (n : ℕ)
    (himage : ∀ k<n, g k '' K k=K (k+1)) :
    finiteComposition g n '' K 0=K n := by
  induction n with
  | zero => simp [finiteComposition]
  | succ n ih =>
    change (g n ∘ finiteComposition g n) '' K 0=K (n+1)
    simp only [Function.comp_def]
    rw [← image_image (g n) (finiteComposition g n) (K 0),
      ih (fun k hk => himage k (by omega)),himage n (by omega)]

/-- Every prefix of a chain of univalent maps has a conformal inverse on
a neighbourhood of the entire initial compact set and its image. -/
theorem exists_conformal_finite_composition
    (g : ℕ → ℂ → ℂ) (K : ℕ → Set ℂ) (hK : IsCompact (K 0)) (n : ℕ)
    (himage : ∀ k<n, g k '' K k=K (k+1))
    (hg : ∀ k<n, AnalyticOnNhd ℂ (g k) (K k))
    (hi : ∀ k<n, InjOn (g k) (K k))
    (hd : ∀ k<n, ∀ z∈K k, deriv (g k) z≠0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      K 0 ⊆ e.source ∧ (e : ℂ → ℂ)=finiteComposition g n ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      e '' K 0=K n := by
  have horbit : ∀ k≤n, MapsTo (finiteComposition g k) (K 0) (K k) := by
    intro k hk z hz
    rw [← image_finiteComposition g K k (fun j hj => himage j (by omega))]
    exact mem_image_of_mem _ hz
  have hA : AnalyticOnNhd ℂ (finiteComposition g n) (K 0) := by
    intro z hz
    exact analyticAt_finiteComposition g n (fun j hj => hg j hj _ (horbit j hj.le hz))
  have hID : ∀ k≤n, InjOn (finiteComposition g k) (K 0) ∧
      ∀ z∈K 0, deriv (finiteComposition g k) z≠0 := by
    intro k hk
    induction k with
    | zero =>
      constructor
      · intro x hx y hy hxy
        exact hxy
      · intro z hz
        simp [finiteComposition]
    | succ k ih =>
      obtain ⟨hki,hkd⟩ := ih (by omega)
      constructor
      · exact (hi k (by omega)).comp hki (horbit k (by omega))
      · intro z hz
        have ha := analyticAt_finiteComposition g k
          (fun j hj => hg j (by omega) _ (horbit j (by omega) hz))
        have hc := (hg k (by omega) _ (horbit k (by omega) hz)).differentiableAt.hasDerivAt.comp z
          ha.differentiableAt.hasDerivAt
        change deriv (g k ∘ finiteComposition g k) z≠0
        rw [hc.deriv]
        exact mul_ne_zero (hd k (by omega) _ (horbit k (by omega) hz)) (hkd z hz)
  obtain ⟨e,he,heq,hea,hei⟩ := exists_conformal_neighbourhood_of_compact_injective
    hK hA (hID n le_rfl).1 (hID n le_rfl).2
  exact ⟨e,he,heq,hea,hei,by rw [heq]; exact image_finiteComposition g K n himage⟩

/-- Forward transport through inverse model prefixes. This is the
coordinate formula that keeps the initial coordinate exactly the identity
in the univalent triangle construction. -/
theorem finiteComposition_forward_coordinate_step
    (f g : ℕ → ℂ → ℂ) (e : ℕ → OpenPartialHomeomorph ℂ ℂ)
    (he : ∀ n, (e n : ℂ → ℂ)=finiteComposition g n)
    (n : ℕ) {z : ℂ} (hz : z∈(e n).target)
    (hnext : (e n).symm z∈(e (n+1)).source) :
    finiteComposition f (n+1) ((e (n+1)).symm (g n z))=
      f n (finiteComposition f n ((e n).symm z)) := by
  have hmap : e (n+1) ((e n).symm z)=g n z := by
    rw [he (n+1)]
    change g n (finiteComposition g n ((e n).symm z))=g n z
    rw [← he n,(e n).right_inv hz]
  rw [← hmap,(e (n+1)).left_inv hnext]
  rfl

end FunctionTheory
