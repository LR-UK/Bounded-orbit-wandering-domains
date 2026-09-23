import Runge.PoleAlgebra

open Polynomial Set

namespace Runge

theorem inverse_factor_product_mem (K : Set ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (hpole : ∀ a (ha : a ∉ K), poleKernel K a ha ∈ S)
    (m : Multiset ℂ) (hm : ∀ a ∈ m, a ∉ K) :
    ∃ F : C(K, ℂ), F ∈ S ∧ ∀ z : K, F z = ((m.map (fun a => (z : ℂ)-a)).prod)⁻¹ := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨1, S.one_mem, by simp⟩
  | @cons a m ih =>
    have ha := hm a (Multiset.mem_cons_self a m)
    obtain ⟨F, hFS, hF⟩ := ih (fun b hb => hm b (Multiset.mem_cons_of_mem hb))
    refine ⟨poleKernel K a ha * F, S.mul_mem (hpole a ha) hFS, ?_⟩
    intro z
    simp [hF z, mul_comm]

/-- All rational functions without poles on `K` belong to any complex algebra
containing polynomials and every simple-pole kernel outside `K`. -/
theorem rationalAlgebra_le_of_polynomials_and_kernels (K : Set ℂ)
    (S : Subalgebra ℂ C(K, ℂ))
    (hpoly : ∀ p : ℂ[X], polynomialMap K p ∈ S)
    (hpole : ∀ a (ha : a ∉ K), poleKernel K a ha ∈ S) : rationalAlgebra K ≤ S := by
  rintro f ⟨p, q, hq, hf⟩
  by_cases hq0 : q = 0
  · have hf0 : f = 0 := by
      apply ContinuousMap.ext
      intro z
      exact False.elim (hq z (by simp [hq0]))
    rw [hf0]
    exact S.zero_mem
  · have hr : ∀ a ∈ q.roots, a ∉ K := by
      intro a ha haK
      exact hq ⟨a, haK⟩ (Polynomial.isRoot_of_mem_roots ha)
    obtain ⟨F, hFS, hF⟩ := inverse_factor_product_mem K S hpole q.roots hr
    have heq : f = polynomialMap K p * algebraMap ℂ C(K, ℂ) (q.leadingCoeff)⁻¹ * F := by
      apply ContinuousMap.ext
      intro z
      rw [hf z, (IsAlgClosed.splits q).eval_eq_prod_roots]
      simp [hF z, div_eq_mul_inv, mul_assoc, mul_comm]
    rw [heq]
    exact S.mul_mem (S.mul_mem (hpoly p) (S.algebraMap_mem _)) hFS

theorem rationalClosure_le_of_polynomials_and_kernels (K : Set ℂ) [CompactSpace K]
    (S : Subalgebra ℂ C(K, ℂ)) (hS : IsClosed (S : Set C(K, ℂ)))
    (hpoly : ∀ p : ℂ[X], polynomialMap K p ∈ S)
    (hpole : ∀ a (ha : a ∉ K), poleKernel K a ha ∈ S) : rationalClosure K ≤ S :=
  (rationalAlgebra K).topologicalClosure_minimal
    (rationalAlgebra_le_of_polynomials_and_kernels K S hpoly hpole) hS

end Runge
