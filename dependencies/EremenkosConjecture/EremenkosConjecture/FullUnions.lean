import EremenkosConjecture.FullNeighbourhoods

/-!
# Fullness of the compact unions in the approximation construction

Polynomial separation shows that adjoining finitely many points preserves
fullness. For two full compact sets separated by a vertical line, the maximum
principle rules out bounded components of the complement of their union.
-/

open Set Metric Polynomial Bornology

namespace EremenkosConjecture

theorem isConnected_compl_insert (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (a : ℂ) : IsConnected (insert a K)ᶜ := by
  apply isConnected_compl_of_polynomial_separation _ (hK.insert a)
  intro z hz
  have hza : z ≠ a := fun h => hz (Or.inl h)
  have hzK : z ∉ K := fun h => hz (Or.inr h)
  obtain ⟨p, hpz, hpK⟩ := Runge.exists_polynomial_separator K hK hfull z hzK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let M : ℝ := (R + ‖a‖) / ‖z - a‖
  have hden : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hM : 0 < M := div_pos (add_pos_of_pos_of_nonneg hR (norm_nonneg _)) hden
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < 1 / (2 * M)) (by norm_num : (1 / 2 : ℝ) < 1)
  let q : Polynomial ℂ := C (z - a)⁻¹ * (X - C a) * p ^ n
  have hqz : q.eval z = 1 := by simp [q, hpz, sub_ne_zero.mpr hza]
  refine ⟨q, 1 / 2, ?_, by rw [hqz, norm_one]; norm_num⟩
  intro w hw
  rcases hw with rfl | hw
  · simp [q]
  · have hbound : ‖w - a‖ / ‖z - a‖ ≤ M :=
      div_le_div_of_nonneg_right ((norm_sub_le _ _).trans
        (by linarith [hKR w hw])) hden.le
    apply le_of_lt
    calc
      ‖q.eval w‖ = (‖w - a‖ / ‖z - a‖) * ‖p.eval w‖ ^ n := by
        simp only [q, eval_mul, eval_C, eval_sub, eval_X, eval_pow,
          norm_mul, norm_inv, norm_pow]
        ring
      _ ≤ M * (1 / 2 : ℝ) ^ n := mul_le_mul hbound
        (pow_le_pow_left₀ (norm_nonneg _) (hpK w hw).le n) (by positivity) hM.le
      _ < M * (1 / (2 * M)) := mul_lt_mul_of_pos_left hn hM
      _ = 1 / 2 := by field_simp

theorem isConnected_compl_union_finite (K P : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hP : P.Finite) : IsConnected (K ∪ P)ᶜ := by
  induction P, hP using Set.Finite.induction_on with
  | empty => simpa using hfull
  | @insert a P ha hP ih =>
    simpa only [union_insert] using isConnected_compl_insert (K ∪ P)
      (hK.union hP.isCompact) ih a

private theorem isPreconnected_vertical (a : ℝ) : IsPreconnected {z : ℂ | z.re = a} := by
  have hconv : Convex ℝ {z : ℂ | z.re = a} := by
    convert (convex_halfSpace_re_le a).inter (convex_halfSpace_re_ge a) using 1
    ext z
    simp only [Set.mem_ofPred_eq, mem_inter_iff]
    exact le_antisymm_iff
  exact hconv.isPreconnected

private theorem not_isBounded_vertical (a : ℝ) : ¬ IsBounded {z : ℂ | z.re = a} := by
  intro h
  obtain ⟨R, hR⟩ := h.exists_norm_le
  have H := hR (a + ((|R| + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  have hi := Complex.abs_im_le_norm (a + ((|R| + 1 : ℝ) : ℂ) * Complex.I)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hi
  rw [abs_of_pos (by positivity)] at hi
  have habs := le_abs_self R
  linarith

/-- Full compact sets separated by a vertical line have a full union. -/
theorem isConnected_compl_union_separated (K L : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L)
    (hKfull : IsConnected Kᶜ) (hLfull : IsConnected Lᶜ)
    (a : ℝ) (hKa : ∀ z ∈ K, z.re < a) (hLa : ∀ z ∈ L, a < z.re) :
    IsConnected (K ∪ L)ᶜ := by
  apply isConnected_compl_of_unbounded_components _ (hK.union hL).isBounded
  intro z hz hb
  let D := connectedComponentIn (K ∪ L)ᶜ z
  have hzD : z ∈ D := mem_connectedComponentIn hz
  have hfront : frontier D ⊆ K ∪ L := by
    simpa only [compl_compl] using
      frontier_component_subset_compl (hK.union hL).isClosed.isOpen_compl hz
  have hline : {w : ℂ | w.re = a} ⊆ (K ∪ L)ᶜ := by
    intro w hw hwKL
    rcases hwKL with hwK | hwL
    · exact (ne_of_lt (hKa w hwK)) hw
    · exact (ne_of_gt (hLa w hwL)) hw
  have hne : ∀ w ∈ D, w.re ≠ a := by
    intro w hw heq
    have hsub := (isPreconnected_vertical a).subset_connectedComponentIn heq hline
    have heqD : connectedComponentIn (K ∪ L)ᶜ w = D := (connectedComponentIn_eq hw).symm
    rw [heqD] at hsub
    exact not_isBounded_vertical a (hb.subset hsub)
  have hd := (isPreconnected_connectedComponentIn : IsPreconnected D).mapsTo_Ioi_or_Iio
    Complex.continuous_re.continuousOn hne
  have rule_out (A : Set ℂ) (hA : IsCompact A) (hAf : IsConnected Aᶜ)
      (hDA : frontier D ⊆ A) (hzA : z ∉ A) : False := by
    obtain ⟨p, hpz, hpA⟩ := Runge.exists_polynomial_separator A hA hAf z hzA
    have H := Complex.norm_le_of_forall_mem_frontier_norm_le hb
      p.differentiable.diffContOnCl (fun w hw => (hpA w (hDA hw)).le)
      (subset_closure hzD)
    rw [hpz, norm_one] at H
    norm_num at H
  rcases hd with hd | hd
  · apply rule_out L hL hLfull _ (fun h => hz (Or.inr h))
    have hcl : closure D ⊆ {w : ℂ | a ≤ w.re} :=
      (isClosed_le continuous_const Complex.continuous_re).closure_subset_iff.mpr
        (fun w hw => show a ≤ w.re from (hd hw).le)
    intro w hw
    rcases hfront hw with hwK | hwL
    · exact False.elim ((not_lt_of_ge (hcl hw.1)) (hKa w hwK))
    · exact hwL
  · apply rule_out K hK hKfull _ (fun h => hz (Or.inl h))
    have hcl : closure D ⊆ {w : ℂ | w.re ≤ a} :=
      (isClosed_le Complex.continuous_re continuous_const).closure_subset_iff.mpr
        (fun w hw => show w.re ≤ a from (hd hw).le)
    intro w hw
    rcases hfront hw with hwK | hwL
    · exact hwK
    · exact False.elim ((not_lt_of_ge (hcl hw.1)) (hLa w hwL))

end EremenkosConjecture
