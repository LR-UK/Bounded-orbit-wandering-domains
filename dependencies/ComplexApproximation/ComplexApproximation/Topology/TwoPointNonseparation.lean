import ComplexApproximation.Topology.Nonseparation
import ComplexApproximation.Topology.FilledContinua

/-!
# The two-point disjoint Janiszewski theorem and filling disjoint compacta

This strengthens the continuous-logarithm proof in Nonseparation by using
the relevant connected components instead of assuming the whole complements
connected. It supports full separating exhaustions for polynomial approximation.
-/

open Set Metric Function Bornology
open scoped Topology

namespace ComplexApproximation

set_option autoImplicit false

private theorem two_point_exp_difference_constant {S : Set ℂ} (hS : IsPreconnected S)
    {f g : ℂ → ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (he : EqOn (Complex.exp ∘ f) (Complex.exp ∘ g) S)
    {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) : f x - g x = f y - g y := by
  apply Complex.isCoveringMap_exp.constOn_of_comp hS (hf.sub hg) ?_ hx hy
  intro a ha b hb
  apply Subtype.ext
  change Complex.exp (f a - g a) = Complex.exp (f b - g b)
  have hea : Complex.exp (f a) = Complex.exp (g a) := he ha
  have heb : Complex.exp (f b) = Complex.exp (g b) := he hb
  rw [Complex.exp_sub, Complex.exp_sub, hea, heb,
    div_self (Complex.exp_ne_zero _), div_self (Complex.exp_ne_zero _)]

private theorem two_point_no_separating_component_of_disjoint
    (A B C : Set ℂ) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hfront : frontier C ⊆ A ∪ B) {x y : ℂ}
    (hx : x ∈ (A ∪ B)ᶜ) (hy : y ∈ (A ∪ B)ᶜ)
    (hAy : y ∈ connectedComponentIn Aᶜ x)
    (hBy : y ∈ connectedComponentIn Bᶜ x)
    (hxC : x ∈ C) (hyC : y ∉ C) : False := by
  classical
  obtain ⟨θ, hθA, hθB, _⟩ := exists_continuous_zero_one_of_isClosed hA hB hAB
  let κ : ℂ := 2 * Real.pi * Complex.I
  have hκexp : Complex.exp κ = 1 := Complex.exp_two_pi_mul_I
  have hκne : κ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let t : ℂ → ℂ := fun z => (θ z : ℂ) * κ
  have ht : Continuous t := (Complex.continuous_ofReal.comp θ.continuous).mul continuous_const
  let F : ℂ → ℂ := fun z => if z ∈ C then Complex.exp (t z) else 1
  have hF : Continuous F := by
    apply Continuous.if ?_ (Complex.continuous_exp.comp ht) continuous_const
    intro z hz
    rcases hfront hz with hzA | hzB
    · have H : θ z = 0 := hθA hzA
      simp [t, H]
    · have H : θ z = 1 := hθB hzB
      simpa [t, H] using hκexp
  have hFne (z : ℂ) : F z ≠ 0 := by
    dsimp [F]
    split_ifs
    · exact Complex.exp_ne_zero _
    · exact one_ne_zero
  have hsc : IsSimplyConnected (univ : Set ℂ) :=
    (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨L, hL, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_univ
    hF.continuousOn (by rintro ⟨z, _, hz⟩; exact hFne z hz)
  have hLcont : Continuous L := continuousOn_univ.mp hL
  let u : ℂ → ℂ := fun z => if z ∈ C then t z - κ else 0
  let v : ℂ → ℂ := fun z => if z ∈ C then t z else 0
  have hu : ContinuousOn u Aᶜ := by
    apply ContinuousOn.if ?_ (ht.sub continuous_const).continuousOn continuousOn_const
    intro z hz
    have hzB : z ∈ B := (hfront hz.2).resolve_left hz.1
    have H : θ z = 1 := hθB hzB
    simp [t, H, κ]
  have hv : ContinuousOn v Bᶜ := by
    apply ContinuousOn.if ?_ ht.continuousOn continuousOn_const
    intro z hz
    have hzA : z ∈ A := (hfront hz.2).resolve_right hz.1
    have H : θ z = 0 := hθA hzA
    simp [t, H]
  have hue (z : ℂ) : Complex.exp (u z) = F z := by
    by_cases hz : z ∈ C
    · simp only [u, F, ite_eq_left hz, Complex.exp_sub, hκexp, div_one]
    · simp [u, F, hz]
  have hve (z : ℂ) : Complex.exp (v z) = F z := by
    by_cases hz : z ∈ C <;> simp [v, F, hz]
  have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
  have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
  have hyA : y ∈ Aᶜ := fun h => hy (Or.inl h)
  have hyB : y ∈ Bᶜ := fun h => hy (Or.inr h)
  have H₁ := two_point_exp_difference_constant isPreconnected_connectedComponentIn
    hLcont.continuousOn (hu.mono (connectedComponentIn_subset Aᶜ x))
    (fun z _ => (hLe (mem_univ z)).trans (hue z).symm) (mem_connectedComponentIn hxA) hAy
  have H₂ := two_point_exp_difference_constant isPreconnected_connectedComponentIn
    hLcont.continuousOn (hv.mono (connectedComponentIn_subset Bᶜ x))
    (fun z _ => (hLe (mem_univ z)).trans (hve z).symm) (mem_connectedComponentIn hxB) hBy
  simp only [u, v, ite_eq_left hxC, ite_eq_right hyC, sub_zero] at H₁ H₂
  apply hκne
  linear_combination H₁ - H₂



/-- Points not separated by either of two disjoint closed plane sets are
not separated by their union. -/
theorem mem_connectedComponentIn_compl_union_disjoint
    (A B : Set ℂ) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    {x y : ℂ} (hx : x ∈ (A ∪ B)ᶜ)
    (hAy : y ∈ connectedComponentIn Aᶜ x)
    (hBy : y ∈ connectedComponentIn Bᶜ x) :
    y ∈ connectedComponentIn (A ∪ B)ᶜ x := by
  by_contra hyC
  have hy : y ∈ (A ∪ B)ᶜ := fun h => h.elim
    (connectedComponentIn_subset Aᶜ x hAy)
    (connectedComponentIn_subset Bᶜ x hBy)
  apply two_point_no_separating_component_of_disjoint A B
    (connectedComponentIn (A ∪ B)ᶜ x) hA hB hAB ?_
    hx hy hAy hBy (mem_connectedComponentIn hx) hyC
  simpa only [compl_compl] using
    frontier_component_subset_compl (hA.union hB).isOpen_compl hx

/-- An unbounded complementary component of a bounded plane set contains
the whole exterior of any ball containing that set. -/
theorem exterior_subset_component_of_not_mem_fill
    {A : Set ℂ} {z : ℂ} (hz : z ∉ fill A)
    {R : ℝ} (hR : 0 < R) (hAR : ∀ a ∈ A, ‖a‖ ≤ R) :
    {w : ℂ | R < ‖w‖} ⊆ connectedComponentIn Aᶜ z := by
  have hfar : ∃ b ∈ connectedComponentIn Aᶜ z, R < ‖b‖ := by
    by_contra! H
    exact hz (isBounded_iff_forall_norm_le.mpr ⟨R, H⟩)
  obtain ⟨b, hb, hbR⟩ := hfar
  have hext : {w : ℂ | R < ‖w‖} ⊆ Aᶜ :=
    fun w hw hwa => (not_lt_of_ge (hAR w hwa)) hw
  have hsub := (isConnected_exterior R hR).isPreconnected.subset_connectedComponentIn hbR hext
  rwa [← connectedComponentIn_eq hb] at hsub

/-- Filling distributes over a disjoint union of compact plane sets.
The sets and their fillings need not be connected. -/
theorem fill_union_disjoint_compacts
    (A B : Set ℂ) (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) :
    fill (A ∪ B) = fill A ∪ fill B := by
  apply Subset.antisymm
  · intro z hz
    by_contra hzfill
    have hzA : z ∉ fill A := fun h => hzfill (Or.inl h)
    have hzB : z ∉ fill B := fun h => hzfill (Or.inr h)
    have hzAB : z ∈ (A ∪ B)ᶜ := fun h => h.elim
      (fun h => hzA (subset_fill A h)) (fun h => hzB (subset_fill B h))
    obtain ⟨R, hR, hbound⟩ := (hA.union hB).isBounded.exists_pos_norm_le
    have hEA := exterior_subset_component_of_not_mem_fill hzA hR
      (fun a ha => hbound a (Or.inl ha))
    have hEB := exterior_subset_component_of_not_mem_fill hzB hR
      (fun a ha => hbound a (Or.inr ha))
    have hE : {w : ℂ | R < ‖w‖} ⊆ connectedComponentIn (A ∪ B)ᶜ z := by
      intro w hw
      exact mem_connectedComponentIn_compl_union_disjoint A B hA.isClosed hB.isClosed
        hAB hzAB (hEA hw) (hEB hw)
    change IsBounded (connectedComponentIn (A ∪ B)ᶜ z) at hz
    exact not_isBounded_exterior R (hz.subset hE)
  · exact union_subset (fill_mono subset_union_left) (fill_mono subset_union_right)

end ComplexApproximation
