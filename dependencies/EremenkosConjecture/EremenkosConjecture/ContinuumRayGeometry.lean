import EremenkosConjecture.RayGeometry
import EremenkosConjecture.PlaneTopology
import ComplexApproximation.Topology.HorizontalEscape
import Runge.PolynomialSeparation

/-! # Attaching a horizontal ray at a rightmost point

The ray attached to a full compact set creates no bounded complementary
component. On the right of its endpoint, vertical rays escape to infinity;
any hypothetical bounded hole therefore has its entire boundary in the
original compact set, contradicting polynomial separation.
-/

open Set Metric Complex Bornology

namespace EremenkosConjecture

theorem unbounded_component_right_of_attached_ray {X : Set ℂ} {ζ z : ℂ}
    (hmax : ∀ x ∈ X, x.re ≤ ζ.re) (hz : z ∉ X ∪ horizontalRay ζ)
    (hzre : ζ.re < z.re) :
    ¬ IsBounded (connectedComponentIn (X ∪ horizontalRay ζ)ᶜ z) := by
  have hzim : z.im ≠ ζ.im := fun h => hz (Or.inr ⟨hzre.le, h⟩)
  rcases lt_or_gt_of_ne hzim with him | him
  · apply ComplexApproximation.not_isBounded_component_of_affine_ray
      (v := -I) (neg_ne_zero.mpr I_ne_zero)
    intro t ht hw
    have hre : (z + (t : ℂ) * -I).re = z.re := by simp
    have him' : (z + (t : ℂ) * -I).im = z.im - t := by simp [sub_eq_add_neg]
    rcases hw with hwX | hwR
    · have := hmax _ hwX
      rw [hre] at this
      linarith
    · have hwim := hwR.2
      rw [him'] at hwim
      linarith
  · apply ComplexApproximation.not_isBounded_component_of_affine_ray
      (v := I) I_ne_zero
    intro t ht hw
    have hre : (z + (t : ℂ) * I).re = z.re := by simp
    have him' : (z + (t : ℂ) * I).im = z.im + t := by simp
    rcases hw with hwX | hwR
    · have := hmax _ hwX
      rw [hre] at this
      linarith
    · have hwim := hwR.2
      rw [him'] at hwim
      linarith

theorem noBoundedComplementComponents_union_horizontalRay {X : Set ℂ} {ζ : ℂ}
    (hX : IsCompact X) (hfull : IsConnected Xᶜ) (hζ : ζ ∈ X)
    (hmax : ∀ x ∈ X, x.re ≤ ζ.re) :
    ComplexApproximation.NoBoundedComplementComponents (X ∪ horizontalRay ζ) := by
  intro z hz hb
  let D := connectedComponentIn (X ∪ horizontalRay ζ)ᶜ z
  have hleft : D ⊆ {w : ℂ | w.re ≤ ζ.re} := by
    intro w hw
    by_contra h
    have hwE := connectedComponentIn_subset (X ∪ horizontalRay ζ)ᶜ z hw
    have hcomp := connectedComponentIn_eq hw
    exact unbounded_component_right_of_attached_ray hmax hwE (lt_of_not_ge h)
      (hcomp ▸ hb)
  have hclleft : closure D ⊆ {w : ℂ | w.re ≤ ζ.re} :=
    closure_minimal hleft (isClosed_le Complex.continuous_re continuous_const)
  have hfront : frontier D ⊆ X := by
    intro w hw
    have h := frontier_component_subset_compl
      (hX.isClosed.union (isClosed_horizontalRay ζ)).isOpen_compl hz hw
    simp only [compl_compl] at h
    rcases h with hwX | hwR
    · exact hwX
    · have hre := le_antisymm (hclleft hw.1) hwR.1
      have heq : w = ζ := Complex.ext hre hwR.2
      exact heq.symm ▸ hζ
  obtain ⟨p, hpz, hpX⟩ := Runge.exists_polynomial_separator X hX hfull z
    (fun h => hz (Or.inl h))
  have hn := Complex.norm_le_of_forall_mem_frontier_norm_le hb
    p.differentiable.diffContOnCl (fun w hw => (hpX w (hfront hw)).le)
    (subset_closure (mem_connectedComponentIn hz))
  rw [hpz, norm_one] at hn
  norm_num at hn

end EremenkosConjecture
