import BoundedWanderingDomains.DensityDeficit
import BoundedWanderingDomains.AreaTransport

open MeasureTheory Filter Set InnerProductSpace Laplacian
open scoped Topology ContDiff ENNReal

namespace AreaDeficit

/-- Restrict the checked analytic estimate to a measurable set on which
the cutoff is at least one. The positive deficit is expressed directly
as a difference of ENNReal area weights, as required by AreaTransport. -/
theorem density_deficit_on_set
    (F : Finset ℂ) {V W : Set ℂ} (hV : IsOpen V) (hW : MeasurableSet W)
    {a b chi : ℂ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hchi : ContDiff ℝ 2 chi) (hc : HasCompactSupport chi)
    (hchi0 : ∀ x, 0 ≤ chi x) (hsupp : tsupport chi ⊆ V)
    (hchiW : ∀ x ∈ W, 1 ≤ chi x) (hWF : ∀ x ∈ W, x ∉ F)
    (ha : ∀ x ∈ V, x ∉ F → 0 < a x ∧ ContDiffAt ℝ 2 a x)
    (hb : ∀ x ∈ V, x ∉ F → 0 < b x ∧ ContDiffAt ℝ 2 b x)
    (hca : ∀ x ∈ V, x ∉ F → Δ (fun z => Real.log (a z)) x = (a x)^2)
    (hcb : ∀ x ∈ V, x ∉ F → Δ (fun z => Real.log (b z)) x = (b x)^2)
    (hbound : ∀ x ∈ V, x ∉ F → max (Real.log (a x) - Real.log (b x)) 0 ≤ M) :
    (∫⁻ x in W, ENNReal.ofReal ((a x)^2) - ENNReal.ofReal ((b x)^2)) ≤
      ENNReal.ofReal (M * ∫ x, |Δ chi x|) := by
  have hmain := density_deficit_cutoff F hV hM0 hchi hc hchi0 hsupp ha hb hca hcb hbound
  apply le_trans ?_ hmain
  apply le_trans ?_ (setLIntegral_le_lintegral W _)
  apply setLIntegral_mono' hW
  intro x hx
  rw [← ENNReal.ofReal_sub _ (sq_nonneg _), ite_eq_right (hWF x hx)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (a x)^2 - (b x)^2 ≤ max ((a x)^2 - (b x)^2) 0 := le_max_left _ _
    _ ≤ chi x * max ((a x)^2 - (b x)^2) 0 :=
      le_mul_of_one_le_left (le_max_right _ _) (hchiW x hx)

end AreaDeficit
