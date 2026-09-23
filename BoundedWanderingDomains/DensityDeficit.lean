import BoundedWanderingDomains.PositivePart
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Filter Set InnerProductSpace Laplacian
open scoped Topology ContDiff ENNReal

namespace AreaDeficit

/-- The curvature −1 density deficit estimate, including finite punctures.
The integral is extended nonnegative: its finiteness is a conclusion.
All Laplacians here are mathlib's Euclidean Laplacian on `ℂ`.
-/
theorem density_deficit_cutoff
    (F : Finset ℂ) {V : Set ℂ} (hV : IsOpen V)
    {a b chi : ℂ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hchi : ContDiff ℝ 2 chi) (hc : HasCompactSupport chi)
    (hchi0 : ∀ x, 0 ≤ chi x) (hsupp : tsupport chi ⊆ V)
    (ha : ∀ x ∈ V, x ∉ F → 0 < a x ∧ ContDiffAt ℝ 2 a x)
    (hb : ∀ x ∈ V, x ∉ F → 0 < b x ∧ ContDiffAt ℝ 2 b x)
    (hca : ∀ x ∈ V, x ∉ F → Δ (fun z => Real.log (a z)) x = (a x)^2)
    (hcb : ∀ x ∈ V, x ∉ F → Δ (fun z => Real.log (b z)) x = (b x)^2)
    (hbound : ∀ x ∈ V, x ∉ F → max (Real.log (a x) - Real.log (b x)) 0 ≤ M) :
    (∫⁻ x, ENNReal.ofReal (chi x *
      (if x ∈ F then 0 else max ((a x)^2 - (b x)^2) 0))) ≤
        ENNReal.ofReal (M * ∫ x, |Δ chi x|) := by
  let u : ℂ → ℝ := fun x => Real.log (a x) - Real.log (b x)
  have hal (x) (hx : x ∈ V) (hf : x ∉ F) :
      ContDiffAt ℝ 2 (fun z => Real.log (a z)) x :=
    (ha x hx hf).2.log (ne_of_gt (ha x hx hf).1)
  have hbl (x) (hx : x ∈ V) (hf : x ∉ F) :
      ContDiffAt ℝ 2 (fun z => Real.log (b z)) x :=
    (hb x hx hf).2.log (ne_of_gt (hb x hx hf).1)
  have hu (x) (hx : x ∈ V) (hf : x ∉ F) : ContDiffAt ℝ 2 u x :=
    (hal x hx hf).sub (hbl x hx hf)
  have hdu (x) (hx : x ∈ V) (hf : x ∉ F) : Δ u x = (a x)^2 - (b x)^2 := by
    have hh := (hal x hx hf).laplacian_sub (hbl x hx hf)
    simpa only [Pi.sub_def, hca x hx hf, hcb x hx hf] using hh
  have hup (p) (hp : p ∈ tsupport chi) (_hf : p ∈ F) :
      ∃ B : ℝ, ∀ᶠ z in 𝓝 p, z ∉ F → u z ≤ B := by
    refine ⟨M, ?_⟩
    filter_upwards [hV.mem_nhds (hsupp hp)] with z hz hf
    exact (le_max_left (u z) 0).trans (hbound z hz hf)
  have hpos (x) (hx : x ∈ tsupport chi) (hf : x ∉ F) (hp : 0 < u x) : 0 ≤ Δ u x := by
    rw [hdu x (hsupp hx) hf]
    have hab : b x < a x := (Real.log_lt_log_iff (hb x (hsupp hx) hf).1
      (ha x (hsupp hx) hf).1).mp (sub_pos.mp hp)
    have hbp := (hb x (hsupp hx) hf).1
    nlinarith
  have hneg (x) (hx : x ∈ tsupport chi) (hf : x ∉ F) (hn : u x ≤ 0) : Δ u x ≤ 0 := by
    rw [hdu x (hsupp hx) hf]
    have hab : a x ≤ b x := (Real.log_le_log_iff (ha x (hsupp hx) hf).1
      (hb x (hsupp hx) hf).1).mp (sub_nonpos.mp hn)
    have hap := (ha x (hsupp hx) hf).1
    nlinarith
  have hmain := positive_part_cutoff F hM0 hchi hc hchi0
    (fun x hx => hu x (hsupp hx)) hup
    (fun x hx => hbound x (hsupp hx)) hpos hneg
  convert hmain using 1
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ tsupport chi
  · by_cases hf : x ∈ F
    · simp [hf]
    · simp [hf, hdu x (hsupp hx) hf]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end AreaDeficit
