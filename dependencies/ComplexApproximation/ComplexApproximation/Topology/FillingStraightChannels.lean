import ComplexApproximation.Topology.HorizontalEscape
import ComplexApproximation.Topology.Filling

open Set Metric Complex

namespace ComplexApproximation

/-- Filling bounded holes does not widen a horizontal channel in a vertical
slab: upward and downward rays witness unbounded complementary components. -/
theorem fill_preserves_channel_in_vertical_slab
    {E : Set ℂ} {A B c h : ℝ}
    (hchannel : ∀ z ∈ E, A < z.re → z.re < B → |z.im - c| ≤ h) :
    ∀ z ∈ fill E, A < z.re → z.re < B → |z.im - c| ≤ h := by
  intro z hz hzA hzB
  by_contra hn
  have hout : h < |z.im - c| := lt_of_not_ge hn
  rcases lt_abs.mp hout with hupper | hlower
  · apply not_isBounded_component_of_affine_ray (E := Eᶜ) (z := z) (v := I) I_ne_zero _ hz
    intro t ht hw
    have hre : (z + (t : ℂ) * I).re = z.re := by simp
    have him : (z + (t : ℂ) * I).im = z.im + t := by simp
    have hc := (abs_le.mp (hchannel _ hw (by simpa [hre] using hzA)
      (by simpa [hre] using hzB))).2
    rw [him] at hc
    linarith
  · apply not_isBounded_component_of_affine_ray (E := Eᶜ) (z := z) (v := -I)
      (neg_ne_zero.mpr I_ne_zero) _ hz
    intro t ht hw
    have hre : (z + (t : ℂ) * -I).re = z.re := by simp
    have him : (z + (t : ℂ) * -I).im = z.im - t := by simp [sub_eq_add_neg]
    have hc := (abs_le.mp (hchannel _ hw (by simpa [hre] using hzA)
      (by simpa [hre] using hzB))).1
    rw [him] at hc
    linarith

/-- The interior of the filling has the same gate-width bound at the right
edge of the slab, even when the original closed set includes a vertical edge
of the larger halfstrip there. -/
theorem interior_fill_gate_bound
    {E : Set ℂ} {A B c h : ℝ} (hAB : A < B)
    (hchannel : ∀ z ∈ E, A < z.re → z.re < B → |z.im - c| ≤ h) :
    ∀ z ∈ interior (fill E), z.re = B → |z.im - c| ≤ h := by
  intro z hz hzB
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let t := min (ε / 2) ((B - A) / 2)
  have ht : 0 < t := lt_min (half_pos hε) (half_pos (sub_pos.mpr hAB))
  have htε : t < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have htBA : t < B - A := (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hAB))
  let w := z - (t : ℂ)
  have hwball : w ∈ ball z ε := by
    change dist (z - (t : ℂ)) z < ε
    simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht] using htε
  have hwfill : w ∈ fill E := interior_subset (hball hwball)
  have hwre : w.re = B - t := by simp [w, hzB]
  have hwim : w.im = z.im := by simp [w]
  have hb := fill_preserves_channel_in_vertical_slab hchannel w hwfill
    (by rw [hwre]; linarith) (by rw [hwre]; linarith)
  simpa only [hwim] using hb

end ComplexApproximation
