import ComplexApproximation.Topology.FillingStraightChannels

open Set Complex

namespace ComplexApproximation

/-- Filling bounded holes preserves a horizontal strip bound. -/
theorem fill_preserves_im_bound {E : Set ℂ} {c H : ℝ}
    (hE : ∀ z ∈ E, |z.im - c| ≤ H) :
    ∀ z ∈ fill E, |z.im - c| ≤ H := by
  intro z hz
  exact fill_preserves_channel_in_vertical_slab
    (A := z.re - 1) (B := z.re + 1) (fun w hw _ _ => hE w hw) z hz
    (by linarith) (by linarith)

/-- A leftward ray shows that filling cannot cross a common lower bound
on real parts. -/
theorem fill_preserves_re_lower_bound {E : Set ℂ} {L : ℝ}
    (hE : ∀ z ∈ E, L ≤ z.re) : ∀ z ∈ fill E, L ≤ z.re := by
  intro z hz
  by_contra hn
  have hsmall : z.re < L := lt_of_not_ge hn
  apply not_isBounded_component_of_affine_ray (E := Eᶜ) (z := z) (v := -1)
    (by norm_num) _ hz
  intro t ht hw
  have hb := hE _ hw
  have hre : (z + (t : ℂ) * (-1)).re = z.re - t := by simp [sub_eq_add_neg]
  rw [hre] at hb
  linarith

end ComplexApproximation
