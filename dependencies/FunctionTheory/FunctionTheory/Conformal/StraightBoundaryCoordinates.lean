import FunctionTheory.Conformal.StraightBoundaryLimit

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

/-- One-sided boundary limits in a translated and rotated local coordinate.
The original domain may occupy both sides of the boundary arc. -/
theorem exists_boundary_limit_at_straight_side_in_coordinates
    {U : Set ℂ} {f : ℂ → ℂ} {c α : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hα : α ≠ 0) (hR : 0 < R)
    (hhalf : ∀ z ∈ ball (0 : ℂ) R, 0 < z.re → c + α * z ∈ U)
    (hline : ∀ z ∈ ball (0 : ℂ) R, z.re = 0 → c + α * z ∉ U) :
    ∃ a ∈ sphere (0 : ℂ) 1,
      Tendsto f (𝓝[U ∩ {z : ℂ | 0 < ((z - c) / α).re}] c) (𝓝 a) := by
  let φ : ℂ → ℂ := fun z => c + α * z
  let ψ : ℂ → ℂ := fun z => (z - c) / α
  let V := φ ⁻¹' U
  have hφd : Differentiable ℂ φ := by dsimp [φ]; fun_prop
  have hψc : Continuous ψ := by dsimp [ψ]; fun_prop
  have hφψ : ∀ z, φ (ψ z) = z := by intro z; dsimp [φ, ψ]; field_simp; ring
  have hψφ : ∀ z, ψ (φ z) = z := by
    intro z
    dsimp [φ, ψ]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hα]
  have hφbij : BijOn φ V U := by
    refine ⟨fun _ hz => hz, ?_, ?_⟩
    · intro x _ y _ heq
      have h := congrArg ψ heq
      simpa only [hψφ] using h
    · intro y hy
      exact ⟨ψ y, by change φ (ψ y) ∈ U; simpa only [hφψ] using hy, hφψ y⟩
  obtain ⟨a, ha, hlim⟩ := exists_boundary_limit_at_straight_side
    (hU.preimage hφd.continuous) (hf.comp hφd.differentiableOn hφbij.mapsTo)
    (hbij.comp hφbij) hR hhalf hline
  have ht : Tendsto ψ (𝓝[U ∩ {z : ℂ | 0 < ((z - c) / α).re}] c)
      (𝓝[V ∩ {z : ℂ | 0 < z.re}] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := hψc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[U ∩ {z : ℂ | 0 < ((z - c) / α).re}] c ≤ 𝓝 c)
      simpa only [ψ, sub_self, zero_div] using h
    · filter_upwards [self_mem_nhdsWithin] with z hz
      refine ⟨?_, hz.2⟩
      change φ (ψ z) ∈ U
      simpa only [hφψ] using hz.1
  refine ⟨a, ha, ?_⟩
  simpa only [Function.comp_def, hφψ] using hlim.comp ht

end FunctionTheory
