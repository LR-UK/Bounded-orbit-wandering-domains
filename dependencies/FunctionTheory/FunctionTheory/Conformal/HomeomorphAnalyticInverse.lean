import TauCeti.Analysis.Complex.Conformal.Biholomorph

open Set Filter Function
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- The inverse of a plane homeomorphism is holomorphic at the image of any
point where the homeomorphism is holomorphic. Injectivity supplies the
nonvanishing derivative; no extra derivative hypothesis is required. -/
theorem analyticAt_homeomorph_symm (e : ℂ ≃ₜ ℂ) {z : ℂ}
    (hz : AnalyticAt ℂ (e : ℂ → ℂ) z) : AnalyticAt ℂ (e.symm : ℂ → ℂ) (e z) := by
  let U := {w : ℂ | AnalyticAt ℂ (e : ℂ → ℂ) w}
  have hU : IsOpen U := isOpen_analyticAt ℂ (e : ℂ → ℂ)
  have he : DifferentiableOn ℂ (e : ℂ → ℂ) U := fun w hw => hw.differentiableAt.differentiableWithinAt
  have hI : IsOpen ((e : ℂ → ℂ) '' U) := e.isOpenMap U hU
  have hez : e z∈(e : ℂ → ℂ) '' U := ⟨z,hz,rfl⟩
  have hInv : AnalyticAt ℂ (invFunOn (e : ℂ → ℂ) U) (e z) :=
    (DifferentiableOn.invFunOn he hU e.injective.injOn).analyticAt (hI.mem_nhds hez)
  apply hInv.congr
  filter_upwards [hI.mem_nhds hez] with w hw
  obtain ⟨a,ha,rfl⟩ := hw
  simpa only [e.symm_apply_apply] using e.injective.injOn.leftInvOn_invFunOn ha

/-- Holomorphy of the inverse on the image of an arbitrary set. -/
theorem analyticOnNhd_homeomorph_symm_image (e : ℂ ≃ₜ ℂ) {K : Set ℂ}
    (hK : AnalyticOnNhd ℂ (e : ℂ → ℂ) K) :
    AnalyticOnNhd ℂ (e.symm : ℂ → ℂ) (e '' K) := by
  rintro w ⟨z,hz,rfl⟩
  exact analyticAt_homeomorph_symm e (hK z hz)

end FunctionTheory
