import FunctionTheory.RiemannSphere.RiemannMapping
import FunctionTheory.Conformal.ReflectionInjectivity
import FunctionTheory.Conformal.StripEndCoordinates
import FunctionTheory.Conformal.HalfPlaneKernel
import FunctionTheory.Conformal.StripEndAsymptotics
import FunctionTheory.Conformal.RiemannMapping
import FunctionTheory.Conformal.KernelConvergence
import FunctionTheory.Conformal.ImaginaryBounds
import FunctionTheory.Conformal.StripEndMap

/-! # Main classical function-theory results

This gallery refers to the exact checked declarations. Upstream Tau Ceti names
are retained; the actual-domain and kernel-convergence interfaces are additional
results. See `MAIN_RESULTS.md` for hypotheses and mathematical explanations.
-/

namespace FunctionTheory.MainTheorems

open Set Metric Filter Asymptotics
open scoped Topology

/-- The public Tau Ceti statement, reproduced without changing its hypotheses. -/
theorem riemann_mapping {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, BijOn f U (ball 0 1) ∧ DifferentiableOn ℂ f U ∧
      ∀ z ∈ U, deriv f z ≠ 0 :=
  TauCeti.riemannMapping hUo hUc hU

/-- A basepoint and positive real derivative determine the normalized map. -/
theorem normalized_riemann_mapping {U : Set ℂ} {z₀ : ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, TauCeti.IsNormalizedRiemannMapOn f U z₀ ∧
      ∀ g : ℂ → ℂ, TauCeti.IsNormalizedRiemannMapOn g U z₀ → EqOn g f U :=
  TauCeti.riemannMapping_normalized hUo hUc hU hz₀

/-- Neither direction of this map is defined outside its mathematical domain. -/
theorem riemann_mapping_on_domain {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ e : U ≃ₜ ball (0 : ℂ) 1,
      FunctionTheory.IsHolomorphicFunctionOn U (fun z => (e z : ℂ)) ∧
      FunctionTheory.IsHolomorphicFunctionOn (ball (0 : ℂ) 1)
        (fun z => (e.symm z : ℂ)) :=
  FunctionTheory.exists_riemannMap_on_domain hUo hUc hU

alias schwarz_reflection := TauCeti.exists_differentiableOn_eqOn_conj_of_symmetric
alias montel := TauCeti.montel
alias hurwitz_injectivity := TauCeti.hurwitz_injOn
alias bounded_kernel_convergence := FunctionTheory.normalized_riemannMaps_tendsto_on_bounded_kernel

alias halfplane_kernel_convergence := FunctionTheory.normalized_riemannMaps_tendsto_on_halfPlane_kernel
alias reflected_strip_end_derivative_estimate := FunctionTheory.stripEnd_logDeriv_estimate

alias conformal_schwarz_reflection := FunctionTheory.exists_positive_conformal_reflection_at_zero
alias strip_end_asymptotics := FunctionTheory.stripEnd_estimates_of_reflected_map

/-- The reused public Carathéodory continuity theorem, with its exact scope. -/
theorem caratheodory_continuity {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : Bornology.IsBounded (f '' ball c r))
    (hJ : TauCeti.IsJordanCurve (frontier (f '' ball c r))) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) :=
  TauCeti.exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier hr hf hinj hb hJ

/-- Boundary-normalized Riemann mapping, with functions on their actual domains. -/
theorem boundary_normalized_riemann_map {Ω : Set ℂ} {z₀ p : ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩJ : TauCeti.IsJordanCurve (frontier Ω))
    (hz₀ : z₀ ∈ Ω) (hp : p ∈ frontier Ω) :
    ∃ (e : ball (0 : ℂ) 1 ≃ₜ Ω) (G : C(closedBall (0 : ℂ) 1, ℂ)),
      IsHolomorphicFunctionOn (ball (0 : ℂ) 1) (fun z => (e z : ℂ)) ∧
      IsHolomorphicFunctionOn Ω (fun z => (e.symm z : ℂ)) ∧
      (∀ z : ball (0 : ℂ) 1, G ⟨z, ball_subset_closedBall z.property⟩ = (e z : ℂ)) ∧
      G ⟨0, mem_closedBall_self zero_le_one⟩ = z₀ ∧ G ⟨1, by simp⟩ = p ∧ range G = closure Ω :=
  exists_boundary_normalized_disc_map_on_domain hΩo hΩc hΩb hΩJ hz₀ hp

/-- A conformal strip map normalized at an interior point and the right end,
with both quantitative end estimates. The Jordan condition on the exponential
image is explicit; constructing such domains is a separate geometric task. -/
theorem normalized_strip_map {U : Set ℂ} {z₀ : ℂ} {L R : ℝ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUS : U ⊆ standardHorizontalStrip) (hleft : ∀ z ∈ U, L ≤ z.re)
    (htail : ∀ z ∈ standardHorizontalStrip, R < z.re → z ∈ U)
    (hJordan : TauCeti.IsJordanCurve (frontier (exponentialImage U))) (hz₀ : z₀ ∈ U) :
    ∃ (φ : ℂ → ℂ) (ρ : ℝ), DifferentiableOn ℂ φ U ∧
      BijOn φ U standardHorizontalStrip ∧ φ z₀ = 0 ∧
      (fun z => deriv φ z - 1) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      (fun z => φ z - (z + (ρ : ℂ))) =O[comap Complex.re atTop ⊓ 𝓟 U]
        (fun z => Real.exp (-z.re)) ∧
      Tendsto (fun z => (φ z).re) (comap Complex.re atTop ⊓ 𝓟 U) atTop :=
  exists_normalized_strip_map_of_jordan_exponential_image hUo hUc hUS hleft htail hJordan hz₀

/-- Riemann mapping also applies to domains containing infinity. Both maps
are defined only on their actual domains; the sphere omits two distinct points. -/
theorem spherical_riemann_mapping
    (U : TopologicalSpace.Opens (OnePoint ℂ))
    (hUc : IsSimplyConnected (U : Set (OnePoint ℂ)))
    (hU : ∃ p q : OnePoint ℂ, p ∉ U ∧ q ∉ U ∧ p ≠ q) :
    ∃ e : U ≃ₜ unitDiskDomain,
      ContMDiff OneDimension.I OneDimension.I (↑(⊤ : ℕ∞)) e ∧
      ContMDiff OneDimension.I OneDimension.I (↑(⊤ : ℕ∞)) e.symm :=
  exists_riemannMap_on_sphere_domain U hUc hU

end FunctionTheory.MainTheorems
