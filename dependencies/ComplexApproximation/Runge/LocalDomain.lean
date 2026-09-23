import Runge.Holomorphic
import FunctionTheory.Holomorphic

/-!
# Runge approximation for functions with their actual domain

`IsHolomorphicFunctionOn U f` is a local property of `f : U → ℂ`.
Local representatives are used only to connect the domain-restricted function
to Mathlib's differential calculus. No values outside `U` are part of the input.
`HasHolomorphicExtension K f` expresses the neighbourhood-extension hypothesis
for a function whose domain is just the compact set `K`.
-/

open Filter Set Polynomial
open scoped Topology

namespace Runge

/-- Compatibility name for holomorphy on an actual domain. -/
abbrev IsHolomorphicFunctionOn := FunctionTheory.IsHolomorphicFunctionOn

/-- Compatibility name for the internal extension used in ambient calculus. -/
noncomputable abbrev domainExtension := @FunctionTheory.domainExtension

@[simp] theorem domainExtension_apply {U : Set ℂ} (f : U → ℂ)
    (z : ℂ) (hz : z ∈ U) : domainExtension f z = f ⟨z, hz⟩ :=
  FunctionTheory.domainExtension_apply f z hz

theorem IsHolomorphicFunctionOn.differentiableOn_extension
    {U : Set ℂ} (hU : IsOpen U) {f : U → ℂ}
    (hf : IsHolomorphicFunctionOn U f) : DifferentiableOn ℂ (domainExtension f) U :=
  FunctionTheory.IsHolomorphicFunctionOn.differentiableOn_extension hU hf

theorem isHolomorphicFunctionOn_restrict {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    IsHolomorphicFunctionOn U (fun z => g z) :=
  FunctionTheory.isHolomorphicFunctionOn_restrict hU hg

/-- The neighbourhood-extension condition for a function defined just on `K`. -/
def HasHolomorphicExtension (K : Set ℂ) (f : K → ℂ) : Prop :=
  ∃ (U : Set ℂ) (_hU : IsOpen U) (hKU : K ⊆ U) (g : U → ℂ),
    IsHolomorphicFunctionOn U g ∧ ∀ z : K, g ⟨z, hKU z.property⟩ = f z

theorem rational_approximation_on_domain (K : Set ℂ) (hK : IsCompact K)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      ∀ (z : ℂ) (hz : z ∈ K), ‖f ⟨z, hKU hz⟩ - p.eval z / q.eval z‖ < ε := by
  obtain ⟨p, q, hq, hpq⟩ := rational_approximation_of_holomorphic K hK U hU hKU
    (domainExtension f) (hf.differentiableOn_extension hU) ε hε
  exact ⟨p, q, hq, fun z hz => by simpa [domainExtension, hKU hz] using hpq z hz⟩

theorem prescribed_poles_approximation_on_domain (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      ∀ (z : ℂ) (hz : z ∈ K), ‖f ⟨z, hKU hz⟩ - p.eval z / q.eval z‖ < ε := by
  obtain ⟨p, q, hq, hqK, hqP, hpq⟩ := prescribed_poles_approximation_of_holomorphic
    K hK P hP U hU hKU (domainExtension f) (hf.differentiableOn_extension hU) ε hε
  exact ⟨p, q, hq, hqK, hqP,
    fun z hz => by simpa [domainExtension, hKU hz] using hpq z hz⟩

theorem polynomial_approximation_on_domain (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : U → ℂ) (hf : IsHolomorphicFunctionOn U f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ (z : ℂ) (hz : z ∈ K), ‖f ⟨z, hKU hz⟩ - p.eval z‖ < ε := by
  obtain ⟨p, hp⟩ := polynomial_approximation_of_holomorphic K hK hconn U hU hKU
    (domainExtension f) (hf.differentiableOn_extension hU) ε hε
  exact ⟨p, fun z hz => by simpa [domainExtension, hKU hz] using hp z hz⟩

theorem rational_approximation_on_compact (K : Set ℂ) (hK : IsCompact K)
    (f : K → ℂ) (hf : HasHolomorphicExtension K f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      ∀ z : K, ‖f z - p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε := by
  obtain ⟨U, hU, hKU, g, hg, heq⟩ := hf
  obtain ⟨p, q, hq, hpq⟩ := rational_approximation_on_domain K hK U hU hKU g hg ε hε
  exact ⟨p, q, hq, fun z => by simpa only [heq z] using hpq z z.property⟩

theorem prescribed_poles_approximation_on_compact (K : Set ℂ) (hK : IsCompact K)
    (P : Set ℂ) (hP : MeetsBoundedComplementComponents K P)
    (f : K → ℂ) (hf : HasHolomorphicExtension K f) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ a : ℂ, q.eval a = 0 → a ∈ P) ∧
      ∀ z : K, ‖f z - p.eval (z : ℂ) / q.eval (z : ℂ)‖ < ε := by
  obtain ⟨U, hU, hKU, g, hg, heq⟩ := hf
  obtain ⟨p, q, hq, hqK, hqP, hpq⟩ :=
    prescribed_poles_approximation_on_domain K hK P hP U hU hKU g hg ε hε
  exact ⟨p, q, hq, hqK, hqP, fun z => by simpa only [heq z] using hpq z z.property⟩

theorem polynomial_approximation_on_compact (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) (f : K → ℂ) (hf : HasHolomorphicExtension K f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z : K, ‖f z - p.eval (z : ℂ)‖ < ε := by
  obtain ⟨U, hU, hKU, g, hg, heq⟩ := hf
  obtain ⟨p, hp⟩ := polynomial_approximation_on_domain K hK hconn U hU hKU g hg ε hε
  exact ⟨p, fun z => by simpa only [heq z] using hp z z.property⟩

end Runge
