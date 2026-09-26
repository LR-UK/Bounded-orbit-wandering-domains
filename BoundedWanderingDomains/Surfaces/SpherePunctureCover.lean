/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.LegacyDiscCoverBridge
import RiemannDynamics.Uniformization.HolomorphicEquiv

/-! # A concrete disc cover of the thrice-punctured sphere -/

open Set Topology TopologicalSpace OnePoint
open scoped Manifold

namespace AreaDeficit.Surfaces

/-- The normalized thrice-punctured sphere. -/
def normalizedThricePuncturedSphere : Opens ℂ̂ :=
  ⟨({(∞ : ℂ̂), ((0 : ℂ) : ℂ̂), ((1 : ℂ) : ℂ̂)} : Set ℂ̂)ᶜ,
    (((Set.finite_singleton (((1 : ℂ) : ℂ̂))).insert
      (((0 : ℂ) : ℂ̂))).insert (∞ : ℂ̂)).isClosed.isOpen_compl⟩

/-- The normalized thrice-punctured sphere has a concrete holomorphic
universal covering by the unit disc. -/
theorem DiscCover.nonempty_normalizedThricePuncturedSphere :
    Nonempty (DiscCover normalizedThricePuncturedSphere) := by
  let U : Opens ℂ̂ := normalizedThricePuncturedSphere
  have hinf : (∞ : ℂ̂) ∉ (U : Set ℂ̂) := by
    simp [U, normalizedThricePuncturedSphere]
  obtain ⟨V, hVimg, ⟨e⟩⟩ :=
    RiemannDynamics.exists_diffeomorph_opens_planar U hinf
  let P : Finset ℂ := {0, 1}
  let W : Opens ℂ :=
    ⟨((↑P : Set ℂ)ᶜ), P.finite_toSet.isClosed.isOpen_compl⟩
  have hPcard : 2 ≤ P.card := by simp [P]
  have hVW : V = W := by
    apply Opens.ext
    ext z
    have hzV : z ∈ (V : Set ℂ) ↔ ((z : ℂ̂) ∈ (U : Set ℂ̂)) := by
      constructor
      · intro hz
        change (z : ℂ̂) ∈ (U : Set ℂ̂)
        rw [← hVimg]
        exact ⟨z, hz, rfl⟩
      · intro hz
        change (z : ℂ̂) ∈ (U : Set ℂ̂) at hz
        rw [← hVimg] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        have : w = z := OnePoint.coe_injective hwz
        simpa [this] using hw
    change z ∈ (V : Set ℂ) ↔ z ∈ (W : Set ℂ)
    rw [hzV]
    simp [U, W, P, normalizedThricePuncturedSphere]
  subst V
  obtain ⟨p⟩ := DiscCover.nonempty_finitelyPuncturedPlane P hPcard
  exact ⟨p.transDiffeomorph e.symm⟩

/-- Deleting any three distinct points from the Riemann sphere produces a
surface with a holomorphic universal disc covering. -/
theorem DiscCover.nonempty_sphere_compl_three {a b c : ℂ̂}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let U : Opens ℂ̂ :=
      ⟨({a, b, c} : Set ℂ̂)ᶜ,
        (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
    Nonempty (DiscCover U) := by
  let U : Opens ℂ̂ :=
    ⟨({a, b, c} : Set ℂ̂)ᶜ,
      (((Set.finite_singleton c).insert b).insert a).isClosed.isOpen_compl⟩
  obtain ⟨g, hga, hgb, hgc⟩ :=
    RiemannDynamics.exists_gl_smul_eq_zero_one_infty hab hac hbc
  obtain ⟨eg, heg⟩ := RiemannDynamics.exists_gl_smul_diffeomorph g
  obtain ⟨V, hVimg, ⟨e⟩⟩ :=
    RiemannDynamics.exists_diffeomorph_opens_image eg U
  have hV : V = normalizedThricePuncturedSphere := by
    apply Opens.ext
    rw [hVimg]
    change (eg.toHomeomorph : ℂ̂ → ℂ̂) '' ({a, b, c} : Set ℂ̂)ᶜ =
      ({(∞ : ℂ̂), ((0 : ℂ) : ℂ̂), ((1 : ℂ) : ℂ̂)} : Set ℂ̂)ᶜ
    rw [eg.toHomeomorph.image_compl]
    congr 1
    have hegh : (eg.toHomeomorph : ℂ̂ → ℂ̂) = (g • ·) := heg
    rw [hegh]
    ext z
    simp [hga, hgb, hgc, or_comm, or_left_comm, or_assoc]
  subst V
  obtain ⟨p⟩ := DiscCover.nonempty_normalizedThricePuncturedSphere
  exact ⟨p.transDiffeomorph e.symm⟩

end AreaDeficit.Surfaces

#print axioms AreaDeficit.Surfaces.DiscCover.nonempty_normalizedThricePuncturedSphere
#print axioms AreaDeficit.Surfaces.DiscCover.nonempty_sphere_compl_three
