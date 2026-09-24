/- 
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SpherePole
import BoundedWanderingDomains.AreaAnchorFree
import FunctionTheory.RiemannSphere.Coordinates

/-!
# Compact sets in sphere charts

The partial homeomorphism omitting any chosen sphere point identifies its
complement with the complex plane. Compact sets avoiding the pole become
compact planar sets. This supplies the topological input to transferring
the curvature −1 area estimates to the sphere.
-/

open Set OnePoint
open scoped Topology RiemannSphere ENNReal

namespace AreaDeficit

private theorem compact_preimage_of_open_partial_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (hs : e.source = Set.univ)
    {K : Set Y} (hK : IsCompact K) (hKt : K ⊆ e.target) :
    IsCompact (e ⁻¹' K) := by
  have heq : e ⁻¹' K = e.symm '' K := by
    ext z
    constructor
    · intro hz
      exact ⟨e z, hz, e.left_inv (by simp [hs])⟩
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ K
      rw [e.right_inv (hKt hy)]
      exact hy
  rw [heq]
  exact hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)

/-- A Möbius chart from the complex plane onto the sphere with one pole
omitted. -/
noncomputable def spherePoleChart (p : OnePoint ℂ) :
    OpenPartialHomeomorph ℂ (OnePoint ℂ) :=
  p.rec RiemannSphere.coeOpenPartialHomeomorph RiemannSphere.omittedPointParam

@[simp] theorem spherePoleChart_source (p : OnePoint ℂ) :
    (spherePoleChart p).source = Set.univ := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe a => exact RiemannSphere.omittedPointParam_source a

@[simp] theorem spherePoleChart_target (p : OnePoint ℂ) :
    (spherePoleChart p).target = {p}ᶜ := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe a => exact RiemannSphere.omittedPointParam_target a

/-- Closed omitted sets in a sphere domain remain closed in a pole chart. -/
theorem closed_sphere_set_in_pole_chart {A : Set (OnePoint ℂ)}
    (hA : IsClosed A) (p : OnePoint ℂ) :
    IsClosed ((spherePoleChart p) ⁻¹' A) := by
  have hcont : Continuous (spherePoleChart p) :=
    continuousOn_univ.mp (by simpa [spherePoleChart_source] using
      (spherePoleChart p).continuousOn)
  exact hA.preimage hcont

/-- A compact sphere set avoiding the pole has compact planar coordinates. -/
theorem compact_sphere_set_in_pole_chart {K : Set (OnePoint ℂ)}
    (hK : IsCompact K) {p : OnePoint ℂ} (hp : p ∉ K) :
    IsCompact ((spherePoleChart p) ⁻¹' K) := by
  have hKt : K ⊆ (spherePoleChart p).target := by
    intro z hz
    rw [spherePoleChart_target]
    exact fun hzp => hp (hzp ▸ hz)
  exact compact_preimage_of_open_partial_homeomorph
    (spherePoleChart p) (spherePoleChart_source p) hK hKt

/-- The planar compact-removal estimate applies uniformly to the coordinate
images of sphere compact sets avoiding the same pole. The integral remains
in planar coordinates until conformal invariance of the area form is proved. -/
theorem uniform_compact_gain_in_pole_chart
    {K L : Set (OnePoint ℂ)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) {p : OnePoint ℂ} (hpK : p ∉ K) (hpL : p ∉ L) :
    ∃ T : ℝ≥0∞, T ≠ ⊤ ∧ ∀ (A : Set ℂ) (hA : IsClosed A)
      {c d : ℂ} (hcd : c ≠ d) (hc : c ∈ A) (hd : d ∈ A),
      (∫⁻ z in ((spherePoleChart p) ⁻¹' L) ∩ Aᶜ,
        hyperbolicAreaWeight (A ∪ ((spherePoleChart p) ⁻¹' K))
          (hA.union (compact_sphere_set_in_pole_chart hK hpK).isClosed)
          hcd (Or.inl hc) (Or.inl hd) z -
        hyperbolicAreaWeight A hA hcd hc hd z) ≤ T := by
  have hLKchart : Disjoint ((spherePoleChart p) ⁻¹' L)
      ((spherePoleChart p) ⁻¹' K) := by
    apply Set.disjoint_left.mpr
    intro z hzL hzK
    exact Set.disjoint_left.mp hKL hzK hzL
  exact uniform_compact_gain_plane
    (compact_sphere_set_in_pole_chart hL hpL)
    (compact_sphere_set_in_pole_chart hK hpK) hLKchart

end AreaDeficit

#print axioms AreaDeficit.compact_sphere_set_in_pole_chart
#print axioms AreaDeficit.uniform_compact_gain_in_pole_chart
