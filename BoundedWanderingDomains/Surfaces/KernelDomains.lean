/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SubdomainDensity
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic

/-! # Density comparison for nested open subdomains

This comparison supplies the uniform upper density bound in the kernel
convergence argument: a fixed limiting domain lies inside every approximant.
-/

open Set Function Filter
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- Inclusion of two open subdomains decreases the intrinsic density,
when both densities are expressed in the same ambient coordinate. -/
theorem density_nested_subdomains
    {V W : TopologicalSpace.Opens M} (hWV : W ≤ V)
    (p : DiscCover V) (q : DiscCover W) (hV : Nonempty V) (hW : Nonempty W)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : W} (hx : (x : M) ∈ c.source) :
    p.density (c.subtypeRestr hV) ⟨(x : M), hWV x.property⟩ ≤
      q.density (c.subtypeRestr hW) x := by
  let i : W → V := fun y => ⟨(y : M), hWV y.property⟩
  have hi : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i :=
    (mdifferentiable_subtypeVal_comp_iff V i).mp (mdifferentiable_subtype_val W)
  let d := c.subtypeRestr hW
  let e := c.subtypeRestr hV
  have hd := mdifferentiableOn_subtypeRestr hW hc
  have he := mdifferentiableOn_subtypeRestr hV hc
  have hxd : x ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  have hxe : i x ∈ e.source := by
    simpa only [e, i, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  have hs := q.density_schwarz p hi hd he hxd hxe
  have hid : (e ∘ i ∘ d.symm) =ᶠ[𝓝 (d x)] id := by
    filter_upwards [d.open_target.mem_nhds (d.map_source hxd)] with z hz
    exact d.right_inv hz
  have hder : deriv (e ∘ i ∘ d.symm) (d x) = 1 := by
    rw [hid.deriv_eq]
    simp
  change p.density e (i x) * ‖deriv (e ∘ i ∘ d.symm) (d x)‖ ≤ q.density d x at hs
  simpa only [hder, norm_one, mul_one] using hs

/-- A fixed subdomain provides one upper bound for every containing
domain. No area estimate or convergence assumption enters this bound. -/
theorem density_sequence_bounded_by_subdomain
    (V : ℕ → TopologicalSpace.Opens M) {W : TopologicalSpace.Opens M}
    (hWV : ∀ n, W ≤ V n) (p : ∀ n, DiscCover (V n)) (q : DiscCover W)
    (hV : ∀ n, Nonempty (V n)) (hW : Nonempty W)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : W} (hx : (x : M) ∈ c.source) :
    ∀ n, 0 ≤ (p n).density (c.subtypeRestr (hV n))
        ⟨(x : M), hWV n x.property⟩ ∧
      (p n).density (c.subtypeRestr (hV n))
        ⟨(x : M), hWV n x.property⟩ ≤ q.density (c.subtypeRestr hW) x := by
  intro n
  have hxn : (⟨(x : M), hWV n x.property⟩ : V n) ∈ (c.subtypeRestr (hV n)).source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  exact ⟨((p n).density_pos (mdifferentiableOn_subtypeRestr (hV n) hc) hxn).le,
    density_nested_subdomains (hWV n) (p n) q (hV n) hW hc hx⟩

end AreaDeficit.Surfaces.DiscCover
