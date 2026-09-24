/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.SphericalShrinking

open Set Filter Metric OnePoint
open scoped Topology

namespace AreaDeficit

/-- Uniform spherical convergence to a finite constant is equivalent to
uniform Euclidean convergence to that constant. -/
theorem uniform_spherical_finite_iff {F : ℕ → ℂ → ℂ} {K : Set ℂ} {a : ℂ} :
    TendstoUniformlyOn (fun n z => (F n z : OnePoint ℂ)) (fun _ => (a : OnePoint ℂ))
      atTop K ↔ TendstoUniformlyOn F (fun _ => a) atTop K := by
  rw [← tendsto_prod_principal_iff, ← tendsto_prod_principal_iff]
  exact OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff.symm

/-- Uniform spherical convergence to infinity is uniform escape in modulus. -/
theorem uniform_spherical_infty_iff {F : ℕ → ℂ → ℂ} {K : Set ℂ} :
    TendstoUniformlyOn (fun n z => (F n z : OnePoint ℂ)) (fun _ => ∞) atTop K ↔
      ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖F n z‖ := by
  rw [← tendsto_prod_principal_iff]
  have heq : Tendsto (fun p : ℕ × ℂ => (F p.1 p.2 : OnePoint ℂ))
      (atTop ×ˢ 𝓟 K) (𝓝 ∞) ↔
      Tendsto (fun p : ℕ × ℂ => ‖F p.1 p.2‖) (atTop ×ˢ 𝓟 K) atTop := by
    rw [tendsto_norm_atTop_iff_cobounded, cobounded_eq_cocompact,
      ← coclosedCompact_eq_cocompact, ← OnePoint.comap_coe_nhds_infty,
      tendsto_comap_iff]
    rfl
  change Tendsto (fun p : ℕ × ℂ => (F p.1 p.2 : OnePoint ℂ))
    (atTop ×ˢ 𝓟 K) (𝓝 ∞) ↔ _
  rw [heq]
  constructor
  · intro h R
    simpa only [eventually_prod_principal_iff] using h.eventually_gt_atTop R
  · intro h
    apply Filter.tendsto_atTop.2
    intro R
    simpa only [eventually_prod_principal_iff] using
      (h R).mono (fun n hn z hz => (hn z hz).le)

end AreaDeficit
