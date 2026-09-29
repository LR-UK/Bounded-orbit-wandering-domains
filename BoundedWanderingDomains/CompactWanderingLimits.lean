module

/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
public import BoundedWanderingDomains.UniformSphericalConstants

@[expose] public section

open Set Filter Metric Function OnePoint NoWanderingDomains
open scoped Topology

namespace AreaDeficit

/-- Montel and disjointness give a constant spherical subsequential limit
uniformly on an arbitrary compact continuum in the source domain. -/
theorem constant_subsequence_on_compact_continuum
    {F : ℕ → ℂ → ℂ} {U K : Set ℂ} {a b : ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hKc : IsConnected K) (hKU : K ⊆ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hab : a ≠ b)
    (homit : ∀ n z, z ∈ U → F n z ≠ a ∧ F n z ≠ b)
    (hdis : Pairwise (fun n m => Disjoint (F n '' U) (F m '' U))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : OnePoint ℂ,
      TendstoUniformlyOn (fun n z => (F (φ n) z : OnePoint ℂ))
        (fun _ => c) atTop K := by
  let G : ℕ → ℂ → OnePoint ℂ := fun n z => (F n z : OnePoint ℂ)
  have hGh : ∀ n, SphereHolomorphicOn (G n) U :=
    fun n => (hF n).sphereHolomorphicOn hU
  have hN : ∀ z ∈ K, IsNormalAt (range G) z := by
    apply fun z hz => FunctionTheory.isNormalAt_of_two_omitted_values hab hU
      (by rintro _ ⟨n, rfl⟩; exact hGh n)
      (by
        rintro _ ⟨n, rfl⟩ w hw
        exact ⟨fun h => (homit n w hw).1 (OnePoint.coe_injective h),
          fun h => (homit n w hw).2 (OnePoint.coe_injective h), OnePoint.coe_ne_infty _⟩)
      (hKU hz)
  obtain ⟨V, hVo, hKV, hVN⟩ := exists_normal_open_superset_of_compact hK hN
  obtain ⟨x, hx⟩ := hKc.nonempty
  let W := connectedComponentIn (V ∩ U) x
  have hWo : IsOpen W := (hVo.inter hU).connectedComponentIn
  have hxW : x ∈ W := mem_connectedComponentIn ⟨hKV hx, hKU hx⟩
  have hKW : K ⊆ W := hKc.isPreconnected.subset_connectedComponentIn hx
    (subset_inter hKV hKU)
  have hWV : W ⊆ V := (connectedComponentIn_subset _ _).trans inter_subset_left
  have hWU : W ⊆ U := (connectedComponentIn_subset _ _).trans inter_subset_right
  obtain ⟨φ, hφ, g, hg⟩ := (hVN.mono hWV) (fun n => ⟨G n, mem_range_self n⟩)
  have hgd : Pairwise (fun n m => Disjoint ((G (φ n)) '' W) ((G (φ m)) '' W)) := by
    intro n m hnm
    apply disjoint_left.mpr
    rintro p ⟨v, hv, hvp⟩ ⟨w, hw, hwp⟩
    have he : F (φ n) v = F (φ m) w := OnePoint.coe_injective (hvp.trans hwp.symm)
    exact disjoint_left.mp (hdis (hφ.injective.ne hnm))
      (mem_image_of_mem _ (hWU hv)) (he ▸ mem_image_of_mem _ (hWU hw))
  have hconst := limit_constant_of_disjoint_sphere_images hWo
    isPreconnected_connectedComponentIn hxW
    (fun n => FunctionTheory.sphereHolomorphicOn_mono (hGh (φ n)) hWo hWU) hg hgd
  refine ⟨φ, hφ, g x, ?_⟩
  exact ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hg.mono hKW)).congr_right (fun z hz => hconst z (hKW hz))

end AreaDeficit
