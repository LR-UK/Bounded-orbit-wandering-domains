module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.BKL.ComponentRecovery

@[expose] public section

/-! # Recovering components with control only on added points

The exceptional set controls the images of points added by analytic completion.
It need not contain every global singular value encountered by the completed
orbits. This distinction permits application to individual inverse components.
-/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

omit [LocallyCompactSpace X] [IsManifold 𝓘(ℂ) 1 X] in
theorem mem_trapped_of_completed_orbit_avoids_added_images
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) {E : Set X} {x : X}
    (hlanding : ∀ n, (f.denseCompletion.totalize^[n]) x ∉ f.source →
      (f.denseCompletion.totalize^[n + 1]) x ∈ E)
    (havoid : ¬ ∃ n, (f.denseCompletion.totalize^[n]) x ∈ E) : x ∈ f.trapped := by
  apply f.mem_trapped_of_denseCompletion_stays hf
  intro n
  by_contra hn
  exact havoid ⟨n + 1, hlanding n hn⟩

omit [IsManifold 𝓘(ℂ) 1 X] in
theorem good_completed_region_subset_component_of_added_images
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (W : TopologicalSpace.Opens X) (hWc : IsConnected (W : Set X))
    (hWnormal : f.denseCompletion.IsNormalOn W) {E : Set X}
    (hiso : ∀ x ∈ (W : Set X), ∀ᶠ y in 𝓝 x,
      (∃ n, (f.denseCompletion.totalize^[n]) y ∈ E) → y = x)
    (hlanding : ∀ x ∈ (W : Set X), ∀ n,
      (f.denseCompletion.totalize^[n]) x ∉ f.source →
        (f.denseCompletion.totalize^[n + 1]) x ∈ E)
    {a : X} (haW : a ∈ W) (haE : ¬ ∃ n, (f.denseCompletion.totalize^[n]) a ∈ E) :
    (W : Set X) \ {x | ∃ n, (f.denseCompletion.totalize^[n]) x ∈ E} ⊆
      connectedComponentIn f.omega a := by
  let A := (W : Set X) \ {x | ∃ n, (f.denseCompletion.totalize^[n]) x ∈ E}
  have haA : a ∈ A := ⟨haW, haE⟩
  obtain ⟨hAo, hAc⟩ := BKL.isOpen_isConnected_diff_of_locally_isolated W hWc hiso ⟨a, haA⟩
  have hAtr : A ⊆ f.trapped := by
    intro x hx
    exact f.mem_trapped_of_completed_orbit_avoids_added_images hf
      (hlanding x hx.1) hx.2
  have hn : f.IsNormalOn A := f.isNormalOn_of_denseCompletion hf hAtr
    (f.denseCompletion.isNormalOn_mono sdiff_subset hWnormal)
  have hAn : A ⊆ f.omega := fun x hx => ⟨A, hAo, hx, hAtr, hn⟩
  exact hAc.isPreconnected.subset_connectedComponentIn haA hAn

variable [FirstCountableTopology X]

local instance completionRecoveryUniformSpace : UniformSpace (OnePoint X) :=
  uniformSpaceOfCompactR1

/-- Finite control of added-point images suffices to recover the original
normality component from a completed filling. -/
theorem completed_region_subset_component_of_added_images
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (U : ℕ → Set X)
    (hUs : ∀ j, U j ⊆ f.source) (hnext : ∀ j, MapsTo f.totalize (U j) (U (j + 1)))
    (W : TopologicalSpace.Opens X) (hWc : IsConnected (W : Set X))
    (hWn : (W : Set X) ⊆ f.denseCompletion.omega)
    (hWnormal : f.denseCompletion.IsNormalOn W)
    (hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : OnePoint X,
        TendstoLocallyUniformlyOn
          (fun n z => ((f.denseCompletion.totalize^[times (ψ n)]) z : OnePoint X))
          (fun _ => b) atTop W)
    {E : Set X} (hE : E.Finite)
    (hlanding : ∀ x ∈ (W : Set X), ∀ k,
      (f.denseCompletion.totalize^[k]) x ∉ f.source →
        (f.denseCompletion.totalize^[k + 1]) x ∈ E)
    {n : ℕ} {a : X} (haW : a ∈ W) (haU : a ∈ U n)
    (hUeq : U n = connectedComponentIn f.omega a)
    (havoid : ∀ k, Disjoint (U (n + k)) E)
    (hnopunct : ∀ k e, e ∈ E → ¬ BKL.IsPuncture (U (n + k)) e) :
    (W : Set X) ⊆ U n := by
  have hg := f.isOpenHolomorphic_denseCompletion hf
  have hnextg : ∀ j, MapsTo f.denseCompletion.totalize (U j) (U (j + 1)) := by
    intro j x hx
    rw [f.denseCompletion_totalize_eq hf.2 (hUs j hx)]
    exact hnext j hx
  have haE : ¬ ∃ k, (f.denseCompletion.totalize^[k]) a ∈ E := by
    rintro ⟨k, hk⟩
    exact disjoint_left.mp (havoid k) (BKL.iterate_mapsTo_forward_sets hnextg n k haU) hk
  have hiso : ∀ x ∈ (W : Set X), ∀ᶠ y in 𝓝 x,
      (∃ k, (f.denseCompletion.totalize^[k]) y ∈ E) → y = x := fun _ hx =>
    f.denseCompletion.eventually_eq_of_finite_backwardOrbit_constant_limits hg W.isOpen
      hWn hlim hE hx
  have hgood := f.good_completed_region_subset_component_of_added_images hf.2 W hWc hWnormal
    hiso hlanding haW haE
  rw [← hUeq] at hgood
  exact BKL.subset_forward_domain_of_no_downstream_punctures hnextg
    (fun j V hVW hVo => f.denseCompletion.isOpen_image_totalize_iterate hg hVo
      (hVW.trans hWn) j) W.isOpen hgood hiso havoid hnopunct

end SurfaceDynamics.LocalMap
