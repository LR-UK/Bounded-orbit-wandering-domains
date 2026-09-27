/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CompactCentreNormal
import BoundedWanderingDomains.Surfaces.CoordinateDiscParam
import BoundedWanderingDomains.Surfaces.LocalIterateHolomorphic

/-! # Compact marked orbits give local normality -/

open Set Function Filter
open Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

/-- If one marked orbit in an open trapped neighbourhood remains in a compact
set, ordinary Montel on the universal covering disc makes the iterates normal
on a smaller neighbourhood of the marked point. -/
theorem mem_omega_of_compact_orbit (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (p : DiscCover X) (W : TopologicalSpace.Opens X)
    (hW : (W : Set X) ⊆ f.trapped) (x : W) {K : Set X} (hK : IsCompact K)
    (hcompact : ∀ n, f.orbitOn W hW n x ∈ K) :
    (x : X) ∈ f.omega := by
  obtain ⟨D, hDcenter, hDsub⟩ :=
    exists_coordDisk_center_closedCarrier_subset W.isOpen x.property
  let V : Set X := Set.range D.param
  have hVopen : IsOpen V := D.isOpenEmbedding_param.isOpen_range
  have hxV : (x : X) ∈ V := by
    refine ⟨discZero, ?_⟩
    rw [D.param_zero, hDcenter]
  have hVW : V ⊆ W := by
    rintro y ⟨z, rfl⟩
    exact hDsub (D.param_mem_closedCarrier z)
  have hVT : V ⊆ f.trapped := hVW.trans hW
  refine ⟨V, hVopen, hxV, hVT, ?_⟩
  intro s hs
  let F : ℕ → unitDisc → X := fun n z =>
    f.orbitOn W hW (s n) ⟨D.param z, hVW ⟨z, rfl⟩⟩
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := by
    intro n
    let d : unitDisc → W := fun z => ⟨D.param z, hVW ⟨z, rfl⟩⟩
    have hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) d := by
      apply (mdifferentiable_subtypeVal_comp_iff W d).mp
      exact D.mdifferentiable_param
    exact (f.mdifferentiable_orbitOn hf W hW (s n)).comp
      hd
  have hFzero : ∀ n, F n discZero ∈ K := by
    intro n
    simpa only [F, D.param_zero, hDcenter] using hcompact (s n)
  letI : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  obtain ⟨a, G, ha, hconv⟩ := p.exists_normal_disc_subsequence hK F hF hFzero
  let e : unitDisc ≃ₜ V := D.isOpenEmbedding_param.toIsEmbedding.toHomeomorph
  let q : V → unitDisc := e.symm
  have hq : Continuous q := e.symm.continuous
  refine ⟨a, ha, G ∘ q, ?_⟩
  have hpull := hconv.comp q hq
  apply hpull.congr
  intro n y
  have he : D.param (q y) = (y : X) := by
    exact congrArg Subtype.val (e.apply_symm_apply y)
  rw [f.compactifiedIterate_eq_orbit (s (a n)) ⟨y, hVT y.property⟩]
  change (F (a n) (q y) : OnePoint X) =
    (f.orbitOn W hW (s (a n))
      ⟨(y : X), hVW y.property⟩ : OnePoint X)
  simp only [F]
  congr 2
  exact Subtype.ext he

/-- A disc cover of an open subsurface is enough for the compact-centre
Montel argument.  All nearby orbits only have to remain in that subsurface;
compactness is required solely for the marked orbit. -/
theorem mem_omega_of_compact_orbit_in_subsurface
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O : TopologicalSpace.Opens X) (p : DiscCover O)
    (W : TopologicalSpace.Opens X) (hW : (W : Set X) ⊆ f.trapped)
    (horbitO : ∀ n y, f.orbitOn W hW n y ∈ O)
    (x : W) {C : Set O} (hC : IsCompact C)
    (hcompact : ∀ n,
      (⟨f.orbitOn W hW n x, horbitO n x⟩ : O) ∈ C) :
    (x : X) ∈ f.omega := by
  obtain ⟨D, hDcenter, hDsub⟩ :=
    exists_coordDisk_center_closedCarrier_subset W.isOpen x.property
  let V : Set X := Set.range D.param
  have hVopen : IsOpen V := D.isOpenEmbedding_param.isOpen_range
  have hxV : (x : X) ∈ V := by
    refine ⟨discZero, ?_⟩
    rw [D.param_zero, hDcenter]
  have hVW : V ⊆ W := by
    rintro y ⟨z, rfl⟩
    exact hDsub (D.param_mem_closedCarrier z)
  have hVT : V ⊆ f.trapped := hVW.trans hW
  refine ⟨V, hVopen, hxV, hVT, ?_⟩
  intro s hs
  let d : unitDisc → W := fun z => ⟨D.param z, hVW ⟨z, rfl⟩⟩
  let F : ℕ → unitDisc → O := fun n z =>
    ⟨f.orbitOn W hW (s n) (d z), horbitO (s n) (d z)⟩
  have hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) d := by
    apply (mdifferentiable_subtypeVal_comp_iff W d).mp
    exact D.mdifferentiable_param
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := by
    intro n
    apply (mdifferentiable_subtypeVal_comp_iff O (F n)).mp
    exact (f.mdifferentiable_orbitOn hf W hW (s n)).comp hd
  have hFzero : ∀ n, F n discZero ∈ C := by
    intro n
    have he : d discZero = x := by
      apply Subtype.ext
      simp only [d, D.param_zero, hDcenter]
    simpa only [F, he] using hcompact (s n)
  letI : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  obtain ⟨a, G, ha, hconv⟩ :=
    p.exists_normal_disc_subsequence_ambient O hC F hF hFzero
  let e : unitDisc ≃ₜ V := D.isOpenEmbedding_param.toIsEmbedding.toHomeomorph
  let q : V → unitDisc := e.symm
  have hq : Continuous q := e.symm.continuous
  refine ⟨a, ha, G ∘ q, ?_⟩
  have hpull := hconv.comp q hq
  apply hpull.congr
  intro n y
  have he : D.param (q y) = (y : X) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  rw [f.compactifiedIterate_eq_orbit (s (a n)) ⟨y, hVT y.property⟩]
  change (((F (a n) (q y) : O) : X) : OnePoint X) =
    (f.orbitOn W hW (s (a n))
      ⟨(y : X), hVW y.property⟩ : OnePoint X)
  simp only [F]
  congr 2
  exact Subtype.ext he

/-- The same local-normality argument may use a disc cover of an open
subsurface, provided the whole family of local orbit values stays in a fixed
compact subset of that subsurface. -/
theorem mem_omega_of_compact_orbits_in_subsurface
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (O : TopologicalSpace.Opens X) (p : DiscCover O)
    (W : TopologicalSpace.Opens X) (hW : (W : Set X) ⊆ f.trapped)
    (horbitO : ∀ n y, f.orbitOn W hW n y ∈ O)
    (x : W) {C : Set O} (hC : IsCompact C)
    (hcompact : ∀ n y,
      (⟨f.orbitOn W hW n y, horbitO n y⟩ : O) ∈ C) :
    (x : X) ∈ f.omega := by
  obtain ⟨D, hDcenter, hDsub⟩ :=
    exists_coordDisk_center_closedCarrier_subset W.isOpen x.property
  let V : Set X := Set.range D.param
  have hVopen : IsOpen V := D.isOpenEmbedding_param.isOpen_range
  have hxV : (x : X) ∈ V := by
    refine ⟨discZero, ?_⟩
    rw [D.param_zero, hDcenter]
  have hVW : V ⊆ W := by
    rintro y ⟨z, rfl⟩
    exact hDsub (D.param_mem_closedCarrier z)
  have hVT : V ⊆ f.trapped := hVW.trans hW
  refine ⟨V, hVopen, hxV, hVT, ?_⟩
  intro s hs
  let d : unitDisc → W := fun z => ⟨D.param z, hVW ⟨z, rfl⟩⟩
  let F : ℕ → unitDisc → O := fun n z =>
    ⟨f.orbitOn W hW (s n) (d z),
      horbitO (s n) (d z)⟩
  have hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) d := by
    apply (mdifferentiable_subtypeVal_comp_iff W d).mp
    exact D.mdifferentiable_param
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) := by
    intro n
    apply (mdifferentiable_subtypeVal_comp_iff O (F n)).mp
    exact (f.mdifferentiable_orbitOn hf W hW (s n)).comp hd
  have hFrange : ∀ n z, F n z ∈ C := fun n z => hcompact (s n) (d z)
  letI : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  obtain ⟨a, G, ha, hconv⟩ :=
    p.exists_normal_disc_subsequence_compact_range O hC F hF hFrange
  let e : unitDisc ≃ₜ V := D.isOpenEmbedding_param.toIsEmbedding.toHomeomorph
  let q : V → unitDisc := e.symm
  have hq : Continuous q := e.symm.continuous
  refine ⟨a, ha, G ∘ q, ?_⟩
  have hpull := hconv.comp q hq
  apply hpull.congr
  intro n y
  have he : D.param (q y) = (y : X) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  rw [f.compactifiedIterate_eq_orbit (s (a n)) ⟨y, hVT y.property⟩]
  change (((F (a n) (q y) : O) : X) : OnePoint X) =
    (f.orbitOn W hW (s (a n))
      ⟨(y : X), hVW y.property⟩ : OnePoint X)
  simp only [F]
  congr 2
  exact Subtype.ext he

end SurfaceDynamics.LocalMap
