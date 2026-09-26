/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.FiniteChartCriticalCover
import BoundedWanderingDomains.Surfaces.CompactChartPatches

/-! # Finite branch values on an arbitrary compact surface set -/

open Set Function
open scoped Manifold

namespace SurfaceDynamics

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [LocallyCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology N] [LocallyCompactSpace N] [T2Space N]
  [DecidableEq N]

/-- An open holomorphic map has only finitely many branch values coming from
any fixed compact source set. The conclusion also retains a source/target
chart pair witnessing nonvanishing derivative away from those values. -/
theorem exists_finite_branch_values_on_compact
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hopen : IsOpenMap f) {L : Set M} (hL : IsCompact L) :
    ∃ E : Finset N, ∀ x ∈ L, f x ∉ E →
      ∃ (c : OpenPartialHomeomorph M ℂ) (d : OpenPartialHomeomorph N ℂ),
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) d d.source ∧
        x ∈ c.source ∧ f x ∈ d.source ∧
          deriv (d ∘ f ∘ c.symm) (c x) ≠ 0 := by
  obtain ⟨I, A, D, hA, _hD, hAD, hDc, _hDC, hcover⟩ :=
    AreaDeficit.Surfaces.compact_finite_chart_patches
      (L := L) (C := Set.univ) hL (by simp)
  have hfL : IsCompact (f '' L) := hL.image hf.continuous
  obtain ⟨J, B, Eo, hB, _hEo, hBE, hEd, _hEN, hfcover⟩ :=
    AreaDeficit.Surfaces.compact_finite_chart_patches
      (L := f '' L) (C := Set.univ) hfL (by simp)
  let idx := L × (f '' L)
  let Q : Finset idx := I.product J
  let c : idx → OpenPartialHomeomorph M ℂ := fun a => chartAt ℂ (a.1 : M)
  let d : idx → OpenPartialHomeomorph N ℂ := fun a => chartAt ℂ (a.2 : N)
  let Ks : L → Set M := fun i => (chartAt ℂ (i : M)).symm '' A i
  let Kt : (f '' L) → Set N := fun j => (chartAt ℂ (j : N)).symm '' B j
  let K : idx → Set M := fun a => Ks a.1 ∩ f ⁻¹' Kt a.2
  have hKs : ∀ i, IsCompact (Ks i) := by
    intro i
    exact (hA i).image_of_continuousOn
      ((chartAt ℂ (i : M)).continuousOn_symm.mono ((hAD i).trans (hDc i)))
  have hKt : ∀ j, IsCompact (Kt j) := by
    intro j
    exact (hB j).image_of_continuousOn
      ((chartAt ℂ (j : N)).continuousOn_symm.mono ((hBE j).trans (hEd j)))
  have hKcompact : ∀ a, IsCompact (K a) := by
    intro a
    exact (hKs a.1).inter_right ((hKt a.2).isClosed.preimage hf.continuous)
  have hKc : ∀ a, K a ⊆ (c a).source := by
    rintro a x ⟨⟨z, hz, rfl⟩, _⟩
    exact (chartAt ℂ (a.1 : M)).map_target ((hAD a.1).trans (hDc a.1) hz)
  have hfKd : ∀ a, f '' K a ⊆ (d a).source := by
    rintro a _ ⟨x, ⟨_, z, hz, heq⟩, rfl⟩
    rw [← heq]
    exact (chartAt ℂ (a.2 : N)).map_target ((hBE a.2).trans (hEd a.2) hz)
  have hKcover : L ⊆ ⋃ a ∈ Q, K a := by
    intro x hx
    obtain ⟨i, hiI, hxi⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hfx : f x ∈ f '' L := ⟨x, hx, rfl⟩
    obtain ⟨j, hjJ, hfj⟩ := Set.mem_iUnion₂.mp (hfcover hfx)
    apply Set.mem_iUnion₂.mpr
    exact ⟨(i, j), Finset.mem_product.mpr ⟨hiI, hjJ⟩, hxi, hfj⟩
  obtain ⟨F, hF⟩ := exists_finite_chart_branch_values Q K c d
    (fun a => (mdifferentiable_chart (I := 𝓘(ℂ)) (a.1 : M)).1)
    (fun a => (mdifferentiable_chart (I := 𝓘(ℂ)) (a.2 : N)).1)
    hf hopen hKcompact hKc hfKd hKcover
  refine ⟨F, ?_⟩
  intro x hx hxF
  obtain ⟨a, _haQ, hxa, hder⟩ := hF x hx hxF
  exact ⟨c a, d a,
    (mdifferentiable_chart (I := 𝓘(ℂ)) (a.1 : M)).1,
    (mdifferentiable_chart (I := 𝓘(ℂ)) (a.2 : N)).1,
    hKc a hxa, hfKd a ⟨x, hxa, rfl⟩, hder⟩

end SurfaceDynamics

#print axioms SurfaceDynamics.exists_finite_branch_values_on_compact
