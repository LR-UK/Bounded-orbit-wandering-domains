/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.ClassBFillLimits
import BoundedWanderingDomains.CompactWanderingLimits
import BoundedWanderingDomains.BackwardOrbitMontel
import EremenkosConjecture.PlaneSimpleConnectivity

/-! # Simple connectivity of class-B wandering components

Constant limits extend from compact continua to their fillings. Thus normality
extends across every hole, and maximality of the Fatou component fills it.
Only tract simple connectivity is used from the Eremenko--Lyubich project.
-/

open Set Filter Function Metric OnePoint NoWanderingDomains
open scoped Topology

namespace AreaDeficit

/-- Filled compact continua in a class-B wandering component consist of
Fatou points. -/
theorem fill_subset_fatou_of_classB_wandering {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) (hB : ComplexDynamics.MemClassB f)
    {U : ℕ → Set ℂ} (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hfm : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (hKU : K ⊆ U 0) :
    ComplexApproximation.fill K ⊆ ComplexDynamics.fatouSet f := by
  have hUo : IsOpen (U 0) := by
    obtain ⟨p, _, hp⟩ := hU 0
    rw [hp]
    exact (ComplexDynamics.isOpen_fatouSet f).connectedComponentIn
  obtain ⟨x, hx⟩ := hKc.nonempty
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (infinite_of_mem_nhds x (hUo.mem_nhds (hKU hx))).nontrivial
  have hit : ∀ n, MapsTo (f^[n]) (U 0) (U n) := by
    intro n
    induction n with
    | zero => exact mapsTo_id _
    | succ n ih => simpa only [iterate_succ'] using (hfm n).comp ih
  have hnormal : ComplexDynamics.IsNormalSequenceOn (ComplexDynamics.sphericalIterate f)
      (interior (ComplexApproximation.fill K)) := by
    have heq : (inferInstance : MetricSpace (OnePoint ℂ)).toUniformSpace =
        ComplexDynamics.riemannSphereUniformSpace := unique_uniformity_of_compact rfl rfl
    intro φ hφ
    let ns : ℕ → ℕ := fun n => φ (n+1) - 1
    have hpos : ∀ n, 0 < φ (n+1) := fun n =>
      lt_of_lt_of_le (Nat.zero_lt_succ n) (hφ.id_le (n+1))
    have hns : ∀ n, ns n + 1 = φ (n+1) := fun n => Nat.sub_add_cancel (hpos n)
    let F : ℕ → ℂ → ℂ := fun n => f^[ns n + 1]
    have hFo : ∀ n, DifferentiableOn ℂ (F n) (U 0) :=
      fun n => (hf.1.iterate (ns n+1)).differentiableOn
    have hFomit : ∀ n z, z ∈ U 0 → F n z ≠ a ∧ F n z ≠ b := by
      intro n z hz
      have hi := hit (ns n+1) hz
      exact ⟨fun he => disjoint_left.mp (hdis (by omega : ns n+1 ≠ 0)) (he ▸ hi) ha,
        fun he => disjoint_left.mp (hdis (by omega : ns n+1 ≠ 0)) (he ▸ hi) hb⟩
    have hFd : Pairwise (fun n m => Disjoint (F n '' U 0) (F m '' U 0)) := by
      intro n m hnm
      apply (hdis (show ns n+1 ≠ ns m+1 from by
        rw [hns n, hns m]
        exact hφ.injective.ne (by omega))).mono (hit _).image_subset (hit _).image_subset
    obtain ⟨ψ, hψ, c, hc⟩ := constant_subsequence_on_compact_continuum
      hUo hK hKc hKU hFo hab hFomit hFd
    have hfill := uniform_spherical_constant_on_fill hf hB hK hKc (ns := ns ∘ ψ) hc
    rw [heq] at hfill
    have hl := (hfill.mono interior_subset).tendstoLocallyUniformlyOn
    have hls := tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hl
    refine ⟨fun n => ψ n + 1, fun i j hij => Nat.add_lt_add_right (hψ hij) 1,
      fun _ => c, ?_⟩
    simpa only [ComplexDynamics.sphericalIterate, Function.comp_def, hns] using hls
  intro z hz
  by_cases hzK : z ∈ K
  · obtain ⟨p, _, hp⟩ := hU 0
    exact (hp ▸ hKU hzK : z ∈ connectedComponentIn (ComplexDynamics.fatouSet f) p) |>
      connectedComponentIn_subset _ _
  · have hzI : z ∈ interior (ComplexApproximation.fill K) := by
      apply ((hK.isClosed.isOpen_compl.connectedComponentIn).subset_interior_iff.mpr
        (show connectedComponentIn Kᶜ z ⊆ ComplexApproximation.fill K from ?_))
        (mem_connectedComponentIn hzK)
      intro w hw
      change Bornology.IsBounded (connectedComponentIn Kᶜ w)
      exact (connectedComponentIn_eq hw) ▸ hz
    exact ⟨_, isOpen_interior, hzI, hnormal⟩

/-- A class-B wandering Fatou component is simply connected. -/
theorem classB_wandering_component_simplyConnected {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) (hB : ComplexDynamics.MemClassB f)
    {U : ℕ → Set ℂ} (hU : ∀ n, ComplexDynamics.IsFatouComponent f (U n))
    (hfm : ∀ n, MapsTo f (U n) (U (n+1)))
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) :
    IsSimplyConnected (U 0) := by
  obtain ⟨p, hp, hcomp⟩ := hU 0
  have hUo : IsOpen (U 0) := hcomp ▸ (ComplexDynamics.isOpen_fatouSet f).connectedComponentIn
  have hUc : IsConnected (U 0) := hcomp ▸ isConnected_connectedComponentIn_iff.mpr hp
  apply FunctionTheory.isSimplyConnected_of_compact_connected_subsets hUo hUc
  intro K hK hKc hKU
  let L := ComplexApproximation.fill K
  have hL : IsCompact L := ComplexApproximation.isCompact_fill hK
  have hLc : IsConnected L := ComplexApproximation.isConnected_fill hK.isClosed hKc
  have hLf : IsConnected Lᶜ := ComplexApproximation.isConnected_compl_fill hK
  have hLF : L ⊆ ComplexDynamics.fatouSet f :=
    fill_subset_fatou_of_classB_wandering hf hB hU hfm hdis hK hKc hKU
  obtain ⟨x, hx⟩ := hKc.nonempty
  have hLU : L ⊆ U 0 := by
    have hs := hLc.isPreconnected.subset_connectedComponentIn
      (ComplexApproximation.subset_fill K hx) hLF
    rwa [← connectedComponentIn_eq (hcomp ▸ hKU hx), ← hcomp] at hs
  obtain ⟨N, _, _, hNU⟩ := EremenkosConjecture.exists_nested_jordan_neighbourhoods_within
    L (U 0) hL hLc hLf hUo hLU
  exact ⟨interior (N 0).carrier, (N 0).simplyConnectedInterior,
    (ComplexApproximation.subset_fill K).trans (N 0).contains, interior_subset.trans hNU⟩

end AreaDeficit
