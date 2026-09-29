module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.DistinctSelection
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ShrinkingCharts
public import BoundedWanderingDomains.Surfaces.SingularEncounters.LocalFiniteEncounters
public import BoundedWanderingDomains.Surfaces.ConditionalDiscShrink
public import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
public import Mathlib.Topology.Order.IsLUB

@[expose] public section

/-! # Distinct singular encounters in shrinking full inverse components -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X]

theorem exists_shrinking_encounters_of_not_locally_finite
    (p : DiscCover X) (f : LocalMap X) (hf : Continuous f.map)
    (c : ℕ → f.source) (F : ℕ → unitDisc → X)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hFs : ∀ n, range (F n) ⊆ f.source)
    (hF0 : ∀ n, F n discZero = (c n : X))
    (hstep : ∀ n, f.map (c n) = F (n + 1) discZero)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    (hforward : ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ n,
      MapsTo f.totalize (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R})
        (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}))
    {K : Set X} (hK : IsCompact K) (hcK : ∀ n, (c n : X) ∈ K)
    {x : X} (hnot : ¬ f.LocallyFiniteComponentEncounters hf c x) :
    ∃ (Q : ℕ → RiemannDynamics.CoordDisk X) (φ : ℕ → ℕ) (s : ℕ → X),
      StrictMono φ ∧ Injective s ∧ (∀ n, (Q n).center = x) ∧
      (∀ O ∈ 𝓝 x, ∀ᶠ n in atTop, (Q n).closedCarrier ⊆ O) ∧
      (∀ n, s n ∈ f.componentSingularValues hf
        ⟨range (Q n).param, (Q n).isOpenEmbedding_param.isOpen_range⟩ (c (φ n))) ∧
      ∀ r : ℝ, r < 1 → ∀ᶠ n in atTop,
        F (φ n) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ r} ⊆
          f.inverseComponentSource hf
            ⟨range (Q n).param, (Q n).isOpenEmbedding_param.isOpen_range⟩ (c (φ n)) := by
  classical
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  obtain ⟨Q, hQ, hshrink⟩ := exists_shrinking_coordDisks x
  let D : ℕ → TopologicalSpace.Opens X := fun m =>
    ⟨range (Q m).param, (Q m).isOpenEmbedding_param.isOpen_range⟩
  have hxD (m : ℕ) : x ∈ D m := ⟨discZero, (Q m).param_zero.trans (hQ m)⟩
  have hDconn (m : ℕ) : IsConnected (D m : Set X) :=
    isConnected_range (Q m).isOpenEmbedding_param.continuous
  choose L hL hxL hLD using fun m => exists_compact_between isCompact_singleton
    (D m).isOpen (singleton_subset_iff.mpr (hxD m))
  obtain ⟨R, _, hR, hRlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
  let P : ℕ → ℕ → X → Prop := fun m n s =>
    s ∈ f.componentSingularValues hf (D m) (c n) ∧
      F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R m} ⊆ f.inverseComponentSource hf (D m) (c n)
  have hselect : ∀ m N : ℕ, ∀ E : Finset X,
      ∃ n, N ≤ n ∧ ∃ s, s ∉ E ∧ P m n s := by
    intro m N E
    have hsmall := (tendsto_add_atTop_nat 1).eventually
      (p.eventually_avoids_closed_of_centre hK (hL m).isClosed (D m).isOpen.isClosed_compl
        (disjoint_left.mpr (fun y hy hn => hn (hLD m hy))) F hF
        (fun n => (hF0 n).symm ▸ hcK n) hdis (hR m).1.le (hR m).2)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
    obtain ⟨n, hn, hnB, s, hs, hsE⟩ :=
      f.exists_new_singular_encounter_of_not_locally_finite hf c hnot (D m)
        ⟨interior (L m), isOpen_interior⟩ (hDconn m) (hxL m (mem_singleton x))
        (fun y hy => hLD m (interior_subset hy)) E (max N M)
    have hnextD : F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R m} ⊆ D m := by
      rintro y ⟨w, hw, rfl⟩
      apply not_not.mp
      apply hM n (le_trans (le_max_right N M) hn)
      · rw [← hstep]
        exact interior_subset hnB
      · exact hw
    have hzR : discZero ∈ {w : unitDisc | ‖(w : ℂ)‖ ≤ R m} := by
      change ‖(0 : ℂ)‖ ≤ R m
      simpa using (hR m).1.le
    have hA : IsPreconnected (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R m}) :=
      ((unitDisc_closed_radius_connected (hR m).1.le (hR m).2).image _
        (hF n).continuous.continuousOn).isPreconnected
    refine ⟨n, le_trans (le_max_left N M) hn, s, hsE, hs, ?_⟩
    apply f.subset_inverseComponentSource_of_preconnected hf (D m) (c n) hA
      ((image_subset_range _ _).trans (hFs n)) ⟨discZero, hzR, hF0 n⟩
    intro y hy
    rw [← f.totalize_eq y.2]
    exact hnextD (hforward (R m) (hR m).1.le (hR m).2 n hy)
  obtain ⟨μ, φ, s, hμ, hφ, hs, hP⟩ := exists_increasing_distinct_selection P hselect
  refine ⟨fun n => Q (μ n), φ, s, hφ, hs, fun n => hQ (μ n), ?_,
    fun n => (hP n).1, ?_⟩
  · intro O hO
    exact hμ.tendsto_atTop.eventually (hshrink O hO)
  · intro r hr
    have hevent := (hRlim.comp hμ.tendsto_atTop).eventually (Ioi_mem_nhds hr)
    filter_upwards [hevent] with n hn
    exact (image_mono (fun w hw => hw.trans hn.le)).trans (hP n).2

end SurfaceDynamics.LocalMap
