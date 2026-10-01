module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FiniteControlCharts
public import BoundedWanderingDomains.Surfaces.ConditionalDiscShrink

@[expose] public section

/-! # Compactness turns local finite encounters into finite analytic control -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]

theorem exists_finite_disc_control_of_locally_finite_encounters
    (p : ComponentwiseDiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
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
    (hfinite : ∀ x ∈ K, f.LocallyFiniteComponentEncounters hf.2.continuous c x) :
    ∃ (I : Finset K) (target : ↥I → TopologicalSpace.Opens X) (H : Finset X)
      (inner : ↥I → Set X),
      (∀ i, IsCompact (inner i)) ∧ (∀ i, inner i ⊆ target i) ∧
      ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ᶠ n in atTop,
        ∃ (i : ↥I) (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source),
          f.HasComponentPuncturedDisc (H : Set X)
            (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}) ∧
          ((target i : Set X) \ (H : Set X) ⊆ (f.restrictSource V hV).regularValues) ∧
          (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}) ⊆ V ∧
          (F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}) ⊆ inner i := by
  classical
  choose D Q L E N hD hQ hL hxL hLQ hQD hQE hcontrol using
    fun x : K => f.exists_component_control_chart hf c (hfinite x x.2)
  have hcover : K ⊆ ⋃ x : K, interior (L x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxL ⟨x, hx⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => interior (L x))
    (fun _ => isOpen_interior) hcover
  let target : ↥I → TopologicalSpace.Opens X := fun i =>
    ⟨range (Q i.val).param, (Q i.val).isOpenEmbedding_param.isOpen_range⟩
  let H : Finset X := Finset.univ.biUnion (fun i : ↥I => insert (Q i.val).center (E i.val))
  have hEH (i : ↥I) : E i.val ⊆ H := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_insert_of_mem hx⟩
  have hcenterH (i : ↥I) : (Q i.val).center ∈ H :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_insert_self _ _⟩
  refine ⟨I, target, H, fun i => L i.val, fun i => hL i.val, fun i => hLQ i.val, ?_⟩
  intro R hR hR1
  have hcoverI : K ⊆ ⋃ i : ↥I, interior (L i.val) := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hI hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hix⟩
  have hsmall := (tendsto_add_atTop_nat 1).eventually
    (p.disjoint_disc_images_eventually_in_cover hK F hF
      (fun n => (hF0 n).symm ▸ hcK n) hdis (fun i : ↥I => interior (L i.val))
      (fun _ => isOpen_interior) hcoverI hR1)
  have havoid := (tendsto_add_atTop_nat 1).eventually
    (AreaDeficit.eventually_disjoint_finite hdis H.finite_toSet)
  have hlate : ∀ᶠ n : ℕ in atTop, ∀ i : ↥I, N i.val ≤ n :=
    eventually_all.mpr (fun i => eventually_ge_atTop (N i.val))
  filter_upwards [hsmall, havoid, hlate] with n hn hnH hnN
  obtain ⟨i, hi⟩ := hn
  have hzR : discZero ∈ {w : unitDisc | ‖(w : ℂ)‖ ≤ R} := by
    change ‖(0 : ℂ)‖ ≤ R
    simpa using hR
  have hnextL : F (n + 1) '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R} ⊆ L i.val := by
    rintro y ⟨w, hw, rfl⟩
    exact interior_subset (hi w hw)
  have hcL : f.map (c n) ∈ L i.val := by
    rw [hstep]
    exact hnextL ⟨discZero, hzR, rfl⟩
  have hcH : f.map (c n) ∉ H := by
    rw [hstep]
    exact fun hh => disjoint_left.mp hnH (mem_range_self discZero) hh
  have himage : MapsTo f.totalize
      (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R})
      (range (Q i.val).param \ (H : Set X)) := by
    intro y hy
    have hy' := hforward R hR hR1 n hy
    refine ⟨hLQ i.val (hnextL hy'), ?_⟩
    exact fun hh => disjoint_left.mp hnH (image_subset_range _ _ hy') hh
  have hA : IsPreconnected (F n '' {w : unitDisc | ‖(w : ℂ)‖ ≤ R}) :=
    ((unitDisc_closed_radius_connected hR hR1).image _ (hF n).continuous.continuousOn).isPreconnected
  have hcD : f.map (c n) ∈ D i.val := by
    obtain ⟨w, hw⟩ := hLQ i.val hcL
    exact hw ▸ hQD i.val ((Q i.val).param_mem_closedCarrier w)
  obtain ⟨hbkl, hAV, hreg⟩ := f.hasComponentPuncturedDisc_of_inverse_component_control
    hf (D i.val) (hD i.val) (Q i.val) (hQD i.val) (E i.val) H (hEH i) (hcenterH i)
    (hQE i.val) (c n) hcD (fun he => hcH (hEH i he))
    (hcontrol i.val n (hnN i) hcL) hA
    ((image_subset_range _ _).trans (hFs n))
    ⟨discZero, hzR, hF0 n⟩ himage
  exact ⟨i, f.inverseComponentSource hf.2.continuous (D i.val) (c n),
    f.inverseComponentSource_subset _ _ _, hbkl, hreg, hAV, hnextL⟩

end SurfaceDynamics.LocalMap
