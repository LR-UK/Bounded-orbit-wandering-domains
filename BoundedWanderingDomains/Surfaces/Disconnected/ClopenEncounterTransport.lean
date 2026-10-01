module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.Disconnected.ClopenSourceRestriction
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterConsequences

@[expose] public section

/-! # Encounter sequences survive deletion of irrelevant source components -/

open Set Function Filter Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem HasSingularEncounterSequenceAt.of_clopenSourceRestriction
    (f : LocalMap X) (hf : Continuous f.map)
    (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    (hVc : IsClosed ((Subtype.val : f.source → X) ⁻¹' (V : Set X)))
    (z : (f.restrictSource V hV).trapped) {W : Set X} {x : X}
    (hW : W ⊆ (f.restrictSource V hV).trapped)
    (h : (f.restrictSource V hV).HasSingularEncounterSequenceAt
      (hf.comp (continuous_subtype_val.subtype_mk _)) W z x) :
    f.HasSingularEncounterSequenceAt hf W
      ⟨z, f.restrictSource_trapped_subset V hV z.property⟩ x := by
  let g := f.restrictSource V hV
  let hg := hf.comp (continuous_subtype_val.subtype_mk (fun y : V => hV y.property))
  let zf : f.trapped := ⟨z, f.restrictSource_trapped_subset V hV z.property⟩
  have horbit : ∀ n, g.orbit n z = f.orbit n zf := by
    intro n
    have he := f.restrictSource_iterate_eq_of_restricted_trapped V hV z.property n
    rw [g.iterate_eq_some_orbit n z, f.iterate_eq_some_orbit n zf] at he
    exact Option.some.inj he
  have htotal : ∀ y ∈ W, ∀ n, (g.totalize^[n]) y = (f.totalize^[n]) y := by
    intro y hy n
    rw [g.totalize_iterate_orbit n ⟨y, hW hy⟩,
      f.totalize_iterate_orbit n ⟨y, f.restrictSource_trapped_subset V hV (hW hy)⟩]
    have he := f.restrictSource_iterate_eq_of_restricted_trapped V hV (hW hy) n
    rw [g.iterate_eq_some_orbit n ⟨y, hW hy⟩,
      f.iterate_eq_some_orbit n ⟨y, f.restrictSource_trapped_subset V hV (hW hy)⟩] at he
    exact Option.some.inj he
  obtain ⟨Q, φ, s, hφ, hs, hQ, hshrink, hsing, hcapture⟩ := h
  have hbase : ∀ n, g.map ⟨g.orbit (φ n) z, g.orbit_mem_source (φ n) z⟩ ∈ (Q n).carrier :=
    fun n => g.base_map_mem_of_component_singular_value hg _ _ (hsing n)
  have hcomp : ∀ n, g.inverseComponentSource hg (Q n).carrier
      ⟨g.orbit (φ n) z, g.orbit_mem_source (φ n) z⟩ =
      f.inverseComponentSource hf (Q n).carrier ⟨f.orbit (φ n) zf, f.orbit_mem_source (φ n) zf⟩ := by
    intro n
    rw [f.inverseComponentSource_restrictSource_clopen_eq hf V hV hVc _ _ (hbase n)]
    congr 1
    exact Subtype.ext (horbit (φ n))
  refine ⟨Q, φ, s, hφ, hs, hQ, hshrink, ?_, ?_⟩
  · intro n
    have hn := hsing n
    rw [f.componentSingularValues_restrictSource_clopen_eq hf V hV hVc _ _ (hbase n)] at hn
    have he : (⟨g.orbit (φ n) z, hV (g.orbit_mem_source (φ n) z)⟩ : f.source) =
        ⟨f.orbit (φ n) zf, f.orbit_mem_source (φ n) zf⟩ := Subtype.ext (horbit (φ n))
    rw [he] at hn
    exact hn
  · intro L hL hLW
    filter_upwards [hcapture L hL hLW] with n hn
    intro y hy
    rw [← hcomp n, ← htotal y (hLW hy) (φ n)]
    exact hn hy

end SurfaceDynamics.LocalMap
