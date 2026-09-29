module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.FullRestrictionComponents
public import BoundedWanderingDomains.Surfaces.SingularEncounters.EncounterConsequences
public import BoundedWanderingDomains.Surfaces.SingularEncounters.RestrictionIteration

@[expose] public section

/-! # Returning the selected encounters to the original surface -/

open Set Function Filter Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem HasSingularEncounterSequenceAt.of_fullRestriction
    (f : LocalMap X) (hf : Continuous f.map)
    (O V : TopologicalSpace.Opens X) (hVs : (V : Set X) ⊆ f.source)
    (hVO : (V : Set X) ⊆ O)
    (hm : ∀ x : (f.restrictSource V hVs).source, (f.restrictSource V hVs).map x ∈ O)
    (hg : Continuous ((f.restrictSource V hVs).restrictAmbient O hVO hm).map)
    (hfull : ∀ u : f.source, (u : X) ∈ O → f.map u ∈ O → (u : X) ∈ V)
    {B : Set X} (hB : IsClosed B)
    (hremoved : ∀ u : f.source, (u : X) ∉ O → f.map u ∈ B)
    (zg : ((f.restrictSource V hVs).restrictAmbient O hVO hm).trapped)
    (zf : f.trapped) (hbase : ((zg : O) : X) = (zf : X))
    {W : Set O} (hW : W ⊆ ((f.restrictSource V hVs).restrictAmbient O hVO hm).trapped)
    {x : O} (hxB : (x : X) ∉ B)
    (h : ((f.restrictSource V hVs).restrictAmbient O hVO hm).HasSingularEncounterSequenceAt
      hg W zg x) :
    f.HasSingularEncounterSequenceAt hf (Subtype.val '' W) zf (x : X) := by
  classical
  let g := (f.restrictSource V hVs).restrictAmbient O hVO hm
  obtain ⟨Q, φ, s, hφ, hs, hQ, hshrink, hsingular, hcapture⟩ := h
  have horbit : ∀ n, ((g.orbit n zg : O) : X) = f.orbit n zf := by
    intro n
    calc
      ((g.orbit n zg : O) : X) = ((g.totalize^[n]) (zg : O) : X) := by
        rw [g.totalize_iterate_orbit]
      _ = (f.totalize^[n]) (((zg : O) : X)) :=
        f.totalize_iterate_restrictAmbient_restrictSource O V hVs hVO hm zg zg.2 n
      _ = (f.totalize^[n]) (zf : X) := congrArg (f.totalize^[n]) hbase
      _ = f.orbit n zf := f.totalize_iterate_orbit n zf
  have havoid : ∀ᶠ k in atTop, ((Q k).carrier : Set O) ⊆ Subtype.val ⁻¹' Bᶜ :=
    hshrink _ ((hB.isOpen_compl.preimage continuous_subtype_val).mem_nhds hxB)
  obtain ⟨N, hN⟩ := eventually_atTop.mp havoid
  have hpre (k : ℕ) (hk : N ≤ k) :
      ∀ u : f.source, f.map u ∈ ambientOpen O (Q k).carrier → (u : X) ∈ V := by
    intro u hu
    obtain ⟨y, hy, hyu⟩ := hu
    have hyB : (y : X) ∉ B := hN k hk hy
    apply hfull u
    · by_contra huO
      exact hyB (hyu.symm ▸ hremoved u huO)
    · exact hyu ▸ y.2
  have haD (k : ℕ) :
      g.map ⟨g.orbit (φ k) zg, g.orbit_mem_source (φ k) zg⟩ ∈ (Q k).carrier :=
    g.base_map_mem_of_component_singular_value hg _ _ (hsingular k)
  have hcomp (k : ℕ) (hk : N ≤ k) :
      Subtype.val '' (g.inverseComponentSource hg (Q k).carrier
        ⟨g.orbit (φ k) zg, g.orbit_mem_source (φ k) zg⟩ : Set O) =
        (f.inverseComponentSource hf ((Q k).inAmbient O).carrier
          ⟨f.orbit (φ k) zf, f.orbit_mem_source (φ k) zf⟩ : Set X) := by
    rw [EmbeddedDisc.inAmbient_carrier]
    simpa only [horbit] using f.inverseComponentSource_fullRestriction_image hf O V hVs hVO hm
      hg (Q k).carrier (hpre k hk) ⟨g.orbit (φ k) zg, g.orbit_mem_source (φ k) zg⟩ (haD k)
  have hsing (k : ℕ) (hk : N ≤ k) :
      (s k : X) ∈ f.componentSingularValues hf ((Q k).inAmbient O).carrier
        ⟨f.orbit (φ k) zf, f.orbit_mem_source (φ k) zf⟩ := by
    rw [EmbeddedDisc.inAmbient_carrier]
    have hh := f.componentSingularValues_fullRestriction_subset hf O V hVs hVO hm
      hg (Q k).carrier (hpre k hk) ⟨g.orbit (φ k) zg, g.orbit_mem_source (φ k) zg⟩
      (haD k) ⟨s k, hsingular k, rfl⟩
    simpa only [horbit] using hh
  refine ⟨fun n => (Q (n + N)).inAmbient O, fun n => φ (n + N),
    fun n => (s (n + N) : X), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    exact hφ (Nat.add_lt_add_right hnm N)
  · intro n m hnm
    exact Nat.add_right_cancel (hs (Subtype.val_injective hnm))
  · intro n
    obtain ⟨w, hw⟩ := hQ (n + N)
    exact ⟨w, congrArg Subtype.val hw⟩
  · intro A hA
    have hh := (tendsto_add_atTop_nat N).eventually
      (hshrink (Subtype.val ⁻¹' A) (continuous_subtype_val.continuousAt.preimage_mem_nhds hA))
    filter_upwards [hh] with n hn
    rintro y ⟨w, rfl⟩
    exact hn (mem_range_self w)
  · intro n
    exact hsing (n + N) (by omega)
  · intro L hL hLW
    have hLO : L ⊆ O := by
      intro y hy
      obtain ⟨w, _, rfl⟩ := hLW hy
      exact w.2
    let L' : Set O := Subtype.val ⁻¹' L
    have hLeq : (Subtype.val : O → X) '' L' = L :=
      image_preimage_eq_of_subset (fun y hy => ⟨⟨y, hLO hy⟩, rfl⟩)
    have hL' : IsCompact L' := by
      rw [IsEmbedding.subtypeVal.isCompact_iff, hLeq]
      exact hL
    have hL'W : L' ⊆ W := by
      intro y hy
      obtain ⟨w, hw, hwy⟩ := hLW hy
      exact Subtype.ext hwy ▸ hw
    have hcap := (tendsto_add_atTop_nat N).eventually (hcapture L' hL' hL'W)
    filter_upwards [hcap] with n hn
    intro y hy
    let yo : O := ⟨y, hLO hy⟩
    have hyo : yo ∈ L' := hy
    have himage : ((g.totalize^[φ (n + N)]) yo : X) ∈
        Subtype.val '' (g.inverseComponentSource hg (Q (n + N)).carrier
          ⟨g.orbit (φ (n + N)) zg, g.orbit_mem_source (φ (n + N)) zg⟩ : Set O) :=
      ⟨_, hn hyo, rfl⟩
    rw [hcomp (n + N) (by omega)] at himage
    rw [f.totalize_iterate_restrictAmbient_restrictSource O V hVs hVO hm yo
      (hW (hL'W hyo))] at himage
    exact himage

end SurfaceDynamics.LocalMap
