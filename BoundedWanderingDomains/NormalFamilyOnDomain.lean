/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.NormalFamilies
import BoundedWanderingDomains.SphericalShrinking

/-! # From local normality to a convergent subsequence on a plane domain -/

open Set Metric Function Filter OnePoint NoWanderingDomains
open scoped Topology Uniformity UniformConvergence

namespace AreaDeficit

/-- A locally normal sequence of continuous maps on any locally compact,
second-countable metric space admits a locally uniformly convergent
subsequence.  The domain may itself be an open-set subtype, which is the form
needed for meromorphic Fatou components. -/
theorem subsequence_of_local_normality
    {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MetricSpace Y] [CompactSpace Y]
    {f : ℕ → X → Y} (hfc : ∀ n, Continuous (f n))
    (hN : ∀ z : X, IsNormalAt (range f) z) :
    ∃ (φ : ℕ → ℕ) (g : X → Y), StrictMono φ ∧
      TendstoLocallyUniformly (fun n => f (φ n)) g atTop := by
  let 𝒦 : Set (Set X) := {K | IsCompact K}
  have h𝒦 : ∀ K ∈ 𝒦, IsCompact K := fun _ h => h
  have : (𝓤 (X →ᵤ[𝒦] Y)).IsCountablyGenerated := by
    have : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
    let e : CompactExhaustion X := default
    apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n => e n)
    · intro n
      exact e.isCompact n
    · exact e.subset
    · intro K hK
      exact (e.exists_superset_of_isCompact hK).imp (fun n hn => hn)
  let F : (X →ᵤ[𝒦] Y) → X → Y := UniformOnFun.toFun 𝒦
  let q : ℕ → (X →ᵤ[𝒦] Y) := fun n => UniformOnFun.ofFun 𝒦 (f n)
  let B : Set (X →ᵤ[𝒦] Y) := range q
  have hc := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝒦
    (α := Y) (s := B) (F := F) .id ?_ ?_
  · obtain ⟨g, _, φ, hφ, ht⟩ := hc.tendsto_subseq
      (fun n => subset_closure (mem_range_self n))
    refine ⟨φ, F g, hφ, ?_⟩
    simpa [tendstoLocallyUniformly_iff_forall_isCompact,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝒦, F, q,
      Function.comp_def] using ht
  · rintro K hK z hz
    have he : EquicontinuousAt (fun i : B => F i) z := by
      rw [Metric.equicontinuousAt_iff]
      intro e he
      obtain ⟨d, hd, hd'⟩ := (hN z).equicontinuousAt
        (by rintro _ ⟨n, rfl⟩; exact hfc n) e he
      refine ⟨d, hd, ?_⟩
      intro w hw i
      obtain ⟨n, hn⟩ := i.property
      have hi : F i = f n := by
        change UniformOnFun.toFun 𝒦 i = f n
        rw [← hn]
        rfl
      rw [hi]
      simpa only [dist_comm] using hd' _ (mem_range_self n) w hw
    exact he.equicontinuousWithinAt _
  · intro K hK z hz
    exact ⟨univ, isCompact_univ, fun _ _ => mem_univ _⟩

theorem spherical_subsequence_of_local_normality {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → OnePoint ℂ} (hfc : ∀ n, Continuous (f n))
    (hN : ∀ z ∈ U, IsNormalAt (range f) z) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → OnePoint ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by
  let 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  have h𝔖 : ∀ K ∈ 𝔖, IsCompact K := fun _ h => h.2
  have : (𝓤 (ℂ →ᵤ[𝔖] OnePoint ℂ)).IsCountablyGenerated := by
    have := hU.locallyCompactSpace
    have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
    let e : CompactExhaustion U := default
    apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n => (↑) '' e n)
    · intro n
      exact ⟨image_val_subset, (e.isCompact n).image continuous_subtype_val⟩
    · exact monotone_image.comp e.subset
    · rintro K ⟨hKU, hK⟩
      lift K to Set U using hKU
      rw [← Subtype.isCompact_iff] at hK
      exact (e.exists_superset_of_isCompact hK).imp (fun n hn => by gcongr)
  let F : (ℂ →ᵤ[𝔖] OnePoint ℂ) → ℂ → OnePoint ℂ := UniformOnFun.toFun 𝔖
  let q : ℕ → (ℂ →ᵤ[𝔖] OnePoint ℂ) := fun n => UniformOnFun.ofFun 𝔖 (f n)
  let B : Set (ℂ →ᵤ[𝔖] OnePoint ℂ) := range q
  have hc := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖
    (α := OnePoint ℂ) (s := B) (F := F) .id ?_ ?_
  · obtain ⟨g, _, φ, hφ, ht⟩ := hc.tendsto_subseq
      (fun n => subset_closure (mem_range_self n))
    refine ⟨φ, F g, hφ, ?_⟩
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hU,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖, F, q, Function.comp_def] using ht
  · rintro K ⟨hKU, _⟩ z hz
    have he : EquicontinuousAt (fun i : B => F i) z := by
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hd⟩ := (hN z (hKU hz)).equicontinuousAt
        (by rintro _ ⟨n, rfl⟩; exact hfc n) ε hε
      refine ⟨δ, hδ, ?_⟩
      intro w hw i
      obtain ⟨n, hn⟩ := i.property
      have hi : F i = f n := by change UniformOnFun.toFun 𝔖 i = f n; rw [← hn]; rfl
      rw [hi]
      simpa only [dist_comm] using hd _ (mem_range_self n) w hw
    exact he.equicontinuousWithinAt _
  · intro K hK z hz
    exact ⟨univ, isCompact_univ, fun _ _ => mem_univ _⟩

end AreaDeficit
