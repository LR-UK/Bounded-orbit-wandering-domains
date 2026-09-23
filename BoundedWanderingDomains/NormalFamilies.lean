import BoundedWanderingDomains.RiemannMappingFull
import BoundedWanderingDomains.LocalPunctures
import Mathlib.Topology.Sequences

open Set Metric Function Filter
open scoped Topology Uniformity UniformConvergence

namespace AreaDeficit

/-- Montel compactness for a uniformly bounded family on an arbitrary open
plane set. The conclusion includes holomorphicity of the limit. -/
theorem bounded_holomorphic_subsequence {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {M : ℝ}
    (hd : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ n z, z ∈ U → ‖f n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U ∧
      DifferentiableOn ℂ g U := by
  let 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  have h𝔖 : ∀ K ∈ 𝔖, IsCompact K := fun _ h => h.2
  have : (𝓤 (ℂ →ᵤ[𝔖] ℂ)).IsCountablyGenerated := by
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
  let F : (ℂ →ᵤ[𝔖] ℂ) → ℂ → ℂ := UniformOnFun.toFun 𝔖
  let q : ℕ → (ℂ →ᵤ[𝔖] ℂ) := fun n => UniformOnFun.ofFun 𝔖 (f n)
  let B : Set (ℂ →ᵤ[𝔖] ℂ) := range q
  have hBd : ∀ g ∈ B, DifferentiableOn ℂ (F g) U := by
    rintro g ⟨n, rfl⟩
    exact hd n
  have hBb : ∀ g ∈ B, ∀ z ∈ U, ‖F g z‖ ≤ M := by
    rintro g ⟨n, rfl⟩
    exact hb n
  have hc := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖
    (α := ℂ) (s := B) (F := F) .id ?_ ?_
  · obtain ⟨g, _, φ, hφ, ht⟩ := hc.tendsto_subseq
      (fun n => subset_closure (mem_range_self n))
    have hl : TendstoLocallyUniformlyOn (fun n => f (φ n)) (F g) atTop U := by
      simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hU,
        UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖, F, q, Function.comp_def] using ht
    exact ⟨φ, F g, hφ, hl, hl.differentiableOn (Eventually.of_forall (fun n => hd (φ n))) hU⟩
  · rintro K ⟨hKU, _⟩ z hz
    exact (Complex.equicontinuousAt_of_forall_norm_le (hU.mem_nhds (hKU hz))
      (fun i : B => hBd i i.2) ⟨M, fun i z hz => hBb i i.2 z hz⟩).equicontinuousWithinAt _
  · intro K hK z hz
    exact ⟨closedBall 0 M, isCompact_closedBall 0 M,
      fun g hg => by simpa only [mem_closedBall_zero_iff] using hBb g hg z (hK.1 hz)⟩

/-- Hurwitz plus the open mapping theorem: a nonconstant locally uniform
limit avoids the closure of all values eventually omitted by the family.
The omitted set need not be closed, finite or countable. -/
theorem nonconstant_limit_avoids_closure {U A : Set ℂ}
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hd : ∀ n, DifferentiableOn ℂ (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U)
    (homit : ∀ a ∈ A, ∀ᶠ n in atTop, ∀ z ∈ U, f n z ≠ a)
    (hn : ¬∃ c, ∀ z ∈ U, g z = c) :
    Disjoint (g '' U) (closure A) := by
  have hgd := hl.differentiableOn (Eventually.of_forall hd) hU
  have hga : AnalyticOnNhd ℂ g U := hgd.analyticOnNhd hU
  have hgo : IsOpen (g '' U) :=
    (hga.is_constant_or_isOpen hUc).resolve_left hn U subset_rfl hU
  have havoid : ∀ z ∈ U, g z ∉ A := by
    intro z hz ha
    have hs : TendstoLocallyUniformlyOn (fun n w => f n w - g z)
        (fun w => g w - g z) atTop U := hl.fun_sub
          ((tendsto_const_nhds.tendstoUniformlyOn_const U).tendstoLocallyUniformlyOn)
    have hh := Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn
      hU hUc ((homit (g z) ha).mono (fun n hn w hw => sub_ne_zero.mpr (hn w hw)))
      (Eventually.of_forall (fun n => (hd n).sub_const (g z))) hs
    rcases hh with hc | hc
    · exact hn ⟨g z, fun w hw => sub_eq_zero.mp (hc hw)⟩
    · exact hc z hz (sub_self _)
  apply disjoint_left.mpr
  rintro y hy hyA
  obtain ⟨a, ha, haA⟩ := mem_closure_iff.mp hyA (g '' U) hgo hy
  obtain ⟨z, hz, rfl⟩ := ha
  exact havoid z hz haA

/-- In particular, if the centre value lies in the closure of the
eventually omitted set, any holomorphic limit is constant. -/
theorem limit_constant_at_omitted_closure {U A : Set ℂ}
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {x : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hd : ∀ n, DifferentiableOn ℂ (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U)
    (homit : ∀ a ∈ A, ∀ᶠ n in atTop, ∀ z ∈ U, f n z ≠ a)
    (hbase : g x ∈ closure A) :
    ∃ c, ∀ z ∈ U, g z = c := by
  by_contra hn
  exact disjoint_left.mp (nonconstant_limit_avoids_closure hU hUc hd hl homit hn)
    (mem_image_of_mem g hx) hbase

end AreaDeficit
