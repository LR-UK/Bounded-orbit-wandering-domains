import ComplexDynamics.Trapping

/-! # Bungee orbits and a Julia criterion from escaping subsequences -/

open Function Filter Set Metric
open scoped Topology Uniformity OnePoint

namespace ComplexDynamics

/-- A bungee orbit is unbounded and does not tend to infinity. -/
def bungeeSet (f : ℂ → ℂ) : Set ℂ := (boundedOrbitSet f ∪ escapingSet f)ᶜ

theorem mem_bungeeSet_iff {f : ℂ → ℂ} {z : ℂ} :
    z ∈ bungeeSet f ↔ z ∉ boundedOrbitSet f ∧ z ∉ escapingSet f := by
  simp [bungeeSet]

/-- An escaping subsequence and a bounded subsequence certify a bungee orbit. -/
theorem mem_bungeeSet_of_subsequences {f : ℂ → ℂ} {z : ℂ} {φ ψ : ℕ → ℕ}
    (hinfty : Tendsto (fun n => ‖(f^[φ n]) z‖) atTop atTop)
    (hψ : Tendsto ψ atTop atTop) {R : ℝ}
    (hbounded : ∀ᶠ n in atTop, ‖(f^[ψ n]) z‖ ≤ R) : z ∈ bungeeSet f := by
  rw [mem_bungeeSet_iff]
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨n, hn⟩ := (hinfty.eventually (eventually_gt_atTop M)).exists
    exact (not_lt_of_ge (hM (φ n))) hn
  · intro hescape
    have ht := (hescape.comp hψ).eventually (eventually_gt_atTop R)
    obtain ⟨n, hn, hn'⟩ := (ht.and hbounded).exists
    exact (not_lt_of_ge hn') hn

/-- Local normality is impossible at a point with an escaping subsequence
when points trapped in a fixed compact set accumulate there. This also
applies to bungee points and requires no Montel theorem. -/
theorem mem_juliaSet_of_escape_subsequence_of_closure_trappedSet {f : ℂ → ℂ}
    (hf : Continuous f) {B : Set ℂ} (hB : IsCompact B) {z : ℂ}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hz : Tendsto (fun n => ‖(f^[φ n]) z‖) atTop atTop)
    (hacc : z ∈ closure (trappedSet f B)) : z ∈ juliaSet f := by
  rintro ⟨U, hU, hzU, hnormal⟩
  obtain ⟨ψ, hψ, g, hg⟩ := hnormal φ hφ
  have hgc : Continuous g := hg.continuous
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
      OnePoint.continuous_coe.comp ((hf.iterate (φ (ψ n))).comp continuous_subtype_val)))
  let S : Set RiemannSphere := (fun w : ℂ => (w : RiemannSphere)) '' B
  have hS : IsClosed S := (hB.image OnePoint.continuous_coe).isClosed
  have hpoint : ∀ w : U, Tendsto (fun n => sphericalIterate f (φ (ψ n)) w)
      atTop (𝓝 (g w)) :=
    fun w => hg.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ w)
  have hsub : ((↑) : U → ℂ) ⁻¹' trappedSet f B ⊆ g ⁻¹' S := by
    intro w hw
    apply hS.mem_of_tendsto (hpoint w)
    exact ((hφ.comp hψ).tendsto_atTop.eventually hw).mono fun n hn =>
      ⟨(f^[φ (ψ n)]) w, hn, rfl⟩
  have hcl : (⟨z, hzU⟩ : U) ∈ closure (((↑) : U → ℂ) ⁻¹' trappedSet f B) :=
    hU.isOpenMap_subtype_val.preimage_closure_subset_closure_preimage hacc
  have hmem : g ⟨z, hzU⟩ ∈ S := closure_minimal hsub (hS.preimage hgc) hcl
  have hzinfty : Tendsto (fun n => sphericalIterate f (φ n) z) atTop
      (𝓝 (∞ : RiemannSphere)) :=
    tendsto_coe_sphere_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hz)
  have heq : g ⟨z, hzU⟩ = (∞ : RiemannSphere) :=
    tendsto_nhds_unique (hpoint ⟨z, hzU⟩) (hzinfty.comp hψ.tendsto_atTop)
  rw [heq] at hmem
  exact OnePoint.infty_notMem_image_coe hmem

end ComplexDynamics

namespace ComplexDynamics

theorem trappedSet_subset_boundedOrbitSet {f : ℂ → ℂ} {B : Set ℂ}
    (hB : Bornology.IsBounded B) : trappedSet f B ⊆ boundedOrbitSet f := by
  intro z hz
  obtain ⟨M, hM, hbound⟩ := hB.exists_pos_norm_le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hz
  refine ⟨max M (∑ k ∈ Finset.range N, ‖(f^[k]) z‖), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hbound _ (hN n hn)).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    exact Finset.single_le_sum (fun k _ => norm_nonneg ((f^[k]) z))
      (Finset.mem_range.mpr (lt_of_not_ge hn))

end ComplexDynamics
