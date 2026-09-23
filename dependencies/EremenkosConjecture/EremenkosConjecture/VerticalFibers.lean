import EremenkosConjecture.PlaneTopology

open Set Metric Bornology

namespace EremenkosConjecture

theorem unbounded_component_of_vertical_ray {K : Set ℂ} {z : ℂ}
    {s : ℝ} (hs : |s| = 1)
    (hray : ∀ t : ℝ, 0 ≤ t → (⟨z.re, z.im + s * t⟩ : ℂ) ∉ K) :
    ¬ IsBounded (connectedComponentIn Kᶜ z) := by
  let f : ℝ → ℂ := fun t => ⟨z.re, z.im + s * t⟩
  have hf : Continuous f := by
    have heq : f = fun t => (z.re : ℂ) + ((z.im + s * t : ℝ) : ℂ) * Complex.I := by
      funext t
      apply Complex.ext <;> simp [f]
    rw [heq]
    fun_prop
  have hconn : IsConnected (f '' Ici 0) := isConnected_Ici.image f hf.continuousOn
  have hz : z ∈ f '' Ici 0 := ⟨0, by simp, by simp [f]⟩
  have hsub : f '' Ici 0 ⊆ Kᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hray t ht
  have hcomp := hconn.isPreconnected.subset_connectedComponentIn hz hsub
  intro hbounded
  obtain ⟨R, hRpos, hR⟩ := hbounded.exists_pos_norm_le
  let t := R + |z.im| + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hnorm := hR (f t) (hcomp ⟨t, ht, rfl⟩)
  have him : |z.im + s * t| ≤ R := (Complex.abs_im_le_norm (f t)).trans hnorm
  have htriangle := abs_add_le (z.im + s * t) (-z.im)
  have hst : |s * t| = t := by rw [abs_mul, hs, one_mul, abs_of_nonneg ht]
  have heq : z.im + s * t + -z.im = s * t := by ring
  rw [heq, hst, abs_neg] at htriangle
  dsimp [t] at htriangle
  linarith

/-- A bounded plane set with interval-shaped vertical sections is full. -/
theorem isConnected_compl_of_vertical_fibers {K : Set ℂ} (hK : IsBounded K)
    (hfiber : ∀ x : ℝ, OrdConnected {y : ℝ | (⟨x, y⟩ : ℂ) ∈ K}) :
    IsConnected Kᶜ := by
  apply isConnected_compl_of_unbounded_components K hK
  intro z hz
  by_cases hbelow : ∃ y : ℝ, y ≤ z.im ∧ (⟨z.re, y⟩ : ℂ) ∈ K
  · obtain ⟨y, hy, hyK⟩ := hbelow
    apply unbounded_component_of_vertical_ray (s := 1) (by norm_num)
    intro t ht hmem
    have hzK := (hfiber z.re).out hyK hmem (show z.im ∈ Icc y (z.im + 1 * t) by
      constructor
      · exact hy
      · linarith)
    exact hz hzK
  · apply unbounded_component_of_vertical_ray (s := -1) (by norm_num)
    intro t ht hmem
    exact hbelow ⟨z.im + -1 * t, by linarith, hmem⟩

end EremenkosConjecture
