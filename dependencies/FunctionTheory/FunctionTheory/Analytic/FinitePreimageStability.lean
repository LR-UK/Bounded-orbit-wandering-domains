import FunctionTheory.Analytic.FiniteComposition
import FunctionTheory.Topology.FiniteOrbitDomain
import FunctionTheory.Analytic.PreimageStability
import Mathlib.Tactic

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A finite analytic orbit on a compact set has independent positive target
and map-approximation tolerances giving nearby preimages for every sufficiently
close analytic system. All intermediate evaluations stay in the actual domains.
This is the finite observation saved in the triangle boundary addendum. -/
theorem exists_finite_composition_preimage_stability
    (g : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (N : ℕ) {K : Set ℂ}
    (hK : IsCompact K) (hU : ∀ k < N, IsOpen (U k))
    (hg : ∀ k < N, AnalyticOnNhd ℂ (g k) (U k))
    (horbit : ∀ k < N, MapsTo (finiteComposition g k) K (U k))
    (hnc : ∀ a ∈ K, ∀ k < N, ¬ ∀ᶠ z in 𝓝 (finiteComposition g k a),
      g k z = g k (finiteComposition g k a))
    {η : ℝ} (hη : 0 < η) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧
      ∃ δ > 0, ∃ ρ > 0, ∀ (f : ℕ → ℂ → ℂ) (P : Set ℂ),
        (∀ k < N, AnalyticOnNhd ℂ (f k) (U k)) →
        (∀ k < N, ∀ z ∈ U k, ‖g k z - f k z‖ ≤ ρ) →
        (∀ a ∈ K, infEDist (finiteComposition g N a) P ≤ ENNReal.ofReal δ) →
        (∀ k < N, MapsTo (finiteComposition f k) W (U k)) ∧
        ∀ a ∈ K, ∃ z ∈ W, finiteComposition f N z ∈ P ∧ dist a z < η := by
  have hgc : ∀ k < N, ContinuousOn (g k) (U k) :=
    fun k hk => (hg k hk).continuousOn
  have hD := isOpen_finiteOrbitDomain g U N hU hgc
  have hKD : K ⊆ finiteOrbitDomain g U N := fun a ha k hk => horbit k hk ha
  obtain ⟨W, hW, hKW, hWD, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK hD hKD
  have hWsub : W ⊆ finiteOrbitDomain g U N := subset_closure.trans hWD
  have hGa : AnalyticOnNhd ℂ (finiteComposition g N) W :=
    (analyticOnNhd_finiteOrbitDomain g U N hg).mono hWsub
  have hGnc : ∀ a ∈ K, ¬ ∀ᶠ z in 𝓝 a, finiteComposition g N z = finiteComposition g N a := by
    intro a ha
    exact locally_nonconstant_finiteComposition g N
      (fun k hk => hg k hk _ (horbit k hk ha)) (hnc a ha)
  obtain ⟨δ, hδ, Hδ⟩ := compact_preimage_density_of_approximation
    hW hK hKW hGa hGnc hη
  obtain ⟨ρ, hρ, Hρ⟩ := finiteComposition_approximation_on_compact g U (closure W)
    hWc N hU hgc (fun k hk z hz => hWD hz k hk) (δ / 2) (half_pos hδ)
  refine ⟨W, hW, hKW, hWc, δ, hδ, ρ / 2, half_pos hρ, ?_⟩
  intro f P hf hclose hP
  have Hnear : ∀ k < N, ∀ z ∈ U k, dist (f k z) (g k z) < ρ := by
    intro k hk z hz
    calc
      dist (f k z) (g k z) = ‖g k z - f k z‖ := by rw [dist_eq_norm, norm_sub_rev]
      _ ≤ ρ / 2 := hclose k hk z hz
      _ < ρ := half_lt_self hρ
  obtain ⟨Hdist, Hdomain⟩ := Hρ f Hnear
  have Hfa : AnalyticOnNhd ℂ (finiteComposition f N) W := by
    intro z hz
    exact analyticAt_finiteComposition f N
      (fun k hk => hf k hk _ (Hdomain k hk (subset_closure hz)))
  have Hdiff : ∀ z ∈ W, ‖finiteComposition g N z - finiteComposition f N z‖ < δ := by
    intro z hz
    have H := Hdist N le_rfl z (subset_closure hz)
    have H' : ‖finiteComposition g N z - finiteComposition f N z‖ < δ / 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using H
    exact H'.trans (half_lt_self hδ)
  exact ⟨fun k hk z hz => Hdomain k hk (subset_closure hz),
    Hδ P (finiteComposition f N) hP Hfa Hdiff⟩

end FunctionTheory
