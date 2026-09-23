import EremenkosConjecture.IterateApproximation
import EremenkosConjecture.Univalence
import EremenkosConjecture.ConformalCharts
import ComplexDynamics.Iteration
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set Metric Function

namespace EremenkosConjecture

/-- Compact univalent-iterate stability, the injectivity and orbit-control
parts of Corollary 2.7. A conformal inverse of the reference iterate supplies
the local isomorphism on its domain. -/
theorem approximate_univalent_iterates_on_compact
    (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (n : ℕ) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : EqOn (g^[n]) e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (horbit : ∀ k < n, MapsTo (g^[k]) e.source U)
    (K : Set ℂ) (hK : IsCompact K) (hKG : K ⊆ e.source)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      (∀ z ∈ U, dist (f z) (g z) < δ) →
      InjOn (f^[n]) K ∧
      (∀ k ≤ n, ∀ z ∈ K, dist ((f^[k]) z) ((g^[k]) z) < ε) ∧
      (∀ k < n, MapsTo (f^[k]) K U) := by
  obtain ⟨W, hW, hKW, hWG, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK e.open_source hKG
  let e' := e.restrOpen W hW
  have hKe' : K ⊆ e'.source := fun z hz => ⟨hKG hz, hKW hz⟩
  have he'i : DifferentiableOn ℂ e'.symm e'.target := hei.mono (fun z hz => hz.1)
  obtain ⟨η, hη, Hη⟩ := exists_injective_approximation_tolerance e' he'i K hK hKe'
  obtain ⟨δ, hδ, Hδ⟩ := iterate_approximation_on_compact g U (closure W) hWc hU
    hg.continuousOn n (fun k hk z hz => horbit k hk (hWG hz))
    (min ε η) (lt_min hε hη)
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  obtain ⟨happrox, hdom⟩ := Hδ f hclose
  have hfn : DifferentiableOn ℂ (f^[n]) e'.source :=
    ComplexDynamics.differentiableOn_iterate_of_mapsTo f U e'.source hf n
      (fun k hk z hz => hdom k hk (subset_closure hz.2))
  have hfnclose : ∀ z ∈ e'.source, dist ((f^[n]) z) (e' z) ≤ η := by
    intro z hz
    change dist ((f^[n]) z) (e z) ≤ η
    rw [← he hz.1]
    exact ((happrox n le_rfl z (subset_closure hz.2)).trans_le (min_le_right _ _)).le
  refine ⟨(Hη (f^[n]) hfn hfnclose).1, ?_, ?_⟩
  · intro k hk z hz
    exact (happrox k hk z (subset_closure (hKW hz))).trans_le (min_le_left _ _)
  · intro k hk z hz
    exact hdom k hk (subset_closure (hKW hz))

/-- Iteration stability with an ambient conformal extension near the compact
set. This is the stronger invariant used in the polynomial induction. -/
theorem approximate_ambient_conformal_iterates_on_compact
    (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (n : ℕ) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : EqOn (g^[n]) e e.source) (hei : DifferentiableOn ℂ e.symm e.target)
    (H : ℂ ≃ₜ ℂ) (heH : EqOn e H e.source)
    (horbit : ∀ k < n, MapsTo (g^[k]) e.source U)
    (K : Set ℂ) (hK : IsCompact K) (hKG : K ⊆ e.source)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      (∀ z ∈ U, dist (f z) (g z) < δ) →
      (∃ (G : ℂ ≃ₜ ℂ) (V : Set ℂ), IsOpen V ∧ K ⊆ V ∧ V ⊆ e.source ∧
        EqOn (f^[n]) G V ∧ DifferentiableOn ℂ G V ∧
          DifferentiableOn ℂ G.symm (G '' V)) ∧
      (∀ k ≤ n, ∀ z ∈ K, dist ((f^[k]) z) ((g^[k]) z) < ε) ∧
      (∀ k < n, MapsTo (f^[k]) K U) := by
  obtain ⟨W, hW, hKW, hWG, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK e.open_source hKG
  let e' := e.restrOpen W hW
  have hehol : DifferentiableOn ℂ e e.source :=
    (ComplexDynamics.differentiableOn_iterate_of_mapsTo g U e.source hg n horbit).congr he.symm
  have he'hol : DifferentiableOn ℂ e' e'.source := hehol.mono inter_subset_left
  have hKe' : K ⊆ e'.source := fun z hz => ⟨hKG hz, hKW hz⟩
  have he'i : DifferentiableOn ℂ e'.symm e'.target := hei.mono (fun z hz => hz.1)
  have he'H : EqOn e' H e'.source := fun z hz => heH hz.1
  obtain ⟨η, hη, Hη⟩ := exists_ambient_conformal_approximation_tolerance
    e' he'hol he'i H he'H K hK hKe'
  obtain ⟨δ, hδ, Hδ⟩ := iterate_approximation_on_compact g U (closure W) hWc hU
    hg.continuousOn n (fun k hk z hz => horbit k hk (hWG hz))
    (min ε η) (lt_min hε hη)
  refine ⟨δ, hδ, fun f hf hclose => ?_⟩
  obtain ⟨happrox, hdom⟩ := Hδ f hclose
  have hfn : DifferentiableOn ℂ (f^[n]) e'.source :=
    ComplexDynamics.differentiableOn_iterate_of_mapsTo f U e'.source hf n
      (fun k hk z hz => hdom k hk (subset_closure hz.2))
  have hfnclose : ∀ z ∈ e'.source, dist ((f^[n]) z) (e' z) ≤ η := by
    intro z hz
    change dist ((f^[n]) z) (e z) ≤ η
    rw [← he hz.1]
    exact ((happrox n le_rfl z (subset_closure hz.2)).trans_le (min_le_right _ _)).le
  obtain ⟨G, V, hV, hKV, hVe', heq, hG, hGi⟩ := Hη (f^[n]) hfn hfnclose
  refine ⟨⟨G, V, hV, hKV, fun z hz => (hVe' hz).1, heq, hG, hGi⟩, ?_, ?_⟩
  · intro k hk z hz
    exact (happrox k hk z (subset_closure (hKW hz))).trans_le (min_le_left _ _)
  · intro k hk z hz
    exact hdom k hk (subset_closure (hKW hz))

end EremenkosConjecture
