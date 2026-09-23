import EremenkosConjecture.UniformEscapeConstruction
import EremenkosConjecture.Transcendence
import ComplexDynamics.TranscendentalApproximation

/-! # Proposition 3.2 for compact nonseparating boundary subsets -/

open Set Metric Function ComplexDynamics

namespace EremenkosConjecture
namespace UniformEscapeData

theorem exists_polynomial_stage (D : UniformEscapeData) (n : ℕ) :
    ∃ p : Polynomial ℂ, D.StageProperty n p.eval := by
  induction n with
  | zero =>
    exact ⟨Polynomial.C (-3), by simpa using D.stageProperty_initial⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq, _⟩ := D.exists_polynomial_extension n p hp 1 zero_lt_one
    exact ⟨q, hq⟩

/-- **Proposition 3.2.** Prescribe trapping on arbitrary compact nonseparating
subsets of the boundaries of nested full compacta. The conclusion includes
transcendence even if the nested compacta eventually become empty. -/
theorem prescribed_boundary_itinerary (D : UniformEscapeData) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      MapsTo f (controlDisc 0) trappingDisc ∧
      (∀ n, MapsTo (f^[n + 1]) (D.P n) trappingDisc) ∧
      ∀ n, InjOn (f^[n]) (D.K n) ∧ MapsTo (f^[n]) (D.K n) (targetDisc n) := by
  by_cases hne : ∀ n, (D.K n).Nonempty
  · have hcap := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      D.K (fun n => (D.nested n).trans interior_subset) hne (D.compact 0)
      (fun n => (D.compact n).isClosed)
    obtain ⟨z, hz⟩ := hcap
    obtain ⟨f, hf, htrap, hpoints, hmaps, _⟩ := D.exists_entire_uniform_escape_itinerary
    exact ⟨f, transcendental_of_targetDiscs_and_trapping f hf z
      (fun n => (hmaps n).2 (mem_iInter.mp hz n)) htrap, htrap, hpoints, hmaps⟩
  · push Not at hne
    obtain ⟨N, hN⟩ := hne
    have hKN : D.K N = ∅ := hN
    obtain ⟨p, hp⟩ := D.exists_polynomial_stage N
    obtain ⟨δ, hδ, hstable⟩ := D.stageProperty_stability_closed N p hp
    obtain ⟨f, hf, hclose⟩ := exists_transcendentalEntire_near_polynomial p (controlDisc N)
      (isCompact_closedBall _ _) δ hδ
    have hs := hstable f hf.1 (fun z hz => by simpa only [dist_eq_norm] using hclose z hz)
    have hempty (j : ℕ) (hj : N ≤ j) : D.K j = ∅ :=
      subset_empty_iff.mp (hKN ▸ D.antitone hj)
    refine ⟨f, hf, hs.1, ?_, ?_⟩
    · intro n z hz
      by_cases hn : n < N
      · exact hs.2.2.2 n hn hz
      · have H := D.points_subset n hz
        rw [hempty n (by omega)] at H
        exact False.elim H
    · intro n
      by_cases hn : n ≤ N
      · exact ⟨(hs.2.2.1 n hn).injOn, hs.2.1 n hn⟩
      · rw [hempty n (by omega)]
        exact ⟨injOn_empty _, mapsTo_empty _ _⟩

end UniformEscapeData
end EremenkosConjecture
