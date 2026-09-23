import EremenkosConjecture.NormalizedData
import EremenkosConjecture.UniformEscapeConstruction
import EremenkosConjecture.Transcendence
import ComplexDynamics.Wandering

/-! # Wandering compacta contained in the unit disk -/

open Set Metric Function ComplexDynamics

namespace EremenkosConjecture

/-- Data sufficient to deduce all dynamical conclusions of Theorem 3.1.
The trapping set also permits an elementary proof after affine conjugation. -/
structure UniformWanderingWitness (K : Set ℂ) where
  f : ℂ → ℂ
  transcendental : IsTranscendentalEntire f
  B : Set ℂ
  compactB : IsCompact B
  escape : EscapesUniformlyOn f K
  disjoint : ∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)
  boundary : frontier K ⊆ closure (trappedSet f B)
  ambient : ∀ n, ∃ H : ℂ ≃ₜ ℂ, EqOn (f^[n]) H K

theorem UniformWanderingWitness.julia_boundary {K : Set ℂ} (W : UniformWanderingWitness K)
    (hK : IsClosed K) : frontier K ⊆ juliaSet W.f := by
  intro z hz
  exact mem_juliaSet_of_escape_of_closure_trappedSet W.transcendental.1.continuous W.compactB
    (W.escape.subset_escapingSet (hK.closure_eq ▸ hz.1)) (W.boundary hz)

theorem UniformWanderingWitness.wandering {K : Set ℂ} (W : UniformWanderingWitness K)
    (hK : IsCompact K) : ∀ z ∈ interior K,
    IsWanderingDomain W.f (connectedComponentIn (interior K) z) :=
  wandering_of_uniformEscape_of_trappedBoundary W.f W.transcendental.1.continuous K W.B
    hK W.compactB W.escape W.boundary W.ambient W.disjoint

theorem exists_uniformWanderingWitness_normalized (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hne : K.Nonempty) (hnorm : K ⊆ targetDisc 0) :
    Nonempty (UniformWanderingWitness K) := by
  obtain ⟨D, hKD, hcap, hboundary⟩ := exists_uniformEscapeData K hK hfull hnorm
  obtain ⟨f, hf, htrap, hpoints, hmaps, hcharts⟩ := D.exists_entire_uniform_escape_itinerary
  have hmapK (n : ℕ) : MapsTo (f^[n]) K (targetDisc n) :=
    fun z hz => (hmaps n).2 (hKD n hz)
  have hescape := escapesUniformlyOn_of_targetDiscs f K hmapK
  have hdisjoint : ∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K) :=
    fun n m hnm => (disjoint_targetDisc hnm).mono (hmapK n).image_subset (hmapK m).image_subset
  have htrapSub : trappingDisc ⊆ controlDisc 0 := by
    simpa only [controlDisc, trappingDisc, Nat.cast_zero, mul_zero, add_zero] using
      (ball_subset_closedBall : ball (-3 : ℂ) 1 ⊆ closedBall (-3) 1)
  have hforward : MapsTo f (controlDisc 0) (controlDisc 0) := fun z hz => htrapSub (htrap hz)
  have hP : (⋃ n, D.P n) ⊆ trappedSet f (controlDisc 0) := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact mem_trappedSet_of_iterate_mem hforward (htrapSub (hpoints n hn))
  obtain ⟨z, hz⟩ := hne
  refine ⟨{
    f := f
    transcendental := transcendental_of_targetDiscs_and_trapping f hf z (fun n => hmapK n hz) htrap
    B := controlDisc 0
    compactB := isCompact_closedBall _ _
    escape := hescape
    disjoint := hdisjoint
    boundary := hboundary.trans (closure_mono hP)
    ambient := ?_
  }⟩
  intro n
  obtain ⟨H, V, hV, hDV, heq, hH, hHi⟩ := hcharts n
  exact ⟨H, fun z hz => heq (hDV (hKD n hz))⟩

/-- Theorem 3.1 for nonempty full compacta contained in the unit disk. -/
theorem wandering_compactum_normalized (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hne : K.Nonempty) (hnorm : K ⊆ targetDisc 0) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧
      (∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)) ∧
      EscapesUniformlyOn f K ∧ frontier K ⊆ juliaSet f ∧
      ∀ z ∈ interior K, IsWanderingDomain f (connectedComponentIn (interior K) z) := by
  obtain ⟨W⟩ := exists_uniformWanderingWitness_normalized K hK hfull hne hnorm
  exact ⟨W.f, W.transcendental, W.disjoint, W.escape, W.julia_boundary hK.isClosed, W.wandering hK⟩

end EremenkosConjecture
