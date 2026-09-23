import EremenkosConjecture.IterateApproximation
import ComplexDynamics.Iteration
import Mathlib.Data.Finset.Lattice.Fold

/-! # Stability of compact orbit constraints -/

open Set Metric Function

namespace EremenkosConjecture

/-- A compact finite orbit landing in an open target still lands there after
a sufficiently small uniform perturbation on its domain. -/
theorem exists_iterate_target_tolerance (g : ℂ → ℂ) (U K V : Set ℂ)
    (hK : IsCompact K) (hU : IsOpen U) (hg : ContinuousOn g U)
    (n : ℕ) (horbit : ∀ k < n, MapsTo (g^[k]) K U)
    (hV : IsOpen V) (hmap : MapsTo (g^[n]) K V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ,
      (∀ z ∈ U, dist (f z) (g z) < δ) → MapsTo (f^[n]) K V := by
  have hcont := ComplexDynamics.continuousOn_iterate_of_mapsTo g U K hg n horbit
  obtain ⟨r, hr, htube⟩ := (hK.image_of_continuousOn hcont).exists_thickening_subset_open
    hV hmap.image_subset
  obtain ⟨δ, hδ, Hδ⟩ := iterate_approximation_on_compact g U K hK hU hg n horbit r hr
  refine ⟨δ, hδ, fun f hf z hz => htube ?_⟩
  exact mem_thickening_iff.mpr ⟨(g^[n]) z, mem_image_of_mem _ hz, (Hδ f hf).1 n le_rfl z hz⟩

/-- A finite family of approximation tolerances has a common positive lower
bound. The formulation also covers an empty indexing type. -/
theorem exists_common_positive_tolerance {ι : Type*} [Finite ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  classical
  let := Fintype.ofFinite ι
  by_cases hi : Nonempty ι
  · let := hi
    refine ⟨Finset.univ.inf' Finset.univ_nonempty r, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff _).mpr (fun i _ => hr i)
    · intro i
      exact Finset.inf'_le r (Finset.mem_univ i)
  · exact ⟨1, zero_lt_one, fun i => False.elim (hi ⟨i⟩)⟩

/-- Properties stable under uniform holomorphic approximation on `U`. -/
def ApproximationStable (g : ℂ → ℂ) (U : Set ℂ) (P : (ℂ → ℂ) → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
    (∀ z ∈ U, dist (f z) (g z) < δ) → P f

theorem ApproximationStable.and {g : ℂ → ℂ} {U : Set ℂ}
    {P Q : (ℂ → ℂ) → Prop} (hP : ApproximationStable g U P)
    (hQ : ApproximationStable g U Q) : ApproximationStable g U (fun f => P f ∧ Q f) := by
  obtain ⟨δ, hδ, Hδ⟩ := hP
  obtain ⟨ε, hε, Hε⟩ := hQ
  exact ⟨min δ ε, lt_min hδ hε, fun f hf hc =>
    ⟨Hδ f hf (fun z hz => (hc z hz).trans_le (min_le_left _ _)),
     Hε f hf (fun z hz => (hc z hz).trans_le (min_le_right _ _))⟩⟩

theorem ApproximationStable.forall_finite {ι : Type*} [Finite ι]
    {g : ℂ → ℂ} {U : Set ℂ} {P : ι → (ℂ → ℂ) → Prop}
    (hP : ∀ i, ApproximationStable g U (P i)) :
    ApproximationStable g U (fun f => ∀ i, P i f) := by
  classical
  choose r hr hcontrol using hP
  obtain ⟨δ, hδ, hδr⟩ := exists_common_positive_tolerance r hr
  exact ⟨δ, hδ, fun f hf hc i =>
    hcontrol i f hf (fun z hz => (hc z hz).trans_le (hδr i))⟩

theorem ApproximationStable.mono {g : ℂ → ℂ} {U : Set ℂ}
    {P Q : (ℂ → ℂ) → Prop} (hP : ApproximationStable g U P)
    (hPQ : ∀ f, P f → Q f) : ApproximationStable g U Q := by
  obtain ⟨δ, hδ, Hδ⟩ := hP
  exact ⟨δ, hδ, fun f hf hc => hPQ f (Hδ f hf hc)⟩

theorem approximationStable_iterate_target (g : ℂ → ℂ) (U K V : Set ℂ)
    (hK : IsCompact K) (hU : IsOpen U) (hg : ContinuousOn g U)
    (n : ℕ) (horbit : ∀ k < n, MapsTo (g^[k]) K U)
    (hV : IsOpen V) (hmap : MapsTo (g^[n]) K V) :
    ApproximationStable g U (fun f => MapsTo (f^[n]) K V) := by
  obtain ⟨δ, hδ, Hδ⟩ := exists_iterate_target_tolerance g U K V hK hU hg n horbit hV hmap
  exact ⟨δ, hδ, fun f _ hc => Hδ f hc⟩

end EremenkosConjecture
