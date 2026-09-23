import Runge.MarkedMeromorphicApproximation
import FunctionTheory.Analytic.FiniteOrbitMarks
import FunctionTheory.Topology.IterateApproximationDomains
import Mathlib.Data.Finset.Lattice.Fold

open Set Filter Polynomial FunctionTheory
open scoped Topology

namespace Runge

set_option autoImplicit false

/-- One meromorphic Runge approximation can retain finitely many return
maps, with independent lengths and error bounds. Intermediate orbit domains
and regularity survive, and values and centred local degrees of all marked
returns are preserved exactly. -/
theorem meromorphic_approximation_preserving_finite_returns
    {I : Type*} [Fintype I] [Nonempty I]
    (A : Set ℂ) (hA : IsCompact A) (g : ℂ → ℂ) (hg : MeromorphicOn g A)
    (K : I → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (n : I → ℕ) (U : I → ℕ → Set ℂ)
    (hU : ∀ i j, j < n i → IsOpen (U i j))
    (hUA : ∀ i j, j < n i → U i j ⊆ A)
    (hgU : ∀ i j, j < n i → AnalyticOnNhd ℂ g (U i j))
    (horbit : ∀ i j, j < n i → MapsTo (g^[j]) (K i) (U i j))
    (C : I → Finset ℂ) (hC : ∀ i c, c ∈ C i → c ∈ K i)
    (hnc : ∀ i c, c ∈ C i → ¬ ∀ᶠ z in 𝓝 c, g^[n i] z = g^[n i] c)
    (ε : ℝ) (hε : 0 < ε) (η : I → ℝ) (hη : ∀ i, 0 < η i) :
    ∃ f : ℂ → ℂ, MeromorphicOn f univ ∧
      AnalyticOnNhd ℂ (fun z => g z - f z) A ∧
      (∀ z ∈ A, ‖g z - f z‖ < ε) ∧
      (∀ i j, j ≤ n i → ∀ z ∈ K i, dist (f^[j] z) (g^[j] z) < η i) ∧
      (∀ i j, j < n i → MapsTo (f^[j]) (K i) (U i j)) ∧
      (∀ i j, j < n i → AnalyticOnNhd ℂ f (U i j)) ∧
      ∀ i c, c ∈ C i →
        f^[n i] c = g^[n i] c ∧
        analyticOrderAt (fun z => f^[n i] z - f^[n i] c) c =
          analyticOrderAt (fun z => g^[n i] z - g^[n i] c) c := by
  classical
  choose d hd H using fun i =>
    iterate_approximation_on_compact_with_domains g (U i) (K i) (hK i) (n i)
      (hU i) (fun j hj => (hgU i j hj).continuousOn) (horbit i) (η i) (hη i)
  let τ : ℝ := min ε (Finset.univ.inf' Finset.univ_nonempty d)
  have hτ : 0 < τ :=
    lt_min hε ((Finset.lt_inf'_iff _).mpr (fun i _ => hd i))
  have hτd : ∀ i, τ ≤ d i := fun i =>
    (min_le_right _ _).trans (Finset.inf'_le d (Finset.mem_univ i))
  have hτeps : τ ≤ ε := min_le_left _ _
  have hreg : ∀ i c, c ∈ C i → ∀ j < n i, AnalyticAt ℂ g (g^[j] c) := by
    intro i c hc j hj
    exact hgU i j hj _ (horbit i j hj (hC i c hc))
  let S : Finset ℂ := Finset.univ.biUnion (fun i => finiteOrbitMarks g (C i) (n i))
  have hS : ∀ a, a ∈ S ↔ ∃ i, a ∈ finiteOrbitMarks g (C i) (n i) := by
    intro a
    simp only [S,Finset.mem_biUnion,Finset.mem_univ,true_and]
  have hSA : ∀ a ∈ S, a ∈ A := by
    intro a ha
    obtain ⟨i,hi⟩ := (hS a).mp ha
    obtain ⟨j,hj,c,hc,rfl⟩ := mem_finiteOrbitMarks.mp hi
    exact hUA i j hj (horbit i j hj (hC i c hc))
  have hSr : ∀ a ∈ S, AnalyticAt ℂ g a ∧ ¬ ∀ᶠ z in 𝓝 a, g z = g a := by
    intro a ha
    obtain ⟨i,hi⟩ := (hS a).mp ha
    exact finiteOrbitMarks_analytic_and_nonconstant (hreg i) (hnc i) a hi
  have hP : MeetsBoundedComplementComponents A univ := by
    intro a ha _
    exact ⟨a,mem_connectedComponentIn ha,mem_univ a⟩
  obtain ⟨p,q,f,_,_,hf,_,herr,hclose,hregular,hmarks⟩ :=
    meromorphic_approximation_preserving_marked_local_degrees A hA univ hP g hg S hSA
      (fun a ha => (hSr a ha).1) (fun a ha => (hSr a ha).2) τ hτ
  have hfU : ∀ i j, j < n i → AnalyticOnNhd ℂ f (U i j) := by
    intro i j hj z hz
    exact hregular z (hUA i j hj hz) (hgU i j hj z hz)
  have Happrox : ∀ i,
      (∀ j ≤ n i, ∀ z ∈ K i, dist (f^[j] z) (g^[j] z) < η i) ∧
      ∀ j < n i, MapsTo (f^[j]) (K i) (U i j) := by
    intro i
    apply H i f
    intro j hj z hz
    rw [dist_eq_norm,norm_sub_rev]
    exact (hclose z (hUA i j hj hz)).trans_le (hτd i)
  have hmark : ∀ i c, c ∈ C i → ∀ j < n i, g^[j] c ∈ S := by
    intro i c hc j hj
    exact (hS _).mpr ⟨i,mem_finiteOrbitMarks.mpr ⟨j,hj,c,hc,rfl⟩⟩
  refine ⟨f,hf,herr,(fun z hz => (hclose z hz).trans_le hτeps),
    (fun i => (Happrox i).1),(fun i => (Happrox i).2),hfU,?_⟩
  intro i c hc
  exact iterate_value_and_local_degree_eq_of_finite_orbit_data (hreg i c hc)
    (fun j hj => hregular _ (hSA _ (hmark i c hc j hj)) (hreg i c hc j hj))
    (fun j hj => (hmarks _ (hmark i c hc j hj)).1)
    (fun j hj => (hmarks _ (hmark i c hc j hj)).2)

end Runge
