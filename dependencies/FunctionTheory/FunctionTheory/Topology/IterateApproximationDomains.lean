import FunctionTheory.Topology.FiniteComposition
import FunctionTheory.Analytic.FiniteOrbitLocalDegree
import Mathlib.Topology.MetricSpace.ProperSpace

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A constant sequence of maps gives the usual iterates. -/
theorem finiteComposition_const_eq_iterate {X : Type*} (g : X → X) (n : ℕ) :
    finiteComposition (fun _ => g) n = g^[n] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [finiteComposition, ih, Function.iterate_succ']

/-- Finite-iterate approximation with a separately prescribed open domain
at each intermediate step. All intermediate domain conditions survive. -/
theorem iterate_approximation_on_compact_with_domains
    {X : Type*} [MetricSpace X] (g : X → X) (U : ℕ → Set X)
    (K : Set X) (hK : IsCompact K) (n : ℕ)
    (hU : ∀ k < n, IsOpen (U k)) (hg : ∀ k < n, ContinuousOn g (U k))
    (horbit : ∀ k < n, MapsTo (g^[k]) K (U k)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : X → X,
      (∀ k < n, ∀ z ∈ U k, dist (f z) (g z) < δ) →
      (∀ k ≤ n, ∀ z ∈ K, dist (f^[k] z) (g^[k] z) < ε) ∧
      ∀ k < n, MapsTo (f^[k]) K (U k) := by
  obtain ⟨δ,hδ,H⟩ := finiteComposition_approximation_on_compact
    (fun _ => g) U K hK n hU hg (by
      simpa only [finiteComposition_const_eq_iterate] using horbit) ε hε
  refine ⟨δ,hδ,fun f hf => ?_⟩
  simpa only [finiteComposition_const_eq_iterate] using H (fun _ => f) hf

/-- Analytic finite orbit data on a compact set extend to a relatively
compact open neighbourhood with a strict margin at every prescribed
intermediate domain. -/
theorem exists_open_finite_orbit_neighborhood {g : ℂ → ℂ}
    {K W : Set ℂ} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (U : ℕ → Set ℂ) (n : ℕ)
    (hU : ∀ j < n, IsOpen (U j))
    (hreg : ∀ j < n, AnalyticOnNhd ℂ (g^[j]) K)
    (horbit : ∀ j < n, MapsTo (g^[j]) K (U j)) :
    ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ W ∧ IsCompact (closure V) ∧
      ∀ j < n, AnalyticOnNhd ℂ (g^[j]) (closure V) ∧
        MapsTo (g^[j]) (closure V) (U j) := by
  let S : Fin n → Set ℂ := fun j =>
    {z | AnalyticAt ℂ (g^[j.val]) z} ∩ (g^[j.val]) ⁻¹' U j
  have hSo : ∀ j, IsOpen (S j) := by
    intro j
    have ha : AnalyticOnNhd ℂ (g^[j.val]) {z | AnalyticAt ℂ (g^[j.val]) z} :=
      fun z hz => hz
    exact ha.continuousOn.isOpen_inter_preimage (isOpen_analyticAt ℂ (g^[j.val])) (hU j j.isLt)
  have hP : IsOpen (W ∩ ⋂ j, S j) := hW.inter (isOpen_iInter_of_finite hSo)
  have hKP : K ⊆ W ∩ ⋂ j, S j := by
    intro z hz
    exact ⟨hKW hz,mem_iInter.mpr (fun j => ⟨hreg j j.isLt z hz, horbit j j.isLt hz⟩)⟩
  obtain ⟨V,hV,hKV,hVP,hVc⟩ := exists_open_between_and_isCompact_closure hK hP hKP
  refine ⟨V,hV,hKV,(fun z hz => (hVP hz).1),hVc,?_⟩
  intro j hj
  exact ⟨fun z hz => (mem_iInter.mp (hVP hz).2 ⟨j,hj⟩).1,
    fun z hz => (mem_iInter.mp (hVP hz).2 ⟨j,hj⟩).2⟩

end FunctionTheory
