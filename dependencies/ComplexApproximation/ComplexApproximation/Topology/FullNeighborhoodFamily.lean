import ComplexApproximation.Topology.FullCompactSets
import FunctionTheory.Topology.LocallyFiniteCompactFamily
import FunctionTheory.Topology.BoundaryBarriers
import Mathlib.Analysis.Normed.Module.Connected

open Set Filter Metric
open scoped Topology

namespace ComplexApproximation

set_option autoImplicit false

/-- Disjoint escaping full compacta have escaping open neighbourhoods
whose compact closures are full and pairwise disjoint. -/
theorem exists_disjoint_escaping_open_full_neighborhoods
    (K U : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (hfull : ∀ n, IsConnected (K n)ᶜ)
    (hdis : Pairwise (fun n m => Disjoint (K n) (K m)))
    (hescape : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K n, R < ‖z‖)
    (hU : ∀ n, IsOpen (U n)) (hKU : ∀ n, K n ⊆ U n) :
    ∃ W : ℕ → Set ℂ,
      (∀ n, IsOpen (W n)) ∧ (∀ n, K n ⊆ W n) ∧
      (∀ n, IsCompact (closure (W n))) ∧
      (∀ n, IsConnected (closure (W n))ᶜ) ∧
      (∀ n, closure (W n) ⊆ U n) ∧
      Pairwise (fun n m => Disjoint (closure (W n)) (closure (W m))) ∧
      ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ closure (W n), R < ‖z‖ := by
  obtain ⟨V, hVo, hKV, hVc, hVU, hVdis, hVe⟩ :=
    FunctionTheory.exists_disjoint_escaping_open_neighborhoods K U hK hdis hescape hU hKU
  have H : ∀ n, ∃ W : Set ℂ, IsOpen W ∧ K n ⊆ W ∧ IsCompact (closure W) ∧
      IsConnected (closure W)ᶜ ∧ closure W ⊆ V n := fun n =>
    exists_open_full_compact_neighbourhood (K n) (V n) (hK n) (hfull n) (hVo n) (hKV n)
  choose W hWo hKW hWc hWf hWV using H
  have hsub : ∀ n, closure (W n) ⊆ closure (V n) := fun n => (hWV n).trans subset_closure
  exact ⟨W, hWo, hKW, hWc, hWf, fun n => (hsub n).trans (hVU n),
    fun n m hnm => (hVdis hnm).mono (hsub n) (hsub m),
    fun R => (hVe R).mono (fun n hn z hz => hn z (hsub n hz))⟩

/-- The two independent approximation pieces can both be chosen full:
one around the model compact and one around its finite exterior targets. -/
theorem exists_full_boundary_barrier_neighborhood
    {K W : Set ℂ} (hK : IsCompact K) (hfull : IsConnected Kᶜ)
    (hW : IsOpen W) (hKW : K ⊆ W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Q R U : Set ℂ),
      Q.Finite ∧ Q ⊆ W \ K ∧ frontier K ⊆ thickening δ Q ∧
      IsCompact R ∧ IsConnected Rᶜ ∧ Q ⊆ interior R ∧ R ⊆ W \ K ∧
      IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧
      IsConnected (closure U)ᶜ ∧ closure U ⊆ W ∧ Disjoint (closure U) R := by
  obtain ⟨Q, _, _, hQfin, hQsub, hcover, _⟩ :=
    FunctionTheory.exists_boundary_barrier_neighborhood hK hW hKW hδ
  have hQfull : IsConnected Qᶜ :=
    hQfin.countable.isConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]
      norm_num)
  obtain ⟨R, hRc, hRf, hQR, hRW⟩ :=
    exists_full_compact_neighbourhood Q (W \ K) hQfin.isCompact hQfull
      (hW.sdiff hK.isClosed) hQsub
  have hKWout : K ⊆ W \ R := by
    intro z hz
    exact ⟨hKW hz, fun hr => (hRW hr).2 hz⟩
  obtain ⟨U, hU, hKU, hUc, hUf, hUR⟩ :=
    exists_open_full_compact_neighbourhood K (W \ R) hK hfull
      (hW.sdiff hRc.isClosed) hKWout
  exact ⟨Q, R, U, hQfin, hQsub, hcover, hRc, hRf, hQR, hRW,
    hU, hKU, hUc, hUf, fun z hz => (hUR hz).1,
    disjoint_left.mpr (fun z hz hzr => (hUR hz).2 hzr)⟩

end ComplexApproximation
