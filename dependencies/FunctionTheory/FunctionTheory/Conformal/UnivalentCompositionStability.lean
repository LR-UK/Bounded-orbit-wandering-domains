import FunctionTheory.Analytic.FinitePreimageStability
import FunctionTheory.Conformal.UnivalenceStability
import TauCeti.Analysis.Complex.Conformal.Biholomorph

open Set Function Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Close perturbations of a finite univalent system have a univalent
composite on a neighbourhood of the initial compact set. The estimate
controls the composite and every intermediate domain at the same time. -/
theorem exists_univalent_finite_composition_tolerance
    (g : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) {K : Set ℂ} (hK : IsCompact K) (N : ℕ)
    (hU : ∀ k<N, IsOpen (U k))
    (hg : ∀ k<N, AnalyticOnNhd ℂ (g k) (U k))
    (hi : ∀ k<N, InjOn (g k) (U k))
    (horbit : ∀ k<N, MapsTo (finiteComposition g k) K (U k))
    {η : ℝ} (hη : 0<η) :
    ∃ δ>0, ∀ f : ℕ → ℂ → ℂ,
      (∀ k<N, AnalyticOnNhd ℂ (f k) (U k)) →
      (∀ k<N, ∀ z∈U k, dist (f k z) (g k z)≤δ) →
      ∃ b : OpenPartialHomeomorph ℂ ℂ,
        K ⊆ b.source ∧ (b : ℂ → ℂ)=finiteComposition f N ∧
        AnalyticOnNhd ℂ b b.source ∧ AnalyticOnNhd ℂ b.symm b.target ∧
        (∀ z∈K, dist (b z) (finiteComposition g N z)<η) ∧
        ∀ k<N, MapsTo (finiteComposition f k) K (U k) := by
  let D := finiteOrbitDomain g U N
  have hD : IsOpen D := isOpen_finiteOrbitDomain g U N hU (fun k hk => (hg k hk).continuousOn)
  have hKD : K ⊆ D := fun z hz k hk => horbit k hk hz
  have hGa : AnalyticOnNhd ℂ (finiteComposition g N) D := analyticOnNhd_finiteOrbitDomain g U N hg
  have hGi : InjOn (finiteComposition g N) D := by
    have H : ∀ k≤N, InjOn (finiteComposition g k) D := by
      intro k hk
      induction k with
      | zero => intro x hx y hy hxy; exact hxy
      | succ k ih => exact (hi k (by omega)).comp (ih (by omega)) (fun z hz => hz k (by omega))
    exact H N le_rfl
  obtain ⟨V,hV,hKV,hVD,hVc⟩ := exists_open_between_and_isCompact_closure hK hD hKD
  obtain ⟨W,hW,hKW,hWV,hWc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  have hVa : AnalyticOnNhd ℂ (finiteComposition g N) V := hGa.mono (subset_closure.trans hVD)
  have hVi : InjOn (finiteComposition g N) V := hGi.mono (subset_closure.trans hVD)
  let e := hVa.differentiableOn.toOpenPartialHomeomorph hV hVi
  have hei : DifferentiableOn ℂ e.symm e.target :=
    hVa.differentiableOn.differentiableOn_toOpenPartialHomeomorph_symm hV hVi
  obtain ⟨a,ha,Ha⟩ := exists_injective_approximation_tolerance e hei (closure W) hWc hWV
  obtain ⟨ρ,hρ,Hρ⟩ := finiteComposition_approximation_on_compact g U (closure V) hVc N hU
    (fun k hk => (hg k hk).continuousOn) (fun k hk z hz => hVD hz k hk)
    (min η a) (lt_min hη ha)
  refine ⟨ρ/2,half_pos hρ,?_⟩
  intro f hf hclose
  obtain ⟨Hdist,Hdom⟩ := Hρ f (fun k hk z hz => (hclose k hk z hz).trans_lt (half_lt_self hρ))
  have hFa : AnalyticOnNhd ℂ (finiteComposition f N) V := by
    intro z hz
    exact analyticAt_finiteComposition f N
      (fun k hk => hf k hk _ (Hdom k hk (subset_closure hz)))
  have hFi : InjOn (finiteComposition f N) (closure W) :=
    (Ha (finiteComposition f N) hFa.differentiableOn (fun z hz =>
      ((Hdist N le_rfl z (subset_closure hz)).trans_le (min_le_right η a)).le)).1
  have hWFa := hFa.mono (subset_closure.trans hWV)
  have hWFi := hFi.mono subset_closure
  let b := hWFa.differentiableOn.toOpenPartialHomeomorph hW hWFi
  refine ⟨b,hKW,rfl,hWFa,?_,?_,?_⟩
  · exact (hWFa.differentiableOn.differentiableOn_toOpenPartialHomeomorph_symm hW hWFi).analyticOnNhd
      b.open_target
  · intro z hz
    exact (Hdist N le_rfl z (subset_closure (hKV hz))).trans_le (min_le_left η a)
  · intro k hk z hz
    exact Hdom k hk (subset_closure (hKV hz))

end FunctionTheory
