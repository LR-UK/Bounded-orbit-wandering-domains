module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.DenseFinitePunctures

@[expose] public section

/-! # Fatou transfer of a uniform chart gain estimate -/

open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace AreaDeficit.Surfaces

/-- A fixed compact-chart gain bound passes to a pointwise limit. The
geometric work in the kernel theorem is to supply the stated convergence. -/
theorem chart_gain_bound_of_pointwise_limit {A : Set ℂ}
    (hA : MeasurableSet A) (g : ℂ → ℝ≥0∞)
    (gseq : ℕ → ℂ → ℝ≥0∞) (hg : ∀ n, Measurable (gseq n))
    (hlim : ∀ z ∈ A, Tendsto (fun n => gseq n z) atTop (𝓝 (g z)))
    {B : ℝ≥0∞} (hB : ∀ n, (∫⁻ z in A, gseq n z) ≤ B) :
    (∫⁻ z in A, g z) ≤ B := by
  calc
    (∫⁻ z in A, g z) =
        ∫⁻ z in A, liminf (fun n => gseq n z) atTop := by
          apply setLIntegral_congr_fun hA
          intro z hz
          exact (hlim z hz).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ z in A, gseq n z) atTop := by
      exact lintegral_liminf_le (μ := volume.restrict A) hg
    _ ≤ B := by
      have hh : liminf (fun n => ∫⁻ z in A, gseq n z) atTop ≤
          liminf (fun _ : ℕ => B) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hB)
      simpa using hh

end AreaDeficit.Surfaces
