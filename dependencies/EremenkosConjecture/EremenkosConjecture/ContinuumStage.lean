import EremenkosConjecture.ContinuumNeighbourhoods
import EremenkosConjecture.RayStage
import EremenkosConjecture.ConformalEmbedding
import ComplexApproximation.Topology.HomeomorphicTail

open Set Metric Function

namespace EremenkosConjecture

open Scaffolding

/-- Local chart information for an iterate on a closed inset. Forward and
inverse uniform continuity supply the approximation margins; the tail condition
transports the approximation sets. -/
structure LocalIterateChart (f : ℂ → ℂ) (n : ℕ) (P : Set ℂ) where
  chart : OpenPartialHomeomorph ℂ ℂ
  agrees : ∀ z, chart z = (f^[n]) z
  contains : P ⊆ chart.source
  connected_source : IsConnected chart.source
  inverse_holomorphic : DifferentiableOn ℂ chart.symm chart.target
  forward_uniform : UniformContinuousOn chart P
  inverse_uniform : UniformContinuousOn chart.symm (chart '' P)
  tail : ComplexApproximation.HasHomeomorphicTailOn chart P

theorem exists_zero_localIterateChart (f : ℂ → ℂ) (P : Set ℂ) :
    Nonempty (LocalIterateChart f 0 P) := by
  refine ⟨{
    chart := OpenPartialHomeomorph.refl ℂ
    agrees := fun _ => rfl
    contains := subset_univ _
    connected_source := isConnected_univ
    inverse_holomorphic := differentiableOn_id
    forward_uniform := uniformContinuous_id.uniformContinuousOn
    inverse_uniform := uniformContinuous_id.uniformContinuousOn
    tail := ⟨∅, isCompact_empty, Homeomorph.refl ℂ, fun _ _ => rfl⟩ }⟩

/-- The recursive invariant for a prescribed continuum. The neighbourhood
family is fixed; the depth increases as the construction chooses smaller insets.
No successor existence is assumed in this definition. -/
structure ContinuumStage {X : Set ℂ}
    (D : ContinuumNeighbourhoods X rayBase (1 / 16)) (j : ℕ) where
  f : ℂ → ℂ
  entire : Differentiable ℂ f
  depth : ℕ
  reserve : ℝ
  reserve_pos : 0 < reserve
  affine : ∀ z ∈ closedSourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100 - reserve
  trapping : ∀ z ∈ trappingDisk, ‖f z‖ ≤ 1 / 4 - reserve
  charts : ∀ k ≤ returnTime j, Nonempty (LocalIterateChart f k (D.region depth))
  orbitTubes : ∀ k < returnTime j,
    HasUniformTube ((f^[k]) '' D.region depth) (background j)
  targetMargin : ∃ d : ℝ, 0 < d ∧ ∀ z ∈ D.region depth,
    (height j + 7) / 4 + d ≤ ((f^[returnTime j]) z).im ∧
      ((f^[returnTime j]) z).im ≤ (height j + 11) / 4 - d

theorem exists_initial_continuumStage {X : Set ℂ}
    (D : ContinuumNeighbourhoods X rayBase (1 / 16)) :
    Nonempty (ContinuumStage D 0) := by
  obtain ⟨f, hf, hsource, hdisk⟩ := exists_initial_entire (1 / 400) (by norm_num)
  refine ⟨{
    f := f
    entire := hf
    depth := 0
    reserve := 1 / 400
    reserve_pos := by norm_num
    affine := ?_
    trapping := ?_
    charts := ?_
    orbitTubes := ?_
    targetMargin := ?_ }⟩
  · intro z hz
    have h := hsource z hz
    linarith
  · intro z hz
    have h := hdisk z hz
    linarith
  · intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact exists_zero_localIterateChart f (D.region 0)
  · intro k hk
    simp at hk
  · refine ⟨1 / 4, by norm_num, ?_⟩
    intro z hz
    have hi := abs_le.mp (D.region_bounds 0 z hz).2
    norm_num [rayBase, height] at hi ⊢
    constructor <;> linarith [hi.1, hi.2]

end EremenkosConjecture
