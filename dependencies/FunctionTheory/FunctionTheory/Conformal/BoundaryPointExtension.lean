import FunctionTheory.Conformal.SlitTipInverse
import Mathlib.Topology.Separation.Basic

open Set Metric Complex Filter Function
open scoped Topology

namespace FunctionTheory

/-- Adjoin a single boundary point to a continuous injection. A limit there
and a value outside the existing range preserve continuity and injectivity. -/
theorem exists_continuous_injective_extension_at_boundary_point
    {g : ℂ → ℂ} {S : Set ℂ} {ξ c : ℂ}
    (hg : ContinuousOn g S) (hi : InjOn g S) (hξ : ξ ∉ S)
    (hc : c ∉ g '' S) (hlim : Tendsto g (𝓝[S] ξ) (𝓝 c)) :
    ∃ G : ℂ → ℂ, ContinuousOn G (insert ξ S) ∧ InjOn G (insert ξ S) ∧
      EqOn G g S ∧ G ξ = c := by
  classical
  let G := Function.update g ξ c
  have hs : insert ξ S \ {ξ} = S := by
    ext z
    simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff]
    aesop
  have heq : EqOn G g S := by
    intro z hz
    have hzξ : z ≠ ξ := fun h => hξ (h ▸ hz)
    exact Function.update_of_ne hzξ c g
  have hG0 : G ξ = c := Function.update_self _ _ _
  refine ⟨G, ?_, ?_, heq, hG0⟩
  · rw [continuousOn_update_iff, hs]
    exact ⟨hg, fun _ => hlim⟩
  · intro z hz w hw he
    rcases hz with rfl | hz
    · rcases hw with rfl | hw
      · rfl
      · rw [hG0, heq hw] at he
        exact (hc ⟨w, hw, he.symm⟩).elim
    · rcases hw with rfl | hw
      · rw [heq hz, hG0] at he
        exact (hc ⟨z, hz, he⟩).elim
      · exact hi hz hw (by rwa [heq hz, heq hw] at he)

end FunctionTheory
