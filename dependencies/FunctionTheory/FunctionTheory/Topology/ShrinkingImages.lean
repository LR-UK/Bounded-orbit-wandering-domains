import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformConvergence

open Set Filter
open scoped Topology Uniformity

namespace FunctionTheory

set_option autoImplicit false

/-- In a sequentially compact uniform space, a sequence of maps whose image
diameters tend uniformly to zero has a uniformly convergent subsequence.
No continuity or compactness of the source is required. -/
theorem exists_uniformly_convergent_subsequence_of_shrinking_images
    {α β : Type*} [UniformSpace β] [SeqCompactSpace β]
    (F : ℕ → α → β) (U : Set α)
    (hsmall : ∀ V ∈ 𝓤 β, ∀ᶠ n in atTop,
      ∀ x ∈ U, ∀ y ∈ U, (F n x,F n y) ∈ V) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : α → β,
      TendstoUniformlyOn (fun n => F (ψ n)) g atTop U := by
  classical
  by_cases hU : U.Nonempty
  · obtain ⟨a,ha⟩ := hU
    obtain ⟨b,ψ,hψ,hb⟩ := SeqCompactSpace.tendsto_subseq (fun n => F n a)
    refine ⟨ψ,hψ,fun _ => b,?_⟩
    intro V hV
    obtain ⟨W,hW,hWV⟩ := comp_mem_uniformity_sets hV
    have hbase := (tendsto_left_nhds_uniformity.comp hb).eventually hW
    have hdiam := hψ.tendsto_atTop.eventually (hsmall W hW)
    filter_upwards [hbase,hdiam] with n hn hd x hx
    exact hWV ⟨F (ψ n) a,hn,hd a ha x hx⟩
  · refine ⟨id,strictMono_id,F 0,?_⟩
    intro V hV
    exact Eventually.of_forall (fun n x hx => (hU ⟨x,hx⟩).elim)

end FunctionTheory
