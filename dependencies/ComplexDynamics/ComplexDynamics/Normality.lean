/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from LR-UK/exp-chaotic, ExpChaotic/Normality.lean.
-/
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

open Function Filter Set
open scoped Topology Uniformity

namespace ComplexDynamics

/-- Every subsequence has a locally uniformly convergent further subsequence.
The limit has precisely the domain `U`. -/
def IsNormalSequenceOn {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    (F : ℕ → α → β) (U : Set α) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : U → β,
      TendstoLocallyUniformly (fun n (z : U) => F (φ (ψ n)) z) g atTop

theorem IsNormalSequenceOn.mono {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ℕ → α → β} {U V : Set α} (h : IsNormalSequenceOn F U) (hVU : V ⊆ U) :
    IsNormalSequenceOn F V := by
  intro φ hφ
  let i : V → U := fun z => ⟨z, hVU z.property⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  obtain ⟨ψ, hψ, g, hg⟩ := h φ hφ
  exact ⟨ψ, hψ, g ∘ i, hg.comp i hi⟩

theorem isNormalSequenceOn_of_tendstoLocallyUniformly
    {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ℕ → α → β} {U : Set α} {g : U → β}
    (h : TendstoLocallyUniformly (fun n (z : U) => F n z) g atTop) :
    IsNormalSequenceOn F U := by
  intro φ hφ
  refine ⟨id, strictMono_id, g, ?_⟩
  intro V hV z
  obtain ⟨t, ht, H⟩ := h V hV z
  exact ⟨t, ht, hφ.tendsto_atTop.eventually H⟩

end ComplexDynamics
