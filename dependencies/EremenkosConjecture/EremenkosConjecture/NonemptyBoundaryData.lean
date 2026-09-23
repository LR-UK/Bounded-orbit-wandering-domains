import EremenkosConjecture.NormalizedData

/-! # Nonempty finite boundary sets for nonempty compacta -/

open Set Metric

namespace EremenkosConjecture

theorem exists_uniformEscapeData_nonempty (K : Set ℂ) (hK : IsCompact K)
    (hfull : IsConnected Kᶜ) (hne : K.Nonempty) (hnorm : K ⊆ targetDisc 0) :
    ∃ D : UniformEscapeData, (∀ n, K ⊆ D.K n) ∧
      (⋂ n, D.K n) = K ∧ frontier K ⊆ closure (⋃ n, D.P n) ∧
      ∀ n, (D.P n).Nonempty := by
  classical
  obtain ⟨D, hKD, hcap, hboundary⟩ := exists_uniformEscapeData K hK hfull hnorm
  have hfront (n : ℕ) : (frontier (D.K n)).Nonempty := by
    apply nonempty_frontier_iff.mpr
    refine ⟨hne.mono (hKD n), ?_⟩
    intro heq
    have H := (D.full n).nonempty
    simpa [heq] using H
  choose a ha using hfront
  let E : UniformEscapeData := { D with
    P := fun n => insert (a n) (D.P n)
    compactP := fun n => (D.compactP n).insert _
    fullP := fun n => isConnected_compl_insert (D.P n) (D.compactP n) (D.fullP n) (a n)
    boundary := fun n => insert_subset (ha n) (D.boundary n) }
  refine ⟨E, hKD, hcap, hboundary.trans (closure_mono ?_), fun n => ⟨a n, Or.inl rfl⟩⟩
  exact iUnion_mono (fun n => subset_insert _ _)

end EremenkosConjecture
