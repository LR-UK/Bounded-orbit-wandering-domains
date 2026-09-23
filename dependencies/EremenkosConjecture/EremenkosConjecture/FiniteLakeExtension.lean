import EremenkosConjecture.LakeExtension

open Set Metric Function

namespace EremenkosConjecture

theorem AmbientDisk.enlarge_to_finset (M D : AmbientDisk) {A : Set ℂ}
    (hA : IsCompact A) (hfull : IsConnected Aᶜ) (hAM : A ⊆ M.inside)
    (hDM : D.carrier ⊆ M.inside) (hAD : Disjoint A D.carrier)
    (s : Finset ℂ) (hs : ∀ q ∈ s, q ∈ M.inside \ A) :
    ∃ E : AmbientDisk, D.carrier ⊆ E.carrier ∧ E.carrier ⊆ M.inside \ A ∧
      ∀ q ∈ s, q ∈ E.inside := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨D, Subset.rfl, ?_, by simp⟩
    exact fun z hz => ⟨hDM hz, fun hzA => Set.disjoint_left.mp hAD hzA hz⟩
  | @insert q s hq ih =>
    obtain ⟨E, hDE, hEV, hsE⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
    have hAE : Disjoint A E.carrier := Set.disjoint_left.mpr (fun z hzA hzE => (hEV hzE).2 hzA)
    obtain ⟨F, hEF, hFV, hqF⟩ := M.enlarge_to_point E hA hfull hAM
      (fun z hz => (hEV hz).1) hAE (hs q (Finset.mem_insert_self _ _))
    refine ⟨F, hDE.trans (hEF.trans F.inside_subset), hFV, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hqF
    · exact hEF (E.inside_subset (hsE z hz))

theorem AmbientDisk.shrink_away_finset (M : AmbientDisk) {A : Set ℂ}
    (hA : IsCompact A) (hfull : IsConnected Aᶜ) (hAM : A ⊆ M.inside)
    (s : Finset ℂ) (hs : ∀ q ∈ s, q ∉ A) :
    ∃ E : AmbientDisk, A ⊆ E.inside ∧ E.carrier ⊆ M.carrier ∧
      ∀ q ∈ s, q ∉ E.carrier := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨M, hAM, Subset.rfl, by simp⟩
  | @insert q s hq ih =>
    obtain ⟨E, hAE, hEM, hsE⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
    obtain ⟨F, hAF, hFE, hqF⟩ := E.shrink_away_point hA hfull hAE
      (hs q (Finset.mem_insert_self _ _))
    refine ⟨F, hAF, hFE.trans (E.inside_subset.trans hEM), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hqF
    · exact fun H => hsE z hz (E.inside_subset (hFE H))

/-- A compact subset of the closure of an open land region admits a finite net in that region. -/
theorem exists_finset_net_in_dense {K U : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ closure U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℂ, (∀ q ∈ s, q ∈ U) ∧ ∀ z ∈ K, ∃ q ∈ s, dist z q < ε := by
  classical
  have hcover : K ⊆ ⋃ q ∈ U, ball q ε := by
    intro z hz
    obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp (hKU hz) ε hε
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, hdist⟩⟩
  obtain ⟨s, hsU, hsFinite, hscover⟩ := hK.elim_finite_subcover_image (fun q _ => isOpen_ball) hcover
  refine ⟨hsFinite.toFinset, ?_, ?_⟩
  · intro q hq
    exact hsU (hsFinite.mem_toFinset.mp hq)
  · intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hscover hz)
    obtain ⟨hqs, hdist⟩ := mem_iUnion.mp hq
    exact ⟨q, hsFinite.mem_toFinset.mpr hqs, hdist⟩

end EremenkosConjecture
