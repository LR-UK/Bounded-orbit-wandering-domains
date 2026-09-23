import EremenkosConjecture.LakeConfiguration

open Set Metric Function

namespace EremenkosConjecture.LakeConfiguration

noncomputable def replaceLake {n : ℕ} (C : LakeConfiguration n) (i : Fin n) (E : AmbientDisk)
    (hE : E.carrier ⊆ C.outer.inside)
    (hdis : ∀ j, j ≠ i → Disjoint E.carrier (C.lake j).carrier) : LakeConfiguration n where
  outer := C.outer
  lake := Function.update C.lake i E
  inside := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hE
    · simpa only [Function.update_of_ne hji] using C.inside j
  disjoint := by
    intro j k hjk
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self, Function.update_of_ne hjk.symm] using hdis k hjk.symm
    · by_cases hki : k = i
      · subst k
        simpa only [Function.update_self, Function.update_of_ne hji] using (hdis j hji).symm
      · simpa only [Function.update_of_ne hji, Function.update_of_ne hki] using C.disjoint hjk

noncomputable def replaceOuter {n : ℕ} (C : LakeConfiguration n) (E : AmbientDisk)
    (hE : C.obstacles ⊆ E.inside) : LakeConfiguration n where
  outer := E
  lake := C.lake
  inside := fun i z hz => hE (mem_iUnion.mpr ⟨i, hz⟩)
  disjoint := C.disjoint

theorem exists_dense_water {n : ℕ} (C : LakeConfiguration n) (i : Option (Fin n))
    {ε : ℝ} (hε : 0 < ε) : ∃ D : LakeConfiguration n, Refines C D ∧ D.DenseWater i ε := by
  classical
  obtain ⟨s, hsD, hnet⟩ := exists_finset_net_in_dense C.compact_land
    (by rw [C.closure_dry]) hε
  cases i with
  | none =>
    obtain ⟨E, hAE, hEM, hsE⟩ := C.outer.shrink_away_finset C.compact_obstacles
      C.full_obstacles C.obstacles_inside s (fun q hq => (hsD q hq).2)
    let D := C.replaceOuter E hAE
    have hCD : Refines C D := ⟨hEM, fun _ => Subset.rfl⟩
    refine ⟨D, hCD, ?_⟩
    intro z hz
    obtain ⟨q, hqs, hdist⟩ := hnet z (hCD.land_anti hz)
    exact ⟨q, hsE q hqs, hdist⟩
  | some i =>
    let t := Finset.univ.erase i
    let A : Set ℂ := ⋃ j ∈ t, (C.lake j).carrier
    have hAc : IsCompact A := t.isCompact_biUnion (fun j _ => (C.lake j).compact)
    have hAf : IsConnected Aᶜ := isConnected_compl_finite_disjoint_union t _
      (fun j _ => (C.lake j).compact) (fun j _ => (C.lake j).full)
      (fun j _ k _ hjk => C.disjoint hjk)
    have hAC : A ⊆ C.obstacles := by
      intro z hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      obtain ⟨_, hzj⟩ := mem_iUnion.mp hj
      exact mem_iUnion.mpr ⟨j, hzj⟩
    have hAi : Disjoint A (C.lake i).carrier := by
      apply disjoint_iUnion_left.mpr
      intro j
      apply disjoint_iUnion_left.mpr
      intro hj
      exact C.disjoint (Finset.mem_erase.mp hj).1
    obtain ⟨E, hiE, hEV, hsE⟩ := C.outer.enlarge_to_finset (C.lake i) hAc hAf
      (hAC.trans C.obstacles_inside) (C.inside i) hAi s
      (fun q hq => ⟨(hsD q hq).1, fun h => (hsD q hq).2 (hAC h)⟩)
    have hdis : ∀ j, j ≠ i → Disjoint E.carrier (C.lake j).carrier := by
      intro j hji
      apply Set.disjoint_left.mpr
      intro z hzE hzj
      exact (hEV hzE).2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr
        ⟨Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, hzj⟩⟩)
    let D := C.replaceLake i E (fun z hz => (hEV hz).1) hdis
    have hCD : Refines C D := by
      refine ⟨Subset.rfl, ?_⟩
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [D, replaceLake, Function.update_self] using hiE
      · simp only [D, replaceLake, Function.update_of_ne hji]
        exact Subset.rfl
    refine ⟨D, hCD, ?_⟩
    intro z hz
    obtain ⟨q, hqs, hdist⟩ := hnet z (hCD.land_anti hz)
    refine ⟨q, ?_, hdist⟩
    simpa only [D, water, replaceLake, Function.update_self] using hsE q hqs

theorem exists_all_waters_dense {n : ℕ} (C : LakeConfiguration n) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : LakeConfiguration n, Refines C D ∧ ∀ i, D.DenseWater i ε := by
  classical
  have hfinite (s : Finset (Option (Fin n))) :
      ∃ D : LakeConfiguration n, Refines C D ∧ ∀ i ∈ s, D.DenseWater i ε := by
    induction s using Finset.induction_on with
    | empty => exact ⟨C, Refines.refl C, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨D, hCD, hsD⟩ := ih
      obtain ⟨E, hDE, hiE⟩ := D.exists_dense_water i hε
      refine ⟨E, hCD.trans hDE, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiE
      · exact (hsD j hj).mono hDE
  obtain ⟨D, hCD, hD⟩ := hfinite Finset.univ
  exact ⟨D, hCD, fun i => hD i (Finset.mem_univ i)⟩

end EremenkosConjecture.LakeConfiguration
