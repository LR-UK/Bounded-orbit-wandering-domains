import EremenkosConjecture.LakeConfiguration
import Mathlib.Data.Fin.Tuple.Basic

open Set Metric Function

namespace EremenkosConjecture.LakeConfiguration

noncomputable def addLake {n : ℕ} (C : LakeConfiguration n) (E : AmbientDisk)
    (hE : E.carrier ⊆ C.dry) : LakeConfiguration (n + 1) where
  outer := C.outer
  lake := Fin.lastCases E C.lake
  inside := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using (show E.carrier ⊆ C.outer.inside from fun z hz => (hE hz).1)
    · simpa only [Fin.lastCases_castSucc] using C.inside j
  disjoint := by
    have hdis (j : Fin n) : Disjoint E.carrier (C.lake j).carrier := by
      apply Set.disjoint_left.mpr
      intro z hzE hzj
      exact (hE hzE).2 (mem_iUnion.mpr ⟨j, hzj⟩)
    intro i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · exact fun H => (H rfl).elim
      · intro _
        simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hdis k
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · intro _
        simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using (hdis k).symm
      · intro hkl
        simpa only [Fin.lastCases_castSucc] using C.disjoint (fun H => hkl (congrArg Fin.castSucc H))

theorem exists_addLake {n : ℕ} (C : LakeConfiguration n) :
    ∃ D : LakeConfiguration (n + 1), D.outer = C.outer ∧ ∀ i, D.lake i.castSucc = C.lake i := by
  obtain ⟨E, hE⟩ := exists_ambientDisk_in_open C.open_dry C.pathConnected_dry.nonempty
  exact ⟨C.addLake E hE, rfl, fun i => by simp only [addLake, Fin.lastCases_castSucc]⟩

end EremenkosConjecture.LakeConfiguration
