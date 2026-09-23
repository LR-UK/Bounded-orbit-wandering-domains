import EremenkosConjecture.LakeDensity
import EremenkosConjecture.NewLake

open Set Metric Function

namespace EremenkosConjecture

namespace LakeConfiguration

structure Step {n : ℕ} (C : LakeConfiguration n) (D : LakeConfiguration (n + 1)) (ε : ℝ) : Prop where
  outer : D.outer.carrier ⊆ C.outer.carrier
  lake : ∀ i, (C.lake i).carrier ⊆ (D.lake i.castSucc).carrier
  dense : ∀ i, D.DenseWater i ε

theorem Step.land_anti {n : ℕ} {C : LakeConfiguration n} {D : LakeConfiguration (n + 1)}
    {ε : ℝ} (h : Step C D ε) : D.land ⊆ C.land := by
  have hobs : C.obstacles ⊆ D.obstacles := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i.castSucc, h.lake i hi⟩
  exact sdiff_subset_sdiff h.outer (interior_mono hobs)

theorem exists_step {n : ℕ} (C : LakeConfiguration n) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : LakeConfiguration (n + 1), Step C D ε := by
  obtain ⟨E, hEC, hlakes⟩ := C.exists_addLake
  obtain ⟨D, hED, hdense⟩ := E.exists_all_waters_dense hε
  refine ⟨D, ⟨?_, ?_, hdense⟩⟩
  · simpa only [hEC] using hED.outer
  · intro i
    simpa only [hlakes i] using hED.lake i.castSucc

noncomputable def initial : LakeConfiguration 0 where
  outer := AmbientDisk.unit
  lake := Fin.elim0
  inside := fun i => Fin.elim0 i
  disjoint := fun i => Fin.elim0 i

end LakeConfiguration

structure WadaConstruction where
  stage : (n : ℕ) → LakeConfiguration n
  step : ∀ n, LakeConfiguration.Step (stage n) (stage (n + 1)) ((1 / 2 : ℝ) ^ n)

theorem exists_wadaConstruction : Nonempty WadaConstruction := by
  classical
  have hex (n : ℕ) (C : LakeConfiguration n) := C.exists_step (ε := (1 / 2 : ℝ) ^ n) (by positivity)
  let next (n : ℕ) (C : LakeConfiguration n) := Classical.choose (hex n C)
  let seq : (n : ℕ) → LakeConfiguration n := Nat.rec LakeConfiguration.initial next
  refine ⟨⟨seq, ?_⟩⟩
  intro n
  exact Classical.choose_spec (hex n (seq n))

namespace WadaConstruction

def island (W : WadaConstruction) (n : ℕ) : Set ℂ := (W.stage n).outer.carrier

def lake (W : WadaConstruction) (n i : ℕ) : Set ℂ :=
  if h : i < n then ((W.stage n).lake ⟨i, h⟩).carrier else ∅

def lakeInterior (W : WadaConstruction) (n i : ℕ) : Set ℂ :=
  if h : i < n then ((W.stage n).lake ⟨i, h⟩).inside else ∅

theorem island_antitone (W : WadaConstruction) : Antitone W.island :=
  antitone_nat_of_succ_le (fun n => (W.step n).outer)

theorem lake_monotone (W : WadaConstruction) (i : ℕ) : Monotone (fun n => W.lake n i) := by
  apply monotone_nat_of_le_succ
  intro n
  change W.lake n i ⊆ W.lake (n + 1) i
  by_cases hin : i < n
  · simp only [lake, dif_pos hin, dif_pos (Nat.lt_succ_of_lt hin)]
    exact (W.step n).lake ⟨i, hin⟩
  · simp only [lake, dif_neg hin, empty_subset]

theorem lakeInterior_eq (W : WadaConstruction) (n i : ℕ) : W.lakeInterior n i = interior (W.lake n i) := by
  by_cases hin : i < n
  · simp only [lakeInterior, lake, dif_pos hin, AmbientDisk.interior_carrier]
  · simp only [lakeInterior, lake, dif_neg hin, interior_empty]

theorem lakeInterior_monotone (W : WadaConstruction) (i : ℕ) : Monotone (fun n => W.lakeInterior n i) := by
  intro n m hnm
  change W.lakeInterior n i ⊆ W.lakeInterior m i
  rw [W.lakeInterior_eq, W.lakeInterior_eq]
  exact interior_mono (W.lake_monotone i hnm)

theorem land_antitone (W : WadaConstruction) : Antitone (fun n => (W.stage n).land) :=
  antitone_nat_of_succ_le (fun n => (W.step n).land_anti)

end WadaConstruction

end EremenkosConjecture
