import EremenkosConjecture.FiniteLakeExtension
import EremenkosConjecture.DiskBirth

open Set Metric Function

namespace EremenkosConjecture

/-- A finite stage of the Lakes of Wada construction. -/
structure LakeConfiguration (n : ℕ) where
  outer : AmbientDisk
  lake : Fin n → AmbientDisk
  inside : ∀ i, (lake i).carrier ⊆ outer.inside
  disjoint : Pairwise (fun i j => Disjoint (lake i).carrier (lake j).carrier)

namespace LakeConfiguration

def obstacles {n : ℕ} (C : LakeConfiguration n) : Set ℂ := ⋃ i, (C.lake i).carrier

def dry {n : ℕ} (C : LakeConfiguration n) : Set ℂ := C.outer.inside \ C.obstacles

def land {n : ℕ} (C : LakeConfiguration n) : Set ℂ := C.outer.carrier \ interior C.obstacles

def water {n : ℕ} (C : LakeConfiguration n) : Option (Fin n) → Set ℂ
  | none => C.outer.carrierᶜ
  | some i => (C.lake i).inside

theorem compact_obstacles {n : ℕ} (C : LakeConfiguration n) : IsCompact C.obstacles :=
  isCompact_iUnion (fun i => (C.lake i).compact)

theorem full_obstacles {n : ℕ} (C : LakeConfiguration n) : IsConnected C.obstaclesᶜ := by
  simpa only [obstacles, Finset.mem_univ, iUnion_true] using isConnected_compl_finite_disjoint_union
    Finset.univ (fun i => (C.lake i).carrier) (fun i _ => (C.lake i).compact)
    (fun i _ => (C.lake i).full) (fun i _ j _ hij => C.disjoint hij)

theorem obstacles_inside {n : ℕ} (C : LakeConfiguration n) : C.obstacles ⊆ C.outer.inside := by
  rintro z ⟨_, ⟨i, rfl⟩, hz⟩
  exact C.inside i hz

theorem open_dry {n : ℕ} (C : LakeConfiguration n) : IsOpen C.dry :=
  C.outer.open_inside.sdiff C.compact_obstacles.isClosed

theorem pathConnected_dry {n : ℕ} (C : LakeConfiguration n) : IsPathConnected C.dry :=
  C.outer.pathConnected_sdiff C.compact_obstacles C.full_obstacles C.obstacles_inside

theorem closure_dry {n : ℕ} (C : LakeConfiguration n) : closure C.dry = C.land :=
  C.outer.closure_sdiff C.compact_obstacles.isClosed C.obstacles_inside

theorem compact_land {n : ℕ} (C : LakeConfiguration n) : IsCompact C.land :=
  C.outer.compact.diff isOpen_interior

theorem connected_land {n : ℕ} (C : LakeConfiguration n) : IsConnected C.land :=
  C.outer.connected_land C.compact_obstacles C.full_obstacles C.obstacles_inside

theorem open_water {n : ℕ} (C : LakeConfiguration n) (i : Option (Fin n)) : IsOpen (C.water i) := by
  cases i with
  | none => exact C.outer.compact.isClosed.isOpen_compl
  | some i => exact (C.lake i).open_inside

theorem connected_water {n : ℕ} (C : LakeConfiguration n) (i : Option (Fin n)) :
    IsConnected (C.water i) := by
  cases i with
  | none => exact C.outer.full
  | some i => exact (C.lake i).connected_inside

structure Refines {n : ℕ} (C D : LakeConfiguration n) : Prop where
  outer : D.outer.carrier ⊆ C.outer.carrier
  lake : ∀ i, (C.lake i).carrier ⊆ (D.lake i).carrier

theorem Refines.refl {n : ℕ} (C : LakeConfiguration n) : Refines C C :=
  ⟨Subset.rfl, fun _ => Subset.rfl⟩

theorem Refines.trans {n : ℕ} {C D E : LakeConfiguration n} (hCD : Refines C D)
    (hDE : Refines D E) : Refines C E := ⟨hDE.outer.trans hCD.outer, fun i => (hCD.lake i).trans (hDE.lake i)⟩

theorem Refines.water_mono {n : ℕ} {C D : LakeConfiguration n} (h : Refines C D)
    (i : Option (Fin n)) : C.water i ⊆ D.water i := by
  cases i with
  | none => exact compl_subset_compl.mpr h.outer
  | some i =>
    change (C.lake i).inside ⊆ (D.lake i).inside
    rw [← (C.lake i).interior_carrier, ← (D.lake i).interior_carrier]
    exact interior_mono (h.lake i)

theorem Refines.land_anti {n : ℕ} {C D : LakeConfiguration n} (h : Refines C D) : D.land ⊆ C.land := by
  have hobs : C.obstacles ⊆ D.obstacles := iUnion_mono (fun i => h.lake i)
  exact sdiff_subset_sdiff h.outer (interior_mono hobs)

def DenseWater {n : ℕ} (C : LakeConfiguration n) (i : Option (Fin n)) (ε : ℝ) : Prop :=
  ∀ z ∈ C.land, ∃ q ∈ C.water i, dist z q < ε

theorem DenseWater.mono {n : ℕ} {C D : LakeConfiguration n} {i : Option (Fin n)} {ε : ℝ}
    (hdense : C.DenseWater i ε) (h : Refines C D) : D.DenseWater i ε := by
  intro z hz
  obtain ⟨q, hq, hdist⟩ := hdense z (h.land_anti hz)
  exact ⟨q, h.water_mono i hq, hdist⟩

end LakeConfiguration

end EremenkosConjecture
