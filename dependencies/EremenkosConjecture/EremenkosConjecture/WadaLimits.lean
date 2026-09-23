import EremenkosConjecture.LakeSeparation
import EremenkosConjecture.NestedContinua
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric Function Filter
open scoped Topology

namespace EremenkosConjecture.WadaConstruction

def waterAt (W : WadaConstruction) (n : ℕ) : Option ℕ → Set ℂ
  | none => (W.island n)ᶜ
  | some i => W.lakeInterior n i

def domain (W : WadaConstruction) (i : Option ℕ) : Set ℂ := ⋃ n, W.waterAt n i

def boundary (W : WadaConstruction) : Set ℂ := ⋂ n, (W.stage n).land

theorem compact_boundary (W : WadaConstruction) : IsCompact W.boundary :=
  (W.stage 0).compact_land.of_isClosed_subset
    (isClosed_iInter (fun n => (W.stage n).compact_land.isClosed)) (iInter_subset _ 0)

theorem connected_boundary (W : WadaConstruction) : IsConnected W.boundary :=
  isConnected_nested_inter (fun n => (W.stage n).compact_land)
    (fun n => (W.stage n).connected_land) W.land_antitone

theorem waterAt_finite (W : WadaConstruction) (n : ℕ) (i : Option (Fin n)) :
    W.waterAt n (i.map Fin.val) = (W.stage n).water i := by
  cases i with
  | none => rfl
  | some i => simp only [waterAt, Option.map_some, lakeInterior, dif_pos i.isLt]; rfl

theorem exists_finite_water (W : WadaConstruction) {n : ℕ} {i : Option ℕ} {z : ℂ}
    (hz : z ∈ W.waterAt n i) : ∃ j : Option (Fin n), j.map Fin.val = i ∧ z ∈ (W.stage n).water j := by
  cases i with
  | none => exact ⟨none, rfl, hz⟩
  | some i =>
    by_cases hin : i < n
    · refine ⟨some ⟨i, hin⟩, rfl, ?_⟩
      simpa only [waterAt, lakeInterior, dif_pos hin, LakeConfiguration.water] using hz
    · simp only [waterAt, lakeInterior, dif_neg hin, mem_empty_iff_false] at hz

theorem waterAt_monotone (W : WadaConstruction) (i : Option ℕ) : Monotone (fun n => W.waterAt n i) := by
  cases i with
  | none => exact fun _ _ h => compl_subset_compl.mpr (W.island_antitone h)
  | some i => exact W.lakeInterior_monotone i

theorem open_waterAt (W : WadaConstruction) (n : ℕ) (i : Option ℕ) : IsOpen (W.waterAt n i) := by
  cases i with
  | none => exact (W.stage n).outer.compact.isClosed.isOpen_compl
  | some i =>
    by_cases hin : i < n
    · simpa only [waterAt, lakeInterior, dif_pos hin] using ((W.stage n).lake ⟨i, hin⟩).open_inside
    · simp only [waterAt, lakeInterior, dif_neg hin, isOpen_empty]

theorem preconnected_waterAt (W : WadaConstruction) (n : ℕ) (i : Option ℕ) :
    IsPreconnected (W.waterAt n i) := by
  cases i with
  | none => exact (W.stage n).outer.full.isPreconnected
  | some i =>
    by_cases hin : i < n
    · simpa only [waterAt, lakeInterior, dif_pos hin] using
        ((W.stage n).lake ⟨i, hin⟩).connected_inside.isPreconnected
    · simp only [waterAt, lakeInterior, dif_neg hin, isPreconnected_empty]

theorem open_domain (W : WadaConstruction) (i : Option ℕ) : IsOpen (W.domain i) :=
  isOpen_iUnion (fun n => W.open_waterAt n i)

theorem connected_domain (W : WadaConstruction) (i : Option ℕ) : IsConnected (W.domain i) := by
  have hne : (W.domain i).Nonempty := by
    cases i with
    | none => exact (W.stage 0).outer.full.nonempty.mono (subset_iUnion _ 0)
    | some k =>
      have H := ((W.stage (k + 1)).lake ⟨k, Nat.lt_succ_self k⟩).connected_inside.nonempty
      have hsub : ((W.stage (k + 1)).lake ⟨k, Nat.lt_succ_self k⟩).inside ⊆ W.domain (some k) := by
        intro z hz
        apply mem_iUnion.mpr
        refine ⟨k + 1, ?_⟩
        simpa only [waterAt, lakeInterior, dif_pos (Nat.lt_succ_self k)] using hz
      exact H.mono hsub
  refine ⟨hne, isPreconnected_of_forall_pair ?_⟩
  intro x hx y hy
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hy
  exact ⟨W.waterAt (max n m) i, (fun _ hz => mem_iUnion.mpr ⟨max n m, hz⟩), W.waterAt_monotone i (le_max_left _ _) hn,
    W.waterAt_monotone i (le_max_right _ _) hm, W.preconnected_waterAt _ i⟩

theorem disjoint_domains (W : WadaConstruction) : Pairwise (Disjoint on W.domain) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨n, hn⟩ := mem_iUnion.mp hzi
  obtain ⟨m, hm⟩ := mem_iUnion.mp hzj
  obtain ⟨a, ha, hza⟩ := W.exists_finite_water (W.waterAt_monotone i (le_max_left n m) hn)
  obtain ⟨b, hb, hzb⟩ := W.exists_finite_water (W.waterAt_monotone j (le_max_right n m) hm)
  have hab : a ≠ b := fun H => hij (ha.symm.trans ((congrArg (Option.map Fin.val) H).trans hb))
  exact Set.disjoint_left.mp ((W.stage (max n m)).disjoint_waters hab) hza hzb

theorem disjoint_boundary_domain (W : WadaConstruction) (i : Option ℕ) :
    Disjoint W.boundary (W.domain i) := by
  apply Set.disjoint_left.mpr
  intro z hz hd
  obtain ⟨n, hn⟩ := mem_iUnion.mp hd
  obtain ⟨j, _, hj⟩ := W.exists_finite_water hn
  exact Set.disjoint_left.mp ((W.stage n).disjoint_land_water j) (mem_iInter.mp hz n) hj

theorem exists_domain_of_not_boundary (W : WadaConstruction) {z : ℂ} (hz : z ∉ W.boundary) :
    ∃ i, z ∈ W.domain i := by
  have hex : ∃ n, z ∉ (W.stage n).land := by
    by_contra! H
    exact hz (mem_iInter.mpr H)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨j, hj⟩ := (W.stage n).exists_water_of_not_land hn
  refine ⟨j.map Fin.val, mem_iUnion.mpr ⟨n, ?_⟩⟩
  rwa [W.waterAt_finite]

theorem boundary_subset_closure_domain (W : WadaConstruction) (i : Option ℕ) :
    W.boundary ⊆ closure (W.domain i) := by
  intro z hz
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  cases i with
  | none =>
    obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
    obtain ⟨q, hq, hdist⟩ := (W.step n).dense none z (mem_iInter.mp hz (n + 1))
    exact ⟨q, mem_iUnion.mpr ⟨n + 1, hq⟩, hdist.trans hn⟩
  | some k =>
    obtain ⟨n, hn, hεn⟩ := ((eventually_ge_atTop k).and (hlim.eventually_lt_const hε)).exists
    have hk : k < n + 1 := by omega
    obtain ⟨q, hq, hdist⟩ := (W.step n).dense (some ⟨k, hk⟩) z (mem_iInter.mp hz (n + 1))
    refine ⟨q, mem_iUnion.mpr ⟨n + 1, ?_⟩, hdist.trans hεn⟩
    simpa only [waterAt, lakeInterior, dif_pos hk, LakeConfiguration.water] using hq

theorem frontier_domain (W : WadaConstruction) (i : Option ℕ) : frontier (W.domain i) = W.boundary := by
  apply Subset.antisymm
  · intro z hz
    by_contra hzb
    obtain ⟨j, hzj⟩ := W.exists_domain_of_not_boundary hzb
    by_cases hji : j = i
    · subst j
      exact hz.2 ((W.open_domain i).interior_eq.symm ▸ hzj)
    · have hdis := W.disjoint_domains hji
      obtain ⟨w, hwj, hwi⟩ := _root_.mem_closure_iff.mp hz.1 (W.domain j) (W.open_domain j) hzj
      exact Set.disjoint_left.mp hdis hwj hwi
  · intro z hz
    exact ⟨W.boundary_subset_closure_domain i hz,
      fun H => Set.disjoint_left.mp (W.disjoint_boundary_domain i) hz (interior_subset H)⟩

end EremenkosConjecture.WadaConstruction
