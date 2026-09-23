import LocalPunctures
import AreaCancellation
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

open Set Function Filter MeasureTheory
open scoped Topology

namespace AreaDeficit

/-- Only preimages inside V are taken. No analyticity is required outside
a neighbourhood of the compact set K containing V. -/
theorem local_preimage_countable {f : ℂ → ℂ} {V K S : Set ℂ}
    (hVK : V ⊆ K) (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ z ∈ K, ¬EventuallyConst f (𝓝 z)) (hS : S.Countable) :
    (V ∩ f ⁻¹' S).Countable := by
  have h := hS.biUnion (fun y _ =>
    (finite_local_preimage hK hf hn (finite_singleton y)).countable)
  apply h.mono
  rintro z ⟨hzV, hzS⟩
  exact mem_iUnion.mpr ⟨f z, mem_iUnion.mpr ⟨hzS, hVK hzV, rfl⟩⟩

theorem backwardTree_countable {α : Type*} {f : α → α} {V S : Set α}
    (hS : S.Countable)
    (hf : ∀ Q : Set α, Q.Countable → (V ∩ f ⁻¹' Q).Countable) (n : ℕ) :
    (backwardTree f V S n).Countable := by
  induction n with
  | zero => exact hS
  | succ n ih => exact ih.union (hf _ ih)

def localBackwardExceptionalSet {α : Type*} (f : α → α) (V S : Set α) : Set α :=
  ⋃ n : ℕ, backwardTree f V S n

theorem localBackwardExceptionalSet_countable {f : ℂ → ℂ} {V K S : Set ℂ}
    (hVK : V ⊆ K) (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ z ∈ K, ¬EventuallyConst f (𝓝 z)) (hS : S.Countable) :
    (localBackwardExceptionalSet f V S).Countable :=
  countable_iUnion (fun n => backwardTree_countable hS
    (fun _ hQ => local_preimage_countable hVK hK hf hn hQ) n)

theorem backwardTree_mem_of_trapped_hits {α : Type*} {f : α → α} {V S : Set α}
    {n : ℕ} {z : α} (hz : ∀ k : ℕ, f^[k] z ∈ V) (hroot : f^[n] z ∈ S) :
    z ∈ backwardTree f V S n := by
  induction n generalizing z with
  | zero => exact hroot
  | succ n ih =>
      apply Or.inr
      refine ⟨hz 0, ih (fun k => ?_) ?_⟩
      · simpa only [iterate_succ_apply] using hz (k + 1)
      · simpa only [iterate_succ_apply] using hroot

theorem trapped_orbit_avoids_of_not_localBackwardExceptionalSet {α : Type*}
    {f : α → α} {V S : Set α} {z : α}
    (htrap : ∀ k : ℕ, f^[k] z ∈ V) (hz : z ∉ localBackwardExceptionalSet f V S)
    (n : ℕ) : f^[n] z ∉ S :=
  fun hn => hz (mem_iUnion.mpr ⟨n, backwardTree_mem_of_trapped_hits htrap hn⟩)

theorem volume_sdiff_localBackwardExceptionalSet {f : ℂ → ℂ} {V K S B : Set ℂ}
    (hVK : V ⊆ K) (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ z ∈ K, ¬EventuallyConst f (𝓝 z)) (hS : S.Countable) :
    volume (B \ localBackwardExceptionalSet f V S) = volume B :=
  measure_sdiff_null ((localBackwardExceptionalSet_countable hVK hK hf hn hS).measure_zero volume)

/-- Values of a total Lean function outside V are irrelevant to the trees. -/
theorem backwardTree_congr_on {α : Type*} {f g : α → α} {V S : Set α}
    (hfg : EqOn f g V) (n : ℕ) : backwardTree f V S n = backwardTree g V S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [backwardTree, ih]
      congr 1
      ext z
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_right (fun hz => by rw [hfg hz])

theorem localBackwardExceptionalSet_congr_on {α : Type*} {f g : α → α} {V S : Set α}
    (hfg : EqOn f g V) : localBackwardExceptionalSet f V S = localBackwardExceptionalSet g V S := by
  unfold localBackwardExceptionalSet
  simp_rw [backwardTree_congr_on hfg]

end AreaDeficit
