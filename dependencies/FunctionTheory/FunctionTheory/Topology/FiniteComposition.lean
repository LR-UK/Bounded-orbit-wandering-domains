import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

open Set Metric
open scoped Topology Uniformity

namespace FunctionTheory

set_option autoImplicit false

/-- Composition of the first `n` members of a sequence; the zeroth composition
is the identity. Thus the paper's `G_k` corresponds to `finiteComposition g (k+1)`. -/
def finiteComposition {X : Type*} (g : ℕ → X → X) : ℕ → X → X
  | 0 => id
  | n + 1 => g n ∘ finiteComposition g n

theorem continuousOn_finiteComposition {X : Type*} [TopologicalSpace X]
    (g : ℕ → X → X) (U : ℕ → Set X) (K : Set X) (n : ℕ)
    (hg : ∀ k < n, ContinuousOn (g k) (U k))
    (horbit : ∀ k < n, MapsTo (finiteComposition g k) K (U k)) :
    ContinuousOn (finiteComposition g n) K := by
  induction n with
  | zero => exact continuousOn_id
  | succ n ih =>
    exact (hg n (Nat.lt_succ_self n)).comp
      (ih (fun k hk => hg k (Nat.lt_succ_of_lt hk))
        (fun k hk => horbit k (Nat.lt_succ_of_lt hk)))
      (horbit n (Nat.lt_succ_self n))

/-- Compactness gives a common continuity radius which also stays inside the
domain. This is the collar argument used for finite iterates in the existing
EremenkosConjecture project, now applied to each member of a sequence. -/
theorem exists_uniform_continuity_collar {X : Type*} [MetricSpace X]
    {g : X → X} {U A : Set X}
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) (hg : ContinuousOn g U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ A, ∀ y, dist y x < r → y ∈ U ∧ dist (g y) (g x) < ε := by
  obtain ⟨r, hr, hrU⟩ := hA.exists_thickening_subset_open hU hAU
  have hmod := hA.uniformContinuousAt_of_continuousAt g
    (fun x hx => (hg x (hAU hx)).continuousAt (hU.mem_nhds (hAU hx)))
    (Metric.dist_mem_uniformity hε)
  obtain ⟨s, hs, hsg⟩ := Metric.mem_uniformity_dist.mp hmod
  refine ⟨min r s, lt_min hr hs, fun x hx y hy => ⟨?_, ?_⟩⟩
  · exact hrU (mem_thickening_iff.mpr ⟨x, hx, hy.trans_le (min_le_left _ _)⟩)
  · have hxy : dist x y < s := by simpa [dist_comm] using hy.trans_le (min_le_right r s)
    have H := hsg (show (x, y) ∈ {p : X × X | dist p.1 p.2 < s} from hxy) hx
    simpa only [Set.mem_ofPred_eq, dist_comm] using H

/-- Uniform stability of a finite sequence of compositions on a compact set,
including all intermediate domain conditions. The approximating functions
need not be continuous. -/
theorem finiteComposition_approximation_on_compact {X : Type*} [MetricSpace X]
    (g : ℕ → X → X) (U : ℕ → Set X) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (hU : ∀ k < n, IsOpen (U k))
    (hg : ∀ k < n, ContinuousOn (g k) (U k))
    (horbit : ∀ k < n, MapsTo (finiteComposition g k) K (U k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ℕ → X → X,
      (∀ k < n, ∀ z ∈ U k, dist (f k z) (g k z) < δ) →
      (∀ k ≤ n, ∀ z ∈ K,
        dist (finiteComposition f k z) (finiteComposition g k z) < ε) ∧
      (∀ k < n, MapsTo (finiteComposition f k) K (U k)) := by
  induction n generalizing ε with
  | zero =>
    refine ⟨1, one_pos, fun f hf => ⟨?_, ?_⟩⟩
    · intro k hk z hz
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      simpa [hk0, finiteComposition] using hε
    · intro k hk
      omega
  | succ n ih =>
    have hcont := continuousOn_finiteComposition g U K n
      (fun k hk => hg k (Nat.lt_succ_of_lt hk))
      (fun k hk => horbit k (Nat.lt_succ_of_lt hk))
    obtain ⟨r, hr, H⟩ := exists_uniform_continuity_collar
      (hK.image_of_continuousOn hcont) (hU n (Nat.lt_succ_self n))
      (horbit n (Nat.lt_succ_self n)).image_subset (hg n (Nat.lt_succ_self n))
      (half_pos hε)
    obtain ⟨δ, hδ, IH⟩ := ih (fun k hk => hU k (Nat.lt_succ_of_lt hk))
      (fun k hk => hg k (Nat.lt_succ_of_lt hk))
      (fun k hk => horbit k (Nat.lt_succ_of_lt hk))
      (min ε r) (lt_min hε hr)
    refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), fun f hf => ?_⟩
    obtain ⟨hclose, hdomain⟩ := IH f
      (fun k hk z hz => (hf k (Nat.lt_succ_of_lt hk) z hz).trans_le (min_le_left _ _))
    have hlast : ∀ z ∈ K, finiteComposition f n z ∈ U n ∧
        dist (g n (finiteComposition f n z)) (g n (finiteComposition g n z)) < ε / 2 := by
      intro z hz
      exact H (finiteComposition g n z) ⟨z, hz, rfl⟩ (finiteComposition f n z)
        ((hclose n le_rfl z hz).trans_le (min_le_right _ _))
    constructor
    · intro k hk z hz
      by_cases hkn : k ≤ n
      · exact (hclose k hkn z hz).trans_le (min_le_left _ _)
      · have hkn : k = n + 1 := by omega
        subst k
        change dist (f n (finiteComposition f n z)) (g n (finiteComposition g n z)) < ε
        exact (dist_triangle _ (g n (finiteComposition f n z)) _).trans_lt (by
          have h₁ := (hf n (Nat.lt_succ_self n) _ (hlast z hz).1).trans_le
            (min_le_right δ (ε / 2))
          have h₂ := (hlast z hz).2
          linarith)
    · intro k hk z hz
      by_cases hkn : k < n
      · exact hdomain k hkn hz
      · have hkn : k = n := by omega
        subst k
        exact (hlast z hz).1

end FunctionTheory
