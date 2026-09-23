import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic.Linarith

/-!
# Stability of finite iterates (Lemma 2.5)

The uniform hypothesis below states both that orbit points stay uniformly inside
the domain and that the same continuity modulus works at all those points.
It applies to unbounded sets as well as compact sets. No regularity of the
approximating map is needed once its uniform error is controlled.
-/

open Function Set Metric Filter
open scoped Topology Uniformity

namespace EremenkosConjecture

variable {X : Type*} [MetricSpace X]

/-- A common continuity modulus around all points of a set, with a uniform
margin inside the domain. This includes points near the set, not just on it. -/
def UniformControlOn (g : X → X) (U A : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
    ∀ x ∈ A, ∀ y, dist y x < r → y ∈ U ∧ dist (g y) (g x) < ε

theorem UniformControlOn.mono {g : X → X} {U A B : Set X}
    (h : UniformControlOn g U A) (hBA : B ⊆ A) : UniformControlOn g U B := by
  intro ε hε
  obtain ⟨r, hr, H⟩ := h ε hε
  exact ⟨r, hr, fun x hx => H x (hBA hx)⟩

/-- Stability through a finite number of iterates, with domain membership
included in the conclusion so local iterations are well-defined. -/
theorem iterate_approximation_of_uniform_control (g : X → X) (U K : Set X) (n : ℕ)
    (hcontrol : ∀ k < n, UniformControlOn g U ((g^[k]) '' K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : X → X, (∀ z ∈ U, dist (f z) (g z) < δ) →
      (∀ k ≤ n, ∀ z ∈ K, dist ((f^[k]) z) ((g^[k]) z) < ε) ∧
      (∀ k < n, MapsTo (f^[k]) K U) := by
  induction n generalizing ε with
  | zero =>
      refine ⟨1, zero_lt_one, fun f hf => ⟨?_, ?_⟩⟩
      · intro k hk z hz
        have : k = 0 := by omega
        subst k
        simpa using hε
      · intro k hk
        omega
  | succ n ih =>
      obtain ⟨r, hr, H⟩ := hcontrol n (Nat.lt_succ_self n) (ε / 2) (half_pos hε)
      obtain ⟨δ, hδ, IH⟩ := ih (fun k hk => hcontrol k (Nat.lt_succ_of_lt hk))
        (min ε r) (lt_min hε hr)
      refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), fun f hf => ?_⟩
      obtain ⟨hclose, hdomain⟩ := IH f (fun z hz => (hf z hz).trans_le (min_le_left _ _))
      have hlast : ∀ z ∈ K, (f^[n]) z ∈ U ∧
          dist (g ((f^[n]) z)) (g ((g^[n]) z)) < ε / 2 := by
        intro z hz
        exact H ((g^[n]) z) ⟨z, hz, rfl⟩ ((f^[n]) z)
          ((hclose n le_rfl z hz).trans_le (min_le_right _ _))
      constructor
      · intro k hk z hz
        by_cases hkn : k ≤ n
        · exact (hclose k hkn z hz).trans_le (min_le_left _ _)
        · have hkn : k = n + 1 := by omega
          subst k
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact (dist_triangle _ (g ((f^[n]) z)) _).trans_lt
            (by have h₁ := (hf ((f^[n]) z) (hlast z hz).1).trans_le
                  (min_le_right δ (ε / 2))
                have h₂ := (hlast z hz).2
                linarith)
      · intro k hk z hz
        by_cases hkn : k < n
        · exact hdomain k hkn hz
        · have : k = n := by omega
          subst k
          exact (hlast z hz).1

/-- Compactness supplies the uniform hypothesis from ordinary local continuity. -/
theorem uniformControlOn_of_isCompact {g : X → X} {U A : Set X}
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) (hg : ContinuousOn g U) :
    UniformControlOn g U A := by
  intro ε hε
  obtain ⟨r, hr, hrU⟩ := hA.exists_thickening_subset_open hU hAU
  have hmod := hA.uniformContinuousAt_of_continuousAt g
    (fun x hx => (hg x (hAU hx)).continuousAt (hU.mem_nhds (hAU hx)))
    (Metric.dist_mem_uniformity hε)
  obtain ⟨s, hs, hsg⟩ := Metric.mem_uniformity_dist.mp hmod
  refine ⟨min r s, lt_min hr hs, fun x hx y hy => ⟨?_, ?_⟩⟩
  · apply hrU
    exact mem_thickening_iff.mpr ⟨x, hx, hy.trans_le (min_le_left _ _)⟩
  · have hxy : dist x y < s := by simpa [dist_comm] using hy.trans_le (min_le_right r s)
    have H := hsg (show (x, y) ∈ {p : X × X | dist p.1 p.2 < s} from hxy) hx
    simpa only [Set.mem_ofPred_eq, dist_comm] using H

/-- The compact-set version of Lemma 2.5. The reference map only needs
continuity on the open domain containing its first `n` orbit images. -/
theorem iterate_approximation_on_compact (g : X → X) (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hg : ContinuousOn g U) (n : ℕ)
    (horbit : ∀ k < n, MapsTo (g^[k]) K U) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : X → X, (∀ z ∈ U, dist (f z) (g z) < δ) →
      (∀ k ≤ n, ∀ z ∈ K, dist ((f^[k]) z) ((g^[k]) z) < ε) ∧
      (∀ k < n, MapsTo (f^[k]) K U) := by
  apply iterate_approximation_of_uniform_control g U K n _ ε hε
  intro k hk
  have hcont : ∀ j ≤ k, ContinuousOn (g^[j]) K := by
    intro j hj
    induction j with
    | zero => simpa using continuousOn_id (s := K)
    | succ j ih =>
        simpa only [Function.iterate_succ'] using
          hg.comp (ih (by omega)) (horbit j (by omega))
  exact uniformControlOn_of_isCompact (hK.image_of_continuousOn (hcont k le_rfl))
    hU (horbit k hk).image_subset hg

end EremenkosConjecture
