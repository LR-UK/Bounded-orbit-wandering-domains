/- Compatibility update, 23 September 2026: current Lean linter suggestions;
mathematical statements and original attribution retained. -/

import ComplexDynamics.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Normality of bounded holomorphic sequences on smaller disks

Schwarz's estimate gives equicontinuity; compactness of bounded equicontinuous
families then supplies the convergent subsequence. This is the bounded case
needed for the trapping regions in the approximation construction.
-/

open Set Metric Function Filter
open scoped Topology Uniformity

namespace ComplexDynamics

theorem isNormalSequenceOn_spherical_of_equicontinuous
    {K : Set ℂ} (hK : IsCompact K) {F : ℕ → ℂ → ℂ}
    (hc : ∀ n, ContinuousOn (F n) K)
    (he : Equicontinuous (fun n (z : K) => F n z))
    {B : Set ℂ} (hB : IsCompact B) (hb : ∀ n, MapsTo (F n) K B) :
    IsNormalSequenceOn (fun n z => (F n z : RiemannSphere)) K := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : ℕ → BoundedContinuousFunction K ℂ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨fun z => F n z, (hc n).domRestrict⟩
  have heG : Equicontinuous (fun (g : range G) (z : K) => g.val z) := by
    intro z V hV
    filter_upwards [he z V hV] with w hw g
    obtain ⟨n, hn⟩ := g.property
    rw [← hn]
    exact hw n
  have hcomp : IsCompact (closure (range G)) :=
    BoundedContinuousFunction.arzela_ascoli B hB (range G)
      (by rintro g z ⟨n, rfl⟩; exact hb n z.property) heG
  intro φ _
  obtain ⟨g, _, ψ, hψ, hg⟩ := hcomp.tendsto_subseq
    (fun n => subset_closure (mem_range_self (φ n)))
  have hu : TendstoUniformly (fun n (z : K) => F (φ (ψ n)) z) g atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hg
  have hgb : ∀ z, g z ∈ B := fun z => hB.isClosed.mem_of_tendsto
    (hu.tendsto_at z) (Eventually.of_forall fun n => hb (φ (ψ n)) z.property)
  refine ⟨ψ, hψ, fun z => (g z : RiemannSphere), ?_⟩
  exact (hB.uniformContinuousOn_of_continuous OnePoint.continuous_coe.continuousOn).comp_tendstoLocallyUniformly
    hu.tendstoLocallyUniformly hgb (Eventually.of_forall fun n z => hb (φ (ψ n)) z.property)

theorem isNormalSequenceOn_spherical_of_bounded_on_ball
    {F : ℕ → ℂ → ℂ} {a : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hf : ∀ n, DifferentiableOn ℂ (F n) (ball a r))
    (hb : ∀ n z, z ∈ ball a r → ‖F n z‖ ≤ M) :
    IsNormalSequenceOn (fun n z => (F n z : RiemannSphere)) (closedBall a (r / 2)) := by
  let K := closedBall a (r / 2)
  have hsub : K ⊆ ball a r := closedBall_subset_ball (half_lt_self hr)
  have hbound (n : ℕ) (x y : K) :
      dist (F n y) (F n x) ≤ (4 * M / r) * dist y x := by
    have hx : dist (x : ℂ) a ≤ r / 2 := x.property
    have hy : dist (y : ℂ) a ≤ r / 2 := y.property
    have ht : ball (x : ℂ) (r / 2) ⊆ ball a r := by
      intro z hz
      exact (dist_triangle z x a).trans_lt (by linarith [mem_ball.mp hz])
    have hd : dist (F n y) (F n x) ≤ 2 * M := by
      calc
        dist (F n y) (F n x) ≤ ‖F n y‖ + ‖F n x‖ := by
          simpa only [dist_eq_norm] using norm_sub_le (F n y) (F n x)
        _ ≤ M + M := add_le_add (hb n y (hsub y.property)) (hb n x (hsub x.property))
        _ = 2 * M := by ring
    by_cases hxy : dist (y : ℂ) x < r / 2
    · have hm : MapsTo (F n) (ball (x : ℂ) (r / 2)) (closedBall (F n x) (2 * M)) := by
        intro z hz
        rw [mem_closedBall, dist_eq_norm]
        exact (norm_sub_le _ _).trans (by
          have hz' := hb n z (ht hz)
          have hx' := hb n x (hsub x.property)
          linarith)
      have H := Complex.dist_le_div_mul_dist_of_mapsTo_ball ((hf n).mono ht) hm hxy
      have heq : 2 * M / (r / 2) = 4 * M / r := by field_simp; ring
      simpa only [heq, Subtype.dist_eq] using H
    · have hr' : 0 < 4 * M / r := by positivity
      have hd' : r / 2 ≤ dist (y : ℂ) x := le_of_not_gt hxy
      have H := mul_le_mul_of_nonneg_left hd' hr'.le
      have heq : (4 * M / r) * (r / 2) = 2 * M := by field_simp; ring
      rw [heq] at H
      exact hd.trans H
  apply isNormalSequenceOn_spherical_of_equicontinuous (isCompact_closedBall _ _)
    (fun n => ((hf n).continuousOn).mono hsub) ?_ (isCompact_closedBall 0 M)
    (fun n z hz => by simpa using hb n z (hsub hz))
  apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => (4 * M / r) * t)
    (by simpa only [mul_zero, id_eq] using (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)))) _
  intro x y n
  exact hbound n y x

theorem isNormalSequenceOn_spherical_of_eventually_bounded_on_ball
    {F : ℕ → ℂ → ℂ} {a : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hf : ∀ n, DifferentiableOn ℂ (F n) (ball a r))
    (hb : ∀ᶠ n in atTop, ∀ z ∈ ball a r, ‖F n z‖ ≤ M) :
    IsNormalSequenceOn (fun n z => (F n z : RiemannSphere)) (closedBall a (r / 2)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  intro φ hφ
  have hnorm := isNormalSequenceOn_spherical_of_bounded_on_ball hr hM
    (fun n => hf (φ (n + N))) (fun n z hz => hN (φ (n + N))
      (le_trans (Nat.le_add_left _ _) (hφ.id_le _)) z hz)
  obtain ⟨ψ, hψ, g, hg⟩ := hnorm id strictMono_id
  exact ⟨fun n => ψ n + N, fun i j hij => Nat.add_lt_add_right (hψ hij) N, g, hg⟩

/-- A bounded forward-invariant open region and all its iterated preimages
lie in the Fatou set. -/
theorem mem_fatouSet_of_iterate_mem_bounded_invariant
    {f : ℂ → ℂ} (hf : IsEntire f) {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hi : MapsTo f U U)
    {z : ℂ} {N : ℕ} (hz : (f^[N]) z ∈ U) : z ∈ fatouSet f := by
  have hpre : IsOpen ((f^[N]) ⁻¹' U) := hU.preimage (hf.continuous.iterate N)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hpre z hz
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_le
  have ht : ∀ᶠ n : ℕ in atTop, ∀ w ∈ ball z r, ‖(f^[n]) w‖ ≤ M := by
    filter_upwards [eventually_ge_atTop N] with n hn w hw
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact hbound _ (hi.iterate k (hball hw))
  have hnormal := isNormalSequenceOn_spherical_of_eventually_bounded_on_ball hr hM
    (fun n => (hf.iterate n).differentiableOn) ht
  exact ⟨ball z (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
    hnormal.mono ball_subset_closedBall⟩

end ComplexDynamics
