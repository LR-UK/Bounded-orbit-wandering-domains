import FinitePunctureMetricInput
import NormalFamilies
import FunctionTheory.Conformal.SchottkyConfinement

open Set Metric Filter Function MeasureTheory
open scoped Topology

namespace AreaDeficit.FinitePunctureMetricInput

/-- Accumulated punctures force density blowup. This is derived from
the classical metric input and checked normal-family theorems; it is
not a new metric assumption. Only a small disc around the base point
is needed in the normal-family argument. -/
theorem density_tendsto_atTop (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (hz : ∀ n, z ∉ P n)
    (hzA : z ∈ closure (⋃ n, (↑(P n) : Set ℂ))) :
    Tendsto (fun n => G.density (P n) z) atTop atTop := by
  classical
  have hc : ∀ n, 2 ≤ (P n).card := by
    intro n
    apply Finset.one_lt_card.mpr
    exact ⟨a, hP (Nat.zero_le n) ha, b, hP (Nat.zero_le n) hb, hab⟩
  have hdmono : Monotone (fun n => G.density (P n) z) :=
    fun i j hij => G.density_mono (hc i) (hP hij) (hz j)
  by_contra hnot
  have hbounded : BddAbove (range (fun n => G.density (P n) z)) := by
    by_contra hn
    apply hnot (hdmono.tendsto_atTop_atTop ?_)
    intro t
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := not_bddAbove_iff.mp hn t
    exact ⟨n, hn.le⟩
  obtain ⟨M, hM⟩ := hbounded
  have hMn : ∀ n, G.density (P n) z ≤ M := fun n => hM (mem_range_self n)
  have hMp : 0 < M := (G.positive (P 0) (hc 0) z (hz 0)).trans_le (hMn 0)
  choose p hp hm h0 he using fun n => G.extremal_disc (P n) (hc n) z (hz n)
  obtain ⟨r, hr, hr1, H⟩ :=
    FunctionTheory.exists_uniform_radius_of_compact_centres_omit_pair
      (isCompact_singleton (x := z)) hab (show (0 : ℝ) < 1 by norm_num)
  have hpA : ∀ n, AnalyticOnNhd ℂ (p n) (ball 0 1) :=
    fun n => (hp n).analyticOnNhd isOpen_ball
  have hmap : ∀ n, MapsTo (p n) (ball 0 r) (ball z 1) := by
    intro n
    simpa only [h0 n] using H (p n) (hpA n)
      (fun w hw heq => hm n hw (heq ▸ hP (Nat.zero_le n) ha))
      (fun w hw heq => hm n hw (heq ▸ hP (Nat.zero_le n) hb))
      (by simp [h0 n])
  have hsub : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1.le
  have hpR : ∀ n, DifferentiableOn ℂ (p n) (ball 0 r) :=
    fun n => (hp n).mono hsub
  have hbound : ∀ n w, w ∈ ball (0 : ℂ) r → ‖p n w‖ ≤ 1 + ‖z‖ := by
    intro n w hw
    have hdist : ‖p n w - z‖ < 1 := by
      simpa only [mem_ball, dist_eq_norm] using hmap n hw
    calc
      ‖p n w‖ ≤ ‖p n w - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + ‖z‖ := by linarith
  obtain ⟨φ, g, hφ, hl, hgd⟩ :=
    bounded_holomorphic_subsequence isOpen_ball hpR hbound
  have hzero : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have hg0 : g 0 = z := by
    have ht := hl.tendsto_at hzero
    have heq : (fun n => p (φ n) 0) = fun _ => z := funext (fun n => h0 (φ n))
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have homit : ∀ c ∈ ⋃ n, (↑(P n) : Set ℂ),
      ∀ᶠ n in atTop, ∀ w ∈ ball (0 : ℂ) r, p (φ n) w ≠ c := by
    intro c hc
    obtain ⟨k, hk⟩ := mem_iUnion.mp hc
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop k)] with n hn
    intro w hw heq
    exact hm (φ n) (hsub hw) (heq ▸ hP hn hk)
  obtain ⟨c, hgc⟩ := limit_constant_at_omitted_closure isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected hzero
    (fun n => hpR (φ n)) hl homit (hg0 ▸ hzA)
  have hgeq : g =ᶠ[𝓝 0] fun _ => c :=
    Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) hr) (fun w hw => hgc w hw)
  have hdg : deriv g 0 = 0 := by rw [hgeq.deriv_eq]; simp
  have hderiv : Tendsto (fun n => ‖deriv (p (φ n)) 0‖) atTop (𝓝 0) := by
    have ht := (hl.deriv (Eventually.of_forall (fun n => hpR (φ n))) isOpen_ball).tendsto_at hzero
    simpa only [hdg, norm_zero, Function.comp_apply] using ht.norm
  have hsmall : ∀ᶠ n in atTop, ‖deriv (p (φ n)) 0‖ < 1 / M :=
    hderiv.eventually (gt_mem_nhds (div_pos zero_lt_one hMp))
  obtain ⟨n, hn⟩ := hsmall.exists
  have heq := he (φ n)
  have hm' := mul_le_mul_of_nonneg_right (hMn (φ n)) (norm_nonneg (deriv (p (φ n)) 0))
  have hlt := (lt_div_iff₀ hMp).mp hn
  nlinarith

end AreaDeficit.FinitePunctureMetricInput
