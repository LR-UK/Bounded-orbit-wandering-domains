/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.InteriorDensityLimit
import BoundedWanderingDomains.DiscCoveringMetric
import BoundedWanderingDomains.GeneralDomainCovering

/-!
# Recover the metric of a general component from finite punctures

The normal-family proof in `InteriorDensityLimit` yields a limit disc mapping
into the component. The Schwarz inequality of a covering identifies the
pointwise limit with the hyperbolic density on that component.
-/

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit.FinitePunctureMetricInput

/-- Pointwise convergence of finite-puncture densities to the covering
hyperbolic density on the limiting component. -/
theorem density_tendsto_component_cover (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (hz : z ∉ closure (⋃ n, (↑(P n) : Set ℂ)))
    {q : ℂ → ℂ}
    (hq : IsHolomorphicDiscCovering q (connectedComponentIn
      (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z)) :
    Tendsto (fun n => G.density (P n) z) atTop (𝓝 (coveringDensity q z)) := by
  classical
  let A := closure (⋃ n, (↑(P n) : Set ℂ))
  let U := connectedComponentIn Aᶜ z
  have hU : IsOpen U := isClosed_closure.isOpen_compl.connectedComponentIn
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hUA : U ⊆ Aᶜ := connectedComponentIn_subset _ _
  have hzP : ∀ n, z ∉ P n :=
    fun n hn => hz (subset_closure (mem_iUnion.mpr ⟨n, hn⟩))
  have hc : ∀ n, 2 ≤ (P n).card := fun n => Finset.one_lt_card.mpr
    ⟨a, hP (Nat.zero_le n) ha, b, hP (Nat.zero_le n) hb, hab⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hzU
  have hbd : ∀ n, G.density (P n) z ≤ 2 / δ := by
    intro n
    have hm : MapsTo (fun w : ℂ => z + w) (ball 0 δ) ((↑(P n) : Set ℂ)ᶜ) := by
      intro w hw hwp
      have hzw : z + w ∈ U := hδU (by simpa [dist_eq_norm] using hw)
      exact hUA hzw (subset_closure (mem_iUnion.mpr ⟨n, hwp⟩))
    simpa using G.schwarz_on_ball (hc n) hδ (by fun_prop) hm
  have hbounded : BddAbove (range (fun n => G.density (P n) z)) :=
    ⟨2 / δ, fun _ hx => by obtain ⟨n, rfl⟩ := hx; exact hbd n⟩
  have hmono : Monotone (fun n => G.density (P n) z) :=
    fun i j hij => G.density_mono (hc i) (hP hij) (hzP j)
  let ell := ⨆ n, G.density (P n) z
  have ht : Tendsto (fun n => G.density (P n) z) atTop (𝓝 ell) :=
    tendsto_atTop_ciSup hmono hbounded
  have hell : 0 < ell := (G.positive (P 0) (hc 0) z (hzP 0)).trans_le
    (le_ciSup hbounded 0)
  choose p hp hm h0 he using fun n => G.extremal_disc (P n) (hc n) z (hzP n)
  have hrbound : ∀ r : ℝ, 0 < r → r < 1 →
      coveringDensity q z * r ≤ ell := by
    intro r hr hr1
    obtain ⟨M, hM⟩ := omitted_pair_bounded_subdisc hab hp
      (fun n w hw heq => hm n hw (heq ▸ hP (Nat.zero_le n) ha))
      (fun n w hw heq => hm n hw (heq ▸ hP (Nat.zero_le n) hb)) h0 hr.le hr1
    have hsub : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1.le
    have hpR := fun n => (hp n).mono hsub
    obtain ⟨φ, g, hφ, hl, hgd⟩ := bounded_holomorphic_subsequence isOpen_ball hpR hM
    have hzero : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
    have hg0 : g 0 = z := by
      have h := hl.tendsto_at hzero
      have heq : (fun n => p (φ n) 0) = fun _ => z := funext (fun n => h0 (φ n))
      rw [heq] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    have hd := (hl.deriv (Eventually.of_forall (fun n => hpR (φ n))) isOpen_ball).tendsto_at hzero
    have heprod : ell * ‖deriv g 0‖ = 2 := by
      have h := (ht.comp hφ.tendsto_atTop).mul hd.norm
      have heq : (fun n => G.density (P (φ n)) z * ‖deriv (p (φ n)) 0‖) =
          fun _ => (2 : ℝ) := funext (fun n => he (φ n))
      simp only [Function.comp_apply] at h
      rw [heq] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    have hdpos : 0 < ‖deriv g 0‖ := by nlinarith [norm_nonneg (deriv g 0)]
    have hgnot : ¬∃ c, ∀ w ∈ ball (0 : ℂ) r, g w = c := by
      rintro ⟨c, hh⟩
      have hge : g =ᶠ[𝓝 0] fun _ => c := Filter.mem_of_superset (ball_mem_nhds _ hr) (fun w hw => hh w hw)
      have hder : deriv g 0 = 0 := by rw [hge.deriv_eq]; simp
      simp [hder] at hdpos
    have homit : ∀ c ∈ ⋃ n, (↑(P n) : Set ℂ),
        ∀ᶠ n in atTop, ∀ w ∈ ball (0 : ℂ) r, p (φ n) w ≠ c := by
      intro c hc
      obtain ⟨k, hk⟩ := mem_iUnion.mp hc
      filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop k)] with n hn
      intro w hw heq
      exact hm (φ n) (hsub hw) (heq ▸ hP hn hk)
    have havoid := nonconstant_limit_avoids_closure isOpen_ball
      (convex_ball (0 : ℂ) r).isPreconnected (fun n => hpR (φ n)) hl homit hgnot
    have hgU : MapsTo g (ball 0 r) U := by
      apply mapsTo_iff_image_subset.mpr
      exact ((convex_ball (0 : ℂ) r).isPreconnected.image g hgd.continuousOn).subset_connectedComponentIn
        ⟨0, hzero, hg0⟩ (fun w hw => fun hwA => disjoint_left.mp havoid hw hwA)
    have hscale : MapsTo (fun w : ℂ => (r : ℂ) * w) (ball 0 1) (ball 0 r) := by
      intro w hw
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      simpa using mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hw) hr
    let t : ℂ → ℂ := fun w => g ((r : ℂ) * w)
    have htDiff : DifferentiableOn ℂ t (ball 0 1) :=
      hgd.comp (by fun_prop) hscale
    have htMaps : MapsTo t (ball 0 1) U := hgU.comp hscale
    have hs := hq.density_schwarz htDiff htMaps
    have hdg : deriv t 0 = deriv g 0 * (r : ℂ) := by
      have hdiff := hgd.differentiableAt (ball_mem_nhds (0 : ℂ) hr)
      have hscaleDiff : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) * w) 0 := by fun_prop
      change deriv (g ∘ (fun w : ℂ => (r : ℂ) * w)) 0 = _
      have hgdiff : DifferentiableAt ℂ g ((r : ℂ) * 0) := by simpa using hdiff
      rw [deriv_comp (𝕜 := ℂ) (𝕜' := ℂ) (0 : ℂ) hgdiff hscaleDiff]
      simp
    have hs' : coveringDensity q z * ‖deriv g 0‖ ≤ 2 / r := by
      change coveringDensity q (g ((r : ℂ) * 0)) * ‖deriv t 0‖ ≤ 2 at hs
      rw [mul_zero, hg0, hdg, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr] at hs
      exact (le_div_iff₀ hr).mpr (by nlinarith)
    apply (mul_le_mul_iff_left₀ hdpos).mp
    calc
      (coveringDensity q z * r) * ‖deriv g 0‖ =
          (coveringDensity q z * ‖deriv g 0‖) * r := by ring
      _ ≤ 2 := (le_div_iff₀ hr).mp hs'
      _ = ell * ‖deriv g 0‖ := heprod.symm
  have hlower : coveringDensity q z ≤ ell := by
    by_contra hnot
    have hlt := lt_of_not_ge hnot
    let T := coveringDensity q z
    have hT : 0 < T := hell.trans hlt
    have hratio : ell / T < 1 := (div_lt_one hT).mpr hlt
    have h := hrbound ((ell / T + 1) / 2) (by positivity) (by linarith)
    have he : T * ((ell / T + 1) / 2) = (ell + T) / 2 := by field_simp
    change T * ((ell / T + 1) / 2) ≤ ell at h
    rw [he] at h
    linarith
  obtain ⟨t, htDiff, htMaps, ht0, htExt⟩ := hq.density_extremal hzU
  have hderpos : 0 < ‖deriv t 0‖ := by
    have hh : ‖deriv t 0‖ ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at htExt
      norm_num at htExt
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hh)
  have hupper : ell ≤ coveringDensity q z := by
    apply ciSup_le
    intro n
    have hmP : MapsTo t (ball 0 1) ((↑(P n) : Set ℂ)ᶜ) := by
      intro w hw hwP
      exact hUA (htMaps hw) (subset_closure (mem_iUnion.mpr ⟨n, hwP⟩))
    have hs := G.schwarz (P n) (hc n) t htDiff hmP
    rw [ht0] at hs
    exact (mul_le_mul_iff_left₀ hderpos).mp (hs.trans_eq htExt.symm)
  exact (le_antisymm hupper hlower) ▸ ht

end AreaDeficit.FinitePunctureMetricInput

namespace AreaDeficit.FinitePunctureMetricInput

/-- Uniformisation supplies the covering required by the density limit
for each point of an arbitrary limiting component. -/
theorem exists_cover_and_density_limit (G : FinitePunctureMetricInput)
    {P : ℕ → Finset ℂ} (hP : Monotone P)
    {a b z : ℂ} (hab : a ≠ b) (ha : a ∈ P 0) (hb : b ∈ P 0)
    (hz : z ∉ closure (⋃ n, (↑(P n) : Set ℂ))) :
    ∃ q : ℂ → ℂ,
      IsHolomorphicDiscCovering q (connectedComponentIn
        (closure (⋃ n, (↑(P n) : Set ℂ)))ᶜ z) ∧
      Tendsto (fun n => G.density (P n) z) atTop (𝓝 (coveringDensity q z)) := by
  let A := closure (⋃ n, (↑(P n) : Set ℂ))
  have haA : a ∈ A := subset_closure (mem_iUnion.mpr ⟨0, ha⟩)
  have hbA : b ∈ A := subset_closure (mem_iUnion.mpr ⟨0, hb⟩)
  obtain ⟨q, hq⟩ := RiemannDynamics.exists_disc_covering_complement_component
    (A := A) isClosed_closure hz hab haA hbA
  exact ⟨q, hq, G.density_tendsto_component_cover hP hab ha hb hz hq⟩

end AreaDeficit.FinitePunctureMetricInput
