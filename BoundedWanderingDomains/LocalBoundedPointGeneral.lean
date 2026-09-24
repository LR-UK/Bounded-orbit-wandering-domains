/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CoveringDiscInjectivity
import BoundedWanderingDomains.EventualCoveringDiscs
import Mathlib.Topology.MetricSpace.Thickening

/-! # The local bounded-point theorem without simple connectivity

Baker filling makes every fixed-radius universal covering disc eventually
embedded. The finite-model area contradiction then applies to those discs.
-/

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit.FinitePunctureMetricInput

/-- No wandering trapped-component orbit has a point orbit compactly contained
in the analytic domain. No simple-connectivity assumption is made. -/
theorem no_wandering_local_orbit_of_compact_point_general (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {U : ℕ → Set ℂ} {z : ℕ → ℂ}
    (hz : ∀ n, z n ∈ interior (trappedSet f V))
    (hU : ∀ n, U n = connectedComponentIn (interior (trappedSet f V)) (z n))
    (hnext : ∀ n, f (z n) = z (n + 1))
    (hzK : ∀ n, z n ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m))) : False := by
  classical
  have hfV := hf.mono (subset_closure : V ⊆ closure V)
  have hnV := fun x hx => hn x (subset_closure hx)
  have hUo : ∀ n, IsOpen (U n) := fun n => by
    rw [hU n]
    exact isOpen_interior.connectedComponentIn
  have hzU : ∀ n, z n ∈ U n := fun n => by
    rw [hU n]
    exact mem_connectedComponentIn (hz n)
  have hUT : ∀ n, U n ⊆ interior (trappedSet f V) := fun n => by
    rw [hU n]
    exact connectedComponentIn_subset _ _
  have hUV : ∀ n, U n ⊆ V :=
    fun n => (hUT n).trans (interior_subset.trans (trappedSet_subset f V))
  have hTF := trapped_interior_forward (analytic_locally_open hfV hnV)
  have hfm : ∀ n, MapsTo f (U n) (U (n + 1)) := by
    intro n
    rw [hU n, hU (n + 1), ← hnext n]
    exact ((hfV.continuousOn.mono
      (interior_subset.trans (trappedSet_subset f V))).mapsTo_connectedComponentIn
      (hz n)).mono_right (connectedComponentIn_mono _ hTF.image_subset)
  obtain ⟨R, hR, hVR⟩ := hVc.isBounded.exists_pos_norm_le
  have hUb : ∀ n x, x ∈ U n → ‖x‖ ≤ R :=
    fun n x hx => hVR x (subset_closure (hUV n hx))
  let a : ℂ := ((R + 1 : ℝ) : ℂ)
  let b : ℂ := ((R + 2 : ℝ) : ℂ)
  have ha : a ∉ V := by
    intro hx
    have h := hVR _ (subset_closure hx)
    dsimp [a] at h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h
    linarith
  have hb : b ∉ V := by
    intro hx
    have h := hVR _ (subset_closure hx)
    dsimp [b] at h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h
    linarith
  have hab : a ≠ b := by
    intro he
    have h := Complex.ofReal_injective he
    linarith
  have hcover : ∀ n, ∃ p : ℂ → ℂ, IsHolomorphicDiscCovering p (U n) ∧ p 0 = z n := by
    intro n
    have hUc : IsConnected (U n) := by
      rw [hU n]
      exact isConnected_connectedComponentIn_iff.mpr (hz n)
    let : ConnectedSpace (U n) := isConnected_iff_connectedSpace.mp hUc
    obtain ⟨q, hq⟩ := RiemannDynamics.exists_disc_covering_open_domain ⟨U n, hUo n⟩
      ⟨z n, hzU n⟩ (infinite_of_mem_nhds (z n) ((hUo n).mem_nhds (hzU n))) hab
      (fun h => ha (hUV n h)) (fun h => hb (hUV n h))
    exact hq.exists_centred (hzU n)
  choose p hp hp0 using hcover
  have hembed : ∀ r : ℝ, 0 < r → r < 1 → ∀ᶠ n in atTop,
      InjOn (p n) (ball 0 r) ∧ IsSimplyConnected (p n '' ball 0 r) := by
    intro r hr hr1
    exact eventually_covering_disc_embedded hV hfV hnV hK hKV hzK hU hp hp0 hnext hfm
      hUb hdis hr hr1
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  let L : Set ℂ := cthickening δ K
  have hL : IsCompact L := hK.cthickening
  have hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, p n '' ball 0 r ⊆ L := by
    intro r hr hr1
    apply eventually_atTop.mp
    filter_upwards [covering_discs_shrink hp hUb hdis hr.le hr1 hδ] with n hn x hx
    apply mem_cthickening_of_dist_le x (z n) δ K (hzK n)
    rw [← hp0 n]
    exact (hn x (image_mono ball_subset_closedBall hx)).le
  have hinj : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, InjOn f (p n '' ball 0 r) := by
    intro r hr hr1
    exact eventually_atTop.mp (eventually_injOn_shrinking_covering_discs
      hK (hfV.mono hKV) (fun x hx => hnV x (hKV hx)) hp hzK hp0 hUb hdis hfm
      (fun n => hfV.differentiableOn.mono (hUV n)) hnext hr hr1
      ((hembed r hr hr1).mono (fun _ h => h.2)))
  exact G.no_wandering_covering_orbit_with_eventual_embedded_discs
    hV hVc hf hn hL hδV hab ha hb hz hU hnext hdis hp hp0
    (fun r hr hr1 => eventually_atTop.mp ((hembed r hr hr1).mono (fun _ h => h.1)))
    hcompact hinj


end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.no_wandering_local_orbit_of_compact_point_general
