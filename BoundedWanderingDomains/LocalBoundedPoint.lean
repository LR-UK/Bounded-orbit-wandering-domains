/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.LocalDiscInjectivity
import BoundedWanderingDomains.EventualCompactDiscs
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The local theorem from one compactly contained point orbit

Only the marked orbit lies in the compact set K. For a hypothetical wandering
orbit, fixed intrinsic discs shrink about their marked points. A fixed compact
thickening of K inside V therefore contains each such disc eventually. The
local power-coordinate argument proves eventual injectivity on those discs;
neither property is an additional hypothesis of the theorem.
-/

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit.FinitePunctureMetricInput

/-- A simply connected wandering trapped-component orbit cannot contain a
point orbit in a compact subset of V. The whole components need not stay in
that compact set, and eventual intrinsic-disc injectivity is derived. -/
theorem no_wandering_local_orbit_of_compact_point (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {U : ℕ → Set ℂ} {z : ℕ → ℂ}
    (hz : ∀ n, z n ∈ interior (trappedSet f V))
    (hU : ∀ n, U n = connectedComponentIn (interior (trappedSet f V)) (z n))
    (hnext : ∀ n, f (z n) = z (n + 1))
    (hsc : ∀ n, IsSimplyConnected (U n))
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
  have hUne : ∀ n, U n ≠ univ := by
    intro n he
    exact ha (hUV n (he ▸ mem_univ a))
  choose u hu hub hu0 using fun n =>
    Complex.exists_bijOn_unitBall_map_eq_zero (hUo n) (hsc n) (hUne n) (hzU n)
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  let L : Set ℂ := cthickening δ K
  have hL : IsCompact L := hK.cthickening
  have hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, chartDisc (u n) (U n) r ⊆ L := by
    intro r hr hr1
    apply eventually_atTop.mp
    filter_upwards [disjoint_bounded_chart_discs_shrink
      hUo hu hub hzU hu0 hUb hdis hr.le hr1 hδ] with n hn x hx
    exact mem_cthickening_of_dist_le x (z n) δ K (hzK n) (hn x hx).le
  have hinj : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, InjOn f (chartDisc (u n) (U n) r) := by
    intro r hr hr1
    exact eventually_atTop.mp (eventually_injOn_shrinking_chart_discs
      hK (hfV.mono hKV) (fun x hx => hnV x (hKV hx))
      hUo hsc hu hub hzU hzK hu0 hUb hdis hfm
      (fun n => hfV.continuousOn.mono (hUV n)) hr.le hr1)
  exact G.no_wandering_chart_orbit_with_eventual_compact_discs
    hV hVc hf hn hL hδV hab ha hb hz hU hnext hdis hu hub hu0 hcompact hinj

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.no_wandering_local_orbit_of_compact_point
