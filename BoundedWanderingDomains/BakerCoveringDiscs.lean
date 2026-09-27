/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.CoveringDiscs
import BoundedWanderingDomains.LocalFilling
import BoundedWanderingDomains.LocalDiscInjectivity
import EremenkosConjecture.PlaneSimpleConnectivity
import Mathlib.Topology.MetricSpace.Thickening

/-! # Baker's filling argument for shrinking covering discs

Fixed-radius universal covering discs eventually embed in trapped components.
Simple connectivity of the entire components is not required.
-/

open Set Metric Function Filter Bornology
open scoped Topology

namespace AreaDeficit

theorem eventually_covering_disc_embedded
    {f : ℂ → ℂ} {V K : Set ℂ} {U : ℕ → Set ℂ} {p : ℕ → ℂ → ℂ}
    {z : ℕ → ℂ} {M : ℝ}
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hn : ∀ x ∈ V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V) (hzK : ∀ n, z n ∈ K)
    (hU : ∀ n, U n = connectedComponentIn (interior (trappedSet f V)) (z n))
    (hp : ∀ n, IsHolomorphicDiscCovering (p n) (U n)) (hp0 : ∀ n, p n 0 = z n)
    (hnext : ∀ n, f (z n) = z (n+1)) (hfm : ∀ n, MapsTo f (U n) (U (n+1)))
    (hb : ∀ n w, w ∈ U n → ‖w‖ ≤ M)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, InjOn (p n) (ball 0 r) ∧ IsSimplyConnected (p n '' ball 0 r) := by
  let C : ℕ → Set ℂ := fun n => p n '' closedBall 0 r
  have hC : ∀ n, IsCompact (C n) := fun n =>
    (isCompact_closedBall 0 r).image_of_continuousOn
      ((hp n).holo.continuousOn.mono (closedBall_subset_ball hr1))
  have hCc : ∀ n, IsConnected (C n) := fun n =>
    ((convex_closedBall (0 : ℂ) r).isConnected ⟨0, mem_closedBall_self hr.le⟩).image
      (p n) ((hp n).holo.continuousOn.mono (closedBall_subset_ball hr1))
  have hCU : ∀ n, C n ⊆ U n := fun n =>
    (image_mono (closedBall_subset_ball hr1)).trans (hp n).maps.image_subset
  have hzC : ∀ n, z n ∈ C n := fun n => ⟨0, mem_closedBall_self hr.le, hp0 n⟩
  have hUV : ∀ n, U n ⊆ V := fun n => by
    rw [hU n]
    exact (connectedComponentIn_subset _ _).trans (interior_subset.trans (trappedSet_subset f V))
  have hCnext : ∀ n, MapsTo f (C n) (C (n+1)) := fun n =>
    mapsTo_closed_covering_disc (hp n) (hp (n+1)) (hf.differentiableOn.mono (hUV n))
      (hfm n) (by rw [hp0, hp0, hnext]) hr1
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨N, hN⟩ := eventually_atTop.mp (covering_discs_shrink hp hb hdis hr.le hr1 hδ)
  have hFV : ∀ n ≥ N, ComplexApproximation.fill (C n) ⊆ V := by
    intro n hnN w hw
    have hbound : ∀ v ∈ C n, ‖v - z n‖ ≤ δ := by
      intro v hv
      have h := (hN n hnN v hv).le
      rwa [hp0, dist_eq_norm] at h
    have hwδ := norm_le_on_fill (hC n) (differentiable_id.sub_const (z n)) hbound w hw
    exact hδV (mem_cthickening_of_dist_le w (z n) δ K (hzK n)
      (by simpa only [dist_eq_norm, id_eq] using hwδ))
  have hFT := fill_subset_trapped_of_forward_fillings hf.continuousOn
    (analytic_locally_open hf hn) (K := fun j => C (N+j)) (fun j => hC (N+j))
    (fun j => hFV (N+j) (by omega))
    (fun j => by simpa only [Nat.add_assoc] using hCnext (N+j))
  have hFU : ∀ n ≥ N, ComplexApproximation.fill (C n) ⊆ U n := by
    intro n hnN
    have hFC : ComplexApproximation.fill (C n) ⊆ trappedSet f V := by
      simpa only [Nat.add_sub_of_le hnN] using hFT (n-N)
    have hCI : C n ⊆ interior (trappedSet f V) := by
      have hCn := hCU n
      rw [hU n] at hCn
      exact hCn.trans (connectedComponentIn_subset _ _)
    have hFI := fill_subset_interior_of_fill_subset (hC n).isClosed hCI hFC
    rw [hU n]
    exact (ComplexApproximation.isConnected_fill (hC n).isClosed (hCc n)).isPreconnected
      |>.subset_connectedComponentIn (ComplexApproximation.subset_fill _ (hzC n)) hFI
  filter_upwards [eventually_ge_atTop N] with n hnN
  let L := ComplexApproximation.fill (C n)
  have hL : IsCompact L := ComplexApproximation.isCompact_fill (hC n)
  have hLc : IsConnected L := ComplexApproximation.isConnected_fill (hC n).isClosed (hCc n)
  have hLf : IsConnected Lᶜ := ComplexApproximation.isConnected_compl_fill (hC n)
  have hUo : IsOpen (U n) := by rw [hU n]; exact isOpen_interior.connectedComponentIn
  obtain ⟨J, _, _, hJU⟩ := EremenkosConjecture.exists_nested_jordan_neighbourhoods_within
    L (U n) hL hLc hLf hUo (hFU n hnN)
  have hCJ : C n ⊆ interior (J 0).carrier := (ComplexApproximation.subset_fill _).trans (J 0).contains
  have hJU' : interior (J 0).carrier ⊆ U n := interior_subset.trans hJU
  have hsc : IsSimplyConnected (ball (0 : ℂ) r) := by
    let : ContractibleSpace (ball (0 : ℂ) r) := Metric.contractibleSpace_ball hr
    change SimplyConnectedSpace (ball (0 : ℂ) r)
    infer_instance
  have hi : InjOn (p n) (ball 0 r) := covering_injOn_domain isOpen_ball hsc
    isOpen_interior (J 0).simplyConnectedInterior (mem_ball_self hr)
    (ball_subset_ball hr1.le) ((hp n).holo.continuousOn.mono (ball_subset_ball hr1.le))
    (fun w hw => hCJ (mem_image_of_mem _ (ball_subset_closedBall hw)))
    ((hp n).covering.mono hJU')
  exact ⟨hi, TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn
    isOpen_ball hsc ((hp n).holo.mono (ball_subset_ball hr1.le)) hi⟩

end AreaDeficit
