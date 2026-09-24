/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.ConditionalWanderingDomains
import BoundedWanderingDomains.CoveringDiscs
import BoundedWanderingDomains.CoveringDiscArea

open Set Metric Function Filter MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit.FinitePunctureMetricInput

/-- The area contradiction for eventually embedded universal covering discs.
The components themselves can be multiply connected. -/
theorem no_wandering_covering_orbit_with_eventual_embedded_discs (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∉ V) (hb : b ∉ V)
    {U : ℕ → Set ℂ} {z : ℕ → ℂ} {p : ℕ → ℂ → ℂ}
    (hz : ∀ n, z n ∈ interior (trappedSet f V))
    (hU : ∀ n, U n = connectedComponentIn (interior (trappedSet f V)) (z n))
    (hnext : ∀ n, f (z n) = z (n + 1))
    (hdisj : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hp : ∀ n, IsHolomorphicDiscCovering (p n) (U n))
    (hp0 : ∀ n, p n 0 = z n)
    (hpinj : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, InjOn (p n) (ball 0 r))
    (hcompact : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, p n '' ball 0 r ⊆ K)
    (hinj : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, InjOn f (p n '' ball 0 r)) : False := by
  classical
  have hfV := hf.mono (subset_closure : V ⊆ closure V)
  have hnV := fun x hx => hn x (subset_closure hx)
  have hUo : ∀ n, IsOpen (U n) := fun n => by rw [hU n]; exact isOpen_interior.connectedComponentIn
  have hzU : ∀ n, z n ∈ U n := fun n => by rw [hU n]; exact mem_connectedComponentIn (hz n)
  have hUT : ∀ n, U n ⊆ interior (trappedSet f V) :=
    fun n => by rw [hU n]; exact connectedComponentIn_subset _ _
  have hfT := trapped_interior_forward (analytic_locally_open hfV hnV)
  have hfm : ∀ n, MapsTo f (U n) (U (n + 1)) := by
    intro n
    rw [hU n, hU (n + 1), ← hnext n]
    exact ((hfV.continuousOn.mono (interior_subset.trans (trappedSet_subset f V))).mapsTo_connectedComponentIn
      (hz n)).mono_right (connectedComponentIn_mono _ (mapsTo_iff_image_subset.mp hfT))
  obtain ⟨P, hP, hanchors, hforward, havoid, hbarrier, hfront, hback⟩ :=
    exists_local_puncture_sequence hV subset_closure hVc hf hn ha hb
  let A := closure (⋃ n, (↑(P n) : Set ℂ))
  have hTA : interior (trappedSet f V) ⊆ Aᶜ := by
    intro x hx hxA
    have hh : x ∈ trappedSet f V ∩ A := ⟨interior_subset hx, hxA⟩
    rw [hbarrier] at hh
    exact hh.2 hx
  have hcomp : ∀ n, connectedComponentIn Aᶜ (z n) = U n := fun n =>
    (barrier_component_eq_trapped_component hV isClosed_closure hfV.continuousOn
      hfront hback hTA (hz n)).trans (hU n).symm
  obtain ⟨H, hH, hbound⟩ := G.local_dynamical_area_bound hV hVc hf hn hK hKV hab
  let C := ENNReal.ofReal (2 * Real.pi) * H
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH
  apply no_uniform_disc_area_bound C.toReal
  intro r hr hr1
  rcases hr.eq_or_lt with rfl | hr
  · simp
  obtain ⟨Ni, hNi⟩ := hinj r hr hr1
  obtain ⟨Nk, hNk⟩ := hcompact r hr hr1
  obtain ⟨Np, hNp⟩ := hpinj r hr hr1
  let N := max Ni (max Nk Np)
  let D : ℕ → Set ℂ := fun n => p n '' ball 0 r
  have hDo : ∀ n, IsOpen (D n) := fun n => (hp n).image_isOpen isOpen_ball (ball_subset_ball hr1.le)
  have hDU : ∀ n, D n ⊆ U n := fun n => (image_mono (ball_subset_ball hr1.le)).trans (hp n).maps.image_subset
  have hfD : ∀ n, MapsTo f (D n) (D (n + 1)) := by
    intro n
    exact mapsTo_covering_disc (hp n) (hp (n+1))
      (hfV.differentiableOn.mono ((hUT n).trans (interior_subset.trans (trappedSet_subset f V))))
      (hfm n) (by rw [hp0, hp0, hnext]) hr1
  let W : Set ℂ := ⋃ n ≥ N, D n
  have hW : MeasurableSet W := MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ => (hDo n).measurableSet))
  have hBW : D N ⊆ W := fun x hx => mem_iUnion₂.mpr ⟨N, le_rfl, hx⟩
  have hWK : W ⊆ K := by
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    exact hNk n (le_trans ((le_max_left Nk Np).trans (le_max_right Ni (max Nk Np))) hn) hx
  have hiW : InjOn f W := by
    intro x hx y hy hxy
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.mp hy
    have hnm : n = m := by
      by_contra hne
      exact disjoint_left.mp (hdisj (by omega : n + 1 ≠ m + 1))
        (hfm n (hDU n hx)) (hxy ▸ hfm m (hDU m hy))
    subst m
    exact hNi n (le_trans (le_max_left Ni (max Nk Np)) hn) hx hy hxy
  have himage : f '' W ⊆ W \ D N := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    refine ⟨mem_iUnion₂.mpr ⟨n + 1, by omega, hfD n hx⟩, ?_⟩
    intro hy
    exact disjoint_left.mp (hdisj (by omega : n + 1 ≠ N))
      (hfm n (hDU n hx)) (hDU N hy)
  have hPN : ∀ j, G.area (P j) (D N) ≤ H := by
    intro j
    apply hbound (P j) (hanchors j).1 (hanchors j).2 (hforward j)
      (D N) W (hDo N).measurableSet hW hBW hWK hiW himage
    intro w hw
    obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp hw
    exact havoid j (f w) (interior_subset (hUT (n + 1) (hfm n (hDU n hn))))
  have harea := G.covering_area_bound hP hab (hanchors 0).1 (hanchors 0).2
    (z := z N) (p := p N)
    (by change IsHolomorphicDiscCovering (p N) (connectedComponentIn Aᶜ (z N));
        rw [hcomp N]; exact hp N)
    (hDo N).measurableSet
    (by change D N ⊆ connectedComponentIn Aᶜ (z N); rw [hcomp N]; exact hDU N) hPN
  have hpi : InjOn (p N) (ball 0 r) := hNp N
    ((le_max_right Nk Np).trans (le_max_right Ni (max Nk Np)))
  have hformula := (hp N).area_image isOpen_ball.measurableSet (ball_subset_ball hr1.le) hpi
  change (∫⁻ x in p N '' ball 0 r, ENNReal.ofReal ((coveringDensity (p N) x)^2)) ≤ C at harea
  rw [hformula] at harea
  rw [ENNReal.ofReal_toReal hC]
  exact harea



end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.no_wandering_covering_orbit_with_eventual_embedded_discs
