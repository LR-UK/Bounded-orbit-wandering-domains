import LocalDynamicalAreaBound
import LocalPunctureSequence
import BarrierComponents
import ChartAreaLimit
import ChartDiscs

open Set Metric Function Filter MeasureTheory
open scoped Topology ENNReal

namespace AreaDeficit.FinitePunctureMetricInput

/-- The conditional local wandering-domain theorem in normalized
Riemann coordinates. Injectivity is required only eventually on each
fixed-radius disc. The starting time may depend on the radius. -/
theorem no_wandering_chart_orbit_with_anchors (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {a b : ℂ} (hab : a ≠ b) (ha : a ∉ V) (hb : b ∉ V)
    {U : ℕ → Set ℂ} {z : ℕ → ℂ} {u : ℕ → ℂ → ℂ}
    (hz : ∀ n, z n ∈ interior (trappedSet f V))
    (hU : ∀ n, U n = connectedComponentIn (interior (trappedSet f V)) (z n))
    (hnext : ∀ n, f (z n) = z (n + 1))
    (hdisj : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hUK : ∀ n, U n ⊆ K)
    (hu : ∀ n, DifferentiableOn ℂ (u n) (U n))
    (hub : ∀ n, BijOn (u n) (U n) (ball 0 1)) (hu0 : ∀ n, u n (z n) = 0)
    (hinj : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ,
      ∀ n ≥ N, InjOn f (chartDisc (u n) (U n) r)) : False := by
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
  obtain ⟨N, hNi⟩ := hinj r hr hr1
  let D : ℕ → Set ℂ := fun n => chartDisc (u n) (U n) r
  have hDo : ∀ n, IsOpen (D n) := fun n => chartDisc_isOpen (hUo n) (hu n) r
  have hDU : ∀ n, D n ⊆ U n := fun _ => inter_subset_left
  have hfD : ∀ n, MapsTo f (D n) (D (n + 1)) := by
    intro n
    apply mapsTo_chartDisc (hUo n) (hu n) (hub n) (hu (n + 1)) (hub (n + 1)).mapsTo
      (hfV.differentiableOn.mono ((hUK n).trans hKV)) (hfm n) (hzU n) (hu0 n)
    · rw [hnext n]
      exact hu0 (n + 1)
    · exact hr1
  let W : Set ℂ := ⋃ n ≥ N, D n
  have hW : MeasurableSet W := MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ => (hDo n).measurableSet))
  have hBW : D N ⊆ W := fun x hx => mem_iUnion₂.mpr ⟨N, le_rfl, hx⟩
  have hWK : W ⊆ K := by
    intro x hx
    obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp hx
    exact hUK n (hDU n hn)
  have hiW : InjOn f W := by
    intro x hx y hy hxy
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.mp hy
    have hnm : n = m := by
      by_contra hne
      exact disjoint_left.mp (hdisj (by omega : n + 1 ≠ m + 1))
        (hfm n (hDU n hx)) (hxy ▸ hfm m (hDU m hy))
    subst m
    exact hNi n hn hx hy hxy
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
  have harea := G.chart_area_bound hP hab (hanchors 0).1 (hanchors 0).2
    (z := z N) (u := u N)
    (by change DifferentiableOn ℂ (u N) (connectedComponentIn Aᶜ (z N)); rw [hcomp N]; exact hu N)
    (by change MapsTo (u N) (connectedComponentIn Aᶜ (z N)) (ball 0 1); rw [hcomp N]; exact (hub N).mapsTo)
    (hDo N).measurableSet
    (by change D N ⊆ connectedComponentIn Aᶜ (z N); rw [hcomp N]; exact hDU N) hPN
  have hformula := chart_disc_area (hUo N) (hu N) (hub N) hr.le hr1
  change (∫⁻ x in chartDisc (u N) (U N) r,
    ENNReal.ofReal ((‖deriv (u N) x‖ * discDensity (u N x))^2)) ≤ C at harea
  rw [chartDisc, hformula] at harea
  rw [disc_area_lintegral hr.le hr1, ENNReal.ofReal_toReal hC]
  exact harea

/-- Final conditional theorem for local functions. A relatively compact
orbit of pairwise distinct simply connected trapped components is
incompatible with eventual injectivity on each fixed intrinsic disc.
Classical finite-puncture geometry is the sole unconstructed parameter. -/
theorem no_wandering_component_orbit (G : FinitePunctureMetricInput)
    {f : ℂ → ℂ} {V K : Set ℂ} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hf : AnalyticOnNhd ℂ f (closure V))
    (hn : ∀ x ∈ closure V, ¬EventuallyConst f (𝓝 x))
    (hK : IsCompact K) (hKV : K ⊆ V)
    {U : ℕ → Set ℂ} {z : ℕ → ℂ}
    (hz : ∀ n, z n ∈ interior (trappedSet f V))
    (hU : ∀ n, U n = connectedComponentIn (interior (trappedSet f V)) (z n))
    (hnext : ∀ n, f (z n) = z (n + 1))
    (hdisj : Pairwise (fun n m => Disjoint (U n) (U m)))
    (hUK : ∀ n, U n ⊆ K) (hsc : ∀ n, IsSimplyConnected (U n))
    (hinj : EventuallyInjectiveOnLargeDiscs f U z) : False := by
  classical
  obtain ⟨R, hR, hVR⟩ := hVc.isBounded.exists_pos_norm_le
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
  have hUo : ∀ n, IsOpen (U n) := fun n => by rw [hU n]; exact isOpen_interior.connectedComponentIn
  have hzU : ∀ n, z n ∈ U n := fun n => by rw [hU n]; exact mem_connectedComponentIn (hz n)
  have hUne : ∀ n, U n ≠ univ := by
    intro n he
    exact ha (hKV (hUK n (he ▸ mem_univ a)))
  choose u hu hub hu0 using fun n =>
    Complex.exists_bijOn_unitBall_map_eq_zero (hUo n) (hsc n) (hUne n) (hzU n)
  apply G.no_wandering_chart_orbit_with_anchors hV hVc hf hn hK hKV hab ha hb
    hz hU hnext hdisj hUK hu hub hu0
  intro r hr hr1
  obtain ⟨N, hN⟩ := hinj r hr hr1
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨v, hv, hvb, hv0, hvi⟩ := hN n hn
  rw [chartDisc_eq (hUo n) (hu n) (hub n) hv hvb (hzU n) (hu0 n) hv0 hr1]
  exact hvi

end AreaDeficit.FinitePunctureMetricInput

#print axioms AreaDeficit.FinitePunctureMetricInput.no_wandering_chart_orbit_with_anchors
#print axioms AreaDeficit.FinitePunctureMetricInput.no_wandering_component_orbit
