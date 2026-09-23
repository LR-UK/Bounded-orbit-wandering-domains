import EremenkosConjecture.PathBarrierData
import EremenkosConjecture.FastEscape
import ComplexDynamics.BoundedNormality
import ComplexDynamics.PathComponents

open Set Metric Function Filter ComplexDynamics

namespace EremenkosConjecture

/-- A fast wandering compactum surrounded by barriers in a bounded Fatou region. -/
structure BarrierWanderingWitness (K : Set ℂ) extends FastWanderingWitness K where
  P : ℕ → Set ℂ
  trap : Set ℂ
  trapOpen : IsOpen trap
  trapBounded : Bornology.IsBounded trap
  trapInvariant : MapsTo f trap trap
  entersTrap : ∀ n z, z ∈ P n → ∃ m, (f^[m]) z ∈ trap
  barrier : ∀ g : ℝ → ℂ, Continuous g → g 0 ∈ K → g 1 ∉ K →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ n, g t ∉ P n) → False

theorem BarrierWanderingWitness.barriers_avoid {K : Set ℂ} (W : BarrierWanderingWitness K)
    (n : ℕ) : Disjoint (W.P n) (escapingSet W.f ∪ juliaSet W.f) := by
  apply Set.disjoint_left.mpr
  intro z hz hS
  obtain ⟨m, hm⟩ := W.entersTrap n z hz
  have hfat := mem_fatouSet_of_iterate_mem_bounded_invariant W.transcendental.1
    W.trapOpen W.trapBounded W.trapInvariant hm
  rcases hS with he | hj
  · obtain ⟨R, _, hR⟩ := W.trapBounded.exists_pos_norm_le
    have ht := mem_trappedSet_of_iterate_mem W.trapInvariant hm
    have hlarge : ∀ᶠ k : ℕ in atTop, R < ‖(W.f^[k]) z‖ := he.eventually (eventually_gt_atTop R)
    obtain ⟨k, hk, hkt⟩ := (hlarge.and ht).exists
    exact (not_lt_of_ge (hR _ hkt)) hk
  · exact hj hfat

theorem BarrierWanderingWitness.no_exit {K : Set ℂ} (W : BarrierWanderingWitness K)
    {x y : ℂ} (hx : x ∈ K) (hxy : JoinedIn (escapingSet W.f ∪ juliaSet W.f) x y) : y ∈ K := by
  by_contra hy
  obtain ⟨γ, hγ⟩ := hxy
  apply W.barrier γ.extend γ.continuous_extend (by simpa using hx) (by simpa using hy)
  intro t ht n hp
  have hmem : γ.extend t ∈ escapingSet W.f ∪ juliaSet W.f := by
    rw [γ.extend_apply ht]
    exact hγ _
  exact Set.disjoint_left.mp (W.barriers_avoid n) hp hmem

theorem BarrierWanderingWitness.escaping_path_components {K : Set ℂ}
    (W : BarrierWanderingWitness K) {x : ℂ} (hx : x ∈ K) :
    pathComponentIn (escapingSet W.f) x = pathComponentIn K x :=
  pathComponentIn_eq_of_no_exit W.escape.subset_escapingSet
    (fun _ hz _ hzy => W.no_exit hz (hzy.mono subset_union_left)) hx

theorem BarrierWanderingWitness.julia_path_components {K : Set ℂ}
    (W : BarrierWanderingWitness K) (hK : IsClosed K) {x : ℂ} (hx : x ∈ frontier K) :
    pathComponentIn (juliaSet W.f) x = pathComponentIn (frontier K) x := by
  have hboundary := W.toUniformWanderingWitness.julia_boundary hK
  have heq := inter_juliaSet_eq_frontier hK W.escape.interior_subset_fatouSet hboundary
  rw [← heq]
  exact pathComponentIn_eq_inter_of_no_exit
    (fun _ hz _ hzy => W.no_exit hz (hzy.mono subset_union_right))
    ⟨hK.closure_eq ▸ hx.1, hboundary hx⟩

theorem exists_barrierWanderingWitness_normalized (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) (hnorm : K ⊆ targetDisc 0)
    {a b : ℂ} (ha : a ∈ frontier K) (hb : b ∈ frontier K) (hab : a ≠ b) :
    Nonempty (BarrierWanderingWitness K) := by
  obtain ⟨A⟩ := exists_pathBarrierData K hK hconn hfull hnorm ha hb hab
  let D := A.data
  obtain ⟨V⟩ := VariableConstruction.exists_entireConstruction D
  have hKD := A.contains
  have hmapK (n : ℕ) : MapsTo (V.f^[n]) K (V.chain.target n) :=
    fun z hz => V.maps_target n (hKD n hz)
  have hdisjoint : ∀ n m : ℕ, n ≠ m → Disjoint ((V.f^[n]) '' K) ((V.f^[m]) '' K) :=
    fun n m hnm => (V.chain.disjoint_targets hnm).mono (hmapK n).image_subset (hmapK m).image_subset
  have htrapSub : trappingDisc ⊆ controlDisc 0 := by
    simpa only [controlDisc, trappingDisc, Nat.cast_zero, mul_zero, add_zero] using
      (ball_subset_closedBall : ball (-3 : ℂ) 1 ⊆ closedBall (-3) 1)
  have hforward : MapsTo V.f (controlDisc 0) (controlDisc 0) :=
    fun z hz => htrapSub ((V.property 0).1 hz)
  have hP : (⋃ n, D.P n) ⊆ trappedSet V.f (controlDisc 0) := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact mem_trappedSet_of_iterate_mem hforward (htrapSub (V.maps_points n hn))
  have haK : a ∈ K := (frontier_subset_iff_isClosed.mpr hK.isClosed) ha
  have hanorm : ‖a‖ < 1 := by simpa [targetDisc] using hnorm haK
  have hr := V.chain.radius_lower 1
  norm_num at hr
  refine ⟨{
    f := V.f
    transcendental := V.transcendental hKD hconn.nonempty A.nonempty
    B := controlDisc 0
    compactB := isCompact_closedBall _ _
    escape := V.escapesUniformly hKD
    disjoint := hdisjoint
    boundary := A.accumulation.trans (closure_mono hP)
    ambient := ?_
    radius := V.chain.radius 1 - 3
    radius_pos := by linarith
    fastAt := V.fastEscapeAtEveryRadius hKD
    marker := a
    marker_boundary := ha
    marker_norm := by linarith
    P := D.P
    trap := trappingDisc
    trapOpen := isOpen_ball
    trapBounded := isBounded_ball
    trapInvariant := fun _ hz => (V.property 0).1 (htrapSub hz)
    entersTrap := fun n z hz => ⟨n + 1, V.maps_points n hz⟩
    barrier := A.barrier
  }⟩
  intro n
  obtain ⟨H, U, hU, hDU, heq, hH, hHi⟩ := V.charts n
  exact ⟨H, fun z hz => heq (hDU (hKD n hz))⟩

end EremenkosConjecture
