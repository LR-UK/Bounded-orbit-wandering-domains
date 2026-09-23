import FunctionTheory.Conformal.CriticalOrders
import FunctionTheory.Conformal.CriticalCorrectionRadius
import FunctionTheory.Conformal.ConformalLiftGluing
import FunctionTheory.Topology.FiniteDisjointBalls
import FunctionTheory.Topology.FiniteDiskGeometry
import Mathlib.Topology.Separation.Regular

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- A holomorphic map with finitely many critical points admits a conformal
correction on any relatively compact open subset containing those points.
Sufficiently close perturbations must retain all marked values and at least
the reference local degrees. All marked points are fixed by the correction. -/
theorem exists_conformal_correction_of_finite_critical_set_order_le
    {U V C : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact (closure V)) (hKU : closure V ⊆ U)
    (hC : C.Finite) (hCV : C ⊆ V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U)
    (hcritical : ∀ z ∈ U, deriv φ z = 0 → z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ c ∈ C, g c = φ c) →
      (∀ c ∈ C, analyticOrderAt (fun z => φ z - φ c) c ≤
        analyticOrderAt (fun z => g z - g c) c) →
      (∀ z ∈ U, ‖φ z - g z‖ ≤ δ) →
      ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V ∧ InjOn θ V ∧ MapsTo θ V U ∧
        DifferentiableOn ℂ (Function.invFunOn θ V) (θ '' V) ∧
        (∀ z ∈ V, ‖θ z - z‖ < ε ∧ g (θ z) = φ z) ∧ ∀ c ∈ C, θ c = c := by
  classical
  let : Fintype C := hC.fintype
  let c : C → ℂ := Subtype.val
  have hrange : range c = C := Subtype.range_val
  have hVU : V ⊆ U := subset_closure.trans hKU
  have hnc := locally_nonconstant_of_finite_critical_set hU hC hcritical
  obtain ⟨ρ, hρ, hsep⟩ := exists_pairwise_disjoint_closedBalls_of_finite hC
  have hdisk := fun i : C => exists_correction_disk_at_locally_nonconstant
    (hφ (c i) (hVU (hCV i.property))) (hnc (c i) (hVU (hCV i.property)))
    hV (hCV i.property) hρ
  choose R hR hRρ hRV Hlocal using hdisk
  have hdisj : Pairwise (fun i j => Disjoint (closedBall (c i) (R i))
      (closedBall (c j) (R j))) := by
    intro i j hij
    exact (hsep (c i) i.property (c j) j.property
      (fun h => hij (Subtype.ext h))).mono
      (closedBall_subset_closedBall (hRρ i)) (closedBall_subset_closedBall (hRρ j))
  obtain ⟨W, hW, hVW, hWU, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  have hWV : V ⊆ W := subset_closure.trans hVW
  have hWsubU : W ⊆ U := subset_closure.trans hWU
  have hRW : ∀ i, closedBall (c i) (R i) ⊆ W := fun i => (hRV i).trans hWV
  have hRU : ∀ i, closedBall (c i) (R i) ⊆ U := fun i => (hRV i).trans hVU
  let D := diskRegularRegion W c R
  let A := diskOverlapCollars c R
  let U₀ := U \ C
  have hU₀ : IsOpen U₀ := hU.sdiff hC.isClosed
  have hD : IsOpen D := isOpen_diskRegularRegion hW c R
  have hDcompact : IsCompact (closure D) := isCompact_closure_diskRegularRegion hWcompact c R
  have hDU : closure D ⊆ U₀ := by
    simpa only [hrange] using closure_diskRegularRegion_subset (c := c) hWU hR
  have hAc : IsCompact A := isCompact_diskOverlapCollars c R
  have hAU : A ⊆ U₀ := by
    simpa only [hrange] using diskOverlapCollars_subset hR hRU hdisj
  have hφ₀ : AnalyticOnNhd ℂ φ U₀ := hφ.mono sdiff_subset
  have hd₀ : ∀ z ∈ U₀, deriv φ z ≠ 0 := fun z hz hzero => hz.2 (hcritical z hz.1 hzero)
  obtain ⟨rA, hrA, δA, hδA, _, HgA⟩ :=
    exists_uniform_injective_approximation_radius hU₀ hAc hAU hφ₀
      (fun z hz => hd₀ z (hAU hz))
  obtain ⟨r, hr, htube⟩ := hK.exists_thickening_subset_open hW hVW
  have hballs : ∀ z ∈ V, ball z r ⊆ W := by
    intro z hz w hw
    exact htube (mem_thickening_iff.mpr ⟨z, subset_closure hz, hw⟩)
  let η := min ε (min (r / 4) (rA / 2))
  have hη : 0 < η := lt_min hε (lt_min (by positivity) (half_pos hrA))
  have hηε : η ≤ ε := min_le_left _ _
  have hηr : 2 * η < r := by
    have hbound : η ≤ r / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hηA : η ≤ rA := ((min_le_right _ _).trans (min_le_right _ _)).trans (half_le_self hrA.le)
  obtain ⟨δD, hδD, HD⟩ := exists_conformal_correction_of_deriv_ne_zero
    hU₀ hD hDcompact hDU hφ₀ (fun z hz => hd₀ z (hDU hz)) hη
  choose d hd Hc using fun i => Hlocal i η hη
  obtain ⟨δC, hδC, HδC⟩ := (Set.finite_range d).isCompact.exists_forall_le'
    continuousOn_id (fun x hx => by obtain ⟨i, rfl⟩ := hx; exact hd i)
  let δ := min δA (min δD δC) / 2
  have hδ : 0 < δ := half_pos (lt_min hδA (lt_min hδD hδC))
  have hδbase : δ < min δA (min δD δC) := half_lt_self (lt_min hδA (lt_min hδD hδC))
  have hδa : δ < δA := hδbase.trans_le (min_le_left _ _)
  have hδd : δ ≤ δD := (hδbase.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδc : ∀ i, δ ≤ d i := fun i =>
    ((hδbase.le.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (HδC (d i) (mem_range_self i))
  refine ⟨δ, hδ, ?_⟩
  intro g hg hvalue horder hclose
  have hg₀ : AnalyticOnNhd ℂ g U₀ := hg.mono sdiff_subset
  have hginj : ∀ z ∈ A, InjOn g (ball z η) := fun z hz =>
    (HgA g hg₀ (fun w hw => (hclose w hw.1).trans_lt hδa) z hz).mono (ball_subset_ball hηA)
  obtain ⟨θD, hθDA, _, hθDU, _, hθDpair, _⟩ :=
    HD g hg₀ (fun z hz => (hclose z hz.1).trans hδd)
  have hlocal := fun i => Hc i g (hg.mono (hRU i))
    (hvalue (c i) i.property) (horder (c i) i.property)
    (fun z hz => (hclose z (hRU i hz)).trans (hδc i))
  choose θc hθcA _hθci hθcU _hθcinv hθcpair hθcc using hlocal
  let O : Option C → Set ℂ := fun i => match i with
    | none => D
    | some i => ball (c i) (R i / 2)
  let θs : Option C → ℂ → ℂ := fun i => match i with
    | none => θD
    | some i => θc i
  have hO : ∀ i, IsOpen (O i) := by
    intro i
    cases i with
    | none => exact hD
    | some i => exact isOpen_ball
  have hcover : (⋃ i, O i) = W := by
    rw [iUnion_option]
    exact diskRegularRegion_union_halfBalls hR hRW
  have hθA : ∀ i, AnalyticOnNhd ℂ (θs i) (O i) := by
    intro i
    cases i with
    | none => exact hθDA
    | some i => exact hθcA i
  have hnear : ∀ i, ∀ z ∈ O i, dist (θs i z) z < η := by
    intro i z hz
    cases i with
    | none => simpa only [θs, dist_eq_norm] using (hθDpair z hz).1
    | some i => simpa only [θs, dist_eq_norm] using (hθcpair i z hz).1
  have hlift : ∀ i, ∀ z ∈ O i, g (θs i z) = φ z := by
    intro i z hz
    cases i with
    | none => exact (hθDpair z hz).2
    | some i => exact (hθcpair i z hz).2
  have htarget : ∀ i, MapsTo (θs i) (O i) U := by
    intro i z hz
    cases i with
    | none => exact (hθDU hz).1
    | some i => exact hRU i (ball_subset_closedBall (hθcU i hz))
  have hinj : ∀ i j, i ≠ j → ∀ z ∈ O i ∩ O j, InjOn g (ball z η) := by
    intro i j hij z hz
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hginj z (diskRegularRegion_inter_halfBall_subset_collars W c R j hz)
    | some i =>
      cases j with
      | none => exact hginj z (diskRegularRegion_inter_halfBall_subset_collars W c R i ⟨hz.2, hz.1⟩)
      | some j =>
        have hij' : i ≠ j := fun h => hij (congrArg some h)
        exact (Set.disjoint_left.mp (hdisj hij')
          (closedBall_subset_closedBall (half_le_self (hR i).le) (ball_subset_closedBall hz.1))
          (closedBall_subset_closedBall (half_le_self (hR j).le) (ball_subset_closedBall hz.2))).elim
  obtain ⟨θ, hθA, hθi, hθU, hθinv, heq, hpair⟩ :=
    exists_glued_conformal_lift_with_collar hV hWV O hO hcover θs hθA hr hηr
      hballs hnear hlift htarget hinj
  refine ⟨θ, hθA.mono hWV, hθi, hθU.mono_left hWV, hθinv, ?_, ?_⟩
  · intro z hz
    exact ⟨by simpa only [dist_eq_norm] using (hpair z (hWV hz)).1.trans_le hηε,
      (hpair z (hWV hz)).2⟩
  · intro z hz
    let i : C := ⟨z, hz⟩
    exact (heq (some i) (mem_ball_self (half_pos (hR i)))).trans (hθcc i)

/-- The finite conformal-correction lemma in critical-multiplicity form.
Only critical points of the reference map need multiplicity constraints;
the remaining marked points need only value interpolation. -/
theorem exists_conformal_correction_of_finite_critical_set
    {U V C : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact (closure V)) (hKU : closure V ⊆ U)
    (hC : C.Finite) (hCV : C ⊆ V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U)
    (hcritical : ∀ z ∈ U, deriv φ z = 0 → z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g U →
      (∀ c ∈ C, g c = φ c) →
      (∀ c ∈ V, deriv φ c = 0 →
        analyticOrderAt (deriv g) c = analyticOrderAt (deriv φ) c) →
      (∀ z ∈ U, ‖φ z - g z‖ ≤ δ) →
      ∃ θ : ℂ → ℂ, AnalyticOnNhd ℂ θ V ∧ InjOn θ V ∧ MapsTo θ V U ∧
        DifferentiableOn ℂ (Function.invFunOn θ V) (θ '' V) ∧
        (∀ z ∈ V, ‖θ z - z‖ < ε ∧ g (θ z) = φ z) ∧ ∀ c ∈ C, θ c = c := by
  obtain ⟨δ, hδ, H⟩ := exists_conformal_correction_of_finite_critical_set_order_le
    hU hV hK hKU hC hCV hφ hcritical hε
  refine ⟨δ, hδ, ?_⟩
  intro g hg hvalue hmult hclose
  apply H g hg hvalue _ hclose
  intro c hc
  have hcU := hKU (subset_closure (hCV hc))
  by_cases hdc : deriv φ c = 0
  · exact (analyticOrderAt_sub_eq_of_deriv_order_eq (hφ c hcU) (hg c hcU)
      (hmult c (hCV hc) hdc).symm).le
  · rw [(hφ c hcU).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hdc]
    have hG : AnalyticAt ℂ (fun z => g z - g c) c := (hg c hcU).sub analyticAt_const
    exact Order.one_le_iff_ne_zero.mpr (hG.analyticOrderAt_ne_zero.mpr (sub_self (g c)))

end FunctionTheory
