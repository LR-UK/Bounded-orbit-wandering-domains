import FunctionTheory.Conformal.ProperDiscQuotient
import FunctionTheory.Conformal.ProperDiscZeros
import FunctionTheory.Conformal.FiniteBlaschke

open Set Metric Filter Function
open scoped Topology BigOperators ComplexConjugate
namespace FunctionTheory
set_option autoImplicit false

/-- Every proper holomorphic self-map of the open disc is a unimodular
constant times a finite product of Blaschke factors. The finite set lists
distinct zeros and the positive natural numbers record their multiplicities. -/
theorem exists_weighted_blaschke_of_isProperMap_holomorphic_disc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1))) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ) (c : ℂ), S.Nonempty ∧
      (∀ a∈S, ‖a‖<1 ∧ 0<n a) ∧ ‖c‖=1 ∧
      EqOn f (fun z => c*∏ a∈S, blaschkeFactor a z ^ n a) (ball (0:ℂ) 1) := by
  classical
  let d := MeromorphicOn.divisor f (ball (0:ℂ) 1)
  have hd : ∀ a : ℂ, 0≤d a := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hfin := finite_divisor_support_of_isProperMap_holomorphic_disc hf hmap hproper
  let S := hfin.toFinset
  let n : ℂ → ℕ := fun a => (d a).toNat
  have hS : ∀ a∈S, ‖a‖<1 := by
    intro a ha
    exact mem_ball_zero_iff.mp (d.supportWithinDomain (hfin.mem_toFinset.mp ha))
  have hn : ∀ a∈S, 0<n a := by
    intro a ha
    have H : d a≠0 := hfin.mem_toFinset.mp ha
    have H0 := hd a
    dsimp only [n]
    omega
  let P : ℂ → ℂ := fun z => ∏ a∈S, (z-a)^n a
  let Q : ℂ → ℂ := fun z => ∏ a∈S, (1-conj a*z)^n a
  let B : ℂ → ℂ := fun z => ∏ a∈S, blaschkeFactor a z ^ n a
  have hQ : AnalyticOnNhd ℂ Q (closedBall (0:ℂ) 1) := by
    intro z hz
    apply Finset.analyticAt_fun_prod
    intro a ha
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow (n a)
  have hQn : ∀ z∈closedBall (0:ℂ) 1, Q z≠0 := by
    intro z hz
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _
      (blaschke_denominator_ne_zero (hS a ha) (mem_closedBall_zero_iff.mp hz)))
  have hB : AnalyticOnNhd ℂ B (closedBall (0:ℂ) 1) := by
    intro z hz
    apply Finset.analyticAt_fun_prod
    intro a ha
    exact ((analyticAt_id.sub analyticAt_const).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (blaschke_denominator_ne_zero (hS a ha) (mem_closedBall_zero_iff.mp hz))).pow (n a)
  have hcircle : ∀ z : ℂ, ‖z‖=1 → ‖B z‖=1 := by
    intro z hz
    simp only [B,norm_prod,norm_pow]
    apply Finset.prod_eq_one
    intro a ha
    rw [norm_blaschkeFactor_eq_one (hS a ha) hz,one_pow]
  have hsmall : ∀ z∈ball (0:ℂ) 1, ‖B z‖≤1 := by
    intro z hz
    simp only [B,norm_prod,norm_pow]
    apply Finset.prod_le_one₀
    · intro a ha
      positivity
    · intro a ha
      exact pow_le_one₀ (norm_nonneg _)
        (norm_blaschkeFactor_lt_one (hS a ha) (mem_ball_zero_iff.mp hz)).le
  have hBP : ∀ z∈closedBall (0:ℂ) 1, B z*Q z=P z := by
    intro z hz
    have H : B z=P z/Q z := by
      simp only [B,blaschkeFactor,div_pow,Finset.prod_div_distrib,P,Q]
    rw [H,div_mul_cancel₀ _ (hQn z hz)]
  obtain ⟨g,hg,hgn,heq⟩ := exists_zero_factorisation_of_isProperMap_holomorphic_disc hf hmap hproper
  have hP : (∏ᶠ u : ℂ, (·-u)^d u)=P := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (by
      rw [Function.FactorizedRational.mulSupport]
      exact hfin.coe_toFinset.ge)]
    funext z
    simp only [Finset.prod_apply,Pi.pow_apply,P]
    apply Finset.prod_congr rfl
    intro a ha
    rw [← Int.toNat_of_nonneg (hd a),zpow_natCast]
  let h : ℂ → ℂ := fun z => g z*Q z
  have hh : AnalyticOnNhd ℂ h (ball (0:ℂ) 1) := hg.mul (hQ.mono ball_subset_closedBall)
  have hhn : ∀ z∈ball (0:ℂ) 1, h z≠0 := fun z hz =>
    mul_ne_zero (hgn z hz) (hQn z (ball_subset_closedBall hz))
  have hfactor : ∀ z∈ball (0:ℂ) 1, f z=B z*h z := by
    intro z hz
    have H := heq hz
    change f z=(∏ᶠ u : ℂ, (·-u)^d u) z*g z at H
    rw [hP] at H
    rw [H,← hBP z (ball_subset_closedBall hz)]
    dsimp only [h]
    ring
  obtain ⟨c,hc,hconst⟩ := eq_unimodular_const_of_proper_disc_factor
    hmap hproper hB.continuousOn hcircle hsmall hh hhn hfactor
  have hresult : EqOn f (fun z => c*B z) (ball (0:ℂ) 1) := by
    intro z hz
    rw [hfactor z hz,hconst hz,mul_comm]
  have hSne : S.Nonempty := by
    by_contra H
    have HS : S=∅ := Finset.not_nonempty_iff_eq_empty.mp H
    have H0 := hresult (mem_ball_self (by norm_num : (0:ℝ)<1))
    have Hnorm : ‖f 0‖<1 := mem_ball_zero_iff.mp (hmap (mem_ball_self one_pos))
    simp only [B,HS,Finset.prod_empty,mul_one] at H0
    rw [H0,hc] at Hnorm
    exact Hnorm.false
  exact ⟨S,n,c,hSne,fun a ha => ⟨hS a ha,hn a ha⟩,hc,hresult⟩

/-- The proper-disc classification in the library's existing finite Blaschke
product interface, with repeated zeros and positive degree. -/
theorem exists_finiteBlaschkeProduct_of_isProperMap_holomorphic_disc
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0:ℂ) 1))
    (hmap : MapsTo f (ball (0:ℂ) 1) (ball (0:ℂ) 1))
    (hproper : IsProperMap (fun z : ball (0:ℂ) 1 =>
      (⟨f z,hmap z.property⟩ : ball (0:ℂ) 1))) :
    ∃ B : FiniteBlaschkeProduct, EqOn f B.eval (ball (0:ℂ) 1) := by
  classical
  obtain ⟨S,n,c,hSne,hSn,hc,hresult⟩ :=
    exists_weighted_blaschke_of_isProperMap_holomorphic_disc hf hmap hproper
  let ι := (a : S) × Fin (n (a:ℂ))
  obtain ⟨a,ha⟩ := hSne
  letI : Nonempty ι := ⟨⟨⟨a,ha⟩,⟨0,(hSn a ha).2⟩⟩⟩
  have hcard : 0<Fintype.card ι := Fintype.card_pos
  let k := Fintype.card ι-1
  have hk : k+1=Fintype.card ι := Nat.sub_add_cancel hcard
  let e : Fin (k+1) ≃ ι := (finCongr hk).trans (Fintype.equivFin ι).symm
  let B : FiniteBlaschkeProduct :=
    { degreePred := k
      zero := fun i => ((e i).1:ℂ)
      zero_lt_one := fun i => (hSn _ (e i).1.property).1
      phase := c
      norm_phase := hc }
  refine ⟨B,?_⟩
  intro z hz
  have H : (∏ i : Fin (k+1), blaschkeFactor ((e i).1:ℂ) z)=
      ∏ i : ι, blaschkeFactor (i.1:ℂ) z :=
    Fintype.prod_equiv e _ _ (fun _ => rfl)
  have H' : (∏ i : ι, blaschkeFactor (i.1:ℂ) z)=
      ∏ a∈S, blaschkeFactor a z ^ n a := by
    simp only [ι,Fintype.prod_sigma,Finset.prod_const,Finset.card_univ,
      Fintype.card_fin]
    exact Finset.prod_coe_sort S (fun a : ℂ => blaschkeFactor a z ^ n a)
  change f z=c*∏ i : Fin (k+1), blaschkeFactor ((e i).1:ℂ) z
  rw [H,H']
  exact hresult hz

end FunctionTheory
