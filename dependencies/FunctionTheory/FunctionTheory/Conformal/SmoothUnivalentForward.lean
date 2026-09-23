import FunctionTheory.Conformal.SmoothForwardChain
import FunctionTheory.Conformal.ForwardChainCollar

open Set Function Filter Metric
open scoped Topology ContDiff
namespace FunctionTheory
set_option autoImplicit false

/-- Finite univalent chains admit small smooth forward corrections, with the
initial coordinate fixed exactly. All inverse charts and intermediate-domain
collars are constructed from the input chain. The only interpolation required
of the perturbed chain is at finitely many prescribed prefix values. -/
theorem exists_smooth_univalent_forward_corrections
    (N : ℕ) (X W C U : ℕ → Set ℂ) (Θ : ℕ → ℂ ≃ₜ ℂ)
    (g : ℕ → ℂ → ℂ) (m : ℕ → ℕ) (ε : ℕ → ℝ)
    (hX : ∀ n≤N, IsCompact (X n)) (hW : ∀ n≤N, IsOpen (W n))
    (hXW : ∀ n≤N, Θ n '' X n⊆W n) (hCX : ∀ n≤N, C n⊆Θ n '' X n)
    (hΘ : ∀ n≤N, ContDiff ℝ (m n) (Θ n : ℂ → ℂ)) (hε : ∀ n≤N, 0<ε n)
    (hU : ∀ n<N, IsOpen (U n)) (hg : ∀ n<N, AnalyticOnNhd ℂ (g n) (U n))
    (hi : ∀ n<N, InjOn (g n) (Θ n '' X n))
    (hd : ∀ n<N, ∀ z∈Θ n '' X n, deriv (g n) z≠0)
    (hAU : ∀ n<N, Θ n '' X n⊆U n)
    (himage : ∀ n<N, g n '' (Θ n '' X n)=Θ (n+1) '' X (n+1)) :
    ∃ δ>0, ∀ f : ℕ → ℂ → ℂ,
      (∀ n<N, AnalyticOnNhd ℂ (f n) (U n)) →
      (∀ n<N, ∀ z∈U n, dist (f n z) (g n z)≤δ) →
      (∀ n≤N, ∀ x∈Θ 0 '' X 0, finiteComposition g n x∈C n →
        finiteComposition f n x=finiteComposition g n x) →
      ∃ E : ℕ → ℂ ≃ₜ ℂ, E 0=Homeomorph.refl ℂ ∧
        (∀ n≤N,
          ContDiff ℝ ∞ (E n : ℂ → ℂ) ∧ ContDiff ℝ ∞ ((E n).symm : ℂ → ℂ) ∧
          AnalyticOnNhd ℂ (E n : ℂ → ℂ) (Θ n '' X n) ∧
          (∀ z∈Θ n '' X n, deriv (E n : ℂ → ℂ) z≠0) ∧
          EqOn (E n : ℂ → ℂ) id (C n) ∧ (∀ z∉W n, E n z=z) ∧
          HasCompactSupport (fun z => E n z-z) ∧ tsupport (fun z => E n z-z)⊆W n ∧
          finiteSmoothNormOn (m n) (fun z => E n (Θ n z)-Θ n z) univ<ENNReal.ofReal (ε n)) ∧
        (∀ n<N, MapsTo (E n) (Θ n '' X n) (U n)) ∧
        ∀ n<N, ∀ z∈Θ n '' X n,
          (fun w => f n (E n w)) =ᶠ[𝓝 z] (fun w => E (n+1) (g n w)) := by
  classical
  let A := fun n => Θ n '' X n
  have hAc : ∀ n≤N, IsCompact (A n) := fun n hn => (hX n hn).image (Θ n).continuous
  have horbit : ∀ k<N, MapsTo (finiteComposition g k) (A 0) (U k) := by
    intro k hk z hz
    apply hAU k hk
    change finiteComposition g k z∈A k
    rw [← image_finiteComposition g A k (fun j hj => himage j (by omega))]
    exact mem_image_of_mem _ hz
  have Hchart := fun i : Fin (N+1) => exists_conformal_finite_composition g A
    (hAc 0 (by omega)) i (fun k hk => himage k (by omega))
    (fun k hk => (hg k (by omega)).mono (hAU k (by omega)))
    (fun k hk => hi k (by omega)) (fun k hk => hd k (by omega))
  choose b hbK hbe hba hbi hbim using Hchart
  let e := fun n => if hn : n≤N then b ⟨n,by omega⟩ else OpenPartialHomeomorph.refl ℂ
  have he : ∀ n≤N, (e n : ℂ → ℂ)=finiteComposition g n := by
    intro n hn; simpa only [e,dif_pos hn] using hbe ⟨n,by omega⟩
  have heK : ∀ n≤N, A 0⊆(e n).source := by
    intro n hn; simpa only [e,dif_pos hn] using hbK ⟨n,by omega⟩
  have hei : ∀ n≤N, AnalyticOnNhd ℂ (e n).symm (e n).target := by
    intro n hn; simpa only [e,dif_pos hn] using hbi ⟨n,by omega⟩
  have heim : ∀ n≤N, e n '' A 0=A n := by
    intro n hn; simpa only [e,dif_pos hn] using hbim ⟨n,by omega⟩
  have Hcollar := fun i : Fin (N+1) => exists_compact_target_collar_for_finite_orbit g U N
    (hAc 0 (by omega)) hU (fun k hk => (hg k hk).continuousOn) horbit (e i) (heK i (by omega))
    (hW i (by omega)) (by rw [heim i (by omega)]; exact hXW i (by omega))
  choose V hVo hVc hAV hVW hVe hVorbit using Hcollar
  let V' := fun n => if hn : n≤N then V ⟨n,by omega⟩ else ∅
  have HV : ∀ n≤N, IsOpen (V' n) ∧ IsCompact (closure (V' n)) ∧ A n⊆V' n ∧
      closure (V' n)⊆W n ∧ closure (V' n)⊆(e n).target ∧
      ∀ k<N, MapsTo (finiteComposition g k) ((e n).symm '' closure (V' n)) (U k) := by
    intro n hn
    simp only [V',dif_pos hn]
    let i : Fin (N+1) := ⟨n,by omega⟩
    refine ⟨hVo i,hVc i,?_,hVW i,hVe i,hVorbit i⟩
    simpa only [heim n hn] using hAV ⟨n,by omega⟩
  obtain ⟨ρ,hρ,Hρ⟩ := exists_smooth_forward_chain_tolerance N X V' C U Θ g e m ε
    hX (fun n hn => (HV n hn).1) (fun n hn => (HV n hn).2.1)
    (fun n hn => (HV n hn).2.2.1) hCX hΘ hε he heK heim
    (fun n hn => (HV n hn).2.2.2.2.1) hei hU hg hAU
    (fun n hn z hz => (himage n hn) ▸ mem_image_of_mem (g n) hz)
    (fun n hn k hk => (HV n hn).2.2.2.2.2 k (by omega))
  obtain ⟨σ,hσ,Hσ⟩ := finiteComposition_approximation_on_compact g U (A 0) (hAc 0 (by omega)) N
    hU (fun k hk => (hg k hk).continuousOn) horbit 1 one_pos
  refine ⟨min ρ (σ/2),lt_min hρ (half_pos hσ),?_⟩
  intro f hf hclose hmarks
  obtain ⟨Hdist,Hdom⟩ := Hσ f (fun k hk z hz =>
    ((hclose k hk z hz).trans (min_le_right _ _)).trans_lt (half_lt_self hσ))
  have hCM : ∀ n≤N, ∀ c∈C n, finiteComposition f n ((e n).symm c)=c := by
    intro n hn c hc
    obtain ⟨x,hx,hxc⟩ := (heim n hn).symm ▸ (show c∈A n from hCX n hn hc)
    have Hgx : finiteComposition g n x=c := by simpa only [he n hn] using hxc
    rw [← hxc,(e n).left_inv (heK n hn hx)]
    rw [he n hn]
    exact hmarks n hn x hx (Hgx.symm ▸ hc)
  obtain ⟨E,hE0,HE,Hconj⟩ := Hρ f hf
    (fun k hk z hz => (hclose k hk z hz).trans (min_le_left _ _)) hCM
  have hEA : ∀ n≤N, AnalyticOnNhd ℂ (E n : ℂ → ℂ) (A n) := by
    intro n hn z hz
    obtain ⟨x,hx,hxz⟩ := (heim n hn).symm ▸ hz
    have hzt : z∈(e n).target := hxz ▸ (e n).map_source (heK n hn hx)
    have hix : (e n).symm z=x := by rw [← hxz,(e n).left_inv (heK n hn hx)]
    have hFA : AnalyticAt ℂ (finiteComposition f n) ((e n).symm z) := by
      rw [hix]
      exact analyticAt_finiteComposition f n (fun k hk => hf k (by omega) _ (Hdom k (by omega) hx))
    exact (hFA.comp (hei n hn z hzt)).congr ((HE n hn).2.2.1 z hz).symm
  refine ⟨E,hE0,?_,?_,Hconj⟩
  · intro n hn
    have H := HE n hn
    refine ⟨H.1,H.2.1,hEA n hn,?_,H.2.2.2.1,?_,H.2.2.2.2.2.1,?_,H.2.2.2.2.2.2.2⟩
    · intro z hz
      exact (TauCeti.exists_injOn_nhds_iff_deriv_ne_zero (hEA n hn z hz)).mp
        ⟨univ,Filter.univ_mem,(E n).injective.injOn⟩
    · intro z hz
      exact H.2.2.2.2.1 z (fun hzV => hz ((HV n hn).2.2.2.1 (subset_closure hzV)))
    · exact H.2.2.2.2.2.2.1.trans (subset_closure.trans (HV n hn).2.2.2.1)
  · intro n hn z hz
    obtain ⟨x,hx,hxz⟩ := (heim n hn.le).symm ▸ (show z∈A n from hz)
    have Hval := ((HE n hn.le).2.2.1 z hz).eq_of_nhds
    change E n z=finiteComposition f n ((e n).symm z) at Hval
    rw [← hxz,(e n).left_inv (heK n hn.le hx)] at Hval
    rw [← hxz,Hval]
    exact Hdom n hn hx

end FunctionTheory
