import FunctionTheory.Conformal.SmoothForwardPrefix
import FunctionTheory.Conformal.UnivalentForwardCoordinates
import Mathlib.Algebra.Order.Field.Pi

open Set Function Filter Metric
open scoped Topology ContDiff
namespace FunctionTheory
set_option autoImplicit false

/-- A finite family of forward corrections has one positive approximation
tolerance. The initial correction is exactly the identity; the other
corrections have prescribed supports and smooth budgets and satisfy the
forward conjugacy as germs. Every support collar is supplied before the
tolerance is selected. Finite prefix interpolation fixes the marked points. -/
theorem exists_smooth_forward_chain_tolerance
    (N : ℕ) (X V C U : ℕ → Set ℂ) (Θ : ℕ → ℂ ≃ₜ ℂ)
    (g : ℕ → ℂ → ℂ) (e : ℕ → OpenPartialHomeomorph ℂ ℂ)
    (m : ℕ → ℕ) (ε : ℕ → ℝ)
    (hX : ∀ n≤N, IsCompact (X n)) (hV : ∀ n≤N, IsOpen (V n))
    (hVc : ∀ n≤N, IsCompact (closure (V n)))
    (hXV : ∀ n≤N, Θ n '' X n⊆V n) (hCX : ∀ n≤N, C n⊆Θ n '' X n)
    (hΘ : ∀ n≤N, ContDiff ℝ (m n) (Θ n : ℂ → ℂ)) (hε : ∀ n≤N, 0<ε n)
    (he : ∀ n≤N, (e n : ℂ → ℂ)=finiteComposition g n)
    (heK : ∀ n≤N, Θ 0 '' X 0⊆(e n).source)
    (heimage : ∀ n≤N, e n '' (Θ 0 '' X 0)=Θ n '' X n)
    (hVe : ∀ n≤N, closure (V n)⊆(e n).target)
    (hei : ∀ n≤N, AnalyticOnNhd ℂ (e n).symm (e n).target)
    (hU : ∀ k<N, IsOpen (U k)) (hg : ∀ k<N, AnalyticOnNhd ℂ (g k) (U k))
    (hAU : ∀ k<N, Θ k '' X k⊆U k)
    (hmap : ∀ k<N, MapsTo (g k) (Θ k '' X k) (Θ (k+1) '' X (k+1)))
    (horbit : ∀ n≤N, ∀ k<n, MapsTo (finiteComposition g k)
      ((e n).symm '' closure (V n)) (U k)) :
    ∃ δ>0, ∀ f : ℕ → ℂ → ℂ,
      (∀ k<N, AnalyticOnNhd ℂ (f k) (U k)) →
      (∀ k<N, ∀ z∈U k, dist (f k z) (g k z)≤δ) →
      (∀ n≤N, ∀ c∈C n, finiteComposition f n ((e n).symm c)=c) →
      ∃ E : ℕ → ℂ ≃ₜ ℂ, E 0=Homeomorph.refl ℂ ∧
        (∀ n≤N,
          ContDiff ℝ ∞ (E n : ℂ → ℂ) ∧ ContDiff ℝ ∞ ((E n).symm : ℂ → ℂ) ∧
          (∀ z∈Θ n '' X n, (E n : ℂ → ℂ) =ᶠ[𝓝 z] (finiteComposition f n ∘ (e n).symm)) ∧
          EqOn (E n : ℂ → ℂ) id (C n) ∧ (∀ z∉V n, E n z=z) ∧
          HasCompactSupport (fun z => E n z-z) ∧ tsupport (fun z => E n z-z)⊆V n ∧
          finiteSmoothNormOn (m n) (fun z => E n (Θ n z)-Θ n z) univ<ENNReal.ofReal (ε n)) ∧
        ∀ n<N, ∀ z∈Θ n '' X n,
          (fun w => f n (E n w)) =ᶠ[𝓝 z] (fun w => E (n+1) (g n w)) := by
  classical
  have H := fun i : Fin (N+1) => exists_smooth_forward_prefix_tolerance
    (Θ i) (m i) (hΘ i (by omega)) (hX i (by omega)) (hV i (by omega)) (hVc i (by omega))
    (hXV i (by omega)) (hCX i (by omega)) (e i) (hVe i (by omega)) (hei i (by omega))
    g U i (he i (by omega)) (fun k hk => hU k (by omega)) (fun k hk => hg k (by omega))
    (horbit i (by omega)) (hε i (by omega))
  choose b hb Hb using H
  obtain ⟨δ,hδ,Hδ⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : Fin (N+1) => (0:ℝ)) (y := b) hb
  refine ⟨δ,hδ,?_⟩
  intro f hf hclose hmarks
  have Hext := fun i : Fin (N+1) => Hb i f (fun k hk => hf k (by omega))
    (fun k hk z hz => (hclose k (by omega) z hz).trans (by simpa only [zero_add] using (Hδ i).le))
    (hmarks i (by omega))
  choose B hBs hBis hBeq hBC hBout hBcomp hBsupp hBnorm using Hext
  let E := fun n => if n=0 then Homeomorph.refl ℂ else
    if hn : n≤N then B ⟨n,by omega⟩ else Homeomorph.refl ℂ
  have HE : ∀ n≤N,
          ContDiff ℝ ∞ (E n : ℂ → ℂ) ∧ ContDiff ℝ ∞ ((E n).symm : ℂ → ℂ) ∧
          (∀ z∈Θ n '' X n, (E n : ℂ → ℂ) =ᶠ[𝓝 z] (finiteComposition f n ∘ (e n).symm)) ∧
          EqOn (E n : ℂ → ℂ) id (C n) ∧ (∀ z∉V n, E n z=z) ∧
          HasCompactSupport (fun z => E n z-z) ∧ tsupport (fun z => E n z-z)⊆V n ∧
          finiteSmoothNormOn (m n) (fun z => E n (Θ n z)-Θ n z) univ<ENNReal.ofReal (ε n) := by
    intro n hn
    by_cases hn0 : n=0
    · subst n
      have hE : E 0=Homeomorph.refl ℂ := by simp [E]
      rw [hE]
      refine ⟨contDiff_id,contDiff_id,?_,fun _ _ => rfl,fun _ _ => rfl,?_,?_,?_⟩
      · intro z hz
        have hzT := hVe 0 (by omega) (subset_closure (hXV 0 (by omega) hz))
        filter_upwards [(e 0).open_target.mem_nhds hzT] with w hw
        have Hinv := (e 0).right_inv hw
        simpa only [he 0 (by omega),finiteComposition,id_eq,Function.comp_apply,Homeomorph.refl_apply] using Hinv.symm
      · simp [HasCompactSupport]
      · simp
      · have hzero : (fun z : ℂ => (Homeomorph.refl ℂ) (Θ 0 z)-Θ 0 z)=(0 : ℂ → ℂ) := by
          funext z; exact sub_self _
        rw [hzero]
        apply finiteSmoothNormOn_lt_of_uniform_margin (hε 0 (by omega))
        intro k hk z hz
        rw [iteratedFDeriv_zero]
        simp only [Pi.zero_apply,norm_zero]
        exact div_nonneg (hε 0 (by omega)).le (by positivity)
    · have hE : E n=B ⟨n,by omega⟩ := by simp [E,hn0,hn]
      rw [hE]
      let i : Fin (N+1) := ⟨n,by omega⟩
      exact ⟨hBs i,hBis i,hBeq i,hBC i,hBout i,hBcomp i,hBsupp i,hBnorm i⟩
  refine ⟨E,by simp [E],HE,?_⟩
  intro n hn z hz
  obtain ⟨x,hx,hxz⟩ := (heimage n hn.le).symm ▸ hz
  have hzT : z∈(e n).target := hxz ▸ (e n).map_source (heK n hn.le hx)
  have hinv : (e n).symm z=x := by rw [← hxz,(e n).left_inv (heK n hn.le hx)]
  have hnext : (e n).symm z∈(e (n+1)).source := by rw [hinv]; exact heK _ (by omega) hx
  have hcont := (e n).symm.continuousAt hzT
  have hGcont := (hg n hn z (hAU n hn hz)).continuousAt
  have Heqnext := hGcont.eventually ((HE (n+1) (by omega)).2.2.1 _ (hmap n hn hz))
  filter_upwards [(HE n hn.le).2.2.1 z hz,Heqnext,(e n).open_target.mem_nhds hzT,
    hcont.eventually ((e (n+1)).open_source.mem_nhds hnext)] with w hw hnw hwT hwS
  rw [hw,hnw]
  have Hmap : e (n+1) ((e n).symm w)=g n w := by
    rw [he (n+1) (by omega)]
    change g n (finiteComposition g n ((e n).symm w))=g n w
    rw [← he n hn.le,(e n).right_inv hwT]
  change f n (finiteComposition f n ((e n).symm w))=
    finiteComposition f (n+1) ((e (n+1)).symm (g n w))
  rw [← Hmap,(e (n+1)).left_inv hwS]
  rfl

end FunctionTheory
