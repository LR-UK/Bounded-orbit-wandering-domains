import FunctionTheory.Conformal.UnivalentFiniteComposition

open Set Function Filter
open scoped Topology

namespace FunctionTheory

set_option autoImplicit false

/-- Forward coordinates for finite univalent chains. The initial coordinate
is the identity near the initial compact. Explicit interpolation of finite
compositions is sufficient to fix marks at every later level. -/
theorem exists_univalent_forward_coordinates
    (f g : ℕ → ℂ → ℂ) (K C : ℕ → Set ℂ) (N : ℕ) (ε : ℕ → ℝ)
    (e b : ℕ → OpenPartialHomeomorph ℂ ℂ)
    (heK : ∀ n≤N, K 0 ⊆ (e n).source)
    (hbK : ∀ n≤N, K 0 ⊆ (b n).source)
    (he : ∀ n, (e n : ℂ → ℂ)=finiteComposition g n)
    (hb : ∀ n, (b n : ℂ → ℂ)=finiteComposition f n)
    (hea : ∀ n≤N, AnalyticOnNhd ℂ (e n) (e n).source)
    (hei : ∀ n≤N, AnalyticOnNhd ℂ (e n).symm (e n).target)
    (hba : ∀ n≤N, AnalyticOnNhd ℂ (b n) (b n).source)
    (hbi : ∀ n≤N, AnalyticOnNhd ℂ (b n).symm (b n).target)
    (himage : ∀ n<N, g n '' K n=K (n+1))
    (hC : ∀ n≤N, C n ⊆ K n)
    (hmarks : ∀ n≤N, ∀ x∈K 0, finiteComposition g n x∈C n →
      finiteComposition f n x=finiteComposition g n x)
    (hclose : ∀ n≤N, ∀ x∈K 0,
      dist (finiteComposition f n x) (finiteComposition g n x)≤ε n) :
    ∃ θ : ℕ → OpenPartialHomeomorph ℂ ℂ,
      (∀ n≤N, K n ⊆ (θ n).source ∧
        AnalyticOnNhd ℂ (θ n) (θ n).source ∧
        AnalyticOnNhd ℂ (θ n).symm (θ n).target ∧
        EqOn (θ n : ℂ → ℂ) id (C n) ∧
        (∀ z∈K n, dist (θ n z) z≤ε n) ∧
        ∀ x∈K 0, θ n (finiteComposition g n x)=finiteComposition f n x) ∧
      EqOn (θ 0 : ℂ → ℂ) id (θ 0).source ∧
      ∀ n<N, ∀ a∈K n,
        (fun z => f n (θ n z)) =ᶠ[𝓝 a] (fun z => θ (n+1) (g n z)) := by
  let θ := fun n => (e n).symm.trans (b n)
  have hvalue : ∀ n z, θ n z=finiteComposition f n ((e n).symm z) := by
    intro n z
    change b n ((e n).symm z)=_
    rw [hb n]
  have him : ∀ n≤N, (e n) '' K 0=K n := by
    intro n hn
    rw [he n]
    exact image_finiteComposition g K n (fun k hk => himage k (by omega))
  have hv : ∀ n≤N, ∀ x∈K 0, θ n (finiteComposition g n x)=finiteComposition f n x := by
    intro n hn x hx
    rw [hvalue n,← he n,(e n).left_inv (heK n hn hx)]
  have hs : ∀ n≤N, K n ⊆ (θ n).source := by
    intro n hn z hz
    obtain ⟨x,hx,rfl⟩ := (him n hn).symm ▸ hz
    refine ⟨(e n).map_source (heK n hn hx),?_⟩
    change (e n).symm (e n x)∈(b n).source
    rw [(e n).left_inv (heK n hn hx)]
    exact hbK n hn hx
  refine ⟨θ,?_,?_,?_⟩
  · intro n hn
    refine ⟨hs n hn,?_,?_,?_,?_,hv n hn⟩
    · intro z hz
      exact (hba n hn _ hz.2).comp (hei n hn _ hz.1)
    · intro z hz
      exact (hea n hn _ hz.2).comp (hbi n hn _ hz.1)
    · intro z hz
      obtain ⟨x,hx,hxz⟩ := (him n hn).symm ▸ hC n hn hz
      have hgxz : finiteComposition g n x=z := by simpa only [he n] using hxz
      rw [← hgxz,hv n hn x hx]
      exact hmarks n hn x hx (hgxz.symm ▸ hz)
    · intro z hz
      obtain ⟨x,hx,hxz⟩ := (him n hn).symm ▸ hz
      have hgxz : finiteComposition g n x=z := by simpa only [he n] using hxz
      rw [← hgxz,hv n hn x hx]
      exact hclose n hn x hx
  · intro z hz
    rw [hvalue 0]
    change (e 0).symm z=z
    have H := (e 0).right_inv hz.1
    simpa only [he 0,finiteComposition,id_eq] using H
  · intro n hn a ha
    obtain ⟨x,hx,hxa⟩ := (him n hn.le).symm ▸ ha
    have hat : a∈(e n).target := hxa ▸ (e n).map_source (heK n hn.le hx)
    have hinv : (e n).symm a=x := by rw [← hxa,(e n).left_inv (heK n hn.le hx)]
    have hnext : (e n).symm a∈(e (n+1)).source := by rw [hinv]; exact heK _ (by omega) hx
    have hcont := (e n).continuousOn_symm.continuousAt ((e n).open_target.mem_nhds hat)
    filter_upwards [(e n).open_target.mem_nhds hat,
      hcont.eventually ((e (n+1)).open_source.mem_nhds hnext)] with z hzt hzn
    rw [hvalue n,hvalue (n+1)]
    exact (finiteComposition_forward_coordinate_step f g e he n hzt hzn).symm

end FunctionTheory
