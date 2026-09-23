import ComplexApproximation.Arakelian
import Mathlib.Topology.Separation.Regular

/-! # Simultaneous approximation on disjoint closed pieces -/

open Set Filter
open scoped Topology

namespace ComplexApproximation

theorem exists_holomorphic_gluing_closed (K L U V : Set ℂ)
    (hK : IsClosed K) (hL : IsClosed L) (hKL : Disjoint K L)
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V) :
    ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ K ∪ L ⊆ W ∧
      DifferentiableOn ℂ h W ∧ (∀ z ∈ K, h =ᶠ[𝓝 z] f) ∧
        (∀ z ∈ L, h =ᶠ[𝓝 z] g) := by
  classical
  obtain ⟨O, P, hO, hP, hKO, hLP, hOP⟩ := normal_separation hK hL hKL
  let O' := O ∩ U
  let P' := P ∩ V
  have hO' : IsOpen O' := hO.inter hU
  have hP' : IsOpen P' := hP.inter hV
  have hd : Disjoint O' P' := hOP.mono inter_subset_left inter_subset_left
  let h := O'.piecewise f g
  have heqf : ∀ z ∈ O', h =ᶠ[𝓝 z] f := by
    intro z hz
    filter_upwards [hO'.mem_nhds hz] with w hw
    exact piecewise_eq_of_mem O' f g hw
  have heqg : ∀ z ∈ P', h =ᶠ[𝓝 z] g := by
    intro z hz
    filter_upwards [hP'.mem_nhds hz] with w hw
    exact piecewise_eq_of_notMem O' f g (fun hwO => Set.disjoint_left.mp hd hwO hw)
  refine ⟨O' ∪ P', h, hO'.union hP', ?_, ?_, ?_, ?_⟩
  · rintro z (hz | hz)
    · exact Or.inl ⟨hKO hz, hKU hz⟩
    · exact Or.inr ⟨hLP hz, hLV hz⟩
  · rintro z (hz | hz)
    · exact ((hf.differentiableAt (hU.mem_nhds hz.2)).congr_of_eventuallyEq
        (heqf z hz)).differentiableWithinAt
    · exact ((hg.differentiableAt (hV.mem_nhds hz.2)).congr_of_eventuallyEq
        (heqg z hz)).differentiableWithinAt
  · exact fun z hz => heqf z ⟨hKO hz, hKU hz⟩
  · exact fun z hz => heqg z ⟨hLP hz, hLV hz⟩

theorem exists_holomorphic_gluing_three_closed (K L M U V W : Set ℂ)
    (hK : IsClosed K) (hL : IsClosed L) (hM : IsClosed M)
    (hKL : Disjoint K L) (hKM : Disjoint K M) (hLM : Disjoint L M)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hKU : K ⊆ U) (hLV : L ⊆ V) (hMW : M ⊆ W)
    (f g h : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g V) (hh : DifferentiableOn ℂ h W) :
    ∃ (D : Set ℂ) (q : ℂ → ℂ), IsOpen D ∧ (K ∪ L) ∪ M ⊆ D ∧
      DifferentiableOn ℂ q D ∧ (∀ z ∈ K, q =ᶠ[𝓝 z] f) ∧
      (∀ z ∈ L, q =ᶠ[𝓝 z] g) ∧ (∀ z ∈ M, q =ᶠ[𝓝 z] h) := by
  obtain ⟨O, p, hO, hKO, hp, hpf, hpg⟩ :=
    exists_holomorphic_gluing_closed K L U V hK hL hKL hU hV hKU hLV f g hf hg
  obtain ⟨D, q, hD, hKD, hq, hqp, hqh⟩ :=
    exists_holomorphic_gluing_closed (K ∪ L) M O W (hK.union hL) hM
      (disjoint_union_left.mpr ⟨hKM, hLM⟩) hO hW hKO hMW p h hp hh
  exact ⟨D, q, hD, hKD, hq,
    fun z hz => (hqp z (Or.inl hz)).trans (hpf z hz),
    fun z hz => (hqp z (Or.inr hz)).trans (hpg z hz), hqh⟩

theorem arakelian_approximation_three_pieces (K L M U V W : Set ℂ)
    (hK : IsClosed K) (hL : IsClosed L) (hM : IsClosed M)
    (hKL : Disjoint K L) (hKM : Disjoint K M) (hLM : Disjoint L M)
    (hArak : IsArakelian ((K ∪ L) ∪ M))
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hKU : K ⊆ U) (hLV : L ⊆ V) (hMW : M ⊆ W)
    (f g h : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g V) (hh : DifferentiableOn ℂ h W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z ∈ K, ‖f z - F z‖ < ε) ∧
      (∀ z ∈ L, ‖g z - F z‖ < ε) ∧
      (∀ z ∈ M, ‖h z - F z‖ < ε) := by
  obtain ⟨O, p, hO, hKO, hp, hpf, hpg⟩ :=
    exists_holomorphic_gluing_closed K L U V hK hL hKL hU hV hKU hLV f g hf hg
  obtain ⟨T, q, hT, hKT, hq, hqp, hqh⟩ :=
    exists_holomorphic_gluing_closed (K ∪ L) M O W (hK.union hL) hM
      (disjoint_union_left.mpr ⟨hKM, hLM⟩) hO hW hKO hMW p h hp hh
  obtain ⟨F, hF, hclose⟩ := arakelian_approximation_of_holomorphic
    ((K ∪ L) ∪ M) hArak T hT hKT q hq ε hε
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro z hz
    have he : q z = f z := (hqp z (Or.inl hz)).eq_of_nhds.trans (hpf z hz).eq_of_nhds
    simpa only [he, norm_sub_rev] using hclose z (Or.inl (Or.inl hz))
  · intro z hz
    have he : q z = g z := (hqp z (Or.inr hz)).eq_of_nhds.trans (hpg z hz).eq_of_nhds
    simpa only [he, norm_sub_rev] using hclose z (Or.inl (Or.inr hz))
  · intro z hz
    simpa only [(hqh z hz).eq_of_nhds, norm_sub_rev] using hclose z (Or.inr hz)

end ComplexApproximation
