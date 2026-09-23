import EremenkosConjecture.Runge
import Mathlib.Topology.Separation.Regular

/-!
# Holomorphic gluing on separated compact sets

Functions with disjoint compact domains can be glued on disjoint open
neighbourhoods. Runge then approximates all prescribed pieces simultaneously.
-/

open Set Metric Filter
open scoped Topology

namespace EremenkosConjecture

theorem exists_holomorphic_gluing (K L U V : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L)
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V) :
    ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ K ∪ L ⊆ W ∧
      DifferentiableOn ℂ h W ∧ (∀ z ∈ K, h =ᶠ[𝓝 z] f) ∧
        (∀ z ∈ L, h =ᶠ[𝓝 z] g) := by
  classical
  obtain ⟨O, P, hO, hP, hKO, hLP, hOP⟩ := normal_separation hK.isClosed hL.isClosed hKL
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

theorem polynomial_approximation_two_pieces (K L U V : Set ℂ)
    (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L)
    (hfull : IsConnected (K ∪ L)ᶜ)
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, (∀ z ∈ K, ‖f z - p.eval z‖ < ε) ∧
      (∀ z ∈ L, ‖g z - p.eval z‖ < ε) := by
  obtain ⟨W, h, hW, hKW, hh, hf', hg'⟩ :=
    exists_holomorphic_gluing K L U V hK hL hKL hU hV hKU hLV f g hf hg
  obtain ⟨p, hp⟩ := Runge.polynomial_approximation_of_holomorphic (K ∪ L)
    (hK.union hL) hfull W hW hKW h hh ε hε
  exact ⟨p, fun z hz => (hf' z hz).eq_of_nhds ▸ hp z (Or.inl hz),
    fun z hz => (hg' z hz).eq_of_nhds ▸ hp z (Or.inr hz)⟩

end EremenkosConjecture
