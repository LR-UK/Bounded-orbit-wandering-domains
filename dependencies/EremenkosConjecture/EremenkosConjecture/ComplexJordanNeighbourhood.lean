import EremenkosConjecture.JordanNeighbourhood
import EremenkosConjecture.FullNeighbourhoods
import Mathlib.Topology.Homeomorph.Lemmas

open Set Metric
open scoped Topology

namespace EremenkosConjecture

/-- The standard identification of the complex plane with the Euclidean plane. -/
noncomputable def complexPlaneHomeomorph : ℂ ≃ₜ Schoenflies.Plane :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((Homeomorph.finTwoArrow (X := ℝ)).symm.trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).toHomeomorph.symm)

/-- A Jordan curve in the complex plane, transported along the coordinate
homeomorphism to the independently verified planar curve definition. -/
def IsComplexJordanCurve (C : Set ℂ) : Prop :=
  Schoenflies.IsJordanCurve (complexPlaneHomeomorph '' C)

theorem exists_jordan_compact_neighbourhood (K U : Set ℂ)
    (hK : IsCompact K) (hconn : IsConnected K) (hfull : IsConnected Kᶜ)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ IsConnected L ∧ IsConnected Lᶜ ∧
      K ⊆ interior L ∧ L ⊆ U ∧ IsComplexJordanCurve (frontier L) ∧
      IsConnected (interior L) ∧ L = closure (interior L) := by
  let e := complexPlaneHomeomorph
  obtain ⟨M, hM, hMf, hKM, hMU⟩ := exists_full_compact_neighbourhood K U hK hfull hU hKU
  have hKp := hK.image e.continuous
  have hKpc := hconn.image e e.continuous.continuousOn
  have hMp := hM.image e.continuous
  have hMpf : IsConnected (e '' M)ᶜ := by
    rw [← e.image_compl]
    exact hMf.image e e.continuous.continuousOn
  have hKpM : e '' K ⊆ interior (e '' M) := by
    rw [← e.image_interior]
    exact image_mono hKM
  obtain ⟨L, hL, hLc, hLf, hKL, hLM, hJ, hLi, hLreg⟩ :=
    exists_jordan_neighbourhood_within_full_compact hKp hKpc hMp hMpf hKpM
  refine ⟨e ⁻¹' L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.isCompact_preimage.mpr hL
  · rw [← e.image_symm]
    exact hLc.image e.symm e.symm.continuous.continuousOn
  · rw [← preimage_compl, ← e.image_symm]
    exact hLf.image e.symm e.symm.continuous.continuousOn
  · rw [← e.preimage_interior]
    exact fun z hz => hKL (mem_image_of_mem e hz)
  · intro z hz
    exact hMU (e.preimage_image M ▸ (show z ∈ e ⁻¹' (e '' M) from hLM hz))
  · change Schoenflies.IsJordanCurve (e '' frontier (e ⁻¹' L))
    rw [e.image_frontier, e.image_preimage]
    exact hJ
  · rw [← e.preimage_interior, ← e.image_symm]
    exact hLi.image e.symm e.symm.continuous.continuousOn
  · rw [← e.preimage_interior, ← e.preimage_closure, ← hLreg]

end EremenkosConjecture
