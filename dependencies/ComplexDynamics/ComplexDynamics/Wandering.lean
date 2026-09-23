import ComplexDynamics.FatouComponents
import ComplexDynamics.Iteration

/-!
# Wandering components from uniform escape and trapped boundary points

This criterion uses the normality and trapped-orbit arguments directly.
Ambient homeomorphisms identify the boundaries of the forward compact images.
-/

open Set Function Filter
open scoped Topology

namespace ComplexDynamics

theorem EscapesUniformlyOn.image_iterate {f : ℂ → ℂ} {K : Set ℂ}
    (h : EscapesUniformlyOn f K) (n : ℕ) : EscapesUniformlyOn f ((f^[n]) '' K) := by
  intro R
  have H := (tendsto_add_atTop_nat n).eventually (h R)
  filter_upwards [H] with m hm w hw
  obtain ⟨z, hz, rfl⟩ := hw
  simpa only [iterate_add_apply] using hm z hz

theorem mapsTo_iterate_trappedSet (f : ℂ → ℂ) (B : Set ℂ) (n : ℕ) :
    MapsTo (f^[n]) (trappedSet f B) (trappedSet f B) := by
  intro z hz
  have H := (tendsto_add_atTop_nat n).eventually hz
  simpa only [trappedSet, Set.mem_ofPred_eq, iterate_add_apply] using H

theorem wandering_of_uniformEscape_of_trappedBoundary
    (f : ℂ → ℂ) (hf : Continuous f) (K B : Set ℂ) (hK : IsCompact K) (hB : IsCompact B)
    (hescape : EscapesUniformlyOn f K)
    (hboundary : frontier K ⊆ closure (trappedSet f B))
    (hambient : ∀ n, ∃ H : ℂ ≃ₜ ℂ, EqOn (f^[n]) H K)
    (hdisjoint : ∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)) :
    ∀ z ∈ interior K, IsWanderingDomain f (connectedComponentIn (interior K) z) := by
  have hcompact (n : ℕ) : IsCompact ((f^[n]) '' K) := hK.image (hf.iterate n)
  have hfrontier (n : ℕ) : frontier ((f^[n]) '' K) = (f^[n]) '' frontier K := by
    obtain ⟨H, heq⟩ := hambient n
    have himage : (f^[n]) '' K = H '' K := image_congr heq
    rw [himage, ← H.image_frontier]
    apply image_congr
    intro z hz
    exact (heq (hK.isClosed.closure_eq ▸ hz.1)).symm
  have hJulia (n : ℕ) : frontier ((f^[n]) '' K) ⊆ juliaSet f := by
    intro w hw
    have hwK : w ∈ (f^[n]) '' K := (hcompact n).isClosed.closure_eq ▸ hw.1
    apply mem_juliaSet_of_escape_of_closure_trappedSet hf hB
      ((hescape.image_iterate n).subset_escapingSet hwK)
    rw [hfrontier n] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact (mapsTo_iterate_trappedSet f B n).closure_of_continuousOn
      (hf.iterate n).continuousOn (hboundary hz)
  have hinterior (n : ℕ) : interior ((f^[n]) '' K) ⊆ fatouSet f :=
    (hescape.image_iterate n).interior_subset_fatouSet
  have hinside (n : ℕ) {z : ℂ} (hz : z ∈ interior K) :
      (f^[n]) z ∈ interior ((f^[n]) '' K) := by
    obtain ⟨H, heq⟩ := hambient n
    have himage : (f^[n]) '' K = H '' K := image_congr heq
    rw [himage, ← H.image_interior, heq (interior_subset hz)]
    exact mem_image_of_mem _ hz
  have hcomponent (n : ℕ) {z : ℂ} (hz : z ∈ interior K) :
      connectedComponentIn (fatouSet f) ((f^[n]) z) ⊆ (f^[n]) '' K := by
    rw [← connectedComponentIn_interior_eq_fatou (hcompact n).isClosed
      (hinterior n) (hJulia n) (hinside n hz)]
    exact (connectedComponentIn_subset _ _).trans interior_subset
  have hJulia₀ : frontier K ⊆ juliaSet f := by simpa only [iterate_zero, image_id] using hJulia 0
  intro z hz
  refine ⟨isFatouComponent_connectedComponentIn_interior hK.isClosed
    hescape.interior_subset_fatouSet hJulia₀ hz, ?_⟩
  intro w hw n m hnm heq
  have hwi : w ∈ interior K := connectedComponentIn_subset _ _ hw
  have hmem : (f^[n]) w ∈ connectedComponentIn (fatouSet f) ((f^[n]) w) :=
    mem_connectedComponentIn (hinterior n (hinside n hwi))
  rw [heq] at hmem
  exact Set.disjoint_left.mp (hdisjoint n m hnm)
    (mem_image_of_mem _ (interior_subset hwi)) (hcomponent m hwi hmem)

end ComplexDynamics
