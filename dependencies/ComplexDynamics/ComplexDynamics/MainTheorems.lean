import ComplexDynamics.Wandering
import ComplexDynamics.BoundedNormality
import ComplexDynamics.FastEscape
import ComplexDynamics.TranscendentalApproximation
import ComplexDynamics.CurvesToInfinity

/-!
# Main statements for mathematical review

Start here to read the advertised results without following the construction.
Every statement below is checked by Lean against the completed proof named on
the following line. MAIN_RESULTS.md explains the notation and hypotheses;
PROOF_MAP.md explains how the proofs fit together.

This is a proved statement gallery, not a Palomar Challenge/Comparator package.
-/

open Set Metric Function Filter
open scoped Topology

namespace ComplexDynamics.MainTheorems

/-- Uniform escape gives a Fatou interior directly. -/
theorem uniform_escape_gives_fatou_interior {f : ℂ → ℂ} {K : Set ℂ}
    (h : EscapesUniformlyOn f K) : interior K ⊆ fatouSet f :=
  ComplexDynamics.EscapesUniformlyOn.interior_subset_fatouSet h

/-- Escape together with accumulation of trapped orbits excludes local normality. -/
theorem escape_and_trapping_give_julia {f : ℂ → ℂ}
    (hf : Continuous f) {B : Set ℂ} (hB : IsCompact B) {z : ℂ}
    (hz : z ∈ escapingSet f) (hacc : z ∈ closure (trappedSet f B)) :
    z ∈ juliaSet f :=
  ComplexDynamics.mem_juliaSet_of_escape_of_closure_trappedSet hf hB hz hacc

/-- The construction criterion for actual wandering Fatou components; all hypotheses are explicit. -/
theorem wandering_criterion
    (f : ℂ → ℂ) (hf : Continuous f) (K B : Set ℂ) (hK : IsCompact K) (hB : IsCompact B)
    (hescape : EscapesUniformlyOn f K)
    (hboundary : frontier K ⊆ closure (trappedSet f B))
    (hambient : ∀ n, ∃ H : ℂ ≃ₜ ℂ, EqOn (f^[n]) H K)
    (hdisjoint : ∀ n m : ℕ, n ≠ m → Disjoint ((f^[n]) '' K) ((f^[m]) '' K)) :
    ∀ z ∈ interior K, IsWanderingDomain f (connectedComponentIn (interior K) z) :=
  ComplexDynamics.wandering_of_uniformEscape_of_trappedBoundary f hf K B hK hB hescape hboundary hambient hdisjoint

/-- The disk definition of maximum modulus agrees with the circle definition. -/
theorem maximum_modulus_on_circle {f : ℂ → ℂ} (hf : IsEntire f) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus f r = sSup ((fun z => ‖f z‖) '' sphere 0 r) :=
  ComplexDynamics.maximumModulus_eq_sphere hf hr

end ComplexDynamics.MainTheorems
