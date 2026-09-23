import EremenkosConjecture.FilledRayInsets
import ComplexApproximation.Topology.ArakelianElementaryGeometry

open Set Metric

namespace EremenkosConjecture

/-- The actual filled compact decoration with a closed halfstrip is Arakelian. -/
theorem isArakelian_filledRayInset {C : Set ℂ} {ζ : ℂ} {s η : ℝ}
    (hC : IsCompact C) (hs : 0 ≤ s) (hη : 0 ≤ η) :
    ComplexApproximation.IsArakelian (filledRayInset C ζ s η) := by
  have hζ : ζ ∈ closedHalfStrip ζ s η := ⟨by linarith, by simpa using hη⟩
  exact ComplexApproximation.isArakelian_fill_compact_union_starConvex hC
    (isClosed_closedHalfStrip ζ s η) hζ ((convex_closedHalfStrip ζ s η).starConvex hζ)

end EremenkosConjecture
