import EremenkosConjecture.ContinuumTargetMap
import EremenkosConjecture.LocalReturnCharts
import EremenkosConjecture.ContinuumStageChoices
import EremenkosConjecture.ScaffoldingReturnMap

open Set Function

namespace EremenkosConjecture

open Scaffolding

/-- The actual return map for a prescribed continuum, on a later member of
the fixed neighbourhood family. -/
structure ContinuumReturnChannel {X : Set ℂ}
    (D : ContinuumNeighbourhoods X rayBase (1 / 16)) (f : ℂ → ℂ) (j start : ℕ) where
  depth : ℕ
  later : start ≤ depth
  domain : Set ℂ
  open_domain : IsOpen domain
  connected_domain : IsConnected domain
  contains : X ∪ horizontalRay rayBase ⊆ domain
  region_subset : D.region depth ⊆ domain
  ψ : ℂ → ℂ
  holomorphic : ∀ k ≤ j + 1, DifferentiableOn ℂ (fun z => (f^[k]) (ψ z)) domain
  charts : ∀ k ≤ j + 1,
    ∃ E : LocalIterateChart (fun z => (f^[k]) (ψ z)) 1 (D.region depth),
      E.chart.source = domain
  orbit : ∀ k < j + 1, MapsTo (fun z => (f^[k]) (ψ z)) domain (insetSourceStrip k)
  target : ∀ z ∈ domain,
    (height (j + 1) + 7) / 4 + 1 / 4 ≤ ((f^[j + 1]) (ψ z)).im ∧
      ((f^[j + 1]) (ψ z)).im ≤ (height (j + 1) + 11) / 4 - 1 / 4
  boundedReturn : ∀ x : ℝ, 1 / ((j : ℝ) + 1) ≤ x → x ≤ (j : ℝ) + 1 →
    |(ψ (rayBase + x)).re| < 1 / 2
  continuumEscape : ∀ z ∈ X, ∀ k ≤ j + 1,
    (j : ℝ) + 2 ≤ |((f^[k]) (ψ z)).re|

theorem exists_continuumReturnChannel {X : Set ℂ} {f : ℂ → ℂ}
    (D : ContinuumNeighbourhoods X rayBase (1 / 16))
    (hX : IsCompact X) (hconn : IsConnected X) (hfull : IsConnected Xᶜ)
    (hζ : rayBase ∈ X) (hmax : ∀ z ∈ X, z.re ≤ rayBase.re)
    (hball : X ⊆ Metric.ball rayBase (1 / 16))
    (hf : DifferentiableOn ℂ f sourceStrips)
    (hclose : ∀ z ∈ sourceStrips, ‖f z - 5 * z‖ ≤ 1 / 100)
    (j start : ℕ) : Nonempty (ContinuumReturnChannel D f j start) := by
  obtain ⟨M⟩ := exists_continuumTargetMap hX hconn hfull hζ hmax hball j
  obtain ⟨R, htail⟩ := M.tail
  obtain ⟨m, hm, hmU⟩ := D.exists_later_region_subset_open M.open_domain M.contains
    (half_pos Real.pi_pos) htail start
  obtain ⟨d, hd⟩ := M.charts (D.region m) (D.geometry m).1.isClosed hmU (D.region_bounds m)
  have hMT : MapsTo M.φ M.domain (targetStrip (j + 1)) := by
    intro z hz
    have hi := abs_lt.mp (M.target z hz)
    constructor <;> linarith [hi.1, hi.2]
  obtain ⟨ψ, hψ, hfinal, horbit, hcharts⟩ := exists_return_map_with_local_charts
    hf hclose (Nat.succ_pos j) M.holomorphic hMT
  refine ⟨{
    depth := m
    later := hm
    domain := M.domain
    open_domain := M.open_domain
    connected_domain := M.connected_domain
    contains := M.contains
    region_subset := hmU
    ψ := ψ
    holomorphic := hψ
    charts := hcharts _ d hd
    orbit := horbit
    target := ?_
    boundedReturn := ?_
    continuumEscape := ?_ }⟩
  · intro z hz
    have he : (f^[j + 1]) (ψ z) = M.φ z := hfinal hz
    rw [he]
    have hi := abs_lt.mp (M.target z hz)
    constructor <;> linarith [hi.1, hi.2]
  · intro x hxmin hxmax
    have hx : 0 ≤ x := (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)).le.trans hxmin
    apply return_map_small_real_part hclose horbit hfinal (M.contains (Or.inr ?_))
      (M.compact_ray x hxmin hxmax)
    exact ⟨by change rayBase.re ≤ rayBase.re + x; linarith, by simp⟩
  · intro z hz
    apply return_map_large_real_parts hclose horbit hfinal
      (by linarith [Nat.cast_nonneg (α := ℝ) j] : (1 / 2 : ℝ) ≤ (j : ℝ) + 2)
      (M.contains (Or.inl hz))
    simpa only [show (j : ℝ) + 2 + 1 = (j : ℝ) + 3 by ring] using M.far_left z hz

end EremenkosConjecture
