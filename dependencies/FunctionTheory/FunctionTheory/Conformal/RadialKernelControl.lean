import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Order.LeftRightNhds

open Set Metric Filter Complex
open scoped Topology

namespace FunctionTheory

/-- Ordinary interior kernel convergence gives simultaneous control on the
compact reference segment used by the separating semicircles. -/
theorem eventually_close_on_radial_segment
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {V : Set ℂ} {ζ a : ℂ} {r R ε : ℝ}
    (hconv : TendstoLocallyUniformlyOn F f atTop V)
    (hsegment : ∀ t ∈ Icc r R, ζ + (t : ℂ) ∈ V)
    (hε : 0 < ε)
    (hf : ∀ t ∈ Icc r R, dist (f (ζ + (t : ℂ))) a < ε / 2) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc r R, dist (F n (ζ + (t : ℂ))) a < ε := by
  let K := (fun t : ℝ => ζ + (t : ℂ)) '' Icc r R
  have hK : IsCompact K := isCompact_Icc.image (continuous_const.add Complex.continuous_ofReal)
  have hKV : K ⊆ V := by rintro _ ⟨t, ht, rfl⟩; exact hsegment t ht
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hconv.mono hKV)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) (ε / 2) (half_pos hε)] with n hn
  intro t ht
  have hd := hn (ζ + (t : ℂ)) (mem_image_of_mem _ ht)
  have hb := hf t ht
  have htri := dist_triangle (F n (ζ + (t : ℂ))) (f (ζ + (t : ℂ))) a
  rw [dist_comm (f _)] at hd
  linarith

/-- The outer radius is first chosen using the limiting map at the attachment
point. Any positive inner radius then gives a compact interior segment, on
which ordinary kernel convergence suffices. -/
theorem exists_outer_radius_for_radial_kernel_control
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {V : Set ℂ} {ζ a : ℂ} {R₀ ε : ℝ}
    (hconv : TendstoLocallyUniformlyOn F f atTop V)
    (hR₀ : 0 < R₀) (hε : 0 < ε)
    (hrad : ∀ t ∈ Ioo 0 R₀, ζ + (t : ℂ) ∈ V)
    (hend : Tendsto (fun t : ℝ => f (ζ + (t : ℂ))) (𝓝[>] 0) (𝓝 a)) :
    ∃ R ∈ Ioo 0 R₀, ∀ r > 0,
      ∀ᶠ n in atTop, ∀ t ∈ Icc r R, dist (F n (ζ + (t : ℂ))) a < ε := by
  have hevent := hend.eventually (Metric.ball_mem_nhds a (half_pos hε))
  obtain ⟨s, hs, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let R := min (R₀ / 2) (s / 2)
  have hR : 0 < R := lt_min (half_pos hR₀) (half_pos hs)
  have hRR₀ : R < R₀ := (min_le_left _ _).trans_lt (half_lt_self hR₀)
  have hRs : R < s := (min_le_right _ _).trans_lt (half_lt_self hs)
  refine ⟨R, ⟨hR, hRR₀⟩, ?_⟩
  intro r hr
  apply eventually_close_on_radial_segment hconv
    (fun t ht => hrad t ⟨hr.trans_le ht.1, ht.2.trans_lt hRR₀⟩) hε
  intro t ht
  exact hsmall ⟨hr.trans_le ht.1, ht.2.trans_lt hRs⟩

end FunctionTheory
