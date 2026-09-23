import Counterexamples.TopologistsSineCurve
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions

/-! # A compact topologist's sine curve

We reuse Mathlib's sine-curve construction by Daniele Bolla and David Loeffler.
The compact truncation will be used in the continuum from Figure 5.
-/

open Set Filter Topology Real Metric

namespace EremenkosConjecture.SineContinuum

open TopologistsSineCurve

noncomputable def graph : Set (ℝ × ℝ) :=
  (fun x : ℝ => (x, sin x⁻¹)) '' Ioc 0 1

noncomputable def base : Set (ℝ × ℝ) := closure graph

theorem base_subset_T : base ⊆ T := by
  rw [base, ← closure_S]
  exact closure_mono (image_mono Ioc_subset_Ioi_self)

theorem mem_base_iff {p : ℝ × ℝ} : p ∈ base ↔ p ∈ T ∧ p.1 ≤ 1 := by
  constructor
  · intro hp
    refine ⟨base_subset_T hp, ?_⟩
    apply closure_minimal (t := {q : ℝ × ℝ | q.1 ≤ 1}) ?_
      (isClosed_le continuous_fst continuous_const) hp
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · rintro ⟨hp, hle⟩
    rcases hp with hp | ⟨y, hy, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hp
      exact subset_closure ⟨x, ⟨hx, hle⟩, rfl⟩
    · have hevent : ∀ᶠ n in atTop, xSeq y n ≤ 1 :=
        (xSeq_tendsto y).eventually_le_const zero_lt_one
      apply isClosed_closure.mem_of_tendsto
        ((xSeq_tendsto y).prodMk_nhds (tendsto_const_nhds (x := y)))
      filter_upwards [hevent] with n hn
      apply subset_closure
      refine ⟨xSeq y n, ⟨xSeq_pos y n, hn⟩, ?_⟩
      simp only [sin_inv_xSeq hy]

theorem base_coordinates {p : ℝ × ℝ} (hp : p ∈ base) :
    p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨hT, hle⟩ := mem_base_iff.mp hp
  rcases hT with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · exact ⟨⟨le_of_lt hx, hle⟩, sin_mem_Icc _⟩
  · exact ⟨⟨le_rfl, zero_le_one⟩, hy⟩

theorem base_norm_le {p : ℝ × ℝ} (hp : p ∈ base) : ‖p‖ ≤ 1 := by
  obtain ⟨hx, hy⟩ := base_coordinates hp
  rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  exact ⟨abs_le.mpr ⟨by linarith [hx.1], hx.2⟩, abs_le.mpr hy⟩

theorem isCompact_base : IsCompact base :=
  (isCompact_closedBall (0 : ℝ × ℝ) 1).of_isClosed_subset isClosed_closure
    (fun _ hp => by simpa only [mem_closedBall, dist_zero_right] using base_norm_le hp)

theorem isConnected_base : IsConnected base := by
  apply IsConnected.closure
  apply (isConnected_Ioc (show (0 : ℝ) < 1 by norm_num)).image
  exact continuousOn_id.prodMk (continuous_sin.continuousOn.comp
    (continuousOn_id.inv₀ (fun x hx => ne_of_gt hx.1)) (mapsTo_univ _ _))

theorem vertical_mem_base {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : (0, y) ∈ base :=
  mem_base_iff.mpr ⟨Or.inr ⟨y, hy, rfl⟩, zero_le_one⟩

theorem right_mem_base : (1, sin 1) ∈ base := by
  apply subset_closure
  exact ⟨1, ⟨zero_lt_one, le_rfl⟩, by simp⟩

theorem base_snd_of_pos {p : ℝ × ℝ} (hp : p ∈ base) (hx : 0 < p.1) :
    p.2 = sin p.1⁻¹ := by
  rcases base_subset_T hp with ⟨x, _, rfl⟩ | ⟨y, _, heq⟩
  · rfl
  · have : p.1 = 0 := congrArg Prod.fst heq.symm
    exact (hx.ne' this).elim

theorem not_joinedIn_T {p q : ℝ × ℝ} (hp : p ∈ T) (hp0 : p.1 = 0)
    (hq : q ∈ T) (hq0 : 0 < q.1) : ¬ JoinedIn T p q := by
  intro hjoin
  have hS : IsPathConnected S := by
    apply ((convex_Ioi (0 : ℝ)).isPathConnected nonempty_Ioi).image'
    exact continuousOn_id.prodMk (continuous_sin.continuousOn.comp
      (continuousOn_id.inv₀ (fun x hx => ne_of_gt hx)) (mapsTo_univ _ _))
  have hZ : IsPathConnected Z :=
    (convex_Icc (-1 : ℝ) 1).isPathConnected (nonempty_Icc.mpr (by norm_num)) |>.image
      (continuous_const.prodMk continuous_id)
  have hpZ : p ∈ Z := by
    rcases hp with ⟨x, hx, heq⟩ | h
    · have : x = 0 := (congrArg Prod.fst heq).trans hp0
      exact (hx.ne' this).elim
    · exact h
  have hqS : q ∈ S := by
    rcases hq with h | ⟨y, _, heq⟩
    · exact h
    · have : q.1 = 0 := congrArg Prod.fst heq.symm
      exact (hq0.ne' this).elim
  apply not_isPathConnected_T
  refine ⟨p, hp, ?_⟩
  intro r hr
  rcases hr with hr | hr
  · exact hjoin.trans ((hS.joinedIn q hqS r hr).mono subset_union_left)
  · exact (hZ.joinedIn p hpZ r hr).mono subset_union_right

end EremenkosConjecture.SineContinuum
