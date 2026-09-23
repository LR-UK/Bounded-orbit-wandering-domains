import LocalPunctures
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.LocalAtTarget

open Set Filter Topology Metric
open scoped Topology

namespace AreaDeficit

/-- Vanishing derivative on a neighbourhood makes an analytic germ constant. -/
theorem analytic_eventuallyConst_of_deriv_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hd : ∀ᶠ z in 𝓝 x, deriv f z = 0) :
    EventuallyConst f (𝓝 x) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hd)
  obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball x r).isPreconnected
    (fun z hz => (hball hz).1.differentiableAt.differentiableWithinAt)
    (fun z hz => (hball hz).2)
  apply eventuallyConst_iff_exists_eventuallyEq.mpr
  refine ⟨c, ?_⟩
  filter_upwards [ball_mem_nhds x hr] with z hz using hc z hz

/-- Only finitely many critical points occur in a compact set on which
the holomorphic function has no constant germ. -/
theorem finite_local_critical_points {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ x ∈ K, ¬EventuallyConst f (𝓝 x)) :
    (K ∩ {z | deriv f z = 0}).Finite := by
  have hd : {z | deriv f z ≠ 0} ∈ codiscreteWithin K := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro x hx
    have he := (hf x hx).deriv.eventually_eq_zero_or_eventually_ne_zero
    have hne := he.resolve_left (fun h => hn x hx
      (analytic_eventuallyConst_of_deriv_zero (hf x hx) h))
    exact mem_of_superset hne subset_union_left
  simpa only [sdiff_eq, compl_ofPred, not_not] using hK.finite_sdiff_of_mem_codiscreteWithin hd

theorem finite_local_critical_values {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ x ∈ K, ¬EventuallyConst f (𝓝 x)) :
    (f '' (K ∩ {z | deriv f z = 0})).Finite :=
  (finite_local_critical_points hK hf hn).image f

/-- A subtype projection is a local homeomorphism at interior points,
even when the subtype is a closed compact neighbourhood. -/
theorem subtype_localHomeomorph_interior {X : Type*} [TopologicalSpace X]
    (K : Set X) :
    IsLocalHomeomorphOn ((↑) : K → X) ((↑) ⁻¹' interior K) := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro x hx
  let U : Set K := (↑) ⁻¹' interior K
  refine ⟨U, (isOpen_interior.preimage continuous_subtype_val).mem_nhds hx, ?_⟩
  refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
  have he : range (U.domRestrict ((↑) : K → X)) = interior K := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hz
      exact ⟨⟨⟨z, interior_subset hz⟩, hz⟩, rfl⟩
  rw [he]
  exact isOpen_interior

/-- A compact restriction of a locally analytic function is a covering
over any target set whose fibres avoid the boundary and critical points.
This is an actual topological covering assertion, not covering data
assumed for a later estimate. -/
theorem compact_analytic_covering {f : ℂ → ℂ} {K S : Set ℂ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hint : ∀ z ∈ K, f z ∈ S → z ∈ interior K)
    (hreg : ∀ z ∈ K, f z ∈ S → deriv f z ≠ 0) :
    IsCoveringMapOn (fun z : K => f z) S := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hf.continuousOn.domRestrict
  have hl : IsLocalHomeomorphOn f (K ∩ f ⁻¹' S) := by
    intro z hz
    let hd := (hf z hz.1).hasStrictDerivAt.hasStrictFDerivAt_equiv
      (hreg z hz.1 hz.2)
    exact ⟨hd.toOpenPartialHomeomorph f, hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  exact hl.comp ((subtype_localHomeomorph_interior K).mono
    (fun z hz => hint z z.2 hz)) (fun z hz => ⟨z.2, hz⟩)

/-- A locally nonconstant holomorphic germ admits a compact disc chart
whose restriction is a covering after deleting its critical values.
The target disc is contained in the image, so the covering is surjective
there. The map only needs to be analytic near the chosen point. -/
theorem exists_local_disc_covering {f : ℂ → ℂ} {V : Set ℂ} {x : ℂ}
    (hV : IsOpen V) (hx : x ∈ V) (hf : AnalyticAt ℂ f x)
    (hn : ¬EventuallyConst f (𝓝 x)) :
    ∃ r > 0, ∃ s > 0,
      closedBall x r ⊆ V ∧ AnalyticOnNhd ℂ f (closedBall x r) ∧
      ball (f x) s ⊆ f '' closedBall x r ∧
      Disjoint (ball (f x) s) (f '' sphere x r) ∧
      IsCoveringMapOn (fun z : closedBall x r => f z)
        (ball (f x) s \ f '' (closedBall x r ∩ {z | deriv f z = 0})) := by
  have hne : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
    refine (hf.eventually_eq_or_eventually_ne (f := f)
      (g := fun _ => f x) analyticAt_const).resolve_left ?_
    intro he
    exact hn (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨f x, he⟩)
  have hnear : ∀ᶠ z in 𝓝 x, z ∈ V ∧ AnalyticAt ℂ f z ∧
      (z ≠ x → f z ≠ f x) := by
    filter_upwards [hV.mem_nhds hx, hf.eventually_analyticAt,
      eventually_nhdsWithin_iff.mp hne] with z hz ha he
    exact ⟨hz, ha, he⟩
  obtain ⟨r, hr, hb⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  have hKV : closedBall x r ⊆ V := fun z hz => (hb hz).1
  have hfa : AnalyticOnNhd ℂ f (closedBall x r) := fun z hz => (hb hz).2.1
  have hbd : f x ∉ f '' sphere x r := by
    rintro ⟨z, hz, he⟩
    exact (hb (sphere_subset_closedBall hz)).2.2
      (ne_of_mem_sphere hz hr.ne') he
  have hc : IsClosed (f '' sphere x r) :=
    ((isCompact_sphere x r).image_of_continuousOn
      (hfa.continuousOn.mono sphere_subset_closedBall)).isClosed
  have hop : 𝓝 (f x) ≤ map f (𝓝 x) :=
    hf.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (fun he => hn (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨f x, he⟩))
  have him : f '' closedBall x r ∈ 𝓝 (f x) :=
    hop (image_mem_map (closedBall_mem_nhds x hr))
  obtain ⟨s, hs, hsB⟩ := Metric.mem_nhds_iff.mp
    (inter_mem him (hc.isOpen_compl.mem_nhds hbd))
  refine ⟨r, hr, s, hs, hKV, hfa, fun z hz => (hsB hz).1, ?_, ?_⟩
  · exact disjoint_left.mpr (fun z hz he => (hsB hz).2 he)
  · apply compact_analytic_covering (isCompact_closedBall x r) hfa
    · intro z hz hzs
      rw [interior_closedBall x hr.ne']
      have hzbd : z ∉ sphere x r := fun he => (hsB hzs.1).2 ⟨z, he, rfl⟩
      exact lt_of_le_of_ne hz (fun he => hzbd he)
    · intro z hz hzs hd
      exact hzs.2 ⟨z, ⟨hz, hd⟩, rfl⟩

end AreaDeficit
