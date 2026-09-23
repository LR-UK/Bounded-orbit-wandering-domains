/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Defs.Sequences

/-!
# Normal families

A family `𝓕` of functions `X → Y` is *normal* on a set `U ⊆ X` if every
sequence in `𝓕` has a subsequence converging locally uniformly on `U` (to
some limit `g : X → Y`). The domain `X` is a topological space and the
target `Y` a uniform space. The classical case has `X = ℂ` and `Y = ℂ`;
the spherical case has `Y = ℂ̂`; the dynamics of rational maps uses
`X = Y = ℂ̂`.

`IsNormalAt 𝓕 z` localizes the notion to a neighborhood of a point; it is
the membership predicate defining the Fatou set.

This file gives the abstract definitions and their monotonicity/transfer
lemmas; `Montel.lean` contains the classical Montel theorem (locally
uniformly bounded ⇒ normal).
-/

open Filter Topology

namespace RiemannDynamics

/-- A family `𝓕` of functions `X → Y` is *normal* on `U` if every sequence
drawn from `𝓕` has a subsequence that converges locally uniformly on `U` to
some limit function `g : X → Y`. -/
def IsNormal {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (𝓕 : Set (X → Y)) (U : Set X) : Prop :=
  ∀ seq : ℕ → 𝓕, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ g : X → Y,
      TendstoLocallyUniformlyOn (fun n => (seq (φ n) : X → Y)) g Filter.atTop U

/-- A family `𝓕` is *normal at a point* `z` if it is normal on some
neighborhood of `z`. -/
def IsNormalAt {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (𝓕 : Set (X → Y)) (z : X) : Prop :=
  ∃ U ∈ nhds z, IsNormal 𝓕 U

/-- A family `𝓕` of complex functions is *locally uniformly bounded* on `U` if
the family is uniformly bounded on every compact subset of `U`. -/
def LocallyUniformlyBounded (𝓕 : Set (ℂ → ℂ)) (U : Set ℂ) : Prop :=
  ∀ K, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝓕, ∀ z ∈ K, ‖f z‖ ≤ M

/-- Normality is antitone in the domain: a family normal on `U` is normal on
any subset of `U`. -/
theorem IsNormal.mono {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {𝓕 : Set (X → Y)} {U V : Set X} (hN : IsNormal 𝓕 U) (hVU : V ⊆ U) :
    IsNormal 𝓕 V := by
  intro seq
  obtain ⟨φ, hφ, g, hg⟩ := hN seq
  exact ⟨φ, hφ, g, hg.mono hVU⟩

/-- Normality passes to subfamilies. -/
theorem IsNormal.of_subfamily {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {𝓕 𝓖 : Set (X → Y)} {U : Set X} (hN : IsNormal 𝓕 U)
    (h𝓖 : 𝓖 ⊆ 𝓕) : IsNormal 𝓖 U := by
  intro seq
  obtain ⟨φ, hφ, g, hg⟩ := hN fun n => ⟨(seq n : X → Y), h𝓖 (seq n).2⟩
  exact ⟨φ, hφ, g, hg⟩

/-- The set of points at which a family is normal is open. -/
theorem isOpen_setOf_isNormalAt {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] (𝓕 : Set (X → Y)) :
    IsOpen {z : X | IsNormalAt 𝓕 z} := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨U, hU, hN⟩
  refine ⟨interior U, fun w hw => ?_, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hU⟩
  exact ⟨interior U, isOpen_interior.mem_nhds hw, hN.mono interior_subset⟩

/-- Normality on two open sets gives normality on their union: extract a
convergent subsequence on `U`, then a further one on `V`; the two limits
agree on the overlap by uniqueness of pointwise limits, so they glue. -/
theorem IsNormal.union {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    [T2Space Y] {𝓕 : Set (X → Y)} {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hNU : IsNormal 𝓕 U) (hNV : IsNormal 𝓕 V) :
    IsNormal 𝓕 (U ∪ V) := by
  classical
  intro seq
  obtain ⟨φ₁, hφ₁, g₁, hg₁⟩ := hNU seq
  obtain ⟨φ₂, hφ₂, g₂, hg₂⟩ := hNV fun n => seq (φ₁ n)
  -- the doubly-extracted subsequence still converges to `g₁` on `U`
  have hg₁' : TendstoLocallyUniformlyOn (fun n => (seq (φ₁ (φ₂ n)) : X → Y))
      g₁ atTop U := by
    intro u hu x hx
    obtain ⟨t, ht, hev⟩ := hg₁ u hu x hx
    exact ⟨t, ht, hφ₂.tendsto_atTop.eventually hev⟩
  -- the two limits agree on the overlap
  have hagree : ∀ x ∈ U ∩ V, g₁ x = g₂ x := fun x hx =>
    tendsto_nhds_unique (hg₁'.tendsto_at hx.1) (hg₂.tendsto_at hx.2)
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, U.piecewise g₁ g₂, ?_⟩
  have hgU : ∀ y ∈ U, U.piecewise g₁ g₂ y = g₁ y := fun y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hgV : ∀ y ∈ V, U.piecewise g₁ g₂ y = g₂ y := by
    intro y hy
    by_cases h : y ∈ U
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact hagree y ⟨h, hy⟩
    · exact Set.piecewise_eq_of_notMem _ _ _ h
  intro u hu x hx
  rcases hx with hxU | hxV
  · obtain ⟨t, ht, hev⟩ := hg₁' u hu x hxU
    refine ⟨t ∩ U, ?_, ?_⟩
    · obtain ⟨s', hs'o, hxs', hs't⟩ := mem_nhdsWithin.mp ht
      rw [mem_nhdsWithin]
      refine ⟨s' ∩ U, hs'o.inter hU, ⟨hxs', hxU⟩, ?_⟩
      rintro y ⟨⟨hys', hyU⟩, -⟩
      exact ⟨hs't ⟨hys', hyU⟩, hyU⟩
    · refine hev.mono fun n hn y hy => ?_
      rw [hgU y hy.2]
      exact hn y hy.1
  · obtain ⟨t, ht, hev⟩ := hg₂ u hu x hxV
    refine ⟨t ∩ V, ?_, ?_⟩
    · obtain ⟨s', hs'o, hxs', hs't⟩ := mem_nhdsWithin.mp ht
      rw [mem_nhdsWithin]
      refine ⟨s' ∩ V, hs'o.inter hV, ⟨hxs', hxV⟩, ?_⟩
      rintro y ⟨⟨hys', hyV⟩, -⟩
      exact ⟨hs't ⟨hys', hyV⟩, hyV⟩
    · refine hev.mono fun n hn y hy => ?_
      rw [hgV y hy.2]
      exact hn y hy.1

/-- On a compact space, a family that is normal at every point is normal on
the whole space: extract a finite subcover of normality neighborhoods and
glue by `IsNormal.union`. -/
theorem isNormal_univ_of_forall_isNormalAt {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [UniformSpace Y] [T2Space Y] {𝓕 : Set (X → Y)}
    (h : ∀ z : X, IsNormalAt 𝓕 z) : IsNormal 𝓕 Set.univ := by
  classical
  choose Uz hUz hNz using h
  have hVmem : ∀ z : X, z ∈ interior (Uz z) := fun z =>
    mem_interior_iff_mem_nhds.mpr (hUz z)
  have hVnorm : ∀ z : X, IsNormal 𝓕 (interior (Uz z)) := fun z =>
    (hNz z).mono interior_subset
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z => interior (Uz z)) (fun z => isOpen_interior)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hVmem x⟩)
  have key : ∀ s : Finset X, IsNormal 𝓕 (⋃ z ∈ s, interior (Uz z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro seq
      refine ⟨id, strictMono_id, (seq 0 : X → Y), ?_⟩
      intro u hu x hx
      obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hx
      exact absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      exact IsNormal.union isOpen_interior
        (isOpen_biUnion fun z _ => isOpen_interior) (hVnorm a) ih
  exact (key t).mono ht

/-- Normality transfers from chart readings to the original family: if the
pre-compositions with an open embedding `e` form a normal family on `U`,
the original family is normal on `e '' U`. The limit is pushed forward
through the local inverse of `e`. -/
theorem IsNormal.of_comp_isOpenEmbedding {X X' Y : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] [UniformSpace Y] {e : X' → X}
    (he : Topology.IsOpenEmbedding e) {𝓕 : Set (X → Y)} {U : Set X'}
    (hN : IsNormal ((fun F => F ∘ e) '' 𝓕) U) : IsNormal 𝓕 (e '' U) := by
  classical
  intro seq
  rcases U.eq_empty_or_nonempty with hUe | ⟨x'₀, hx'₀⟩
  · refine ⟨id, strictMono_id, (seq 0 : X → Y), ?_⟩
    intro u hu x hx
    rw [hUe, Set.image_empty] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨φ, hφ, g, hg⟩ :=
      hN fun n => ⟨(seq n : X → Y) ∘ e, (seq n : X → Y), (seq n).2, rfl⟩
    have hg' : TendstoLocallyUniformlyOn (fun n => (seq (φ n) : X → Y) ∘ e) g
        Filter.atTop U := hg
    have hinj : Function.Injective e := he.isEmbedding.injective
    -- a left inverse of `e`, defined globally via `Function.extend`
    obtain ⟨einv, heinv⟩ : ∃ einv : X → X', ∀ x' : X', einv (e x') = x' :=
      ⟨Function.extend e id fun _ => x'₀,
        fun x' => hinj.extend_apply id (fun _ => x'₀) x'⟩
    have hmaps : Set.MapsTo einv (e '' U) U := by
      rintro _ ⟨x', hx', rfl⟩
      rw [heinv x']
      exact hx'
    -- `einv` is continuous on `e '' U` because `e` maps `𝓝 x'` onto `𝓝 (e x')`
    have hcont : ContinuousOn einv (e '' U) := by
      rintro _ ⟨x', hx', rfl⟩
      have h1 : Filter.Tendsto einv (nhds (e x')) (nhds (einv (e x'))) := by
        rw [heinv x', ← he.map_nhds_eq x', Filter.tendsto_map'_iff]
        have h2 : einv ∘ e = id := funext heinv
        rw [h2]
        exact tendsto_id
      exact ContinuousAt.continuousWithinAt h1
    have hcomp := hg'.comp einv hmaps hcont
    refine ⟨φ, hφ, g ∘ einv, hcomp.congr fun n x hx => ?_⟩
    obtain ⟨x', hx', rfl⟩ := hx
    simp only [Function.comp_apply]
    rw [heinv x']

/-- A normal family of continuous maps on a compact metric space is
uniformly equicontinuous: a failure of uniform equicontinuity yields a
sequence of members and point pairs whose extracted uniform limit would be
both continuous and discontinuous. -/
theorem IsNormal.uniformEquicontinuous {X Y : Type*} [MetricSpace X]
    [CompactSpace X] [MetricSpace Y] {𝓕 : Set (X → Y)}
    (hN : IsNormal 𝓕 Set.univ) (hc : ∀ F ∈ 𝓕, Continuous F) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ F ∈ 𝓕, ∀ z w : X,
      dist z w < δ → dist (F z) (F w) < ε := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ε₀, hε₀, hbad⟩ := hcon
  -- select witnesses of failure at scale `1 / (n + 1)`
  have hsel : ∀ n : ℕ, ∃ F ∈ 𝓕, ∃ z w : X,
      dist z w < 1 / ((n : ℝ) + 1) ∧ ε₀ ≤ dist (F z) (F w) :=
    fun n => hbad (1 / ((n : ℝ) + 1)) (by positivity)
  choose F hF z w hzw hd using hsel
  obtain ⟨φ, hφ, g, hg⟩ := hN fun n => ⟨F n, hF n⟩
  -- on a compact space, locally uniform convergence is uniform
  have hunif : TendstoUniformly (fun n => F (φ n)) g atTop :=
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
      (tendstoLocallyUniformlyOn_univ.mp hg)
  -- the limit is (uniformly) continuous
  have hgc : Continuous g :=
    continuousOn_univ.mp <| (tendstoUniformlyOn_univ.mpr hunif).continuousOn
      (Frequently.of_forall fun n => (hc _ (hF (φ n))).continuousOn)
  have hgu : UniformContinuous g := CompactSpace.uniformContinuous_of_continuous hgc
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.uniformContinuous_iff.mp hgu (ε₀ / 2) (by positivity)
  -- pick an index where uniform closeness and small point separation both hold
  have h1 : ∀ᶠ n : ℕ in atTop, ∀ x : X, dist (g x) (F (φ n) x) < ε₀ / 4 :=
    Metric.tendstoUniformly_iff.mp hunif (ε₀ / 4) (by positivity)
  have h2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) < δ' :=
    (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 δ' hδ'pos
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  -- the selected points at index `φ n` are within `δ'` of each other
  have hδn : dist (z (φ n)) (w (φ n)) < δ' := by
    have hnle : n ≤ φ n := hφ.le_apply
    have hle : (1 : ℝ) / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnle 1)
    exact ((hzw (φ n)).trans_le hle).trans hn2
  -- contradiction with the failure of equicontinuity at index `φ n`
  have hzgz : dist (F (φ n) (z (φ n))) (g (z (φ n))) < ε₀ / 4 := by
    rw [dist_comm]; exact hn1 _
  have hwgw : dist (g (w (φ n))) (F (φ n) (w (φ n))) < ε₀ / 4 := hn1 _
  have hmid : dist (g (z (φ n))) (g (w (φ n))) < ε₀ / 2 := hδ' hδn
  have hlt : dist (F (φ n) (z (φ n))) (F (φ n) (w (φ n))) < ε₀ := by
    calc dist (F (φ n) (z (φ n))) (F (φ n) (w (φ n)))
        ≤ dist (F (φ n) (z (φ n))) (g (z (φ n))) + dist (g (z (φ n))) (g (w (φ n)))
          + dist (g (w (φ n))) (F (φ n) (w (φ n))) := dist_triangle4 _ _ _ _
      _ < ε₀ := by linarith
  exact absurd (hd (φ n)) (not_le.mpr hlt)

/-- A family that is normal at a point and consists of continuous maps is
equicontinuous at that point: a failure of equicontinuity at `p` yields a
sequence of members and points converging to `p` whose extracted locally
uniform limit would be both continuous and discontinuous at `p`. -/
theorem IsNormalAt.equicontinuousAt {X Y : Type*} [MetricSpace X]
    [MetricSpace Y] {𝓕 : Set (X → Y)} {p : X} (hN : IsNormalAt 𝓕 p)
    (hc : ∀ F ∈ 𝓕, Continuous F) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ F ∈ 𝓕, ∀ z : X,
      dist z p < δ → dist (F z) (F p) < ε := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ε₀, hε₀, hbad⟩ := hcon
  -- select witnesses of failure at scale `1 / (n + 1)`
  have hsel : ∀ n : ℕ, ∃ F ∈ 𝓕, ∃ z : X,
      dist z p < 1 / ((n : ℝ) + 1) ∧ ε₀ ≤ dist (F z) (F p) :=
    fun n => hbad (1 / ((n : ℝ) + 1)) (by positivity)
  choose F hF z hzp hd using hsel
  obtain ⟨U, hU, hNU⟩ := hN
  obtain ⟨φ, hφ, g, hg⟩ := hNU fun n => ⟨F n, hF n⟩
  have hpU : p ∈ U := mem_of_mem_nhds hU
  -- the extracted subsequence converges pointwise at `p`
  have htp : Tendsto (fun j => F (φ j) p) atTop (𝓝 (g p)) := hg.tendsto_at hpU
  -- the limit is continuous at `p`
  have hgc : ContinuousAt g p :=
    (hg.continuousOn (Frequently.of_forall fun n =>
      (hc _ (hF (φ n))).continuousOn)).continuousAt hU
  -- locally uniform closeness at scale `ε₀ / 4` on a neighborhood `t` of `p`
  obtain ⟨t, ht, e1⟩ := hg {q : Y × Y | dist q.1 q.2 < ε₀ / 4}
    (Metric.dist_mem_uniformity (by positivity)) p hpU
  rw [nhdsWithin_eq_nhds.mpr hU] at ht
  -- the witness points converge to `p` along the subsequence
  have hz : Tendsto (fun j => z (φ j)) atTop (𝓝 p) := by
    rw [Metric.tendsto_nhds]
    intro ε' hε'
    have h2 : ∀ᶠ j : ℕ in atTop, (1 : ℝ) / ((j : ℝ) + 1) < ε' :=
      (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 ε' hε'
    refine h2.mono fun j hj => ?_
    have hle : (1 : ℝ) / ((φ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hφ.le_apply 1)
    exact ((hzp (φ j)).trans_le hle).trans hj
  -- collect the remaining eventual facts and pick a common index
  have e2 : ∀ᶠ j : ℕ in atTop, dist (F (φ j) p) (g p) < ε₀ / 4 :=
    Metric.tendsto_nhds.mp htp (ε₀ / 4) (by positivity)
  have e3 : ∀ᶠ j : ℕ in atTop, z (φ j) ∈ t := hz.eventually_mem ht
  have e4 : ∀ᶠ j : ℕ in atTop, dist (g (z (φ j))) (g p) < ε₀ / 4 :=
    hz.eventually (Metric.tendsto_nhds.mp hgc.tendsto (ε₀ / 4) (by positivity))
  obtain ⟨j, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := (((e1.and e2).and e3).and e4).exists
  -- contradiction with the failure of equicontinuity at index `φ j`
  have hzg : dist (F (φ j) (z (φ j))) (g (z (φ j))) < ε₀ / 4 := by
    rw [dist_comm]; exact h1 _ h3
  have hpg : dist (g p) (F (φ j) p) < ε₀ / 4 := by
    rw [dist_comm]; exact h2
  have hlt : dist (F (φ j) (z (φ j))) (F (φ j) p) < ε₀ := by
    calc dist (F (φ j) (z (φ j))) (F (φ j) p)
        ≤ dist (F (φ j) (z (φ j))) (g (z (φ j))) + dist (g (z (φ j))) (g p)
          + dist (g p) (F (φ j) p) := dist_triangle4 _ _ _ _
      _ < ε₀ := by linarith
  exact absurd (hd (φ j)) (not_le.mpr hlt)

/-- Normality transfers along post-composition with a uniformly continuous
map: locally uniform convergence of a subsequence is preserved by `T ∘ ·`. -/
theorem IsNormal.comp_uniformContinuous {X Y Z : Type*} [TopologicalSpace X]
    [UniformSpace Y] [UniformSpace Z] {𝓕 : Set (X → Y)} {U : Set X}
    (hN : IsNormal 𝓕 U) {T : Y → Z} (hT : UniformContinuous T) :
    IsNormal ((fun f => fun z => T (f z)) '' 𝓕) U := by
  intro seq
  choose f hf hfe using fun n => (seq n).2
  obtain ⟨φ, hφ, g, hg⟩ := hN fun n => ⟨f n, hf n⟩
  refine ⟨φ, hφ, fun z => T (g z), ?_⟩
  exact (hT.comp_tendstoLocallyUniformlyOn hg).congr
    fun n z _ => congrFun (hfe (φ n)) z

/-- Normality only depends on the restrictions of the family members to `U`:
if every member of `𝓖` agrees on `U` with some member of a normal family
`𝓕`, then `𝓖` is normal. -/
theorem IsNormal.of_forall_exists_eqOn {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {𝓕 𝓖 : Set (X → Y)} {U : Set X} (hN : IsNormal 𝓕 U)
    (h : ∀ g ∈ 𝓖, ∃ f ∈ 𝓕, Set.EqOn f g U) :
    IsNormal 𝓖 U := by
  intro seq
  choose f hf hfe using fun n => h (seq n) (seq n).2
  obtain ⟨φ, hφ, g, hg⟩ := hN fun n => ⟨f n, hf n⟩
  exact ⟨φ, hφ, g, hg.congr fun n => hfe (φ n)⟩

end RiemannDynamics
