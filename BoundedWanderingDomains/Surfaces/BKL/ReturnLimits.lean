/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousOn
import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Maps.Basic
import Mathlib.Data.Set.Function
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import BoundedWanderingDomains.Surfaces.FiniteFibers
import BoundedWanderingDomains.Surfaces.HolomorphicLifting
import BoundedWanderingDomains.Surfaces.LocalPunctures
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import BoundedWanderingDomains.Surfaces.FinitePunctureTopology
import Mathlib.Topology.Separation.Regular

section

/-! # Constant limits of commuting return maps

These elementary topological observations are intended for the BKL extension.
They do not by themselves prove the geometric or dynamical extension.
-/

open Filter Function Topology

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- A continuous map commuting with a family that has the same limit at a point
and its image fixes that limit point. -/
theorem fixed_of_commuting_tendsto {F : ℕ → X → X} {g : X → X} {a : X}
    (hg : ContinuousAt g a)
    (hFa : Tendsto (fun n => F n a) atTop (𝓝 a))
    (hFga : Tendsto (fun n => F n (g a)) atTop (𝓝 a))
    (hcomm : ∀ n, g (F n a) = F n (g a)) : g a = a := by
  apply tendsto_nhds_unique (hg.tendsto.comp hFa)
  exact hFga.congr' (Eventually.of_forall fun n => (hcomm n).symm)

/-- A commuting family converging to the same constant on a neighborhood of that
constant eventually fixes it. -/
theorem eventually_fixed_of_commuting_tendsto {F : ℕ → X → X} {a : X}
    {U : Set X} (hU : U ∈ 𝓝 a)
    (hF : ∀ x ∈ U, Tendsto (fun n => F n x) atTop (𝓝 a))
    (hc : ∀ n, ContinuousAt (F n) a)
    (hcomm : ∀ m n, Function.Commute (F m) (F n)) :
    ∀ᶠ n in atTop, F n a = a := by
  have ha : a ∈ U := mem_of_mem_nhds hU
  have hnear : ∀ᶠ n in atTop, F n a ∈ U := (hF a ha).eventually hU
  exact hnear.mono fun n hn =>
    fixed_of_commuting_tendsto (hc n) (hF a ha) (hF (F n a) hn)
      (fun m => hcomm n m a)

/-- In particular, a family of return iterates with a constant neighborhood
limit eventually consists of iterates fixing that limit. -/
theorem eventually_iterate_fixed_of_tendsto {f : X → X} {times : ℕ → ℕ} {a : X}
    {U : Set X} (hU : U ∈ 𝓝 a)
    (hF : ∀ x ∈ U, Tendsto (fun n => (f^[times n]) x) atTop (𝓝 a))
    (hc : ∀ n, ContinuousAt (f^[times n]) a) :
    ∀ᶠ n in atTop, (f^[times n]) a = a := by
  apply eventually_fixed_of_commuting_tendsto hU hF hc
  intro m n x
  rw [← iterate_add_apply, ← iterate_add_apply, Nat.add_comm]

end SurfaceDynamics.BKL

end

section

/-! # Constant iterate limits and return maps

Factoring through an earlier iterate transfers uniform convergence on a compact
neighborhood to uniform convergence of return maps near the limit point.
The observation map allows convergence to be tested in a compactification.
-/

open Set Function Filter Topology

namespace SurfaceDynamics.BKL

variable {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [UniformSpace Y]

/-- A constant limit at a point already attained by an iterate gives uniform
return convergence on a neighborhood of that limit point. -/
theorem exists_uniform_return_neighborhood
    {f : X → X} (hfo : IsOpenMap f) {j : X → Y}
    {times : ℕ → ℕ} (ht : StrictMono times) {a y : X} {N : ℕ}
    {U : Set X} (hU : IsOpen U) (hy : y ∈ U) (hya : (f^[N]) y = a)
    (hlim : TendstoLocallyUniformlyOn
      (fun n x => j ((f^[times n]) x)) (fun _ => j a) atTop U) :
    ∃ V : Set X, IsOpen V ∧ a ∈ V ∧
      TendstoUniformlyOn (fun n x => j ((f^[times n - N]) x))
        (fun _ => j a) atTop V := by
  obtain ⟨K, hK, hyK, hKU⟩ := exists_compact_subset hU hy
  let V := (f^[N]) '' interior K
  have hopen : ∀ m : ℕ, IsOpenMap (f^[m]) := by
    intro m
    induction m with
    | zero => exact IsOpenMap.id
    | succ m ih =>
      rw [iterate_succ]
      exact ih.comp hfo
  have hV : IsOpen V := hopen N _ isOpen_interior
  have huni := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlim.mono hKU)
  refine ⟨V, hV, ⟨y, hyK, hya⟩, ?_⟩
  intro v hv
  filter_upwards [huni v hv, eventually_ge_atTop N] with n hn hNn
  have hNt : N ≤ times n := hNn.trans (ht.id_le n)
  rintro z ⟨w, hw, rfl⟩
  have he : (f^[times n - N]) ((f^[N]) w) = (f^[times n]) w := by
    rw [← iterate_add_apply, Nat.sub_add_cancel hNt]
  simpa only [he] using hn w (interior_subset hw)

/-- If the observation is an embedding, the return maps eventually fix the
constant limit point. -/
theorem eventually_return_fixed_of_constant_limit [T2Space X]
    {f : X → X} (hf : Continuous f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsEmbedding j)
    {times : ℕ → ℕ} (ht : StrictMono times) {a y : X} {N : ℕ}
    {U : Set X} (hU : IsOpen U) (hy : y ∈ U) (hya : (f^[N]) y = a)
    (hlim : TendstoLocallyUniformlyOn
      (fun n x => j ((f^[times n]) x)) (fun _ => j a) atTop U) :
    ∀ᶠ n in atTop, (f^[times n - N]) a = a := by
  obtain ⟨V, hVo, haV, hV⟩ := exists_uniform_return_neighborhood hfo ht hU hy hya hlim
  apply eventually_iterate_fixed_of_tendsto (hVo.mem_nhds haV)
  · intro x hx
    exact hj.tendsto_nhds_iff.mpr (hV.tendsto_at hx)
  · intro n
    exact (hf.iterate (times n - N)).continuousAt

/-- Such an attained constant limit is periodic, with a positive return time. -/
theorem exists_positive_return_of_constant_limit [T2Space X]
    {f : X → X} (hf : Continuous f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsEmbedding j)
    {times : ℕ → ℕ} (ht : StrictMono times) {a y : X} {N : ℕ}
    {U : Set X} (hU : IsOpen U) (hy : y ∈ U) (hya : (f^[N]) y = a)
    (hlim : TendstoLocallyUniformlyOn
      (fun n x => j ((f^[times n]) x)) (fun _ => j a) atTop U) :
    ∃ k : ℕ, 0 < k ∧ (f^[k]) a = a := by
  have hfix := eventually_return_fixed_of_constant_limit hf hfo hj ht hU hy hya hlim
  obtain ⟨n, hn, hNn⟩ := (hfix.and (eventually_ge_atTop (N + 1))).exists
  exact ⟨times n - N, Nat.sub_pos_of_lt
    ((Nat.lt_of_succ_le hNn).trans_le (ht.id_le n)), hn⟩

/-- The return maps fix the limit point and send one fixed neighborhood into
any prescribed smaller neighborhood. This prepares the analytic contraction
argument without assuming an attracting-cycle classification. -/
theorem exists_shrinking_return_neighborhood [T2Space X]
    {f : X → X} (hf : Continuous f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsOpenEmbedding j)
    {times : ℕ → ℕ} (ht : StrictMono times) {a y : X} {N : ℕ}
    {U : Set X} (hU : IsOpen U) (hy : y ∈ U) (hya : (f^[N]) y = a)
    (hlim : TendstoLocallyUniformlyOn
      (fun n x => j ((f^[times n]) x)) (fun _ => j a) atTop U) :
    ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∀ W : Set X, IsOpen W → a ∈ W →
      ∃ k : ℕ, 0 < k ∧ (f^[k]) a = a ∧ MapsTo (f^[k]) V W := by
  obtain ⟨V, hVo, haV, hV⟩ := exists_uniform_return_neighborhood hfo ht hU hy hya hlim
  have hfix := eventually_return_fixed_of_constant_limit hf hfo hj.isEmbedding ht hU hy hya hlim
  refine ⟨V, hVo, haV, ?_⟩
  intro W hWo haW
  have htarget : j '' W ∈ 𝓝 (j a) := (hj.isOpenMap W hWo).mem_nhds ⟨a, haW, rfl⟩
  have hmaps : ∀ᶠ n in atTop, ∀ x ∈ V, j ((f^[times n - N]) x) ∈ j '' W :=
    eventually_prod_principal_iff.mp ((tendsto_prod_principal_iff.mpr hV).eventually htarget)
  obtain ⟨n, hn, hmap, hNn⟩ :=
    (hfix.and (hmaps.and (eventually_ge_atTop (N + 1)))).exists
  refine ⟨times n - N, Nat.sub_pos_of_lt
    ((Nat.lt_of_succ_le hNn).trans_le (ht.id_le n)), hn, ?_⟩
  intro x hx
  obtain ⟨w, hw, he⟩ := hmap x hx
  exact hj.injective he ▸ hw

end SurfaceDynamics.BKL

end

section

/-! # Reducing a backward orbit to finitely many fibres

An invariant neighborhood of a periodic point with isolated short-return fibres
contains no other point in its backward orbit. Pulling this neighborhood back
reduces all hitting times to a fixed finite collection of fibres.
-/

open Set Function

namespace SurfaceDynamics.BKL

variable {X : Type*} {f : X → X} {a : X}

/-- A return-invariant set with isolated short-return fibres contains no other
point eventually mapped to the distinguished point. -/
theorem eq_of_iterate_eq_of_return_invariant {U : Set X} {k : ℕ}
    (hk : 0 < k) (hU : MapsTo (f^[k]) U U)
    (hfib : ∀ j ≤ k, ∀ x ∈ U, (f^[j]) x = a → x = a)
    {x : X} (hx : x ∈ U) {n : ℕ} (hn : (f^[n]) x = a) : x = a := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hnk : n ≤ k
    · exact hfib n hnk x hx hn
    · have hsmall : n - k < n := by omega
      have hsum : n - k + k = n := by omega
      have htail : (f^[n - k]) ((f^[k]) x) = a := by
        rw [← iterate_add_apply, hsum]
        exact hn
      have hreturn : (f^[k]) x = a := ih (n - k) hsmall (hU hx) htail
      exact hfib k le_rfl x hx hreturn

/-- Once an orbit has entered the preceding invariant set, a later hit of the
distinguished point forces the entry point itself to be that point. -/
theorem iterate_entry_eq_of_eventual_hit {U : Set X} {k N n : ℕ}
    (hk : 0 < k) (hU : MapsTo (f^[k]) U U)
    (hfib : ∀ j ≤ k, ∀ x ∈ U, (f^[j]) x = a → x = a)
    {x : X} (hx : (f^[N]) x ∈ U) (hNn : N ≤ n)
    (hn : (f^[n]) x = a) : (f^[N]) x = a := by
  apply eq_of_iterate_eq_of_return_invariant hk hU hfib hx (n := n - N)
  rw [← iterate_add_apply, Nat.sub_add_cancel hNn]
  exact hn

/-- On a set mapped into the invariant neighborhood in `N` steps, every
backward-orbit point belongs to one of the first `N + 1` fibres. -/
theorem backwardOrbit_subset_finite_fibres {U V : Set X} {k N : ℕ}
    (hk : 0 < k) (hU : MapsTo (f^[k]) U U)
    (hfib : ∀ j ≤ k, ∀ x ∈ U, (f^[j]) x = a → x = a)
    (hV : MapsTo (f^[N]) V U) :
    V ∩ {x | ∃ n : ℕ, (f^[n]) x = a} ⊆
      {x | ∃ n ≤ N, (f^[n]) x = a} := by
  rintro x ⟨hx, n, hn⟩
  by_cases hNn : N ≤ n
  · exact ⟨N, le_rfl, iterate_entry_eq_of_eventual_hit hk hU hfib (hV hx) hNn hn⟩
  · exact ⟨n, by omega, hn⟩

end SurfaceDynamics.BKL

end

section

/-! # Isolating backward orbits near a holomorphic return

Schwarz's lemma makes every smaller concentric disc invariant. Choosing such
a disc to isolate the finitely many short-return fibres then isolates the
entire backward orbit.
-/

open Set Function Filter Metric Topology

namespace SurfaceDynamics.BKL

/-- A holomorphic disc self-map fixing the centre preserves every smaller
concentric disc. -/
theorem mapsTo_smaller_ball_of_holomorphic_return
    {g : ℂ → ℂ} {a : ℂ} {R r : ℝ} (hR : 0 < R) (hr : r ≤ R)
    (hg : DifferentiableOn ℂ g (ball a R)) (ha : g a = a)
    (hm : MapsTo g (ball a R) (ball a R)) :
    MapsTo g (ball a r) (ball a r) := by
  intro z hz
  have hzR := ball_subset_ball hr hz
  have hclosed : MapsTo g (ball a R) (closedBall (g a) R) := by
    rw [ha]
    exact hm.mono_right ball_subset_closedBall
  have hd := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hclosed hzR
  rw [ha, div_self (ne_of_gt hR), one_mul] at hd
  exact hd.trans_lt hz

/-- Finitely many local implications can be imposed on a common
neighbourhood. -/
theorem eventually_all_le {X : Type*} {l : Filter X} {P : ℕ → X → Prop}
    {k : ℕ} (h : ∀ j ≤ k, ∀ᶠ x in l, P j x) :
    ∀ᶠ x in l, ∀ j ≤ k, P j x := by
  induction k with
  | zero =>
      filter_upwards [h 0 le_rfl] with x hx j hj
      simpa only [Nat.le_zero.mp hj] using hx
  | succ k ih =>
      filter_upwards [ih (fun j hj => h j (hj.trans (Nat.le_succ k))),
        h (k + 1) le_rfl] with x hx hxlast j hj
      by_cases hjk : j ≤ k
      · exact hx j hjk
      · have he : j = k + 1 := by omega
        simpa only [he] using hxlast

/-- An invariant holomorphic return and isolated short-return fibres isolate
all preimages of the centre, irrespective of the hitting time. -/
theorem exists_ball_isolating_backwardOrbit_of_holomorphic_return
    {f : ℂ → ℂ} {a : ℂ} {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ (f^[k]) (ball a R)) (ha : (f^[k]) a = a)
    (hm : MapsTo (f^[k]) (ball a R) (ball a R))
    (hfib : ∀ j ≤ k, ∀ᶠ z in 𝓝 a, (f^[j]) z = a → z = a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ∀ z ∈ ball a r, ∀ n : ℕ, (f^[n]) z = a → z = a := by
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (eventually_all_le hfib)
  let r := min R ε
  have hr : 0 < r := lt_min hR hε
  have hrR : r ≤ R := min_le_left _ _
  refine ⟨r, hr, hrR, ?_⟩
  intro z hz n hn
  apply eq_of_iterate_eq_of_return_invariant hk
    (mapsTo_smaller_ball_of_holomorphic_return hR hrR hg ha hm) ?_ hz hn
  intro j hj w hw
  exact he (ball_subset_ball (min_le_right R ε) hw) j hj

end SurfaceDynamics.BKL

end

section

/-! # Backward-orbit isolation in a coordinate chart -/

open Set Function Filter Metric Topology

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X]

/-- The planar Schwarz argument isolates backward orbits on an arbitrary
space once the return map is expressed in a complex chart. -/
theorem exists_neighborhood_isolating_backwardOrbit_of_chart_return
    {f : X → X} {a : X} {k : ℕ} (hk : 0 < k)
    (e : OpenPartialHomeomorph X ℂ) (hae : a ∈ e.source)
    {R : ℝ} (hR : 0 < R) (hball : ball (e a) R ⊆ e.target)
    (hg : DifferentiableOn ℂ (e ∘ (f^[k]) ∘ e.symm) (ball (e a) R))
    (ha : (f^[k]) a = a)
    (hm : MapsTo (f^[k]) (e.symm '' ball (e a) R) (e.symm '' ball (e a) R))
    (hfib : ∀ j ≤ k, ∀ᶠ z in 𝓝 a, (f^[j]) z = a → z = a) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧
      ∀ z ∈ U, ∀ n : ℕ, (f^[n]) z = a → z = a := by
  let g := e ∘ (f^[k]) ∘ e.symm
  have hga : g (e a) = e a := by simp only [g, comp_apply, e.left_inv hae, ha]
  have hgm : MapsTo g (ball (e a) R) (ball (e a) R) := by
    intro z hz
    obtain ⟨w, hw, he⟩ := hm (mem_image_of_mem e.symm hz)
    change e ((f^[k]) (e.symm z)) ∈ ball (e a) R
    rw [← he, e.right_inv (hball hw)]
    exact hw
  have hshort := eventually_all_le hfib
  have hc : Tendsto e.symm (𝓝 (e a)) (𝓝 a) := by
    simpa only [e.left_inv hae] using (e.continuousAt_symm (e.map_source hae)).tendsto
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp (hc.eventually hshort)
  let r := min R ε
  have hr : 0 < r := lt_min hR hε
  have hrR : r ≤ R := min_le_left _ _
  let U := e.symm '' ball (e a) r
  have hU : IsOpen U := e.isOpen_image_symm_of_subset_target isOpen_ball
    ((ball_subset_ball hrR).trans hball)
  have haU : a ∈ U := ⟨e a, mem_ball_self hr, e.left_inv hae⟩
  have hmU : MapsTo (f^[k]) U U := by
    rintro z ⟨w, hw, rfl⟩
    have hgw := mapsTo_smaller_ball_of_holomorphic_return hR hrR hg hga hgm hw
    refine ⟨g w, hgw, ?_⟩
    have hfs : (f^[k]) (e.symm w) ∈ e.source := by
      obtain ⟨v, hv, he⟩ := hm (mem_image_of_mem e.symm (ball_subset_ball hrR hw))
      exact he ▸ e.map_target (hball hv)
    exact e.left_inv hfs
  refine ⟨U, hU, haU, ?_⟩
  intro z hz n hn
  apply eq_of_iterate_eq_of_return_invariant hk hmU ?_ hz hn
  intro j hj w hw
  obtain ⟨v, hv, rfl⟩ := hw
  exact heps (ball_subset_ball (min_le_right R ε) hv) j hj

end SurfaceDynamics.BKL

end

section

/-! # Backward isolation of attained constant limits on surfaces -/

open Set Function Filter Metric Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

/-- A closed discrete set has at most its centre in a sufficiently small
neighbourhood of any given point. -/
theorem eventually_eq_of_mem_closed_discrete
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hSc : IsClosed S) (hSd : IsDiscrete S) (a : X) :
    ∀ᶠ z in 𝓝 a, z ∈ S → z = a := by
  by_cases ha : a ∈ S
  · obtain ⟨V, hVo, hV⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hSd a ha
    have haV : a ∈ V := (hV.symm ▸ mem_singleton a).1
    filter_upwards [hVo.mem_nhds haV] with z hz hzs
    have hz' : z ∈ ({a} : Set X) := hV ▸ (show z ∈ V ∩ S from ⟨hz, hzs⟩)
    exact hz'
  · filter_upwards [hSc.isOpen_compl.mem_nhds ha] with z hz hzs
    exact False.elim (hz hzs)

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [UniformSpace Y]

/-- An attained constant iterate limit of an open holomorphic surface map
has a neighbourhood containing no other point in its backward orbit. -/
theorem exists_neighborhood_isolating_backwardOrbit_of_constant_limit
    {f : X → X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsOpenEmbedding j)
    {times : ℕ → ℕ} (ht : StrictMono times) {a y : X} {N : ℕ}
    {U : Set X} (hU : IsOpen U) (hy : y ∈ U) (hya : (f^[N]) y = a)
    (hlim : TendstoLocallyUniformlyOn
      (fun n x => j ((f^[times n]) x)) (fun _ => j a) atTop U) :
    ∃ W : Set X, IsOpen W ∧ a ∈ W ∧
      ∀ z ∈ W, ∀ n : ℕ, (f^[n]) z = a → z = a := by
  obtain ⟨V, hVo, haV, hV⟩ :=
    exists_shrinking_return_neighborhood hf.continuous hfo hj ht hU hy hya hlim
  let e := chartAt ℂ a
  have hae : a ∈ e.source := mem_chart_source ℂ a
  have hca : e a ∈ e.target := e.map_source hae
  have hnbh : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e a) := by
    apply inter_mem (e.open_target.mem_nhds hca)
    apply (e.continuousAt_symm hca).preimage_mem_nhds
    simpa only [e.left_inv hae] using hVo.mem_nhds haV
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnbh
  let B := e.symm '' ball (e a) R
  have htarget : ball (e a) R ⊆ e.target := hball.trans inter_subset_left
  have hBV : B ⊆ V := by
    rintro x ⟨z, hz, rfl⟩
    exact (hball hz).2
  have hBo : IsOpen B := e.isOpen_image_symm_of_subset_target isOpen_ball htarget
  have haB : a ∈ B := ⟨e a, mem_ball_self hR, e.left_inv hae⟩
  obtain ⟨k, hk, hka, hmap⟩ := hV B hBo haB
  have hm : MapsTo (f^[k]) B B := hmap.mono_left hBV
  have hiter : ∀ n : ℕ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f^[n]) := by
    intro n
    induction n with
    | zero => exact mdifferentiable_id
    | succ n ih =>
        rw [iterate_succ]
        exact ih.comp hf
  have hopen : ∀ n : ℕ, IsOpenMap (f^[n]) := by
    intro n
    induction n with
    | zero => exact IsOpenMap.id
    | succ n ih =>
        rw [iterate_succ]
        exact ih.comp hfo
  have hd : DifferentiableOn ℂ (e ∘ (f^[k]) ∘ e.symm) (ball (e a) R) := by
    intro z hz
    have hs : (f^[k]) (e.symm z) ∈ e.source := by
      obtain ⟨w, hw, he⟩ := hm (mem_image_of_mem e.symm hz)
      exact he ▸ e.map_target (htarget hw)
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm z :=
      ((mdifferentiable_chart (I := 𝓘(ℂ)) a).2 z (htarget hz)).mdifferentiableAt
      (e.open_target.mem_nhds (htarget hz))
    have h12 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ((f^[k]) ∘ e.symm) z :=
      (hiter k (e.symm z)).comp z h1
    have h3 := ((mdifferentiable_chart (I := 𝓘(ℂ)) a).1 _ hs).mdifferentiableAt
      (e.open_source.mem_nhds hs)
    exact ((h3.comp z h12).differentiableAt).differentiableWithinAt
  apply exists_neighborhood_isolating_backwardOrbit_of_chart_return hk e hae hR htarget hd hka hm
  intro n _
  exact eventually_eq_of_mem_closed_discrete
    (isClosed_singleton.preimage (hiter n).continuous)
    (isDiscrete_fiber_of_isOpenMap_of_mdifferentiable (hopen n) (hiter n) a) a

end SurfaceDynamics.BKL

end

section

/-! # Local finiteness of backward orbits near constant-limit regions -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [UniformSpace Y]

/-- If a constant iterate limit is attained in the convergence region, its
backward orbit is locally finite throughout that region. -/
theorem finite_backwardOrbit_near_of_attained_constant_limit
    {f : X → X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsOpenEmbedding j)
    {times : ℕ → ℕ} (ht : StrictMono times) {a y x : X} {N : ℕ}
    {U : Set X} (hU : IsOpen U) (hy : y ∈ U) (hx : x ∈ U) (hya : (f^[N]) y = a)
    (hlim : TendstoLocallyUniformlyOn
      (fun n x => j ((f^[times n]) x)) (fun _ => j a) atTop U) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      (W ∩ {z | ∃ n : ℕ, (f^[n]) z = a}).Finite := by
  classical
  obtain ⟨V, hVo, haV, hiso⟩ :=
    exists_neighborhood_isolating_backwardOrbit_of_constant_limit hf hfo hj ht hU hy hya hlim
  have hconv : Tendsto (fun n => (f^[times n]) x) atTop (𝓝 a) :=
    hj.isEmbedding.tendsto_nhds_iff.mpr (hlim.tendsto_at hx)
  obtain ⟨m, hm⟩ := (hconv.eventually (hVo.mem_nhds haV)).exists
  let t := times m
  have hpre : IsOpen ((f^[t]) ⁻¹' V) := hVo.preimage (hf.continuous.iterate t)
  obtain ⟨K, hK, hxK, hKpre⟩ := exists_compact_subset hpre hm
  have hiter : ∀ n : ℕ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f^[n]) := by
    intro n
    induction n with
    | zero => exact mdifferentiable_id
    | succ n ih =>
        rw [iterate_succ]
        exact ih.comp hf
  have hopen : ∀ n : ℕ, IsOpenMap (f^[n]) := by
    intro n
    induction n with
    | zero => exact IsOpenMap.id
    | succ n ih =>
        rw [iterate_succ]
        exact ih.comp hfo
  have hfinite : (⋃ n : Fin (t + 1), K ∩ (f^[(n : ℕ)]) ⁻¹' {a}).Finite := by
    apply Set.finite_iUnion
    intro n
    exact finite_compact_inter_preimage_of_finite (hopen n) (hiter n) hK (finite_singleton a)
  refine ⟨interior K, isOpen_interior, hxK, hfinite.subset ?_⟩
  rintro z ⟨hz, n, hn⟩
  have hzK := interior_subset hz
  by_cases hnt : n ≤ t
  · exact mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_of_le hnt⟩, hzK, hn⟩
  · have htn : t ≤ n := by omega
    have hhit : (f^[n - t]) ((f^[t]) z) = a := by
      rw [← iterate_add_apply, Nat.sub_add_cancel htn]
      exact hn
    have hzentry : (f^[t]) z = a := hiso _ (hKpre hzK) _ hhit
    exact mem_iUnion.mpr ⟨⟨t, Nat.lt_succ_self t⟩, hzK, hzentry⟩

end SurfaceDynamics.BKL

end

section

/-! # No accumulation of backward orbits in constant-limit regions

Normal subsequences and evaluation at varying points identify any candidate
accumulation limit. The attained-limit return argument then gives local
finiteness and contradicts accumulation.
-/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

/-- Locally uniform convergence to a constant allows the evaluation point
to vary along a convergent sequence. -/
theorem tendsto_evaluation_of_constant_locally_uniform
    {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    {F : ℕ → X → Y} {b : Y}
    (hF : TendstoLocallyUniformlyOn F (fun _ => b) atTop U)
    {z : ℕ → X} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => F n (z n)) atTop (𝓝 b) := by
  have hp := (hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hF) x hx
  have hh := hp.comp (tendsto_id.prodMk hz)
  simpa only [nhds_eq_comap_uniformity, tendsto_comap_iff, Function.comp_def, id_eq] using hh

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [UniformSpace Y] [T2Space Y]

/-- In an open region where every sequence of iterates has a subsequence
converging locally uniformly to a constant, no backward orbit accumulates. -/
theorem not_accPt_backwardOrbit_of_constant_limits
    {f : X → X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsOpenEmbedding j) {U : Set X} (hU : IsOpen U)
    (hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : Y,
        TendstoLocallyUniformlyOn (fun n z => j ((f^[times (ψ n)]) z))
          (fun _ => b) atTop U)
    (a : X) {x : X} (hx : x ∈ U) :
    ¬ AccPt x (𝓟 {z | ∃ n : ℕ, (f^[n]) z = a}) := by
  classical
  intro hacc
  obtain ⟨z, hz, hzall⟩ := exists_seq_forall_of_frequently
    ((accPt_iff_frequently.mp hacc).and_eventually (hU.mem_nhds hx))
  choose τ hτ using fun n => (hzall n).1.2
  have hiter : ∀ n : ℕ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f^[n]) := by
    intro n
    induction n with
    | zero => exact mdifferentiable_id
    | succ n ih =>
        rw [iterate_succ]
        exact ih.comp hf
  have hopen : ∀ n : ℕ, IsOpenMap (f^[n]) := by
    intro n
    induction n with
    | zero => exact IsOpenMap.id
    | succ n ih =>
        rw [iterate_succ]
        exact ih.comp hfo
  have hτlim : Tendsto τ atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    have hshort : ∀ᶠ w in 𝓝 x, ∀ l ≤ k, (f^[l]) w = a → w = x :=
      eventually_all_le (fun l _ => eventually_eq_of_mem_closed_discrete
        (isClosed_singleton.preimage (hiter l).continuous)
        (isDiscrete_fiber_of_isOpenMap_of_mdifferentiable (hopen l) (hiter l) a) x)
    filter_upwards [hz.eventually hshort] with n hn
    by_contra hnk
    exact (hzall n).1.1 (hn (τ n) (by omega) (hτ n))
  obtain ⟨α, hα, hτα⟩ := strictMono_subseq_of_tendsto_atTop hτlim
  obtain ⟨ψ, hψ, b, hb⟩ := hlim (τ ∘ α) hτα
  have hzsub : Tendsto (fun n => z (α (ψ n))) atTop (𝓝 x) :=
    hz.comp (hα.tendsto_atTop.comp hψ.tendsto_atTop)
  have hvalue : b = j a := by
    have hh := tendsto_evaluation_of_constant_locally_uniform hU hx hb hzsub
    have he : (fun n => j ((f^[(τ ∘ α) (ψ n)]) (z (α (ψ n))))) =
        (fun _ : ℕ => j a) := by
      funext n
      exact congrArg j (hτ (α (ψ n)))
    rw [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  rw [hvalue] at hb
  obtain ⟨W, hWo, hxW, hWf⟩ := finite_backwardOrbit_near_of_attained_constant_limit
    hf hfo hj (hτα.comp hψ) hU (hzall 0).2 hx (hτ 0) hb
  have heq := eventually_eq_of_mem_closed_discrete hWf.isClosed hWf.isDiscrete x
  obtain ⟨n, hnW, hnEq⟩ :=
    ((hz.eventually (hWo.mem_nhds hxW)).and (hz.eventually heq)).exists
  exact (hzall n).1.1 (hnEq ⟨hnW, τ n, hτ n⟩)

end SurfaceDynamics.BKL

end

section

/-! # Closed discrete punctures do not disconnect a surface

Two points lie in a relatively compact connected open neighbourhood of a path.
Only finitely many punctures occur there, so finite-puncture connectedness
applies. This avoids any restriction on the number of punctures globally.
-/

open Set Function Filter Topology

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [ConnectedSpace X]

/-- The complement of a closed discrete subset of a connected Riemann surface
is preconnected. -/
theorem isPreconnected_compl_of_closed_discrete {D : Set X}
    (hDc : IsClosed D) (hDd : IsDiscrete D) : IsPreconnected Dᶜ := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  let : PathConnectedSpace X := .of_locallyPathConnectedSpace
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  let p : Path x y := PathConnectedSpace.somePath x y
  have hK : IsCompact (range p) := isCompact_range p.continuous
  have hKc : IsConnected (range p) := isConnected_range p.continuous
  have hxK : x ∈ range p := ⟨0, p.source⟩
  have hyK : y ∈ range p := ⟨1, p.target⟩
  obtain ⟨W, hWo, hKW, _, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ _)
  let V : TopologicalSpace.Opens X := ⟨connectedComponentIn W x, hWo.connectedComponentIn⟩
  have hKV : range p ⊆ V := hKc.isPreconnected.subset_connectedComponentIn hxK hKW
  have hVc : IsConnected (V : Set X) :=
    isConnected_connectedComponentIn_iff.mpr (hKW hxK)
  let : ConnectedSpace V := Subtype.connectedSpace hVc
  let c := chartAt ℂ (⟨x, hKV hxK⟩ : V)
  have hci : c.target.Infinite := infinite_of_mem_nhds (c ⟨x, hKV hxK⟩)
    (c.open_target.mem_nhds (c.map_source (mem_chart_source ℂ _)))
  let : Infinite c.target := hci.to_subtype
  let : Infinite V := Infinite.of_injective (fun z : c.target => c.symm z)
    (fun z w hzw => Subtype.ext (c.symm.injOn z.property w.property hzw))
  have hVcompact : IsCompact (closure (V : Set X)) :=
    hWc.of_isClosed_subset isClosed_closure
      (closure_mono (connectedComponentIn_subset W x))
  have hF : (closure (V : Set X) ∩ D).Finite :=
    (hVcompact.inter_right hDc).finite (hDd.mono inter_subset_right)
  have hFin : (Subtype.val ⁻¹' D : Set V).Finite := by
    have hh := hF.preimage (f := (Subtype.val : V → X)) Subtype.val_injective.injOn
    apply hh.subset
    intro z hz
    exact ⟨subset_closure z.property, hz⟩
  have hc : IsConnected ((Subtype.val ⁻¹' D : Set V)ᶜ) := by
    simpa only [hFin.coe_toFinset] using
      (RiemannDynamics.isConnected_compl_finset hFin.toFinset)
  let T : Set X := Subtype.val '' ((Subtype.val ⁻¹' D : Set V)ᶜ)
  refine ⟨T, ?_, ⟨⟨x, hKV hxK⟩, hx, rfl⟩,
    ⟨⟨y, hKV hyK⟩, hy, rfl⟩,
    (hc.image Subtype.val continuous_subtype_val.continuousOn).isPreconnected⟩
  rintro z ⟨w, hw, rfl⟩
  exact hw

/-- A nonempty complement is therefore connected. -/
theorem isConnected_compl_of_closed_discrete {D : Set X}
    (hDc : IsClosed D) (hDd : IsDiscrete D) (hne : Dᶜ.Nonempty) :
    IsConnected Dᶜ :=
  ⟨hne, isPreconnected_compl_of_closed_discrete hDc hDd⟩

end SurfaceDynamics.BKL

end

section

/-! # Removing backward orbits of finitely many values

Within a constant-limit normality region the full backward orbit of a finite
set is closed and discrete. Its removal therefore preserves connectedness.
-/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

theorem eventually_eq_of_mem_of_not_accPt
    {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    (h : ¬ AccPt x (𝓟 S)) : ∀ᶠ z in 𝓝 x, z ∈ S → z = x := by
  have hh : ∀ᶠ z in 𝓝 x, ¬ (z ≠ x ∧ z ∈ S) :=
    not_frequently.mp (fun hfreq => h (accPt_iff_frequently.mpr hfreq))
  filter_upwards [hh] with z hz hzS
  by_contra hne
  exact hz ⟨hne, hzS⟩

theorem not_accPt_of_eventually_eq_of_mem
    {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    (h : ∀ᶠ z in 𝓝 x, z ∈ S → z = x) : ¬ AccPt x (𝓟 S) := by
  intro ha
  obtain ⟨z, ⟨hz, hzS⟩, heq⟩ :=
    ((accPt_iff_frequently.mp ha).and_eventually h).exists
  exact hz (heq hzS)

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [UniformSpace Y] [T2Space Y]

/-- Finitely many target values have a closed discrete total backward orbit
inside a constant-limit region. -/
theorem isClosed_isDiscrete_backwardOrbit_of_finite_constant_limits
    {f : X → X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsOpenEmbedding j) (U : TopologicalSpace.Opens X)
    (hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : Y,
        TendstoLocallyUniformlyOn (fun n z => j ((f^[times (ψ n)]) z))
          (fun _ => b) atTop U)
    {E : Set X} (hE : E.Finite) :
    IsClosed {z : U | ∃ n : ℕ, (f^[n]) (z : X) ∈ E} ∧
      IsDiscrete {z : U | ∃ n : ℕ, (f^[n]) (z : X) ∈ E} := by
  have hlocal : ∀ x ∈ (U : Set X),
      ∀ᶠ z in 𝓝 x, (∃ n : ℕ, (f^[n]) z ∈ E) → z = x := by
    intro x hx
    have hall : ∀ a ∈ E, ∀ᶠ z in 𝓝 x,
        (∃ n : ℕ, (f^[n]) z = a) → z = x := fun a _ =>
      eventually_eq_of_mem_of_not_accPt
        (not_accPt_backwardOrbit_of_constant_limits hf hfo hj U.isOpen hlim a hx)
    filter_upwards [(hE.eventually_all).mpr hall] with z hz hzn
    obtain ⟨n, hn⟩ := hzn
    exact hz ((f^[n]) z) hn ⟨n, rfl⟩
  have hno : ∀ x : U,
      ¬ AccPt x (𝓟 {z : U | ∃ n : ℕ, (f^[n]) (z : X) ∈ E}) := by
    intro x
    apply not_accPt_of_eventually_eq_of_mem
    filter_upwards [continuous_subtype_val.continuousAt.eventually (hlocal x x.property)]
      with z hz hzs
    exact Subtype.ext (hz hzs)
  refine ⟨isClosed_iff_accPt.mpr (fun x hx => False.elim (hno x hx)), ?_⟩
  exact isDiscrete_iff_discreteTopology.mpr
    (discreteTopology_of_noAccPts (fun x _ => hno x))

/-- Removing those preimages from a connected region leaves a connected
set, provided at least one point remains. -/
theorem isConnected_compl_backwardOrbit_of_finite_constant_limits
    {f : X → X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsOpenEmbedding j) (U : TopologicalSpace.Opens X)
    [ConnectedSpace U]
    (hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : Y,
        TendstoLocallyUniformlyOn (fun n z => j ((f^[times (ψ n)]) z))
          (fun _ => b) atTop U)
    {E : Set X} (hE : E.Finite)
    (hne : ({z : U | ∃ n : ℕ, (f^[n]) (z : X) ∈ E}ᶜ).Nonempty) :
    IsConnected ({z : U | ∃ n : ℕ, (f^[n]) (z : X) ∈ E}ᶜ) := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  obtain ⟨hc, hd⟩ := isClosed_isDiscrete_backwardOrbit_of_finite_constant_limits hf hfo hj U hlim hE
  exact isConnected_compl_of_closed_discrete hc hd hne

end SurfaceDynamics.BKL

end
