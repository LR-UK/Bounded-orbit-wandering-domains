/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Sequences
import BoundedWanderingDomains.Surfaces.LocalMapTotalization
import BoundedWanderingDomains.Surfaces.CompactFilling
import BoundedWanderingDomains.Surfaces.LocalCoveringDiscs
import BoundedWanderingDomains.Surfaces.WanderingDiscShrink
import BoundedWanderingDomains.Surfaces.SurfaceFilling
import BoundedWanderingDomains.Surfaces.CoordinateDiscParam
import Mathlib.Topology.Sets.Opens
import BoundedWanderingDomains.Surfaces.BKL.AnalyticCompletion
import BoundedWanderingDomains.Surfaces.BKL.ComponentRecovery
import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
import BoundedWanderingDomains.Surfaces.CompactClusterSeparation

section

/-! # Constant subsequential limits from shrinking images

No holomorphic limit theorem is needed here: images uniformly close to their
centres converge to a constant whenever the centres converge.
-/

open Set Function Filter Topology
open scoped Uniformity

namespace SurfaceDynamics.BKL

theorem tendstoUniformlyOn_of_close_to_centres
    {ι A Y : Type*} [UniformSpace Y] {l : Filter ι}
    {F : ι → A → Y} {c : ι → Y} {a : Y} {U : Set A}
    (hc : Tendsto c l (𝓝 a))
    (hclose : ∀ v ∈ 𝓤 Y, ∀ᶠ n in l, ∀ x ∈ U, (c n, F n x) ∈ v) :
    TendstoUniformlyOn F (fun _ => a) l U := by
  intro v hv
  obtain ⟨w, hw, hww⟩ := comp_mem_uniformity_sets hv
  filter_upwards [hc.tendstoUniformlyOn_const U w hw, hclose w hw] with n hn hnear
  intro x hx
  exact hww ⟨c n, hn x hx, hnear x hx⟩

theorem exists_constant_limit_subsequence_of_shrinking_images
    {A X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [UniformSpace Y] {j : X → Y} (hj : Continuous j)
    {K : Set X} (hK : IsCompact K) {c : ℕ → X} (hc : ∀ n, c n ∈ K)
    {F : ℕ → A → Y} {U : Set A}
    (hclose : ∀ v ∈ 𝓤 Y, ∀ᶠ n in atTop, ∀ x ∈ U, (j (c n), F n x) ∈ v)
    (times : ℕ → ℕ) (ht : StrictMono times) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ a ∈ K,
      TendstoUniformlyOn (fun n => F (times (ψ n))) (fun _ => j a) atTop U := by
  obtain ⟨a, ha, ψ, hψ, hlim⟩ := hK.tendsto_subseq (fun n => hc (times n))
  refine ⟨ψ, hψ, a, ha, tendstoUniformlyOn_of_close_to_centres
    (hj.continuousAt.tendsto.comp hlim) ?_⟩
  intro v hv
  exact (ht.tendsto_atTop.comp hψ.tendsto_atTop).eventually (hclose v hv)

end SurfaceDynamics.BKL

end

section

/-! # Normality of a trapped region whose forward images shrink -/

open Set Function Filter Topology OnePoint
open scoped Uniformity

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X]

local instance : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1

theorem isNormalOn_of_shrinking_orbits
    (f : LocalMap X) {U : Set X}
    (hstay : ∀ x ∈ U, ∀ n : ℕ, (f.totalize^[n]) x ∈ f.source)
    {K : Set X} (hK : IsCompact K) {c : ℕ → X} (hc : ∀ n, c n ∈ K)
    (hclose : ∀ v ∈ 𝓤 (OnePoint X), ∀ᶠ n in atTop, ∀ x ∈ U,
      ((c n : OnePoint X), ((f.totalize^[n]) x : OnePoint X)) ∈ v) :
    f.IsNormalOn U := by
  intro times ht
  obtain ⟨ψ, hψ, a, _, hlim⟩ := BKL.exists_constant_limit_subsequence_of_shrinking_images
    OnePoint.continuous_coe hK hc hclose times ht
  refine ⟨ψ, hψ, fun _ => (a : OnePoint X), ?_⟩
  apply TendstoUniformly.tendstoLocallyUniformly
  intro v hv
  filter_upwards [hlim v hv] with n hn
  intro x
  have hh := hn (x : X) x.2
  simpa only [compactifiedIterate,
    f.local_iterate_eq_totalize_iterate_of_stays (hstay x x.2)] using hh

theorem subset_omega_of_shrinking_orbits
    (f : LocalMap X) {U : Set X} (hU : IsOpen U)
    (hstay : ∀ x ∈ U, ∀ n : ℕ, (f.totalize^[n]) x ∈ f.source)
    {K : Set X} (hK : IsCompact K) {c : ℕ → X} (hc : ∀ n, c n ∈ K)
    (hclose : ∀ v ∈ 𝓤 (OnePoint X), ∀ᶠ n in atTop, ∀ x ∈ U,
      ((c n : OnePoint X), ((f.totalize^[n]) x : OnePoint X)) ∈ v) :
    U ⊆ f.omega := by
  have htr : U ⊆ f.trapped := by
    intro x hx n
    exact ⟨(f.totalize^[n]) x, hstay x hx n,
      f.local_iterate_eq_totalize_iterate_of_stays (hstay x hx) n⟩
  exact fun x hx => ⟨U, hU, hx, htr, f.isNormalOn_of_shrinking_orbits hstay hK hc hclose⟩

end SurfaceDynamics.LocalMap

end

section

/-! # Normality and constant limits on forward invariant chains of fillings -/

open Set Function Filter Topology
open scoped Manifold Uniformity
open AreaDeficit.Surfaces

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

local instance : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1

omit [LocallyCompactSpace X] [FirstCountableTopology X] in
theorem mapsTo_compactFill_of_forward
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {C D : Set X}
    (hC : IsClosed C) (hCs : compactFill C ⊆ f.source) (hnext : MapsTo f.totalize C D) :
    MapsTo f.totalize (compactFill C) (compactFill D) := by
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  apply mapsTo_iff_image_subset.mpr
  exact (image_compactFill_subset_compactFill_image_local hC hCs
    (f.continuousOn_totalize hf.2.continuous)
    (fun V hVs hVo => f.isOpen_image_totalize hf.1 hVo hVs)).trans
      (compactFill_mono hnext.image_subset)

omit [LocallyCompactSpace X] [FirstCountableTopology X] in
theorem iterates_mem_compactFill_of_forward
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {C : ℕ → Set X}
    (hC : ∀ n, IsClosed (C n)) (hCs : ∀ n, compactFill (C n) ⊆ f.source)
    (hnext : ∀ n, MapsTo f.totalize (C n) (C (n + 1))) :
    ∀ n x, x ∈ compactFill (C n) → ∀ k : ℕ,
      (f.totalize^[k]) x ∈ compactFill (C (n + k)) := by
  intro n x hx k
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      simpa only [Nat.add_succ, iterate_succ_apply'] using
        f.mapsTo_compactFill_of_forward hf (hC (n + k)) (hCs (n + k)) (hnext (n + k)) ih

omit [FirstCountableTopology X] in
theorem shrinking_filled_orbits_close
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {C : ℕ → Set X}
    (hC : ∀ n, IsClosed (C n)) (hCs : ∀ n, compactFill (C n) ⊆ f.source)
    (hnext : ∀ n, MapsTo f.totalize (C n) (C (n + 1))) {c : ℕ → X}
    (hclose : ∀ v ∈ 𝓤 (OnePoint X), ∀ᶠ n in atTop, ∀ x ∈ compactFill (C n),
      ((c n : OnePoint X), (x : OnePoint X)) ∈ v) (n : ℕ) :
    ∀ v ∈ 𝓤 (OnePoint X), ∀ᶠ k in atTop, ∀ x ∈ compactFill (C n),
      ((c (n + k) : OnePoint X), ((f.totalize^[k]) x : OnePoint X)) ∈ v := by
  intro v hv
  have hh := (tendsto_add_atTop_nat n).eventually (hclose v hv)
  filter_upwards [hh] with k hk
  intro x hx
  rw [Nat.add_comm k n] at hk
  exact hk _ (f.iterates_mem_compactFill_of_forward hf hC hCs hnext n x hx k)

theorem interior_compactFill_subset_omega_of_shrinking
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {C : ℕ → Set X}
    (hC : ∀ n, IsClosed (C n)) (hCs : ∀ n, compactFill (C n) ⊆ f.source)
    (hnext : ∀ n, MapsTo f.totalize (C n) (C (n + 1)))
    {K : Set X} (hK : IsCompact K) {c : ℕ → X} (hc : ∀ n, c n ∈ K)
    (hclose : ∀ v ∈ 𝓤 (OnePoint X), ∀ᶠ n in atTop, ∀ x ∈ compactFill (C n),
      ((c n : OnePoint X), (x : OnePoint X)) ∈ v) (n : ℕ) :
    interior (compactFill (C n)) ⊆ f.omega := by
  apply f.subset_omega_of_shrinking_orbits isOpen_interior
    (fun x hx k => hCs (n + k)
      (f.iterates_mem_compactFill_of_forward hf hC hCs hnext n x (interior_subset hx) k))
    hK (fun k => hc (n + k))
  intro v hv
  filter_upwards [f.shrinking_filled_orbits_close hf hC hCs hnext hclose n v hv] with k hk
  exact fun x hx => hk x (interior_subset hx)

end SurfaceDynamics.LocalMap

end

section

/-! # Uniform shrinking of the compact fillings of disjoint covering discs -/

open Set Function Filter Metric Topology
open scoped Manifold Uniformity
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem exists_coordDisk_uniformly_small
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [UniformSpace Y] {j : X → Y} (hj : Continuous j)
    {v : Set (Y × Y)} (hv : v ∈ 𝓤 Y) (x : X) :
    ∃ D : RiemannDynamics.CoordDisk X, D.center = x ∧
      ∀ a ∈ D.closedCarrier, ∀ b ∈ D.closedCarrier, (j a, j b) ∈ v := by
  have hn : (Prod.map j j) ⁻¹' v ∈ 𝓝 (x, x) :=
    (hj.prodMap hj).continuousAt (nhds_le_uniformity (j x) hv)
  rw [nhds_prod_eq] at hn
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hn
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp (inter_mem hA hB)
  obtain ⟨D, hDx, hDW⟩ := exists_coordDisk_center_closedCarrier_subset hWo hxW
  refine ⟨D, hDx, ?_⟩
  intro a ha b hb
  have hab : (a, b) ∈ (Prod.map j j) ⁻¹' v :=
    hAB ⟨(hW (hDW ha)).1, (hW (hDW hb)).2⟩
  exact hab

theorem disjoint_disc_fillings_uniformly_shrink
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] [NoncompactSpace X]
    [UniformSpace Y] {j : X → Y} (hj : Continuous j)
    (q : DiscCover X) {K : Set X} (hK : IsCompact K)
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∀ v ∈ 𝓤 Y, ∀ᶠ n in atTop,
      ∀ x ∈ compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}),
        (j (F n discZero), j x) ∈ v := by
  intro v hv
  choose D hD hsmall using fun x : K => exists_coordDisk_uniformly_small hj hv (x : X)
  have hcover : K ⊆ ⋃ x : K, range (D x).param := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, discZero, (D ⟨x, hx⟩).param_zero.trans (hD ⟨x, hx⟩)⟩
  have hh := q.disjoint_disc_images_eventually_in_cover hK F hF hcentre hdis
    (fun x : K => range (D x).param) (fun x => (D x).isOpenEmbedding_param.isOpen_range)
    hcover hr1
  filter_upwards [hh] with n hn
  obtain ⟨a, ha⟩ := hn
  have hC : F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r} ⊆ (D a).closedCarrier := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := ha z hz
    exact hw ▸ (D a).param_mem_closedCarrier w
  have hzero : discZero ∈ {z : unitDisc | ‖(z : ℂ)‖ ≤ r} := by
    change ‖(0 : ℂ)‖ ≤ r
    simpa only [norm_zero] using hr
  intro x hx
  exact hsmall a (F n discZero) (hC (mem_image_of_mem _ hzero)) x
    (compactFill_subset_coordDisk (D a) hC hx)

end SurfaceDynamics.BKL

end

section

/-! # A connected open neighbourhood between nested fillings -/

open Set Function Topology
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem exists_connected_neighborhood_between_fillings
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    [ConnectedSpace X] {C D O : Set X} (hC : IsClosed C) (hCc : IsConnected C)
    (hO : IsOpen O) (hCO : C ⊆ O) (hOD : O ⊆ D) :
    ∃ W : TopologicalSpace.Opens X, IsConnected (W : Set X) ∧
      compactFill C ⊆ W ∧ (W : Set X) ⊆ interior (compactFill D) := by
  have hCD : C ⊆ D := hCO.trans hOD
  have hCI : C ⊆ interior (compactFill D) :=
    hCO.trans (hO.subset_interior_iff.mpr (hOD.trans (subset_compactFill D)))
  have hfillI : compactFill C ⊆ interior (compactFill D) :=
    compactFill_subset_interior_of_subset hC hCI (compactFill_mono hCD)
  obtain ⟨a, ha⟩ := hCc.nonempty
  let W : TopologicalSpace.Opens X :=
    ⟨connectedComponentIn (interior (compactFill D)) a, isOpen_interior.connectedComponentIn⟩
  refine ⟨W, isConnected_connectedComponentIn_iff.mpr (hCI ha), ?_,
    connectedComponentIn_subset _ _⟩
  exact (isConnected_compactFill hC hCc).isPreconnected.subset_connectedComponentIn
    (subset_compactFill C ha) hfillI

end SurfaceDynamics.BKL

end

section

/-! # The late filled covering discs lie in the original normality components -/

open Set Function Filter Metric Topology
open scoped Manifold Uniformity
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] [NoncompactSpace X]

local instance : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1

theorem disjoint_disc_fillings_eventually_subset_original_component
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : DiscCover X)
    {K : Set X} (hK : IsCompact K) (hKd : Disjoint K (derivedSet f.singularValues))
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hFo : ∀ n, IsOpenMap (F n)) (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    (hsource : ∀ n, range (F n) ⊆ f.source)
    (hcomp : ∀ n, range (F n) = connectedComponentIn f.omega (F n discZero))
    (hnext : ∀ n, MapsTo f.totalize (range (F n)) (range (F (n + 1))))
    (hnextDisc : ∀ r : ℝ, ∀ n,
      MapsTo f.totalize (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})
        (F (n + 1) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ⊆ range (F n) := by
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  have hR : 0 ≤ R := hr.trans hrR.le
  let C : ℕ → Set X := fun n => F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R}
  have hC : ∀ n, IsCompact (C n) := fun n =>
    (unitDisc_closed_radius_compact hR1).image (hF n).continuous
  have hsourceEvent := disjoint_disc_fillings_eventually_subset_denseCompletion f hf q
    hK hKd F hF hcentre hdis hsource hR hR1 (hnextDisc R)
  obtain ⟨E, hE, hcontrol⟩ := disjoint_disc_fillings_eventually_finite_singular_intersection
    f q hK hKd F hF hcentre hdis
  have hevent : ∀ᶠ n in atTop, compactFill (C n) ⊆ f.denseCompletion.source ∧
      compactFill (C n) ∩ f.singularValues ⊆ E ∧
      Disjoint (range (F n)) E ∧ ∀ e ∈ E, ¬ IsPuncture (range (F n)) e := by
    filter_upwards [hsourceEvent, hcontrol R hR1, AreaDeficit.eventually_disjoint_finite hdis hE,
      eventually_no_puncture_in_finite (fun n => range (F n)) hdis hE] with n h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  let T : ℕ → Set X := fun k => C (n + k)
  let g := f.denseCompletion
  have hg : IsOpenHolomorphic g := f.isOpenHolomorphic_denseCompletion hf
  have hT : ∀ k, IsClosed (T k) := fun k => (hC (n + k)).isClosed
  have hTs : ∀ k, compactFill (T k) ⊆ g.source :=
    fun k => (hN (n + k) (hn.trans (Nat.le_add_right n k))).1
  have hTnext : ∀ k, MapsTo g.totalize (T k) (T (k + 1)) := by
    intro k x hx
    change g.totalize x ∈ C (n + (k + 1))
    rw [show g.totalize x = f.totalize x from
      f.denseCompletion_totalize_eq hf.2 (hsource (n + k) (image_subset_range _ _ hx))]
    simpa only [Nat.add_assoc] using hnextDisc R (n + k) hx
  have hclose : ∀ v ∈ 𝓤 (OnePoint X), ∀ᶠ k in atTop, ∀ x ∈ compactFill (T k),
      ((F (n + k) discZero : OnePoint X), (x : OnePoint X)) ∈ v := by
    intro v hv
    have hh := (tendsto_add_atTop_nat n).eventually
      (disjoint_disc_fillings_uniformly_shrink OnePoint.continuous_coe q hK F hF
        hcentre hdis hR hR1 v hv)
    simpa only [T, C, Nat.add_comm] using hh
  let A := F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}
  have hA : IsCompact A := (unitDisc_closed_radius_compact hr1).image (hF n).continuous
  have hAc : IsConnected A :=
    (unitDisc_closed_radius_connected hr hr1).image _ (hF n).continuous.continuousOn
  have hAO : A ⊆ F n '' {z : unitDisc | ‖(z : ℂ)‖ < R} :=
    image_mono (fun _ hz => hz.trans_lt hrR)
  have hO : IsOpen (F n '' {z : unitDisc | ‖(z : ℂ)‖ < R}) :=
    hFo n _ (isOpen_lt continuous_subtype_val.norm continuous_const)
  have hOC : F n '' {z : unitDisc | ‖(z : ℂ)‖ < R} ⊆ C n := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, (show ‖(z : ℂ)‖ ≤ R from hz.le), rfl⟩
  obtain ⟨W, hWc, hAW, hWI⟩ := exists_connected_neighborhood_between_fillings
    hA.isClosed hAc hO hAO hOC
  have hWT : (W : Set X) ⊆ compactFill (T 0) := by
    simpa only [T, Nat.add_zero] using hWI.trans interior_subset
  have horbit : ∀ x ∈ (W : Set X), ∀ k, (g.totalize^[k]) x ∈ compactFill (T k) := by
    intro x hx k
    simpa only [Nat.zero_add] using g.iterates_mem_compactFill_of_forward hg hT hTs hTnext
      0 x (hWT hx) k
  have hstay : ∀ x ∈ (W : Set X), ∀ k, (g.totalize^[k]) x ∈ g.source :=
    fun x hx k => hTs k (horbit x hx k)
  have hcloseOrbit : ∀ v ∈ 𝓤 (OnePoint X), ∀ᶠ k in atTop, ∀ x ∈ (W : Set X),
      ((F (n + k) discZero : OnePoint X), ((g.totalize^[k]) x : OnePoint X)) ∈ v := by
    intro v hv
    filter_upwards [hclose v hv] with k hk
    exact fun x hx => hk _ (horbit x hx k)
  have hWn : (W : Set X) ⊆ g.omega :=
    g.subset_omega_of_shrinking_orbits W.isOpen hstay hK (fun k => hcentre (n + k)) hcloseOrbit
  have hWnormal : g.IsNormalOn W :=
    g.isNormalOn_of_shrinking_orbits hstay hK (fun k => hcentre (n + k)) hcloseOrbit
  have hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : OnePoint X,
        TendstoLocallyUniformlyOn (fun k x => ((g.totalize^[times (ψ k)]) x : OnePoint X))
          (fun _ => b) atTop W := by
    intro times ht
    obtain ⟨ψ, hψ, a, _, ha⟩ := exists_constant_limit_subsequence_of_shrinking_images
      OnePoint.continuous_coe hK (fun k => hcentre (n + k)) hcloseOrbit times ht
    exact ⟨ψ, hψ, (a : OnePoint X), ha.tendstoLocallyUniformlyOn⟩
  have hzero : discZero ∈ {z : unitDisc | ‖(z : ℂ)‖ ≤ r} := by
    change ‖(0 : ℂ)‖ ≤ r
    simpa only [norm_zero] using hr
  have haW : F n discZero ∈ W := hAW (subset_compactFill A (mem_image_of_mem _ hzero))
  apply hAW.trans
  apply f.completed_region_subset_original_component hf (fun j => range (F j))
    hsource hnext W hWc hWn hWnormal hlim hE hstay
    (fun x hx k hs => (hN (n + k) (hn.trans (Nat.le_add_right n k))).2.1
      ⟨horbit x hx k, hs⟩) haW (mem_range_self discZero) (hcomp n)
    (fun k => (hN (n + k) (hn.trans (Nat.le_add_right n k))).2.2.1)
    (fun k => (hN (n + k) (hn.trans (Nat.le_add_right n k))).2.2.2)

end SurfaceDynamics.BKL

end

section

/-! # A covering disc is embedded when its compact filling stays in its domain -/

open Set Function Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem covering_injOn_radius_of_compactFill_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] (U : TopologicalSpace.Opens X) (q : DiscCover U)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (D : RiemannDynamics.CoordDisk X)
    (hD : (fun z => (q.projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r} ⊆ D.closedCarrier)
    (hfill : compactFill ((fun z => (q.projection z : X)) ''
      {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ⊆ U) :
    InjOn q.projection {z : unitDisc | ‖(z : ℂ)‖ < r} := by
  let : LocallyPathConnectedSpace unitDisc := ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  let : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace ℂ U
  let F : unitDisc → X := fun z => q.projection z
  have hF : Continuous F := continuous_subtype_val.comp q.continuous
  obtain ⟨W, hWo, hWsc, hCW, hWU⟩ := exists_simplyConnected_neighborhood_of_compactFill_subset
    ((unitDisc_closed_radius_compact hr1).image hF)
    ((unitDisc_closed_radius_connected hr.le hr1).image _ hF.continuousOn) U.isOpen D hD hfill
  let T : Set U := Subtype.val ⁻¹' W
  have hTsc : IsSimplyConnected T := by
    apply (IsEmbedding.subtypeVal (p := fun x : X => x ∈ U)).isSimplyConnected_image.mp
    have he : (Subtype.val : U → X) '' T = W :=
      image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hWU hx⟩, rfl⟩)
    rw [he]
    exact hWsc
  apply covering_injOn_simplyConnected (p := q.projection)
    (D := {z : unitDisc | ‖(z : ℂ)‖ < r}) (T := T)
    (isOpen_lt continuous_subtype_val.norm continuous_const)
    (unitDisc_open_radius_simplyConnected hr hr1)
    (hWo.preimage continuous_subtype_val) hTsc
    (a := discZero) (by change ‖(0 : ℂ)‖ < r; simpa only [norm_zero] using hr)
    q.continuous.continuousOn
    (fun z hz => hCW (mem_image_of_mem F (show ‖(z : ℂ)‖ ≤ r from hz.le)))
    (fun y _ => q.covering y)

end SurfaceDynamics.BKL

end

section

/-! # Forward control of closed centred covering discs for a local map -/

open Set Function Metric
open scoped Manifold Topology
open AreaDeficit.Surfaces

namespace SurfaceDynamics.LocalMap

theorem mapsTo_covering_closed_radius
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (U W : TopologicalSpace.Opens X) (hUs : (U : Set X) ⊆ f.source)
    (p : DiscCover U) (q : DiscCover W) (hm : MapsTo f.totalize U W)
    (h0 : (q.projection discZero : X) = f.totalize (p.projection discZero)) (r : ℝ) :
    MapsTo f.totalize ((fun z => (p.projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})
      ((fun z => (q.projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) := by
  let g : U → W := fun x => ⟨f.totalize x, hm x.property⟩
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    apply (mdifferentiable_subtypeVal_comp_iff W g).mp
    intro x
    exact ((f.mdifferentiableOn_totalize hf x (hUs x.property)).mdifferentiableAt
      (f.source.isOpen.mem_nhds (hUs x.property))).comp x (mdifferentiable_subtype_val U x)
  have hh := p.mapsTo_closed_radius q hg (Subtype.ext h0) r
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwe⟩ := hh (mem_image_of_mem _ hz)
  exact ⟨w, hw, congrArg Subtype.val hwe⟩

end SurfaceDynamics.LocalMap

end

section

/-! # Eventual embeddedness of centred covers without a connectivity hypothesis -/

open Set Function Filter Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem eventually_injective_centered_covers_of_avoids_derived
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [ConnectedSpace X] [NoncompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : DiscCover X)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hU : ∀ n, f.IsComponent (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (hforward : ∀ n, MapsTo f.totalize (U n) (U (n + 1)))
    (h0 : ∀ n, ((q (n + 1)).projection discZero : X) = f.totalize ((q n).projection discZero))
    {K : Set X} (hK : IsCompact K) (hKd : Disjoint K (derivedSet f.singularValues))
    (hcentre : ∀ n, ((q n).projection discZero : X) ∈ K)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, InjOn (q n).projection {z : unitDisc | ‖(z : ℂ)‖ < r} := by
  let F : ℕ → unitDisc → X := fun n z => (q n).projection z
  have hFU : ∀ n, range (F n) = (U n : Set X) := by
    intro n
    apply Subset.antisymm
    · rintro x ⟨z, rfl⟩
      exact ((q n).projection z).2
    · intro x hx
      obtain ⟨z, hz⟩ := (q n).surjective ⟨x, hx⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  have hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n) :=
    fun n => (mdifferentiable_subtype_val (U n)).comp (q n).holomorphic
  have hFo : ∀ n, IsOpenMap (F n) :=
    fun n => (U n).isOpen.isOpenMap_subtype_val.comp (q n).isOpenMap
  have hUs : ∀ n, (U n : Set X) ⊆ f.source := by
    intro n
    obtain ⟨x, hx, hUx⟩ := hU n
    exact (hUx ▸ connectedComponentIn_subset f.omega x).trans f.omega_subset_source
  have hFdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))) := by
    simpa only [hFU] using hdis
  have hFcomp : ∀ n, range (F n) = connectedComponentIn f.omega (F n discZero) := by
    intro n
    obtain ⟨x, hx, hUx⟩ := hU n
    exact (hFU n).trans (hUx.trans
      (connectedComponentIn_eq (hUx ▸ ((q n).projection discZero).2)))
  have hnext : ∀ n, MapsTo f.totalize (range (F n)) (range (F (n + 1))) := by
    simpa only [hFU] using hforward
  have hnextDisc : ∀ R : ℝ, ∀ n,
      MapsTo f.totalize (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R})
        (F (n + 1) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R}) := fun R n =>
    f.mapsTo_covering_closed_radius hf.2 (U n) (U (n + 1)) (hUs n)
      (q n) (q (n + 1)) (hforward n) (h0 n) R
  have hfill := disjoint_disc_fillings_eventually_subset_original_component f hf p hK hKd
    F hF hFo hcentre hFdis (fun n => (hFU n).symm ▸ hUs n) hFcomp hnext hnextDisc hr.le hr1
  choose D hD _ using fun x : K =>
    exists_coordDisk_center_closedCarrier_subset isOpen_univ (mem_univ (x : X))
  have hcover : K ⊆ ⋃ x : K, range (D x).param := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, discZero, (D ⟨x, hx⟩).param_zero.trans (hD ⟨x, hx⟩)⟩
  have hsmall := p.disjoint_disc_images_eventually_in_cover hK F hF hcentre hFdis
    (fun x : K => range (D x).param) (fun x => (D x).isOpenEmbedding_param.isOpen_range)
    hcover hr1
  filter_upwards [hfill, hsmall] with n hn hs
  obtain ⟨a, ha⟩ := hs
  apply covering_injOn_radius_of_compactFill_subset (U n) (q n) hr hr1 (D a) ?_
    ((hFU n) ▸ hn)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨w, hw⟩ := ha z hz
  change F n z ∈ (D a).closedCarrier
  exact hw ▸ (D a).param_mem_closedCarrier w

end SurfaceDynamics.BKL

end

section

/-! # Compact tail neighbourhoods avoiding a closed set -/

open Set Function Filter Topology

namespace SurfaceDynamics.BKL

theorem exists_compact_tail_disjoint_of_cluster_avoids
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (c : ℕ → X) {K S : Set X} (hK : IsCompact K) (hc : ∀ n, c n ∈ K)
    (hS : IsClosed S) (havoid : ∀ x, MapClusterPt x atTop c → x ∉ S) :
    ∃ L : Set X, IsCompact L ∧ Disjoint L S ∧ ∀ᶠ n in atTop, c n ∈ L := by
  let C : Set X := {x | MapClusterPt x atTop c}
  have hC : IsCompact C := hK.of_isClosed_subset isClosed_setOfPred_clusterPt
    (fun x hx => hK.isClosed.mem_of_mapClusterPt hx (Eventually.of_forall hc))
  obtain ⟨B, hBo, hCB, hBS, hBc⟩ := exists_open_between_and_isCompact_closure hC
    hS.isOpen_compl (fun x hx => havoid x hx)
  refine ⟨closure B, hBc, disjoint_left.mpr (fun x hx hs => hBS hx hs), ?_⟩
  exact (eventually_mem_of_compact_cluster_subset c hK hc hBo (fun x hx => hCB hx)).mono
    (fun _ hn => subset_closure hn)

end SurfaceDynamics.BKL

end

section

/-! # Eventual embeddedness when orbit cluster points avoid the derived singular set -/

open Set Function Filter Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem eventually_injective_centered_covers_of_cluster_avoids_derived
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [ConnectedSpace X] [NoncompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : DiscCover X)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hU : ∀ n, f.IsComponent (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (hforward : ∀ n, MapsTo f.totalize (U n) (U (n + 1)))
    (h0 : ∀ n, ((q (n + 1)).projection discZero : X) = f.totalize ((q n).projection discZero))
    {K : Set X} (hK : IsCompact K) (hcentre : ∀ n, ((q n).projection discZero : X) ∈ K)
    (havoid : ∀ x, MapClusterPt x atTop (fun n => ((q n).projection discZero : X)) →
      x ∉ derivedSet f.singularValues)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, InjOn (q n).projection {z : unitDisc | ‖(z : ℂ)‖ < r} := by
  obtain ⟨L, hL, hLd, hevent⟩ := exists_compact_tail_disjoint_of_cluster_avoids
    (fun n => ((q n).projection discZero : X)) hK hcentre
    (isClosed_derivedSet _) havoid
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hforward' : ∀ n, MapsTo f.totalize (U (n + N)) (U ((n + 1) + N)) := by
    intro n
    simpa only [Nat.add_right_comm n N 1] using hforward (n + N)
  have h0' : ∀ n, ((q ((n + 1) + N)).projection discZero : X) =
      f.totalize ((q (n + N)).projection discZero) := by
    intro n
    let c : ℕ → X := fun j => (q j).projection discZero
    change c ((n + 1) + N) = f.totalize (c (n + N))
    rw [Nat.add_right_comm n 1 N]
    exact h0 (n + N)
  have hh := eventually_injective_centered_covers_of_avoids_derived f hf p
    (fun n => U (n + N)) (fun n => q (n + N)) (fun n => hU (n + N))
    (fun n m hnm => hdis (by omega : n + N ≠ m + N)) hforward' h0' hL hLd
    (fun n => hN (n + N) (Nat.le_add_left N n)) hr hr1
  obtain ⟨M, hM⟩ := eventually_atTop.mp hh
  refine eventually_atTop.mpr ⟨M + N, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ n by omega)
  have hk : M ≤ k := by omega
  let P : ℕ → Prop := fun j => InjOn (q j).projection {z : unitDisc | ‖(z : ℂ)‖ < r}
  change P (N + k)
  rw [Nat.add_comm N k]
  exact hM k hk

end SurfaceDynamics.BKL

end
