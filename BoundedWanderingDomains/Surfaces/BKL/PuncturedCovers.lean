/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.CoordinateDiscParam
import EremenkoLyubichConstant.ExteriorCoverClassification
import Mathlib.Analysis.Calculus.Deriv.Inv
import BoundedWanderingDomains.Surfaces.BKL.ReturnLimits
import BoundedWanderingDomains.Surfaces.LocalDynamics
import Mathlib.Topology.DerivedSet
import BoundedWanderingDomains.Surfaces.WanderingDiscShrink
import BoundedWanderingDomains.TrappedComponentCovering
import BoundedWanderingDomains.Surfaces.SurfaceFilling
import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
import BoundedWanderingDomains.Surfaces.PlaneReading
import EremenkoLyubichConstant.TractCovering
import BoundedWanderingDomains.Surfaces.CoveringComponents
import BoundedWanderingDomains.Surfaces.HolomorphicLifting
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic
import BoundedWanderingDomains.Surfaces.SurfaceSingularCovering
import BoundedWanderingDomains.Surfaces.LocalMapTotalization
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import Mathlib.Analysis.Convex.Contractible

section

/-! # Nested coordinate discs with a simply connected ambient neighbourhood -/

open Set Function Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem isSimplyConnected_range_coordDisk_param
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (D : RiemannDynamics.CoordDisk X) : IsSimplyConnected (range D.param) := by
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  have hh := D.isOpenEmbedding_param.isEmbedding.isSimplyConnected_image.mpr
    (show IsSimplyConnected (univ : Set unitDisc) from
      (Homeomorph.Set.univ unitDisc).toHomotopyEquiv.simplyConnectedSpace)
  simpa only [image_univ] using hh

theorem exists_nested_simplyConnected_coordNeighborhood
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] {W : Set X} (hW : IsOpen W) {x : X} (hx : x ∈ W) :
    ∃ (D : RiemannDynamics.CoordDisk X) (V : TopologicalSpace.Opens X),
      D.center = x ∧ IsSimplyConnected (V : Set X) ∧ D.closedCarrier ⊆ V ∧ (V : Set X) ⊆ W := by
  obtain ⟨D₀, hD₀, hD₀W⟩ := exists_coordDisk_center_closedCarrier_subset hW hx
  let V : TopologicalSpace.Opens X := ⟨range D₀.param, D₀.isOpenEmbedding_param.isOpen_range⟩
  have hxV : x ∈ V := ⟨discZero, D₀.param_zero.trans hD₀⟩
  obtain ⟨D, hDx, hDV⟩ := exists_coordDisk_center_closedCarrier_subset V.isOpen hxV
  refine ⟨D, V, hDx, isSimplyConnected_range_coordDisk_param D₀, hDV, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hD₀W (D₀.param_mem_closedCarrier z)

end SurfaceDynamics.BKL

end

section

/-! # Inversion coordinates for the punctured unit disc -/

open Set Function Metric
open scoped Topology
open EremenkoLyubichConstant

namespace SurfaceDynamics.BKL

def puncturedUnitDisc : TopologicalSpace.Opens ℂ :=
  ⟨ball 0 1 \ {0}, isOpen_ball.sdiff isClosed_singleton⟩

theorem inv_mem_exterior_zero {z : ℂ} (hz : z ∈ puncturedUnitDisc) :
    z⁻¹ ∈ exponentialExterior 0 := by
  change Real.exp 0 < ‖z⁻¹‖
  rw [Real.exp_zero, norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hz.2)).mpr (mem_ball_zero_iff.mp hz.1)

theorem inv_mem_puncturedUnitDisc {z : ℂ} (hz : z ∈ exponentialExterior 0) :
    z⁻¹ ∈ puncturedUnitDisc := by
  have hn : 1 < ‖z‖ := by simpa only [exponentialExterior, mem_ofPred_eq, Real.exp_zero] using hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hn)
  refine ⟨?_, inv_ne_zero hz0⟩
  rw [mem_ball_zero_iff, norm_inv]
  exact (inv_lt_one₀ (norm_pos_iff.mpr hz0)).mpr hn

noncomputable def puncturedDiscExterior : puncturedUnitDisc ≃ₜ exponentialExterior 0 where
  toFun z := ⟨(z : ℂ)⁻¹, inv_mem_exterior_zero z.2⟩
  invFun z := ⟨(z : ℂ)⁻¹, inv_mem_puncturedUnitDisc z.2⟩
  left_inv z := Subtype.ext (inv_inv _)
  right_inv z := Subtype.ext (inv_inv _)
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.inv₀ (fun z => z.2.2)) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.inv₀ (fun z => by
      have h := inv_mem_puncturedUnitDisc z.2
      exact fun hz => h.2 (by simp [hz]))) _

@[simp] theorem puncturedDiscExterior_apply (z : puncturedUnitDisc) :
    (puncturedDiscExterior z : ℂ) = (z : ℂ)⁻¹ := rfl

@[simp] theorem puncturedDiscExterior_symm_apply (z : exponentialExterior 0) :
    (puncturedDiscExterior.symm z : ℂ) = (z : ℂ)⁻¹ := rfl

end SurfaceDynamics.BKL

end

section

/-! # Regular punctured coordinate discs away from the derived singular set -/

open Set Function Filter Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem exists_regular_punctured_coordDisk
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) {a : X} (ha : a ∉ derivedSet f.singularValues)
    {O : Set X} (hO : IsOpen O) (haO : a ∈ O) :
    ∃ D : RiemannDynamics.CoordDisk X, D.center = a ∧ D.closedCarrier ⊆ O ∧
      ∀ z : puncturedUnitDisc, D.param ⟨z, z.2.1⟩ ∈ f.regularValues := by
  have he : ∀ᶠ z in 𝓝 a, z ∈ f.singularValues → z = a :=
    eventually_eq_of_mem_of_not_accPt ha
  obtain ⟨W, hW, hWo, haW⟩ := mem_nhds_iff.mp he
  obtain ⟨D, hD, hDW⟩ := exists_coordDisk_center_closedCarrier_subset
    (hWo.inter hO) ⟨haW, haO⟩
  refine ⟨D, hD, hDW.trans inter_subset_right, ?_⟩
  intro z
  by_contra hs
  have hmem : D.param ⟨z, z.2.1⟩ ∈ W := (hDW (D.param_mem_closedCarrier _)).1
  have heq : D.param ⟨z, z.2.1⟩ = a := hW hmem hs
  have hp : D.param ⟨z, z.2.1⟩ = D.param discZero := heq.trans (D.param_zero.trans hD).symm
  have hz : (z : ℂ) = 0 := congrArg (Subtype.val : unitDisc → ℂ) (D.injective_param hp)
  exact z.2.2 hz

end SurfaceDynamics.BKL

end

section

/-! # Shrinking disjoint discs eventually lie in regular punctured target discs -/

open Set Function Filter Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem disjoint_discs_eventually_in_regular_punctured_coordDisk
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (q : DiscCover X) {K : Set X} (hK : IsCompact K)
    (hKd : Disjoint K (derivedSet f.singularValues))
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    {r : ℝ} (hr1 : r < 1) :
    ∀ᶠ n in atTop, ∃ D : RiemannDynamics.CoordDisk X,
      (∀ z : puncturedUnitDisc, D.param ⟨z, z.2.1⟩ ∈ f.regularValues) ∧
      F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r} ⊆
        range (fun z : puncturedUnitDisc => D.param ⟨z, z.2.1⟩) := by
  classical
  choose D hD _ hreg using fun x : K =>
    exists_regular_punctured_coordDisk f (disjoint_left.mp hKd x.2)
      isOpen_univ (mem_univ (x : X))
  have hcover : K ⊆ ⋃ x : K, range (D x).param := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, discZero, (D ⟨x, hx⟩).param_zero.trans (hD ⟨x, hx⟩)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => range (D x).param)
    (fun x => (D x).isOpenEmbedding_param.isOpen_range) hcover
  have hcoverI : K ⊆ ⋃ x : ↥I, range (D x).param := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := mem_iUnion₂.mp (hI hx)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hax⟩
  have hshrink := q.disjoint_disc_images_eventually_in_cover hK F hF hcentre hdis
    (fun x : ↥I => range (D x).param)
    (fun x => (D x).isOpenEmbedding_param.isOpen_range) hcoverI hr1
  have havoid := AreaDeficit.eventually_disjoint_finite hdis
    (Set.finite_range (fun x : ↥I => (D x).center))
  filter_upwards [hshrink, havoid] with n hn hna
  obtain ⟨a, ha⟩ := hn
  refine ⟨D a, hreg a, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨w, hw⟩ := ha z hz
  have hw0 : (w : ℂ) ≠ 0 := by
    intro he
    have hwd : w = discZero := Subtype.ext he
    have hc : F n z = (D a).center := hw.symm.trans (hwd ▸ (D a).param_zero)
    exact disjoint_left.mp hna (mem_range_self z) (hc.symm ▸ mem_range_self a)
  exact ⟨⟨w, w.2, hw0⟩, hw⟩

end SurfaceDynamics.BKL

end

section

/-! # Small simply connected ambient neighbourhoods of wandering disc fillings -/

open Set Function Filter Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem disjoint_disc_fillings_eventually_in_simplyConnected_neighborhood
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] [NoncompactSpace X]
    (q : DiscCover X) {K : Set X} (hK : IsCompact K)
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    {r : ℝ} (hr1 : r < 1) :
    ∀ᶠ n in atTop, ∃ W : TopologicalSpace.Opens X,
      IsSimplyConnected (W : Set X) ∧
      compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ⊆ W := by
  choose D V hD hV hDV _ using fun x : K =>
    exists_nested_simplyConnected_coordNeighborhood isOpen_univ (mem_univ (x : X))
  have hcover : K ⊆ ⋃ x : K, range (D x).param := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, discZero, (D ⟨x, hx⟩).param_zero.trans (hD ⟨x, hx⟩)⟩
  have hh := q.disjoint_disc_images_eventually_in_cover hK F hF hcentre hdis
    (fun x : K => range (D x).param) (fun x => (D x).isOpenEmbedding_param.isOpen_range)
    hcover hr1
  filter_upwards [hh] with n hn
  obtain ⟨a, ha⟩ := hn
  refine ⟨V a, hV a, ?_⟩
  apply (compactFill_subset_coordDisk (D a) ?_).trans (hDV a)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨w, hw⟩ := ha z hz
  exact hw ▸ (D a).param_mem_closedCarrier w

end SurfaceDynamics.BKL

end

section

/-! # Holomorphic coverings in coordinates supplied by an open embedding -/

open Set Function Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

variable {M N X : Type*}
  [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem exists_holomorphic_covering_over_openEmbedding
    {f : M → X} {t : N → X}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t) (hte : IsOpenEmbedding t)
    (hc : IsCoveringMapOn f (range t)) :
    ∃ (V : TopologicalSpace.Opens M), (V : Set M) = f ⁻¹' range t ∧
      ∃ p : V → N, IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧
        t ∘ p = f ∘ (Subtype.val : V → M) := by
  let V : TopologicalSpace.Opens M := ⟨f ⁻¹' range t, hte.isOpen_range.preimage hf.continuous⟩
  let e : N ≃ₜ range t := hte.isEmbedding.toHomeomorph
  let P : V → range t := (range t).restrictPreimage f
  have hP : IsCoveringMap P := hc.isCoveringMap_restrictPreimage
  let p : V → N := e.symm ∘ P
  have hp : IsCoveringMap p := hP.homeomorph_comp e.symm
  have hfac : t ∘ p = f ∘ (Subtype.val : V → M) := by
    funext z
    have he := congrArg Subtype.val (e.apply_symm_apply (P z))
    exact he
  have hph : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p :=
    mdifferentiable_lift ht hte.isLocalHomeomorph hp.continuous
      (hfac.symm ▸ hf.comp (mdifferentiable_subtype_val V))
  exact ⟨V, rfl, p, hp, hph, hfac⟩

end SurfaceDynamics.BKL

end

section

/-! # Covering composition and components over plane domains

The source may be any locally connected Hausdorff space. This allows the
preimage of a local map's source in the ambient universal disc to be used.
-/

open Set Function Metric Topology
open FunctionTheory

namespace SurfaceDynamics.BKL

theorem coveringOn_comp_covering_to_plane
    {E Y : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace Y]
    {p : E → Y} {q : Y → ℂ} {U : Set ℂ}
    (hp : IsCoveringMap p) (hq : IsCoveringMapOn q U)
    (hqc : Continuous q) (hU : IsOpen U) :
    IsCoveringMapOn (q ∘ p) U := by
  have hc : Continuous (q ∘ p) := hqc.comp hp.continuous
  intro y hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU y hy
  let V := ball y r
  let : ContractibleSpace V := (convex_ball y r).contractibleSpace ⟨y, mem_ball_self hr⟩
  let : LocallyPathConnectedSpace V := isOpen_ball.locallyPathConnectedSpace
  have hl : IsLocalHomeomorphOn (q ∘ p) ((q ∘ p) ⁻¹' V) :=
    (hq.mono hball).isLocalHomeomorphOn.comp hp.isLocalHomeomorph.isLocalHomeomorphOn
      (fun _ hx => hx)
  apply isEvenlyCovered_of_sections (U := V) isOpen_ball hc hl _ (mem_ball_self hr)
  intro e he
  let v : C(V, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hq.existsUnique_continuousMap_lifts v
    (a₀ := ⟨q (p e), he⟩) (e₀ := p e) rfl (fun z => hball z.2)
  obtain ⟨t, ⟨ht₀, ht⟩, _⟩ := hp.existsUnique_continuousMap_lifts s
    (⟨q (p e), he⟩ : V) e hs₀.symm
  refine ⟨t, ?_, ?_⟩
  · intro z
    change q (p (t z)) = (z : ℂ)
    rw [show p (t z) = s z from congrFun ht z]
    exact congrFun hs z
  · intro _
    exact ht₀

theorem coveringOn_connectedComponentIn_to_plane
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyConnectedSpace E]
    {f : E → ℂ} {U : Set ℂ} (hf : Continuous f) (hU : IsOpen U)
    (hc : IsCoveringMapOn f U) (e₀ : E) :
    IsCoveringMapOn (fun z : connectedComponentIn (f ⁻¹' U) e₀ => f z) U := by
  let T := connectedComponentIn (f ⁻¹' U) e₀
  have hT : IsOpen T := (hU.preimage hf).connectedComponentIn
  let p : T → ℂ := fun z => f z
  have hpcont : Continuous p := hf.comp continuous_subtype_val
  have hplocal : IsLocalHomeomorph p :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
      hc.isLocalHomeomorphOn.comp hT.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun z _ => connectedComponentIn_subset (f ⁻¹' U) e₀ z.2)
  intro y hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU y hy
  let V := ball y r
  let : ContractibleSpace V := (convex_ball y r).contractibleSpace ⟨y, mem_ball_self hr⟩
  let : LocallyPathConnectedSpace V := isOpen_ball.locallyPathConnectedSpace
  apply isEvenlyCovered_of_sections (U := V) isOpen_ball hpcont
    (hplocal.isLocalHomeomorphOn.mono (subset_univ _)) _ (mem_ball_self hr)
  intro e he
  let q : C(V, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hc.existsUnique_continuousMap_lifts q
    (a₀ := ⟨f e, he⟩) (e₀ := (e : E)) rfl (fun v => hball v.2)
  have hsrange : range s ⊆ f ⁻¹' U := by
    rintro _ ⟨v, rfl⟩
    change f (s v) ∈ U
    rw [show f (s v) = (v : ℂ) from congrFun hs v]
    exact hball v.2
  have hsmem (v : V) : s v ∈ T := by
    have hsub := (isPreconnected_range s.continuous).subset_connectedComponentIn
      (show (e : E) ∈ range s from ⟨⟨f e, he⟩, hs₀⟩) hsrange
    have hv := hsub (mem_range_self v)
    rwa [← connectedComponentIn_eq e.2] at hv
  refine ⟨⟨fun v => ⟨s v, hsmem v⟩, s.continuous.subtype_mk hsmem⟩, ?_, ?_⟩
  · intro v
    exact congrFun hs v
  · intro _
    exact Subtype.ext hs₀

theorem covering_connectedComponentIn_to_plane
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyConnectedSpace E]
    {f : E → ℂ} {U : Set ℂ} (hf : Continuous f) (hU : IsOpen U)
    (hc : IsCoveringMapOn f U) (e₀ : E) :
    IsCoveringMap (fun z : connectedComponentIn (f ⁻¹' U) e₀ =>
      (⟨f z, connectedComponentIn_subset (f ⁻¹' U) e₀ z.2⟩ : U)) := by
  let T := connectedComponentIn (f ⁻¹' U) e₀
  let p : T → ℂ := fun z => f z
  let e : T ≃ₜ (p ⁻¹' U) :=
    { toFun := fun z => ⟨z, connectedComponentIn_subset (f ⁻¹' U) e₀ z.2⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  exact (coveringOn_connectedComponentIn_to_plane hf hU hc e₀).isCoveringMap_restrictPreimage.comp_homeomorph e

end SurfaceDynamics.BKL

end

section

/-! # Holomorphicity of covering equivalences

Topological covering classification supplies a homeomorphism over the base.
For holomorphic covers this homeomorphism and its inverse are holomorphic.
-/

open Function
open scoped Manifold

namespace SurfaceDynamics.BKL

variable {M N B : Type*}
  [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]
  [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) 1 B]

/-- A covering equivalence between holomorphic local homeomorphisms is
biholomorphic. -/
theorem mdifferentiable_cover_equivalence
    {p : M → B} {q : N → B}
    (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q)
    (hpl : IsLocalHomeomorph p) (hql : IsLocalHomeomorph q)
    (h : M ≃ₜ N) (he : q ∘ h = p) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h.symm := by
  refine ⟨AreaDeficit.Surfaces.mdifferentiable_lift hq hql h.continuous
    (he.symm ▸ hp), ?_⟩
  apply AreaDeficit.Surfaces.mdifferentiable_lift hp hpl h.symm.continuous
  have hei : p ∘ h.symm = q := by
    funext x
    rw [← he]
    exact congrArg q (h.apply_symm_apply x)
  exact hei.symm ▸ hq

end SurfaceDynamics.BKL

end

section

/-! # Connected covering components as open plane domains -/

open Set Function Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem covering_comp_puncturedDisc
    {E Y : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace Y]
    {p : E → Y} {q : Y → puncturedUnitDisc}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) :
    IsCoveringMap (q ∘ p) := by
  let f : Y → ℂ := Subtype.val ∘ q
  have hf : IsCoveringMapOn f puncturedUnitDisc := by
    intro z hz
    exact (IsEvenlyCovered.subtypeVal_comp (puncturedUnitDisc : Set ℂ)
      puncturedUnitDisc.isOpen (f := q) (hq ⟨z, hz⟩)).to_isEvenlyCovered_preimage
  have hc := coveringOn_comp_covering_to_plane hp hf
    (continuous_subtype_val.comp hq.continuous) puncturedUnitDisc.isOpen
  let e : E ≃ₜ ((f ∘ p) ⁻¹' (puncturedUnitDisc : Set ℂ)) :=
    { toFun := fun z => ⟨z, (q (p z)).2⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  exact hc.isCoveringMap_restrictPreimage.comp_homeomorph e

theorem covering_connectedComponent_puncturedDisc
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyConnectedSpace E]
    {p : E → puncturedUnitDisc} (hp : IsCoveringMap p) (e₀ : E) :
    IsCoveringMap (fun z : connectedComponent e₀ => p z) := by
  let f : E → ℂ := Subtype.val ∘ p
  have hf : Continuous f := continuous_subtype_val.comp hp.continuous
  have hc : IsCoveringMapOn f puncturedUnitDisc := by
    intro z hz
    exact (IsEvenlyCovered.subtypeVal_comp (puncturedUnitDisc : Set ℂ)
      puncturedUnitDisc.isOpen (f := p) (hp ⟨z, hz⟩)).to_isEvenlyCovered_preimage
  have hpre : f ⁻¹' (puncturedUnitDisc : Set ℂ) = univ :=
    eq_univ_of_forall (fun z => (p z).2)
  have heq : connectedComponentIn (f ⁻¹' (puncturedUnitDisc : Set ℂ)) e₀ =
      connectedComponent e₀ := by rw [hpre, connectedComponentIn_univ]
  have hh := (covering_connectedComponentIn_to_plane hf puncturedUnitDisc.isOpen hc e₀).comp_homeomorph
    (Homeomorph.setCongr heq.symm)
  exact hh

theorem exists_planar_connected_cover_component
    {E : Type*} [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) 1 E]
    {p : E → puncturedUnitDisc} (hp : IsCoveringMap p)
    (hph : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    {i : E → ℂ} (hi : IsOpenEmbedding i) (hih : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i)
    (e₀ : E) :
    ∃ (A : TopologicalSpace.Opens ℂ), (A : Set ℂ) = i '' connectedComponent e₀ ∧
      ConnectedSpace A ∧ ∃ (r : A → puncturedUnitDisc),
        IsCoveringMap r ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) r ∧
        ∀ z (_hz : z ∈ connectedComponent e₀),
          ∀ hzi : i z ∈ A, r ⟨i z, hzi⟩ = p z := by
  let : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace ℂ E
  let C : TopologicalSpace.Opens E := ⟨connectedComponent e₀, isOpen_connectedComponent⟩
  let A : TopologicalSpace.Opens ℂ := ⟨i '' (C : Set E), hi.isOpenMap _ C.isOpen⟩
  let e : C ≃ₜ A := hi.isEmbedding.homeomorphImage (C : Set E)
  let P : C → puncturedUnitDisc := p ∘ Subtype.val
  have hP : IsCoveringMap P := covering_connectedComponent_puncturedDisc hp e₀
  have hPh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := hph.comp (mdifferentiable_subtype_val C)
  have hiC : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e := by
    apply (mdifferentiable_subtypeVal_comp_iff A _).mp
    exact hih.comp (mdifferentiable_subtype_val C)
  have hihomeo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm := by
    apply mdifferentiable_lift hiC e.isLocalHomeomorph e.symm.continuous
    have he : (e : C → A) ∘ e.symm = id := funext e.apply_symm_apply
    rw [he]
    exact mdifferentiable_id
  let r : A → puncturedUnitDisc := P ∘ e.symm
  have hA : ConnectedSpace A :=
    Subtype.connectedSpace (isConnected_connectedComponent.image i hi.continuous.continuousOn)
  refine ⟨A, rfl, hA, r, hP.comp_homeomorph e.symm, hPh.comp hihomeo, ?_⟩
  intro z hz hzi
  have hh : (⟨i z, hzi⟩ : A) = e ⟨z, hz⟩ := rfl
  change P (e.symm ⟨i z, hzi⟩) = p z
  rw [hh, e.symm_apply_apply]
  rfl

end SurfaceDynamics.BKL

end

section

/-! # The full preimage of a regular punctured disc in the ambient universal cover -/

open Set Function Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

theorem exists_lifted_regular_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    (q : DiscCover X) {t : unitDisc → X}
    (ht : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) t) (hte : IsOpenEmbedding t)
    (hreg : ∀ z : puncturedUnitDisc, t ⟨z, z.2.1⟩ ∈ f.regularValues) :
    ∃ (B : TopologicalSpace.Opens unitDisc) (F : B → puncturedUnitDisc),
      IsCoveringMap F ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
      (∀ z : B, q.projection z ∈ f.source) ∧
      (∀ z : B, f.totalize (q.projection z) = t ⟨F z, (F z).2.1⟩) ∧
      (∀ z : unitDisc, q.projection z ∈ f.source →
        f.totalize (q.projection z) ∈ range (fun w : puncturedUnitDisc => t ⟨w, w.2.1⟩) →
        z ∈ B) := by
  let j : puncturedUnitDisc → unitDisc := fun z => ⟨z, z.2.1⟩
  have hjh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j :=
    (mdifferentiable_subtypeVal_comp_iff unitDisc j).mp
      (mdifferentiable_subtype_val puncturedUnitDisc)
  have hje : IsOpenEmbedding j := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap hjh.continuous
    · intro z w hzw
      exact Subtype.ext (congrArg (Subtype.val : unitDisc → ℂ) hzw)
    · exact puncturedUnitDisc.isOpen.isOpenMap_subtype_val.subtype_mk (fun z => z.2.1)
  let τ : puncturedUnitDisc → X := t ∘ j
  have hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ := ht.comp hjh
  have hτe : IsOpenEmbedding τ := hte.comp hje
  have hcov : IsCoveringMapOn f.map (range τ) := by
    apply f.isCoveringMapOn_compl_singularValues.mono
    rintro _ ⟨z, rfl⟩
    simpa only [LocalMap.singularValues, compl_compl, τ, j, comp_apply] using hreg z
  obtain ⟨V, hV, P, hP, hPh, hPfac⟩ :=
    exists_holomorphic_covering_over_openEmbedding hf hτ hτe hcov
  let i : V → X := (Subtype.val : f.source → X) ∘ (Subtype.val : V → f.source)
  have hi : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i :=
    (mdifferentiable_subtype_val f.source).comp (mdifferentiable_subtype_val V)
  have hie : IsOpenEmbedding i := f.source.isOpen.isOpenEmbedding_subtypeVal.comp
    V.isOpen.isOpenEmbedding_subtypeVal
  obtain ⟨B, hB, Q, hQ, hQh, hQfac⟩ :=
    exists_holomorphic_covering_over_openEmbedding q.holomorphic hi hie
      (fun z _ => q.covering z)
  let F : B → puncturedUnitDisc := P ∘ Q
  have hsrc (z : B) : q.projection z ∈ f.source := by
    have he := congrFun hQfac z
    change i (Q z) = q.projection z at he
    rw [← he]
    exact (Q z : f.source).2
  refine ⟨B, F, covering_comp_puncturedDisc hQ hP, hPh.comp hQh, hsrc, ?_, ?_⟩
  · intro z
    have hqz := congrFun hQfac z
    change i (Q z) = q.projection z at hqz
    rw [← hqz]
    change f.totalize ((Q z : f.source) : X) = _
    rw [f.totalize_eq (Q z : f.source).2]
    exact (congrFun hPfac (Q z)).symm
  · intro z hz htz
    change z ∈ (B : Set unitDisc)
    rw [hB]
    change q.projection z ∈ range i
    let x : f.source := ⟨q.projection z, hz⟩
    have hxV : x ∈ V := by
      change x ∈ (V : Set f.source)
      rw [hV]
      change f.map x ∈ range τ
      simpa only [τ, j, Function.comp_def, x, f.totalize_eq hz] using htz
    exact ⟨⟨x, hxV⟩, rfl⟩

end SurfaceDynamics.BKL

end

section

/-! # Connected coverings of a once-punctured disc

This is a coordinate form of the exterior-cover classification already proved
in the Eremenko--Lyubich development. The infinite case is simply connected;
the finite case is conjugate to a positive integral power.
-/

open Set Function
open scoped Topology
open EremenkoLyubichConstant ExteriorFundamentalGroup ExteriorPowerCover

namespace SurfaceDynamics.BKL

theorem simplyConnected_of_exterior_covering_subgroup_bot
    {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] {p : E → exponentialExterior 0}
    (hp : IsCoveringMap p) (e₀ : E)
    (hπ : (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range = ⊥) :
    SimplyConnectedSpace E := by
  let q := expCover 0
  have hq : IsCoveringMap q := isCoveringMap_exp_rightHalfPlane 0
  obtain ⟨w₀, hw₀⟩ := (isAddQuotientCoveringMap_expCover 0).surjective (p e₀)
  let : ContractibleSpace (rightHalfPlane 0) :=
    (show Convex ℝ (rightHalfPlane 0) from by
      simpa [rightHalfPlane] using convex_halfSpace_re_gt 0).contractibleSpace
      ⟨(1 : ℂ), by simp [rightHalfPlane]⟩
  let : LocallyPathConnectedSpace (rightHalfPlane 0) :=
    (isOpen_rightHalfPlane 0).locallyPathConnectedSpace
  have hqπ : (FundamentalGroup.map ⟨q, hq.continuous⟩ w₀).range = ⊥ := by
    apply le_antisymm _ bot_le
    rintro x ⟨a, rfl⟩
    rw [Subgroup.mem_bot, Subsingleton.elim a 1, map_one]
  obtain ⟨h, _, _⟩ := exists_homeomorph_of_covering_subgroups hp hq e₀ w₀ hw₀.symm
    (by rw [hπ]; exact bot_le) (by rw [hqπ]; exact bot_le)
  exact h.toHomotopyEquiv.simplyConnectedSpace

theorem puncturedDisc_covering_dichotomy
    {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] {p : E → puncturedUnitDisc}
    (hp : IsCoveringMap p) (e₀ : E) :
    SimplyConnectedSpace E ∨
      ∃ (d : ℕ), 0 < d ∧ ∃ h : E ≃ₜ puncturedUnitDisc,
        ∀ z, (p z : ℂ) = (h z : ℂ) ^ d := by
  let q := puncturedDiscExterior ∘ p
  have hq : IsCoveringMap q := hp.homeomorph_comp puncturedDiscExterior
  rcases exterior_covering_dichotomy hq e₀ with hπ | ⟨d, hd, e, he⟩
  · exact Or.inl (simplyConnected_of_exterior_covering_subgroup_bot hq e₀ hπ)
  · right
    let e' : E ≃ₜ exponentialExterior 0 := e.trans (.setCongr (by rw [zero_div]))
    let h : E ≃ₜ puncturedUnitDisc := e'.trans puncturedDiscExterior.symm
    refine ⟨d, hd, h, fun z => ?_⟩
    have hh : (e z : ℂ) ^ d = (p z : ℂ)⁻¹ :=
      congrArg Subtype.val (congrFun he z)
    change (p z : ℂ) = ((e z : ℂ)⁻¹) ^ d
    rw [inv_pow, hh, inv_inv]

end SurfaceDynamics.BKL

end

section

/-! # Holomorphic power coverings of the punctured unit disc -/

open Set Function Metric
open scoped Manifold Topology
open EremenkoLyubichConstant (exponentialExterior)
open EremenkoLyubichConstant.ExteriorPowerCover
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

noncomputable def discPower (d : ℕ) (hd : 0 < d) : unitDisc → unitDisc :=
  fun z => ⟨(z : ℂ) ^ d, by
    change (z : ℂ) ^ d ∈ ball 0 1
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hd.ne').mpr
      (mem_ball_zero_iff.mp z.2)⟩

theorem mdifferentiable_discPower (d : ℕ) (hd : 0 < d) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (discPower d hd) := by
  apply (mdifferentiable_subtypeVal_comp_iff unitDisc _).mp
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
    ((fun z : ℂ => z ^ d) ∘ (Subtype.val : unitDisc → ℂ))
  exact ((differentiable_id.pow d).mdifferentiable).comp
    (mdifferentiable_subtype_val unitDisc)

noncomputable def puncturedDiscPower (d : ℕ) (hd : 0 < d) :
    puncturedUnitDisc → puncturedUnitDisc :=
  puncturedDiscExterior.symm ∘ powerCover 0 d hd ∘
    (Homeomorph.setCongr (by rw [zero_div]) :
      exponentialExterior 0 ≃ₜ exponentialExterior (0 / d)) ∘ puncturedDiscExterior

@[simp] theorem puncturedDiscPower_coe (d : ℕ) (hd : 0 < d) (z : puncturedUnitDisc) :
    (puncturedDiscPower d hd z : ℂ) = (z : ℂ) ^ d := by
  change (((z : ℂ)⁻¹) ^ d)⁻¹ = (z : ℂ) ^ d
  rw [inv_pow, inv_inv]

theorem isCoveringMap_puncturedDiscPower (d : ℕ) (hd : 0 < d) :
    IsCoveringMap (puncturedDiscPower d hd) :=
  (((isCoveringMap_powerCover 0 d hd).comp_homeomorph
    (.setCongr (by rw [zero_div]))).comp_homeomorph puncturedDiscExterior).homeomorph_comp
      puncturedDiscExterior.symm

theorem mdifferentiable_puncturedDiscPower (d : ℕ) (hd : 0 < d) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (puncturedDiscPower d hd) := by
  apply (mdifferentiable_subtypeVal_comp_iff puncturedUnitDisc _).mp
  have he : Subtype.val ∘ puncturedDiscPower d hd =
      (fun z : ℂ => z ^ d) ∘ (Subtype.val : puncturedUnitDisc → ℂ) := by
    funext z
    exact puncturedDiscPower_coe d hd z
  rw [he]
  exact ((differentiable_id.pow d).mdifferentiable).comp
    (mdifferentiable_subtype_val puncturedUnitDisc)

end SurfaceDynamics.BKL

end

section

/-! # Filling a bounded injective punctured-disc parametrisation

The removable extension of a holomorphic embedding is again injective. The
inverse function on the punctured image rules out a collision at the centre.
-/

open Set Function Filter Metric Topology

namespace SurfaceDynamics.BKL

/-- A continuous extension at the puncture of a holomorphic injection cannot
identify the new centre with any old point. -/
theorem centre_ne_of_injective_punctured_extension
    {φ g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball 0 r \ {0}))
    (hi : InjOn φ (ball 0 r \ {0})) (hg : ContinuousAt g 0)
    (he : EqOn g φ (ball 0 r \ {0}))
    {y : ℂ} (hy : y ∈ ball 0 r \ {0}) : g 0 ≠ g y := by
  intro hgy
  let P : Set ℂ := ball 0 r \ {0}
  have hPo : IsOpen P := isOpen_ball.sdiff isClosed_singleton
  have hIo : IsOpen (φ '' P) :=
    TauCeti.isOpen_image_of_differentiableOn_of_injOn hPo hφ hi
  have hInv : ContinuousAt (invFunOn φ P) (φ y) :=
    ((hφ.invFunOn hPo hi).differentiableAt
      (hIo.mem_nhds (mem_image_of_mem φ hy))).continuousAt
  have hmem : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ P := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with z hz hz0
    exact ⟨hz, hz0⟩
  have hlim : Tendsto φ (𝓝[≠] 0) (𝓝 (φ y)) := by
    have hh : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) :=
      hg.tendsto.mono_left nhdsWithin_le_nhds
    have heq : g =ᶠ[𝓝[≠] 0] φ := hmem.mono (fun z hz => he hz)
    rw [hgy, he hy] at hh
    exact hh.congr' heq
  have hleft : (invFunOn φ P ∘ φ) =ᶠ[𝓝[≠] 0] id :=
    hmem.mono (fun z hz => hi.leftInvOn_invFunOn hz)
  have hreturn : Tendsto (invFunOn φ P ∘ φ) (𝓝[≠] 0) (𝓝 y) := by
    have hh := hInv.tendsto.comp hlim
    rwa [hi.leftInvOn_invFunOn hy] at hh
  have hy0 : y = 0 := tendsto_nhds_unique (hreturn.congr' hleft) nhdsWithin_le_nhds
  exact hy.2 hy0

/-- Bounded punctured-disc embeddings extend as holomorphic injections across
the puncture. -/
theorem exists_injective_holomorphic_extension
    {φ : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball 0 r \ {0}))
    (hi : InjOn φ (ball 0 r \ {0}))
    (hb : BddAbove (norm ∘ φ '' (ball 0 r \ {0}))) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 r) ∧ InjOn g (ball 0 r) ∧
      EqOn g φ (ball 0 r \ {0}) := by
  classical
  let g := update φ 0 (limUnder (𝓝[≠] 0) φ)
  have hg : DifferentiableOn ℂ g (ball 0 r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr) hφ hb
  have he : EqOn g φ (ball 0 r \ {0}) := fun z hz => update_of_ne hz.2 _ _
  have hcont : ContinuousAt g 0 :=
    (hg.differentiableAt (ball_mem_nhds 0 hr)).continuousAt
  refine ⟨g, hg, ?_, he⟩
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · subst x
    by_contra hy0
    exact centre_ne_of_injective_punctured_extension hr hφ hi hcont he
      ⟨hy, Ne.symm hy0⟩ hxy
  · by_cases hy0 : y = 0
    · subst y
      exact False.elim (centre_ne_of_injective_punctured_extension hr hφ hi hcont he
        ⟨hx, hx0⟩ hxy.symm)
    · apply hi ⟨hx, hx0⟩ ⟨hy, hy0⟩
      rwa [← he ⟨hx, hx0⟩, ← he ⟨hy, hy0⟩]

end SurfaceDynamics.BKL

end

section

/-! # Filling a punctured-disc embedding inside the universal disc

The new centre stays in the open unit disc: the extended image is open and
contained in the closed disc. Thus the ambient covering projection remains
defined at the new point.
-/

open Set Function Filter Metric Topology

namespace SurfaceDynamics.BKL

theorem exists_discValued_injective_holomorphic_extension
    {φ : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (ball 0 r \ {0}))
    (hi : InjOn φ (ball 0 r \ {0}))
    (hm : MapsTo φ (ball 0 r \ {0}) (ball 0 1)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 r) ∧ InjOn g (ball 0 r) ∧
      MapsTo g (ball 0 r) (ball 0 1) ∧ EqOn g φ (ball 0 r \ {0}) := by
  have hb : BddAbove (norm ∘ φ '' (ball 0 r \ {0})) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_ball_zero_iff.mp (hm hz)).le
  obtain ⟨g, hg, hgi, he⟩ := exists_injective_holomorphic_extension hr hφ hi hb
  have hmem : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 r \ {0} := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with z hz hz0
    exact ⟨hz, hz0⟩
  have hlim : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) :=
    (hg.differentiableAt (ball_mem_nhds 0 hr)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgc : MapsTo g (ball 0 r) (closedBall 0 1) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      apply isClosed_closedBall.mem_of_tendsto hlim
      filter_upwards [hmem] with w hw
      rw [he hw]
      exact ball_subset_closedBall (hm hw)
    · rw [he ⟨hz, hz0⟩]
      exact ball_subset_closedBall (hm ⟨hz, hz0⟩)
  have hgo : IsOpen (g '' ball 0 r) :=
    TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hg hgi
  refine ⟨g, hg, hgi, ?_, he⟩
  intro z hz
  have hh : g z ∈ interior (closedBall (0 : ℂ) 1) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (hgo.mem_nhds (mem_image_of_mem g hz)) hgc.image_subset)
  simpa only [interior_closedBall (0 : ℂ) one_ne_zero] using hh

end SurfaceDynamics.BKL

end

section

/-! # A bounded punctured-disc parameter fills to a simply connected domain -/

open Set Function Metric
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.BKL

theorem exists_simplyConnected_filling_of_punctured_parameter
    {A : Set ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (ball 0 1 \ {0}))
    (hi : InjOn φ (ball 0 1 \ {0}))
    (he : φ '' (ball 0 1 \ {0}) = A)
    (hA : A ⊆ ball 0 1) :
    ∃ (g : ℂ → ℂ) (a : ℂ),
      DifferentiableOn ℂ g (ball 0 1) ∧ InjOn g (ball 0 1) ∧
      MapsTo g (ball 0 1) (ball 0 1) ∧
      EqOn g φ (ball 0 1 \ {0}) ∧ g 0 = a ∧ a ∉ A ∧
      g '' ball 0 1 = insert a A ∧ IsOpen (insert a A) ∧
      IsSimplyConnected (insert a A) := by
  have hm : MapsTo φ (ball 0 1 \ {0}) (ball 0 1) := by
    intro z hz
    exact hA (he ▸ mem_image_of_mem φ hz)
  obtain ⟨g, hg, hgi, hgm, hge⟩ :=
    exists_discValued_injective_holomorphic_extension zero_lt_one hφ hi hm
  have h0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have ha : g 0 ∉ A := by
    rw [← he]
    rintro ⟨z, hz, hz0⟩
    have hh : g z = g 0 := (hge hz).trans hz0
    exact hz.2 (hgi hz.1 h0 hh)
  have him : g '' ball 0 1 = insert (g 0) A := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      by_cases hz0 : z = 0
      · exact Or.inl (congrArg g hz0)
      · right
        rw [hge ⟨hz, hz0⟩, ← he]
        exact mem_image_of_mem φ ⟨hz, hz0⟩
    · rintro z (rfl | hz)
      · exact mem_image_of_mem g h0
      · rw [← he] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact ⟨w, hw.1, hge hw⟩
  refine ⟨g, g 0, hg, hgi, hgm, hge, rfl, ha, him, ?_, ?_⟩
  · rw [← him]
    exact TauCeti.isOpen_image_of_differentiableOn_of_injOn isOpen_ball hg hgi
  · rw [← him]
    apply TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn isOpen_ball _ hg hgi
    let : ContractibleSpace (ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, h0⟩
    exact (inferInstance : SimplyConnectedSpace (ball (0 : ℂ) 1))

end SurfaceDynamics.BKL

end

section

/-! # Filling finite covering components inside the universal disc -/

open Set Function Metric
open scoped Manifold Topology
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

structure FilledPuncturedCover (A : TopologicalSpace.Opens ℂ)
    (p : A → puncturedUnitDisc) where
  degree : ℕ
  degree_pos : 0 < degree
  parameter : puncturedUnitDisc ≃ₜ A
  map_parameter : ∀ z, (p (parameter z) : ℂ) = (z : ℂ) ^ degree
  extension : ℂ → ℂ
  holomorphic : DifferentiableOn ℂ extension (ball 0 1)
  injective : InjOn extension (ball 0 1)
  mapsTo : MapsTo extension (ball 0 1) (ball 0 1)
  agrees : ∀ z : puncturedUnitDisc, extension z = (parameter z : ℂ)
  centre_not_mem : extension 0 ∉ A
  image_eq : extension '' ball 0 1 = insert (extension 0) (A : Set ℂ)
  open_filling : IsOpen (insert (extension 0) (A : Set ℂ))
  simplyConnected_filling : IsSimplyConnected (insert (extension 0) (A : Set ℂ))

theorem simplyConnected_or_filledPuncturedCover
    (A : TopologicalSpace.Opens ℂ) [ConnectedSpace A]
    {p : A → puncturedUnitDisc} (hp : IsCoveringMap p)
    (hph : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hA : (A : Set ℂ) ⊆ ball 0 1) :
    IsSimplyConnected (A : Set ℂ) ∨ Nonempty (FilledPuncturedCover A p) := by
  let : LocallyPathConnectedSpace A := A.isOpen.locallyPathConnectedSpace
  let : PathConnectedSpace A := PathConnectedSpace.of_locallyPathConnectedSpace
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  rcases puncturedDisc_covering_dichotomy hp a₀ with hsc | ⟨d, hd, h, hh⟩
  · exact Or.inl hsc
  · right
    have he : puncturedDiscPower d hd ∘ h = p := by
      funext z
      apply Subtype.ext
      exact (puncturedDiscPower_coe d hd (h z)).trans (hh z).symm
    have hhol := mdifferentiable_cover_equivalence hph
      (mdifferentiable_puncturedDiscPower d hd) hp.isLocalHomeomorph
      (isCoveringMap_puncturedDiscPower d hd).isLocalHomeomorph h he
    let φ : ℂ → ℂ := planeExtension ((Subtype.val : A → ℂ) ∘ h.symm)
    have hφeq (z : puncturedUnitDisc) : φ z = (h.symm z : ℂ) := planeExtension_coe _ z
    have hφ : DifferentiableOn ℂ φ (ball 0 1 \ {0}) :=
      planeExtension_differentiableOn ((mdifferentiable_subtype_val A).comp hhol.2)
    have hi : InjOn φ (ball 0 1 \ {0}) := by
      intro x hx y hy hxy
      have hs : h.symm ⟨x, hx⟩ = h.symm ⟨y, hy⟩ := by
        apply Subtype.ext
        exact (hφeq ⟨x, hx⟩).symm.trans (hxy.trans (hφeq ⟨y, hy⟩))
      exact congrArg Subtype.val (h.symm.injective hs)
    have him : φ '' (ball 0 1 \ {0}) = (A : Set ℂ) := by
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        rw [hφeq ⟨z, hz⟩]
        exact (h.symm ⟨z, hz⟩).2
      · intro z hz
        refine ⟨h ⟨z, hz⟩, (h ⟨z, hz⟩).2, ?_⟩
        exact (hφeq _).trans (congrArg Subtype.val (h.symm_apply_apply ⟨z, hz⟩))
    obtain ⟨g, a, hg, hgi, hgm, hge, hga, ha, himg, hgo, hgsc⟩ :=
      exists_simplyConnected_filling_of_punctured_parameter hφ hi him hA
    subst a
    refine ⟨{
      degree := d
      degree_pos := hd
      parameter := h.symm
      map_parameter := ?_
      extension := g
      holomorphic := hg
      injective := hgi
      mapsTo := hgm
      agrees := fun z => (hge z.2).trans (hφeq z)
      centre_not_mem := ha
      image_eq := himg
      open_filling := hgo
      simplyConnected_filling := hgsc }⟩
    intro z
    simpa only [h.apply_symm_apply] using hh (h.symm z)

end SurfaceDynamics.BKL

end
