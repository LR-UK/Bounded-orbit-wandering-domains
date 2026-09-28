/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.BKL.AnalyticCompletion
import BoundedWanderingDomains.Surfaces.LocalMapRestriction
import BoundedWanderingDomains.Surfaces.BKL.ReturnLimits
import BoundedWanderingDomains.Surfaces.OmegaDynamics
import BoundedWanderingDomains.Surfaces.FiniteFibers
import Mathlib.Order.Filter.Cofinite
import BoundedWanderingDomains.Surfaces.LocalCoveringDiscs

section

/-! # Relating the original map to its dense completion by source restriction -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

theorem isNormalOn_mono
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (f : LocalMap X) {A B : Set X} (hAB : A ⊆ B) (hn : f.IsNormalOn B) :
    f.IsNormalOn A := by
  let : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1
  intro φ hφ
  obtain ⟨ψ, hψ, g, hg⟩ := hn φ hφ
  let i : A → B := fun x => ⟨x, hAB x.2⟩
  exact ⟨ψ, hψ, g ∘ i, hg.comp i (continuous_subtype_val.subtype_mk _)⟩

theorem isNormalOn_restrictSource_of_trapped
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (f : LocalMap X) (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
    {W : Set X} (hW : W ⊆ (f.restrictSource V hV).trapped)
    (hn : f.IsNormalOn W) : (f.restrictSource V hV).IsNormalOn W := by
  intro φ hφ
  obtain ⟨ψ, hψ, g, hg⟩ := hn φ hφ
  refine ⟨ψ, hψ, g, ?_⟩
  have heq : (fun n (z : W) =>
      (f.restrictSource V hV).compactifiedIterate (φ (ψ n)) z) =
      (fun n (z : W) => f.compactifiedIterate (φ (ψ n)) z) := by
    funext n z
    unfold compactifiedIterate
    rw [f.restrictSource_iterate_eq_of_restricted_trapped V hV (hW z.property)]
  rw [heq]
  exact hg

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

theorem denseCompletion_restrictSource_eq (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) :
    f.denseCompletion.restrictSource f.source (f.source_subset_denseCompletionSource hf) = f := by
  change LocalMap.mk f.source _ = LocalMap.mk f.source _
  congr 1
  funext x
  exact f.denseCompletionExtension.agrees x (f.source_subset_denseCompletionSource hf x.2) x.2

theorem omega_subset_denseCompletion [LocallyCompactSpace X] (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) : f.omega ⊆ f.denseCompletion.omega := by
  have hh := f.denseCompletion.restrictSource_omega_subset f.source
    (f.source_subset_denseCompletionSource hf)
  rwa [f.denseCompletion_restrictSource_eq hf] at hh

theorem denseCompletion_totalize_eq (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) {x : X} (hx : x ∈ f.source) :
    f.denseCompletion.totalize x = f.totalize x := by
  rw [f.denseCompletion.totalize_eq (f.source_subset_denseCompletionSource hf hx),
    f.totalize_eq hx]
  exact f.denseCompletionExtension.agrees x (f.source_subset_denseCompletionSource hf hx) hx

theorem mem_trapped_of_denseCompletion_stays (f : LocalMap X)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map) {x : X}
    (hstay : ∀ n, (f.denseCompletion.totalize^[n]) x ∈ f.source) : x ∈ f.trapped := by
  have hst : ∀ n, (f.denseCompletion.totalize^[n]) x ∈ f.denseCompletion.source :=
    fun n => f.source_subset_denseCompletionSource hf (hstay n)
  have htr : x ∈ f.denseCompletion.trapped :=
    f.denseCompletion.trappedSet_totalize_eq_trapped ▸ hst
  have hh := f.denseCompletion.restrictSource_mem_trapped_of_orbit_mem f.source
    (f.source_subset_denseCompletionSource hf) htr (fun n => by
      rw [← f.denseCompletion.totalize_iterate_orbit n ⟨x, htr⟩]
      exact hstay n)
  rwa [f.denseCompletion_restrictSource_eq hf] at hh

theorem isNormalOn_of_denseCompletion [LocallyCompactSpace X]
    (f : LocalMap X) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.map)
    {W : Set X} (hW : W ⊆ f.trapped) (hn : f.denseCompletion.IsNormalOn W) :
    f.IsNormalOn W := by
  have hWr : W ⊆ (f.denseCompletion.restrictSource f.source
      (f.source_subset_denseCompletionSource hf)).trapped := by
    rwa [f.denseCompletion_restrictSource_eq hf]
  have hh := f.denseCompletion.isNormalOn_restrictSource_of_trapped f.source
    (f.source_subset_denseCompletionSource hf) hWr hn
  rwa [f.denseCompletion_restrictSource_eq hf] at hh

end SurfaceDynamics.LocalMap

end

section

/-! # Removing a locally isolated set from a connected surface domain -/

open Set Function Filter Topology

namespace SurfaceDynamics.BKL

theorem isOpen_isConnected_diff_of_locally_isolated
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] (W : TopologicalSpace.Opens X) (hWc : IsConnected (W : Set X))
    {B : Set X} (hiso : ∀ x ∈ (W : Set X), ∀ᶠ y in 𝓝 x, y ∈ B → y = x)
    (hne : ((W : Set X) \ B).Nonempty) :
    IsOpen ((W : Set X) \ B) ∧ IsConnected ((W : Set X) \ B) := by
  let : LocallyCompactSpace W := W.isOpen.locallyCompactSpace
  let : ConnectedSpace W := Subtype.connectedSpace hWc
  let B' : Set W := Subtype.val ⁻¹' B
  have hno : ∀ x : W, ¬ AccPt x (𝓟 B') := by
    intro x
    apply not_accPt_of_eventually_eq_of_mem
    filter_upwards [continuous_subtype_val.continuousAt.eventually (hiso x x.2)]
      with y hy hyB
    exact Subtype.ext (hy hyB)
  have hc : IsClosed B' := isClosed_iff_accPt.mpr (fun x hx => False.elim (hno x hx))
  have hd : IsDiscrete B' := isDiscrete_iff_discreteTopology.mpr
    (discreteTopology_of_noAccPts (fun x _ => hno x))
  have hne' : B'ᶜ.Nonempty := by
    obtain ⟨x, hxW, hxB⟩ := hne
    exact ⟨⟨x, hxW⟩, hxB⟩
  have he : (Subtype.val : W → X) '' B'ᶜ = (W : Set X) \ B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxW, hxB⟩
      exact ⟨⟨x, hxW⟩, hxB, rfl⟩
  rw [← he]
  exact ⟨W.isOpen.isOpenMap_subtype_val _ hc.isOpen_compl,
    (isConnected_compl_of_closed_discrete hc hd hne').image _
      continuous_subtype_val.continuousOn⟩

end SurfaceDynamics.BKL

end

section

/-! # Recovering original normality components after filling removable points -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem mem_trapped_of_completed_orbit_avoids_singular_set
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {E : Set X} {x : X}
    (hstay : ∀ n, (f.denseCompletion.totalize^[n]) x ∈ f.denseCompletion.source)
    (hcontrol : ∀ n, (f.denseCompletion.totalize^[n]) x ∈ f.singularValues →
      (f.denseCompletion.totalize^[n]) x ∈ E)
    (havoid : ¬ ∃ n, (f.denseCompletion.totalize^[n]) x ∈ E) : x ∈ f.trapped := by
  apply f.mem_trapped_of_denseCompletion_stays hf.2
  intro n
  by_contra ho
  have hs := f.added_image_mem_singularValues hf
    ⟨(f.denseCompletion.totalize^[n]) x, hstay n⟩ ho
  rw [← f.denseCompletion.totalize_eq (hstay n),
    ← Function.iterate_succ_apply' f.denseCompletion.totalize n x] at hs
  exact havoid ⟨n + 1, hcontrol (n + 1) hs⟩

theorem good_completed_region_subset_original_component
    (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (W : TopologicalSpace.Opens X) (hWc : IsConnected (W : Set X))
    (hWnormal : f.denseCompletion.IsNormalOn W) {E : Set X}
    (hiso : ∀ x ∈ (W : Set X), ∀ᶠ y in 𝓝 x,
      (∃ n, (f.denseCompletion.totalize^[n]) y ∈ E) → y = x)
    (hstay : ∀ x ∈ (W : Set X), ∀ n,
      (f.denseCompletion.totalize^[n]) x ∈ f.denseCompletion.source)
    (hcontrol : ∀ x ∈ (W : Set X), ∀ n,
      (f.denseCompletion.totalize^[n]) x ∈ f.singularValues →
        (f.denseCompletion.totalize^[n]) x ∈ E)
    {a : X} (haW : a ∈ W) (haE : ¬ ∃ n, (f.denseCompletion.totalize^[n]) a ∈ E) :
    (W : Set X) \ {x | ∃ n, (f.denseCompletion.totalize^[n]) x ∈ E} ⊆
      connectedComponentIn f.omega a := by
  let A := (W : Set X) \ {x | ∃ n, (f.denseCompletion.totalize^[n]) x ∈ E}
  have haA : a ∈ A := ⟨haW, haE⟩
  obtain ⟨hAo, hAc⟩ := BKL.isOpen_isConnected_diff_of_locally_isolated W hWc hiso ⟨a, haA⟩
  have hAtr : A ⊆ f.trapped := by
    intro x hx
    exact f.mem_trapped_of_completed_orbit_avoids_singular_set hf
      (hstay x hx.1) (hcontrol x hx.1) hx.2
  have hn : f.IsNormalOn A := f.isNormalOn_of_denseCompletion hf.2 hAtr
    (f.denseCompletion.isNormalOn_mono sdiff_subset hWnormal)
  have hAn : A ⊆ f.omega := fun x hx => ⟨A, hAo, hx, hAtr, hn⟩
  exact hAc.isPreconnected.subset_connectedComponentIn haA hAn

end SurfaceDynamics.LocalMap

end

section

/-! # A local map as a global map on its normality locus

This is the bridge for applying global iterate lemmas to a locally defined
map. Every point of the normality locus has all iterates in the source.
-/

open Set Function
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

def normalitySource (f : LocalMap X) : TopologicalSpace.Opens X :=
  ⟨f.omega, f.isOpen_omega⟩

variable [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

noncomputable def normalitySelfMap (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    f.normalitySource → f.normalitySource :=
  fun x => ⟨f.totalize x, f.totalize_mapsTo_omega hf x.property⟩

theorem mdifferentiable_normalitySelfMap (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f.normalitySelfMap hf) := by
  apply (mdifferentiable_subtypeVal_comp_iff f.normalitySource (f.normalitySelfMap hf)).mp
  intro x
  have hxs := f.omega_subset_source x.property
  exact ((f.mdifferentiableOn_totalize hf.2 x hxs).mdifferentiableAt
    (f.source.isOpen.mem_nhds hxs)).comp x (mdifferentiable_subtype_val f.normalitySource x)

theorem isOpenMap_normalitySelfMap (f : LocalMap X) (hf : IsOpenHolomorphic f) :
    IsOpenMap (f.normalitySelfMap hf) := by
  let i : f.normalitySource → f.source := fun x => ⟨x, f.omega_subset_source x.property⟩
  have hi : IsOpenMap i :=
    f.normalitySource.isOpen.isOpenMap_subtype_val.subtype_mk
      (fun x => f.omega_subset_source x.property)
  have hmap : ∀ x : f.normalitySource, f.map (i x) ∈ f.normalitySource := by
    intro x
    rw [← f.totalize_eq (f.omega_subset_source x.property)]
    exact f.totalize_mapsTo_omega hf x.property
  have ho : IsOpenMap (fun x : f.normalitySource =>
      (⟨f.map (i x), hmap x⟩ : f.normalitySource)) := (hf.1.comp hi).subtype_mk hmap
  have he : f.normalitySelfMap hf = (fun x : f.normalitySource =>
      (⟨f.map (i x), hmap x⟩ : f.normalitySource)) := by
    funext x
    apply Subtype.ext
    exact f.totalize_eq (f.omega_subset_source x.property)
  rwa [he]

theorem normalitySelfMap_iterate_val (f : LocalMap X) (hf : IsOpenHolomorphic f)
    (n : ℕ) (x : f.normalitySource) :
    (((f.normalitySelfMap hf)^[n]) x : X) = (f.totalize^[n]) (x : X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply', iterate_succ_apply']
      exact congrArg f.totalize ih

end SurfaceDynamics.LocalMap

end

section

/-! # Backward orbits of a local map in a constant-limit normality region -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

theorem eventually_eq_of_finite_backwardOrbit_constant_limits
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [UniformSpace Y] [T2Space Y]
    {f : X → X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hfo : IsOpenMap f)
    {j : X → Y} (hj : IsOpenEmbedding j) {U : Set X} (hU : IsOpen U)
    (hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : Y,
        TendstoLocallyUniformlyOn (fun n z => j ((f^[times (ψ n)]) z))
          (fun _ => b) atTop U)
    {E : Set X} (hE : E.Finite) {x : X} (hx : x ∈ U) :
    ∀ᶠ z in 𝓝 x, (∃ n : ℕ, (f^[n]) z ∈ E) → z = x := by
  have hall : ∀ a ∈ E, ∀ᶠ z in 𝓝 x,
      (∃ n : ℕ, (f^[n]) z = a) → z = x := fun a _ =>
    eventually_eq_of_mem_of_not_accPt
      (not_accPt_backwardOrbit_of_constant_limits hf hfo hj hU hlim a hx)
  filter_upwards [(hE.eventually_all).mpr hall] with z hz hzn
  obtain ⟨n, hn⟩ := hzn
  exact hz ((f^[n]) z) hn ⟨n, rfl⟩

end SurfaceDynamics.BKL

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

local instance : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1

theorem eventually_eq_of_finite_backwardOrbit_constant_limits
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {U : Set X} (hU : IsOpen U)
    (hUn : U ⊆ f.omega)
    (hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : OnePoint X,
        TendstoLocallyUniformlyOn (fun n z => ((f.totalize^[times (ψ n)]) z : OnePoint X))
          (fun _ => b) atTop U)
    {E : Set X} (hE : E.Finite) {x : X} (hx : x ∈ U) :
    ∀ᶠ z in 𝓝 x, (∃ n : ℕ, (f.totalize^[n]) z ∈ E) → z = x := by
  let : LocallyCompactSpace f.normalitySource := f.normalitySource.isOpen.locallyCompactSpace
  let : FirstCountableTopology f.normalitySource := TopologicalSpace.Subtype.firstCountableTopology _
  let U' : Set f.normalitySource := Subtype.val ⁻¹' U
  let j : f.normalitySource → OnePoint X := fun z => ((z : X) : OnePoint X)
  have hj : IsOpenEmbedding j :=
    OnePoint.isOpenEmbedding_coe.comp f.normalitySource.isOpen.isOpenEmbedding_subtypeVal
  have hlim' : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : OnePoint X,
        TendstoLocallyUniformlyOn (fun n z => j (((f.normalitySelfMap hf)^[times (ψ n)]) z))
          (fun _ => b) atTop U' := by
    intro times ht
    obtain ⟨ψ, hψ, b, hb⟩ := hlim times ht
    refine ⟨ψ, hψ, b, ?_⟩
    have hh := hb.comp (t := U') (Subtype.val : f.normalitySource → X) (fun _ hz => hz)
      continuous_subtype_val.continuousOn
    simpa [j, U', Function.comp_def, f.normalitySelfMap_iterate_val] using hh
  have hh := BKL.eventually_eq_of_finite_backwardOrbit_constant_limits
    (f.mdifferentiable_normalitySelfMap hf) (f.isOpenMap_normalitySelfMap hf) hj
    (hU.preimage continuous_subtype_val) hlim'
    (hE.preimage (f := (Subtype.val : f.normalitySource → X)) Subtype.val_injective.injOn)
    (show (⟨x, hUn hx⟩ : f.normalitySource) ∈ U' from hx)
  rw [← f.normalitySource.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hUn hx⟩]
  change ∀ᶠ z : f.normalitySource in 𝓝 ⟨x, hUn hx⟩,
    (∃ n : ℕ, (f.totalize^[n]) (z : X) ∈ E) → (z : X) = x
  filter_upwards [hh] with z hz hzn
  apply congrArg Subtype.val (hz ?_)
  obtain ⟨n, hn⟩ := hzn
  refine ⟨n, ?_⟩
  change (((f.normalitySelfMap hf)^[n]) z : X) ∈ E
  rwa [f.normalitySelfMap_iterate_val]

end SurfaceDynamics.LocalMap

end

section

/-! # Discrete fibres and punctures of disjoint surface domains

These lemmas isolate two ingredients of removable-point filling. They do not
assert that the normality locus is preserved by an arbitrary extension.
-/

open Set Filter Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

section Fibres

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-- Points over a finite collection of values form a discrete subset. -/
theorem isDiscrete_preimage_finite [T1Space Y] {f : X → Y}
    (ho : IsOpenMap f) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {E : Set Y} (hE : E.Finite) : IsDiscrete (f ⁻¹' E) := by
  exact hE.isDiscrete.preimage' hf.continuous.continuousOn
    (fun y => isDiscrete_fiber_of_isOpenMap_of_mdifferentiable ho hf y)

/-- Any collection of added points whose images lie in a fixed finite set is
discrete, without a global discreteness assumption on all added points. -/
theorem isDiscrete_of_mapsTo_finite [T1Space Y] {f : X → Y}
    (ho : IsOpenMap f) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {A : Set X} {E : Set Y} (hE : E.Finite) (hA : MapsTo f A E) :
    IsDiscrete A :=
  (isDiscrete_preimage_finite ho hf hE).mono hA

/-- The full inverse image of the finite set meets a compact set finitely. -/
theorem finite_compact_inter_preimage [T2Space Y] {f : X → Y}
    (ho : IsOpenMap f) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {E : Set Y} (hE : E.Finite) {K : Set X} (hK : IsCompact K) :
    (K ∩ f ⁻¹' E).Finite :=
  (hK.inter_right (hE.isClosed.preimage hf.continuous)).finite
    ((isDiscrete_preimage_finite ho hf hE).mono inter_subset_right)

end Fibres

section Punctures

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A puncture is a missing point with a whole punctured neighborhood in the set. -/
def IsPuncture (U : Set X) (e : X) : Prop :=
  e ∉ U ∧ ∃ V : Set X, IsOpen V ∧ e ∈ V ∧ V \ {e} ⊆ U

/-- A point cannot be a puncture of two disjoint surface domains. -/
theorem not_isPuncture_of_disjoint {U V : Set X} (hUV : Disjoint U V)
    {e : X} (hU : IsPuncture U e) : ¬ IsPuncture V e := by
  rintro ⟨_, B, hBo, heB, hBU⟩
  obtain ⟨_, A, hAo, heA, hAU⟩ := hU
  have heq : A ∩ B = {e} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxe
      exact disjoint_left.mp hUV (hAU ⟨hx.1, hxe⟩) (hBU ⟨hx.2, hxe⟩)
    · exact singleton_subset_iff.mpr ⟨heA, heB⟩
  have hopen : IsOpen ({e} : Set X) := heq ▸ hAo.inter hBo
  have himage := (chartAt ℂ e).isOpen_image_of_subset_source hopen
    (singleton_subset_iff.mpr (mem_chart_source ℂ e))
  rw [image_singleton] at himage
  exact not_isOpen_singleton (chartAt ℂ e e) himage

/-- Pairwise disjoint domains eventually have no puncture in a given finite set. -/
theorem eventually_no_puncture_in_finite (U : ℕ → Set X)
    (hdis : Pairwise (fun n m => Disjoint (U n) (U m)))
    {E : Set X} (hE : E.Finite) :
    ∀ᶠ n in atTop, ∀ e ∈ E, ¬ IsPuncture (U n) e := by
  have hone : ∀ e : X, {n : ℕ | IsPuncture (U n) e}.Subsingleton := by
    intro e n hn m hm
    by_contra hnm
    exact not_isPuncture_of_disjoint (hdis hnm) hn hm
  have hbad : {n : ℕ | ∃ e ∈ E, IsPuncture (U n) e}.Finite := by
    have hh := hE.biUnion (fun e _ => (hone e).finite)
    exact hh.subset (by
      rintro n ⟨e, he, hp⟩
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he, hp⟩⟩)
  have hh := hbad.eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at hh
  exact hh.mono (fun n hn e he hp => hn ⟨e, he, hp⟩)

end Punctures

end SurfaceDynamics.BKL

end

section

/-! # A discrete exceptional backward orbit produces a puncture downstream -/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.BKL

theorem iterate_mapsTo_forward_sets
    {X : Type*} {g : X → X} {U : ℕ → Set X}
    (hnext : ∀ n, MapsTo g (U n) (U (n + 1))) (n k : ℕ) :
    MapsTo (g^[k]) (U n) (U (n + k)) := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      simpa only [Nat.add_succ, iterate_succ_apply'] using hnext (n + k) ih

theorem isPuncture_of_isolated_backwardOrbit_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : X → X} {U : ℕ → Set X}
    (hnext : ∀ n, MapsTo g (U n) (U (n + 1)))
    {E W : Set X} {n k : ℕ} {x e : X}
    (hgo : ∀ j V, V ⊆ W → IsOpen V → IsOpen ((g^[j]) '' V))
    (hW : IsOpen W) (hxW : x ∈ W)
    (hgood : W \ {y | ∃ j : ℕ, (g^[j]) y ∈ E} ⊆ U n)
    (hiso : ∀ᶠ y in 𝓝 x, (∃ j : ℕ, (g^[j]) y ∈ E) → y = x)
    (hxe : (g^[k]) x = e) (heU : e ∉ U (n + k)) :
    IsPuncture (U (n + k)) e := by
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.mp hiso
  refine ⟨heU, (g^[k]) '' (W ∩ O), hgo k _ inter_subset_left (hW.inter hOo),
    ⟨x, ⟨hxW, hxO⟩, hxe⟩, ?_⟩
  rintro y ⟨⟨z, ⟨hzW, hzO⟩, rfl⟩, hye⟩
  apply iterate_mapsTo_forward_sets hnext n k
  apply hgood
  refine ⟨hzW, ?_⟩
  intro hzbad
  exact hye ((congrArg (g^[k]) (hO hzO hzbad)).trans hxe)

theorem subset_forward_domain_of_no_downstream_punctures
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : X → X} {U : ℕ → Set X}
    (hnext : ∀ n, MapsTo g (U n) (U (n + 1)))
    {E W : Set X} {n : ℕ}
    (hgo : ∀ j V, V ⊆ W → IsOpen V → IsOpen ((g^[j]) '' V)) (hW : IsOpen W)
    (hgood : W \ {y | ∃ j : ℕ, (g^[j]) y ∈ E} ⊆ U n)
    (hiso : ∀ x ∈ W, ∀ᶠ y in 𝓝 x,
      (∃ j : ℕ, (g^[j]) y ∈ E) → y = x)
    (havoid : ∀ k, Disjoint (U (n + k)) E)
    (hnopunct : ∀ k e, e ∈ E → ¬ IsPuncture (U (n + k)) e) :
    W ⊆ U n := by
  intro x hx
  by_cases hbad : ∃ k : ℕ, (g^[k]) x ∈ E
  · obtain ⟨k, hk⟩ := hbad
    exact False.elim (hnopunct k _ hk
      (isPuncture_of_isolated_backwardOrbit_point hnext hgo hW hx hgood
        (hiso x hx) rfl (fun hu => disjoint_left.mp (havoid k) hu hk)))
  · exact hgood ⟨hx, hbad⟩

end SurfaceDynamics.BKL

end

section

/-! # Iterates of a local open map are open on its normality locus -/

open Set Function Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

theorem isOpen_image_totalize_iterate
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) {V : Set X}
    (hV : IsOpen V) (hVn : V ⊆ f.omega) (k : ℕ) :
    IsOpen ((f.totalize^[k]) '' V) := by
  have hiter : ∀ n, MapsTo (f.totalize^[n]) V f.omega := by
    intro n x hx
    induction n with
    | zero => exact hVn hx
    | succ n ih =>
        rw [iterate_succ_apply']
        exact f.totalize_mapsTo_omega hf ih
  induction k with
  | zero => simpa using hV
  | succ k ih =>
      have he : (f.totalize^[k + 1]) '' V = f.totalize '' ((f.totalize^[k]) '' V) := by
        rw [← image_comp, iterate_succ']
      rw [he]
      exact f.isOpen_image_totalize hf.1 ih
        ((hiter k).image_subset.trans f.omega_subset_source)

end SurfaceDynamics.LocalMap

end

section

/-! # A completed filling belongs to the original wandering component

The finite exceptional values cannot puncture any downstream domain. Local
isolation of their backward orbits then removes every possible added point.
-/

open Set Function Filter Topology
open scoped Manifold

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

local instance : UniformSpace (OnePoint X) := uniformSpaceOfCompactR1

theorem completed_region_subset_original_component
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (U : ℕ → Set X)
    (hUs : ∀ j, U j ⊆ f.source) (hnext : ∀ j, MapsTo f.totalize (U j) (U (j + 1)))
    (W : TopologicalSpace.Opens X) (hWc : IsConnected (W : Set X))
    (hWn : (W : Set X) ⊆ f.denseCompletion.omega)
    (hWnormal : f.denseCompletion.IsNormalOn W)
    (hlim : ∀ times : ℕ → ℕ, StrictMono times →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ b : OnePoint X,
        TendstoLocallyUniformlyOn
          (fun n z => ((f.denseCompletion.totalize^[times (ψ n)]) z : OnePoint X))
          (fun _ => b) atTop W)
    {E : Set X} (hE : E.Finite)
    (hstay : ∀ x ∈ (W : Set X), ∀ k,
      (f.denseCompletion.totalize^[k]) x ∈ f.denseCompletion.source)
    (hcontrol : ∀ x ∈ (W : Set X), ∀ k,
      (f.denseCompletion.totalize^[k]) x ∈ f.singularValues →
        (f.denseCompletion.totalize^[k]) x ∈ E)
    {n : ℕ} {a : X} (haW : a ∈ W) (haU : a ∈ U n)
    (hUeq : U n = connectedComponentIn f.omega a)
    (havoid : ∀ k, Disjoint (U (n + k)) E)
    (hnopunct : ∀ k e, e ∈ E → ¬ BKL.IsPuncture (U (n + k)) e) :
    (W : Set X) ⊆ U n := by
  have hg := f.isOpenHolomorphic_denseCompletion hf
  have hnextg : ∀ j, MapsTo f.denseCompletion.totalize (U j) (U (j + 1)) := by
    intro j x hx
    rw [f.denseCompletion_totalize_eq hf.2 (hUs j hx)]
    exact hnext j hx
  have haE : ¬ ∃ k, (f.denseCompletion.totalize^[k]) a ∈ E := by
    rintro ⟨k, hk⟩
    exact disjoint_left.mp (havoid k) (BKL.iterate_mapsTo_forward_sets hnextg n k haU) hk
  have hiso : ∀ x ∈ (W : Set X), ∀ᶠ y in 𝓝 x,
      (∃ k, (f.denseCompletion.totalize^[k]) y ∈ E) → y = x := fun _ hx =>
    f.denseCompletion.eventually_eq_of_finite_backwardOrbit_constant_limits hg W.isOpen
      hWn hlim hE hx
  have hgood := f.good_completed_region_subset_original_component hf W hWc hWnormal
    hiso hstay hcontrol haW haE
  rw [← hUeq] at hgood
  exact BKL.subset_forward_domain_of_no_downstream_punctures hnextg
    (fun j V hVW hVo => f.denseCompletion.isOpen_image_totalize_iterate hg hVo
      (hVW.trans hWn) j) W.isOpen hgood hiso havoid hnopunct

end SurfaceDynamics.LocalMap

end
