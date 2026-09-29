module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ComponentFilling
public import BoundedWanderingDomains.Surfaces.SingularEncounters.ShrinkingFillings

@[expose] public section

/-! # The componentwise BKL criterion

A compact piece of a wandering covering disc lies in a source restriction
regular over a punctured target disc. The singular values of that restriction
in the larger closed target disc belong to one fixed finite exceptional set.
These hypotheses imply that late compact fillings stay in the original
wandering domains, even when global derived singular values are nearby.
-/

open Set Function Filter Metric Topology
open scoped Manifold
open AreaDeficit.Surfaces

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Local covering data around a compact source piece. Regularity refers to
the visited restriction, and the finite set will be shared by all late pieces. -/
def HasComponentPuncturedDisc (f : LocalMap X) (E A : Set X) : Prop :=
  ∃ (V : TopologicalSpace.Opens X) (hV : (V : Set X) ⊆ f.source)
      (D : RiemannDynamics.CoordDisk X),
    A ⊆ V ∧
    MapsTo f.totalize A (range (fun w : BKL.puncturedUnitDisc => D.param ⟨w, w.2.1⟩)) ∧
    (∀ z : BKL.puncturedUnitDisc,
      D.param ⟨z, z.2.1⟩ ∈ (f.restrictSource V hV).regularValues) ∧
    (f.restrictSource V hV).singularValues ∩ D.closedCarrier ⊆ E

end SurfaceDynamics.LocalMap

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] [NoncompactSpace X]

theorem disjoint_disc_fillings_eventually_controlled_by_restrictions
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : DiscCover X)
    {K : Set X} (hK : IsCompact K)
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    {E : Set X} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hlocal : ∀ᶠ n in atTop,
      f.HasComponentPuncturedDisc E (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})) :
    ∀ᶠ n in atTop,
      compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ⊆ f.denseCompletion.source ∧
      ∀ x ∈ compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}),
        x ∉ f.source → f.denseCompletion.totalize x ∈ E := by
  have hsmall := disjoint_disc_fillings_eventually_in_simplyConnected_neighborhood
    q hK F hF hcentre hdis hr1
  filter_upwards [hlocal, hsmall] with n hn hs
  obtain ⟨V, hV, D, hAV, himage, hreg, hS⟩ := hn
  obtain ⟨W, hW, hAW⟩ := hs
  let : SimplyConnectedSpace W := hW
  exact compactFill_restricted_source_and_added_images f hf q V hV D hreg hS
    ((unitDisc_closed_radius_compact hr1).image (hF n).continuous)
    ((unitDisc_closed_radius_connected hr hr1).image _ (hF n).continuous.continuousOn)
    hAV himage W hAW

variable [FirstCountableTopology X]

theorem disjoint_disc_fillings_eventually_subset_component_of_restricted_covers
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (q : DiscCover X)
    {K : Set X} (hK : IsCompact K)
    (F : ℕ → unitDisc → X) (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hFo : ∀ n, IsOpenMap (F n)) (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    (hsource : ∀ n, range (F n) ⊆ f.source)
    (hcomp : ∀ n, range (F n) = connectedComponentIn f.omega (F n discZero))
    (hnext : ∀ n, MapsTo f.totalize (range (F n)) (range (F (n + 1))))
    (hnextDisc : ∀ r : ℝ, ∀ n,
      MapsTo f.totalize (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r})
        (F (n + 1) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}))
    {E : Set X} (hE : E.Finite)
    (hlocal : ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ᶠ n in atTop,
      f.HasComponentPuncturedDisc E (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R}))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ⊆ range (F n) := by
  have hcontrol := fun R hR hR1 =>
    disjoint_disc_fillings_eventually_controlled_by_restrictions f hf q hK F hF hcentre hdis
      hR hR1 (hlocal R hR hR1)
  exact disjoint_disc_fillings_eventually_subset_component_of_added_images f hf q hK
    F hF hFo hcentre hdis hsource hcomp hnext hnextDisc hE
    (fun R hR hR1 => (hcontrol R hR hR1).mono fun _ h => h.1)
    (fun R hR hR1 => (hcontrol R hR hR1).mono fun _ h => h.2) hr hr1

theorem eventually_injective_centered_covers_of_restricted_covers
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [ConnectedSpace X] [NoncompactSpace X]
    (f : LocalMap X) (hf : IsOpenHolomorphic f) (p : DiscCover X)
    (U : ℕ → TopologicalSpace.Opens X) (q : ∀ n, DiscCover (U n))
    (hU : ∀ n, f.IsComponent (U n))
    (hdis : Pairwise (fun n m => Disjoint (U n : Set X) (U m)))
    (hforward : ∀ n, MapsTo f.totalize (U n) (U (n + 1)))
    (h0 : ∀ n, ((q (n + 1)).projection discZero : X) = f.totalize ((q n).projection discZero))
    {K : Set X} (hK : IsCompact K)
    (hcentre : ∀ n, ((q n).projection discZero : X) ∈ K)
    {E : Set X} (hE : E.Finite)
    (hlocal : ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ᶠ n in atTop,
      f.HasComponentPuncturedDisc E
        ((fun z => ((q n).projection z : X)) '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R}))
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
  have hfill := disjoint_disc_fillings_eventually_subset_component_of_restricted_covers f hf p hK
    F hF hFo hcentre hFdis (fun n => (hFU n).symm ▸ hUs n) hFcomp hnext hnextDisc hE hlocal hr.le hr1
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
