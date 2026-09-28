/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.ConditionalDiscShrink
import BoundedWanderingDomains.Surfaces.PointedCoveringDiscs
import BoundedWanderingDomains.Surfaces.LocalCompactModelPatches
import BoundedWanderingDomains.TrappedComponentCovering

/-! # Eventual injectivity from compact local covering models -/

open Set Function Filter Topology
open AreaDeficit.Surfaces
open scoped Manifold Topology

namespace SurfaceDynamics.LocalMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [DecidableEq X]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- Shrinking, eventually simply connected forward discs eventually lie
on individual sheets of the finitely many compact local covering models. -/
theorem eventually_injOn_wandering_discs
    (p : DiscCover X) (f : LocalMap X) (hf : IsOpenHolomorphic f)
    {K : Set X} (hK : IsCompact K) (hKsource : K ⊆ f.source)
    (F : ℕ → unitDisc → X)
    (hF : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F n))
    (hcentre : ∀ n, F n discZero ∈ K)
    (hdis : Pairwise (fun n m => Disjoint (range (F n)) (range (F m))))
    (hnext : ∀ n, f.totalize (F n discZero) = F (n + 1) discZero)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hopen : ∀ n, IsOpen (F n '' {z : unitDisc | ‖(z : ℂ)‖ < r}))
    (hforward : ∀ n, MapsTo f.totalize
      (F n '' {z : unitDisc | ‖(z : ℂ)‖ < r})
      (F (n + 1) '' {z : unitDisc | ‖(z : ℂ)‖ < r}))
    (hsc : ∀ᶠ n in atTop, IsSimplyConnected
      (F n '' {z : unitDisc | ‖(z : ℂ)‖ < r})) :
    ∀ᶠ n in atTop, InjOn f.totalize (F n '' {z : unitDisc | ‖(z : ℂ)‖ < r}) := by
  classical
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have hpatch : ∀ x : K, ∃ Ks L N : Set X,
      IsCompact Ks ∧ Ks ⊆ f.source ∧ IsCompact L ∧ Ks ⊆ f.source ∧
      IsOpen N ∧ (x : X) ∈ N ∧ N ⊆ interior Ks ∧
      f.totalize '' N ⊆ L ∧ Disjoint L (f.map '' frontier (f.sourceCompact Ks)) := by
    intro x
    exact f.exists_local_compact_model_patch hf f.source
      ⟨x, hKsource x.property⟩ (hKsource x.property)
  choose Ks L N hKs hKssource hL _ hNo hxN hNKs hfNL hsep using hpatch
  have hcoverK : K ⊆ ⋃ x : K, N x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
  obtain ⟨I, hcover⟩ := hK.elim_finite_subcover N hNo hcoverK
  let ι := {x : K // x ∈ I}
  have hcover' : K ⊆ ⋃ i : ι, N i.val := by
    intro x hx
    obtain ⟨a, ha, hxN⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hxN⟩
  have hmodel := fun i : ι =>
    f.exists_finite_branch_values_local_compact_covering hf (hKs i.val) (hKssource i.val)
  choose E hH hcov using hmodel
  let H : ι → Set X := fun i => f.map '' frontier (f.sourceCompact (Ks i.val))
  let Etot : Set X := ⋃ i : ι, (E i : Set X)
  have hEtot : Etot.Finite := Set.finite_iUnion fun i => (E i).finite_toSet
  have havoidE : ∀ᶠ n in atTop, Disjoint (range (F (n + 1))) Etot :=
    (Filter.tendsto_add_atTop_nat 1).eventually
      (AreaDeficit.eventually_disjoint_finite hdis hEtot)
  have havoidH : ∀ᶠ n in atTop, ∀ i : ι, F (n + 1) discZero ∈ L i.val →
      ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → F (n + 1) z ∉ H i := by
    have hh := (Filter.eventually_all_finite Set.finite_univ).2 (fun i _ =>
      p.eventually_avoids_closed_of_centre hK (hL i.val).isClosed
        (hH i).isClosed (hsep i.val) F hF hcentre hdis hr.le hr1)
    have hh' : ∀ᶠ n in atTop, ∀ i : ι, F n discZero ∈ L i.val →
        ∀ z : unitDisc, ‖(z : ℂ)‖ ≤ r → F n z ∉ H i := by
      simpa only [mem_univ, forall_true_left] using hh
    exact (Filter.tendsto_add_atTop_nat 1).eventually hh'
  have hshrink := p.disjoint_disc_images_eventually_in_cover hK F hF hcentre hdis
    (fun i : ι => N i.val) (fun i => hNo i.val) hcover' hr1
  have hscnext := (Filter.tendsto_add_atTop_nat 1).eventually hsc
  filter_upwards [hshrink, havoidE, havoidH, hsc, hscnext] with n hn hnE hnH hnsc hnsc'
  obtain ⟨i, hi⟩ := hn
  let D : Set X := F n '' {z : unitDisc | ‖(z : ℂ)‖ < r}
  let S : TopologicalSpace.Opens X := ⟨F (n + 1) '' {z : unitDisc | ‖(z : ℂ)‖ < r}, hopen _⟩
  have hDN : D ⊆ N i.val := by
    rintro x ⟨z, hz, rfl⟩
    exact hi z (le_of_lt hz)
  have hcentreL : F (n + 1) discZero ∈ L i.val := by
    rw [← hnext n]
    exact hfNL i.val ⟨F n discZero,
      hi discZero (by change ‖(0 : ℂ)‖ ≤ r; simpa using hr.le), rfl⟩
  have hSE : (S : Set X) ⊆ (E i : Set X)ᶜ := by
    rintro y ⟨z, hz, rfl⟩ hyE
    exact disjoint_left.mp hnE (mem_range_self z) (mem_iUnion.mpr ⟨i, hyE⟩)
  have hSH : (S : Set X) ⊆ (H i)ᶜ := by
    rintro y ⟨z, hz, rfl⟩
    exact hnH i hcentreL z (le_of_lt hz)
  obtain ⟨g, hg, hgcov, hge⟩ := hcov i S hSE hSH
  let Q := f.localCompactCoverDomain (Ks i.val) S hf.2.continuous
  have hDQ : D ⊆ Q := by
    intro x hx
    apply f.mem_localCompactCoverDomain_of_mem_interior S hf.2.continuous (hKssource i.val)
      (hNKs i.val (hDN hx))
    rw [← f.totalize_eq]
    exact hforward n hx
  let D' : Set Q := Subtype.val ⁻¹' D
  have heq : (Subtype.val : Q → X) '' D' = D :=
    image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hDQ hx⟩, rfl⟩)
  have hD'sc : IsSimplyConnected D' := by
    apply (Topology.IsEmbedding.subtypeVal (p := fun x : X => x ∈ Q)).isSimplyConnected_image.mp
    rw [heq]
    exact hnsc
  let : LocallyPathConnectedSpace Q := Q.isOpen.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace S := S.isOpen.locallyPathConnectedSpace
  let : SimplyConnectedSpace S := hnsc'
  have hSuniv : IsSimplyConnected (univ : Set S) :=
    (Homeomorph.Set.univ S).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨a, ha⟩ := hnsc.nonempty
  have hinj : InjOn g D' := covering_injOn_simplyConnected
    ((hopen n).preimage continuous_subtype_val) hD'sc isOpen_univ hSuniv
    (a := ⟨a, hDQ ha⟩) ha hg.continuous.continuousOn
    (fun _ _ => mem_univ _) hgcov.isCoveringMapOn
  intro x hx y hy hxy
  have hgxy : g ⟨x, hDQ hx⟩ = g ⟨y, hDQ hy⟩ := by
    apply Subtype.ext
    rw [← congrFun hge ⟨x, hDQ hx⟩, ← congrFun hge ⟨y, hDQ hy⟩]
    exact hxy
  exact congrArg Subtype.val (hinj hx hy hgxy)

end SurfaceDynamics.LocalMap
