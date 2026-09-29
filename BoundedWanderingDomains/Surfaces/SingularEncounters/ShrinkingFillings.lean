module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.SingularEncounters.CompletionRecovery
public import BoundedWanderingDomains.Surfaces.BKL.ShrinkingFillings

@[expose] public section

/-! # Recovering shrinking fillings with componentwise exceptional values

Only the images of added points are controlled by the finite set E. The compact
set containing the centres is allowed to meet the derived global singular set.
-/

open Set Function Filter Metric Topology
open scoped Manifold Uniformity
open AreaDeficit.Surfaces

namespace SurfaceDynamics.BKL

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [FirstCountableTopology X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] [NoncompactSpace X]

local instance singularFillingsUniformSpace : UniformSpace (OnePoint X) :=
  uniformSpaceOfCompactR1

theorem disjoint_disc_fillings_eventually_subset_component_of_added_images
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
    (hfilled : ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ᶠ n in atTop,
      compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R}) ⊆ f.denseCompletion.source)
    (hadded : ∀ R : ℝ, 0 ≤ R → R < 1 → ∀ᶠ n in atTop,
      ∀ x ∈ compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R}),
        x ∉ f.source → f.denseCompletion.totalize x ∈ E)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∀ᶠ n in atTop, compactFill (F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ r}) ⊆ range (F n) := by
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  have hR : 0 ≤ R := hr.trans hrR.le
  let C : ℕ → Set X := fun n => F n '' {z : unitDisc | ‖(z : ℂ)‖ ≤ R}
  have hC : ∀ n, IsCompact (C n) := fun n =>
    (unitDisc_closed_radius_compact hR1).image (hF n).continuous
  have hevent : ∀ᶠ n in atTop, compactFill (C n) ⊆ f.denseCompletion.source ∧
      (∀ x ∈ compactFill (C n), x ∉ f.source → f.denseCompletion.totalize x ∈ E) ∧
      Disjoint (range (F n)) E ∧ ∀ e ∈ E, ¬ IsPuncture (range (F n)) e := by
    filter_upwards [hfilled R hR hR1, hadded R hR hR1,
      AreaDeficit.eventually_disjoint_finite hdis hE,
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
  apply f.completed_region_subset_component_of_added_images hf (fun j => range (F j))
    hsource hnext W hWc hWn hWnormal hlim hE
    (fun x hx k hs => ?_) haW (mem_range_self discZero) (hcomp n)
    (fun k => (hN (n + k) (hn.trans (Nat.le_add_right n k))).2.2.1)
    (fun k => (hN (n + k) (hn.trans (Nat.le_add_right n k))).2.2.2)
  rw [iterate_succ_apply']
  exact (hN (n + k) (hn.trans (Nat.le_add_right n k))).2.1 _ (horbit x hx k) hs

end SurfaceDynamics.BKL
