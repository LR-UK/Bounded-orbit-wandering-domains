/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.GainFatou
import BoundedWanderingDomains.Surfaces.HolomorphicLifting
import BoundedWanderingDomains.Surfaces.SubtypeHolomorphic
import BoundedWanderingDomains.Surfaces.ExtremalDisc
import BoundedWanderingDomains.NormalFamilies

/-! # Lifting varying subdomain covers to one fixed ambient disc -/

open Set Function Filter
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- Every holomorphic covering disc of an open subdomain lifts
holomorphically to the one fixed ambient disc. This puts all members of a
puncture exhaustion in the same bounded target for normal-family arguments. -/
theorem exists_ambient_disc_lift (p : DiscCover M)
    {U : TopologicalSpace.Opens M} (r : DiscCover U) :
    ∃ h : unitDisc → unitDisc,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h ∧
      p.projection ∘ h = (Subtype.val : U → M) ∘ r.projection := by
  let g : unitDisc → M := (Subtype.val : U → M) ∘ r.projection
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
    (mdifferentiable_subtype_val U).comp r.holomorphic
  obtain ⟨w,hw⟩ := p.surjective (g discZero)
  let : LocallyPathConnectedSpace unitDisc :=
    ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  obtain ⟨h,_,hfac,hh⟩ := exists_holomorphic_lift
    p.holomorphic p.covering hg discZero w hw
  exact ⟨h,hh,hfac⟩

end AreaDeficit.Surfaces.DiscCover

open Metric
open scoped Topology
namespace AreaDeficit.Surfaces

/-- A sequence of lifts to the fixed ambient disc admits a locally uniform
holomorphic subsequential limit on every smaller disc. -/
theorem ambient_disc_lifts_normal_subdisc
    (h : ℕ → unitDisc → unitDisc)
    (hh : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h n))
    {r : ℝ} (_hr : 0 < r) (hr1 : r < 1) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn
        (fun n => planeExtension (fun z => (h (φ n) z : ℂ))) g atTop (ball 0 r) ∧
      DifferentiableOn ℂ g (ball 0 r) := by
  let f : ℕ → ℂ → ℂ := fun n => planeExtension (fun z => (h n z : ℂ))
  change ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
    TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop (ball 0 r) ∧
    DifferentiableOn ℂ g (ball 0 r)
  apply AreaDeficit.bounded_holomorphic_subsequence (f := f) (M := 1) isOpen_ball
  · intro n
    exact (planeExtension_differentiableOn
      ((mdifferentiable_subtype_val unitDisc).comp (hh n))).mono
        (ball_subset_ball hr1.le)
  · intro n z hz
    have hz1 : z ∈ ball (0 : ℂ) 1 := (ball_subset_ball hr1.le) hz
    change ‖planeExtension (fun v => (h n v : ℂ)) z‖ ≤ 1
    rw [show planeExtension (fun v => (h n v : ℂ)) z =
      (h n ⟨z,hz1⟩ : ℂ) from planeExtension_coe _ ⟨z,hz1⟩]
    exact le_of_lt (mem_ball_zero_iff.mp (h n ⟨z,hz1⟩).2)

end AreaDeficit.Surfaces

namespace AreaDeficit.Surfaces

/-- A limit of lifts with a fixed interior centre still maps a sufficiently
small source disc into the ambient disc. -/
theorem normal_lift_limit_maps_small_disc
    (h : ℕ → unitDisc → unitDisc)
    (hh : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h n))
    (w : unitDisc) (h0 : ∀ n, h n discZero = w)
    {r : ℝ} (hr1 : r < 1) (hrsmall : ‖(w : ℂ)‖ + 2 * r < 1)
    (φ : ℕ → ℕ) (g : ℂ → ℂ)
    (hl : TendstoLocallyUniformlyOn
      (fun n => planeExtension (fun z => (h (φ n) z : ℂ))) g atTop (ball 0 r)) :
    ∀ z ∈ ball (0 : ℂ) r, g z ∈ ball (0 : ℂ) 1 := by
  intro z hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := (ball_subset_ball hr1.le) hz
  have hb (n : ℕ) : ‖planeExtension (fun v => (h (φ n) v : ℂ)) z‖ ≤
      ‖(w : ℂ)‖ + 2 * ‖z‖ := by
    have hd := unitDisc_displacement (hh (φ n)) ⟨z,hz1⟩
    rw [h0 (φ n)] at hd
    have hdist : ‖(h (φ n) ⟨z,hz1⟩ : ℂ) - (w : ℂ)‖ ≤ 2 * ‖z‖ := by
      simpa only [Subtype.dist_eq,dist_eq_norm] using hd
    rw [show planeExtension (fun v => (h (φ n) v : ℂ)) z =
      (h (φ n) ⟨z,hz1⟩ : ℂ) from planeExtension_coe _ ⟨z,hz1⟩]
    calc
      ‖(h (φ n) ⟨z,hz1⟩ : ℂ)‖ =
          ‖((h (φ n) ⟨z,hz1⟩ : ℂ) - w) + w‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖(h (φ n) ⟨z,hz1⟩ : ℂ) - w‖ + ‖(w : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖(w : ℂ)‖ + 2 * ‖z‖ := by linarith
  have hlim := (hl.tendsto_at hz).norm
  have hbound : ‖g z‖ ≤ ‖(w : ℂ)‖ + 2 * ‖z‖ :=
    le_of_tendsto hlim (Filter.Eventually.of_forall hb)
  exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hbound (by
    have hzlt : ‖z‖ < r := mem_ball_zero_iff.mp hz
    linarith))

end AreaDeficit.Surfaces

namespace AreaDeficit.Surfaces

/-- Normalised lifts have subsequential limits retaining the same centre. -/
theorem ambient_disc_lifts_normal_at_centre
    (h : ℕ → unitDisc → unitDisc)
    (hh : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h n))
    (w : unitDisc) (h0 : ∀ n, h n discZero = w)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn
        (fun n => planeExtension (fun z => (h (φ n) z : ℂ))) g atTop (ball 0 r) ∧
      DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = (w : ℂ) := by
  obtain ⟨φ,g,hφ,hl,hgd⟩ := ambient_disc_lifts_normal_subdisc h hh hr hr1
  refine ⟨φ,g,hφ,hl,hgd,?_⟩
  have hzero : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have ht := hl.tendsto_at hzero
  have heq : (fun n => planeExtension (fun z => (h (φ n) z : ℂ)) 0) =
      fun _ => (w : ℂ) := by
    funext n
    simp only [show (0 : ℂ) = (discZero : ℂ) from rfl,
      planeExtension_coe,h0 (φ n)]
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end AreaDeficit.Surfaces

namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The density-realising disc for any subdomain can be lifted with a
prescribed fixed ambient centre. This is the normalised input for kernel
convergence in a varying sequence of open subdomains. -/
theorem density_extremal_ambient_lift (p : DiscCover M)
    {U : TopologicalSpace.Opens M} (r : DiscCover U)
    {c : OpenPartialHomeomorph U ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : U} (hx : x ∈ c.source) (w : unitDisc)
    (hw : p.projection w = (x : M)) :
    ∃ g : unitDisc → U,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ g discZero = x ∧
      r.density c x * ‖deriv (planeExtension (c ∘ g)) (0 : ℂ)‖ = 2 ∧
      ∃ h : unitDisc → unitDisc,
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h ∧ h discZero = w ∧
        p.projection ∘ h = (Subtype.val : U → M) ∘ g := by
  obtain ⟨g,hg,hg0,hscale⟩ := r.density_extremal_disc hc hx
  let G : unitDisc → M := (Subtype.val : U → M) ∘ g
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G :=
    (mdifferentiable_subtype_val U).comp hg
  have hw' : p.projection w = G discZero := by
    simpa only [G,comp_apply,hg0] using hw
  let : LocallyPathConnectedSpace unitDisc :=
    ChartedSpace.locallyPathConnectedSpace ℂ unitDisc
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  obtain ⟨h,h0,hfac,hh⟩ := exists_holomorphic_lift
    p.holomorphic p.covering hG discZero w hw'
  exact ⟨g,hg,hg0,hscale,h,hh,h0,hfac⟩

end AreaDeficit.Surfaces.DiscCover
