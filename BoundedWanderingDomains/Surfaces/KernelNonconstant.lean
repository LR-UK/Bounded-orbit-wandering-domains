module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.LiftedPunctureClosure

@[expose] public section

/-! # Derivatives of normalized extremal lifts -/

open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- The extremal identity downstairs transfers to a derivative identity
upstairs, in the fixed ambient covering disc. -/
theorem extremal_ambient_lift_derivative (p : DiscCover M)
    {U : TopologicalSpace.Opens M} (r : DiscCover U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : U} (hx : (x : M) ∈ c.source) (w : unitDisc)
    (hw : p.projection w = (x : M))
    (g : unitDisc → U) (_hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (_hg0 : g discZero = x)
    (hscale : r.density (c.subtypeRestr ⟨x⟩) x *
      ‖deriv (planeExtension ((c.subtypeRestr ⟨x⟩) ∘ g)) (0 : ℂ)‖ = 2)
    (h : unitDisc → unitDisc) (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h)
    (hh0 : h discZero = w)
    (hfac : p.projection ∘ h = (Subtype.val : U → M) ∘ g) :
    r.density (c.subtypeRestr ⟨x⟩) x *
      (‖deriv (planeExtension (c ∘ p.projection)) w‖ *
        ‖deriv (planeExtension (fun v => (h v : ℂ))) (0 : ℂ)‖) = 2 := by
  have hxw : p.projection w ∈ c.source := hw ▸ hx
  have hp := ((hc _ hxw).mdifferentiableAt (c.open_source.mem_nhds hxw)).comp w
    (p.holomorphic w)
  have hd := planeExtension_deriv_comp (g := c ∘ p.projection) (h := h)
    (w := discZero) (hh0.symm ▸ hp) (hh discZero)
  rw [hh0] at hd
  have hd0 := hd
  simp only [show (discZero : ℂ) = 0 from rfl] at hd0
  have he : (c.subtypeRestr ⟨x⟩) ∘ g = (c ∘ p.projection) ∘ h := by
    funext v
    simp only [Function.comp_apply]
    change c (g v : M) = c (p.projection (h v))
    rw [show p.projection (h v) = (g v : M) from congrFun hfac v]
  rw [he,hd0,norm_mul] at hscale
  exact hscale

end AreaDeficit.Surfaces.DiscCover

namespace AreaDeficit.Surfaces

/-- Uniformly bounded extremal densities prevent the normal limit of
normalized ambient lifts from collapsing to a constant. -/
theorem extremal_lift_limit_deriv_ne_zero
    (h : ℕ → unitDisc → unitDisc)
    (hh : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h n))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {φ : ℕ → ℕ} {g : ℂ → ℂ}
    (hl : TendstoLocallyUniformlyOn
      (fun n => planeExtension (fun v => (h (φ n) v : ℂ))) g atTop (ball 0 r))
    (a : ℕ → ℝ) (B C : ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ B) (hC : 0 ≤ C)
    (hscale : ∀ n, a n * (C *
      ‖deriv (planeExtension (fun v => (h n v : ℂ))) 0‖) = 2) :
    deriv g 0 ≠ 0 := by
  have hzero : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have hdiff : ∀ n, DifferentiableOn ℂ
      (planeExtension (fun v => (h (φ n) v : ℂ))) (ball 0 r) := by
    intro n
    exact (planeExtension_differentiableOn
      ((mdifferentiable_subtype_val unitDisc).comp (hh (φ n)))).mono
        (ball_subset_ball hr1)
  have hd := (hl.deriv (Eventually.of_forall hdiff) isOpen_ball).tendsto_at hzero
  have hdn : Tendsto (fun n => ‖deriv
      (planeExtension (fun v => (h (φ n) v : ℂ))) 0‖)
      atTop (𝓝 ‖deriv g 0‖) := hd.norm
  have hineq (n : ℕ) : 2 ≤ B * C * ‖deriv
      (planeExtension (fun v => (h (φ n) v : ℂ))) 0‖ := by
    have hn := hscale (φ n)
    have ha' := ha (φ n)
    have hnonneg : 0 ≤ C * ‖deriv
        (planeExtension (fun v => (h (φ n) v : ℂ))) 0‖ :=
      mul_nonneg hC (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right ha'.2 hnonneg]
  have hlim : 2 ≤ B * C * ‖deriv g 0‖ :=
    ge_of_tendsto ((tendsto_const_nhds : Tendsto (fun _ : ℕ => B * C)
      atTop (𝓝 (B * C))).mul hdn)
      (Eventually.of_forall (fun n => by simpa using hineq n))
  intro he
  simp [he] at hlim
  norm_num at hlim

end AreaDeficit.Surfaces

namespace AreaDeficit.Surfaces

/-- The derivative criterion supplies the precise nonconstancy hypothesis
needed for the lifted Hurwitz argument. -/
theorem normal_limit_nonconstant
    {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hder : deriv g 0 ≠ 0) :
    ¬ ∃ c, ∀ z ∈ ball (0 : ℂ) r, g z = c := by
  rintro ⟨c,hc⟩
  have he : g =ᶠ[𝓝 0] fun _ => c :=
    Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) hr) (fun z hz => hc z hz)
  have hzero : deriv g 0 = 0 := by rw [he.deriv_eq]; simp
  exact hder hzero

end AreaDeficit.Surfaces
