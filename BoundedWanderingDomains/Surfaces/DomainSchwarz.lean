module

/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
public import BoundedWanderingDomains.Surfaces.ComponentDensity
public import BoundedWanderingDomains.Surfaces.DiscDilation

@[expose] public section

/-! # Schwarz comparison and extremal discs for disconnected open domains -/
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem domainDensity_mono (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : V} (hx : (x : M) ∈ c.source) :
    p.domainDensity U c ⟨(x : M), hVU x.property⟩ ≤ p.domainDensity V c x := by
  dsimp only [domainDensity]
  exact density_nested_subdomains (componentDomain_mono hVU (x : M))
    (p.componentCover U ⟨(x : M),hVU x.property⟩) (p.componentCover V x)
    ⟨componentPoint U ⟨(x : M),hVU x.property⟩⟩ ⟨componentPoint V x⟩ hc
    (x := componentPoint V x) (show (componentPoint V x : M) ∈ c.source from hx)

theorem domainDensity_extremal_disc (p : DiscCover M)
    (U : TopologicalSpace.Opens M) {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : U} (hx : (x : M) ∈ c.source) :
    ∃ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧
      g discZero = (x : M) ∧ (∀ v, g v ∈ U) ∧
      p.domainDensity U c x * ‖deriv (planeExtension (c ∘ g)) 0‖ = 2 := by
  let q := p.componentCover U x
  let y := componentPoint U x
  have hy : y ∈ (c.subtypeRestr ⟨y⟩).source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, y, componentPoint] using hx
  obtain ⟨G,hG,hG0,he⟩ := q.density_extremal_disc (mdifferentiableOn_subtypeRestr ⟨y⟩ hc) hy
  refine ⟨Subtype.val ∘ G, (mdifferentiable_subtype_val _).comp hG, ?_, ?_, he⟩
  · exact congrArg Subtype.val hG0
  · intro v
    exact componentDomain_le U (x : M) (G v).property

theorem domainDensity_schwarz_disc (p : DiscCover M)
    (U : TopologicalSpace.Opens M) {g : unitDisc → M}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hm : ∀ v, g v ∈ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hx : g discZero ∈ c.source) :
    p.domainDensity U c ⟨g discZero,hm discZero⟩ *
      ‖deriv (planeExtension (c ∘ g)) 0‖ ≤ 2 := by
  let x : U := ⟨g discZero,hm discZero⟩
  let V := componentDomain U (x : M)
  let q := p.componentCover U x
  let d := c.subtypeRestr (show Nonempty V from ⟨componentPoint U x⟩)
  let : SimplyConnectedSpace unitDisc := unitDisc_simplyConnected
  have hrange : range g ⊆ (V : Set M) :=
    (isPreconnected_range hg.continuous).subset_connectedComponentIn
      (mem_range_self discZero) (by rintro _ ⟨v,rfl⟩; exact hm v)
  let G : unitDisc → V := fun v => ⟨g v,hrange (mem_range_self v)⟩
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G :=
    (mdifferentiable_subtypeVal_comp_iff V G).mp hg
  have hxd : G discZero ∈ d.source := by
    simpa only [d, G, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  have hs := q.density_schwarz_disc hG (mdifferentiableOn_subtypeRestr _ hc) discZero hxd
  have hG0 : G discZero = componentPoint U x := Subtype.ext rfl
  have he : d ∘ G = c ∘ g := rfl
  change q.density d (G discZero) * ‖deriv (planeExtension (d ∘ G)) (discZero : ℂ)‖ ≤
    discDensity discZero at hs
  rw [hG0,he] at hs
  simpa only [q, d, x, domainDensity, discDensity, discDenom, show (discZero : ℂ) = 0 from rfl,
    map_zero, sub_zero, div_one] using hs

theorem domainDensity_ratio_le_of_disc_avoidance (p : DiscCover M)
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : V} (hx : (x : M) ∈ c.source)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (havoid : ∀ g : unitDisc → M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      (∀ v, g v ∈ U) → g discZero = (x : M) →
      ∀ z : unitDisc, ‖(z : ℂ)‖ < r → g z ∈ V) :
    p.domainDensity V c x / p.domainDensity U c ⟨(x : M), hVU x.property⟩ ≤ 1 / r := by
  let xu : U := ⟨(x : M),hVU x.property⟩
  obtain ⟨g,hg,hg0,hgm,hscale⟩ := p.domainDensity_extremal_disc U hc (x := xu) hx
  let a := discDilation r hr.le hr1
  have ha := discDilation_holomorphic hr.le hr1
  have ha0 : a discZero = discZero := discDilation_zero hr.le hr1
  have hmap : ∀ z : unitDisc, g (a z) ∈ V := by
    intro z
    apply havoid g hg hgm hg0
    change ‖(r : ℂ) * (z : ℂ)‖ < r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp z.property) hr).trans_eq (mul_one r)
  have hxga : g (a discZero) ∈ c.source := by rwa [ha0,hg0]
  have hs := p.domainDensity_schwarz_disc V (hg.comp ha) hmap hc hxga
  have hcg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (c ∘ g) discZero :=
    ((hc _ (hg0.symm ▸ hx)).mdifferentiableAt
      (c.open_source.mem_nhds (hg0.symm ▸ hx))).comp discZero (hg discZero)
  have hder := planeExtension_deriv_comp (g := c ∘ g) (h := a) (w := discZero)
    (ha0.symm ▸ hcg) (ha discZero)
  rw [ha0] at hder
  simp only [show (discZero : ℂ) = 0 from rfl] at hder
  have he : c ∘ (g ∘ a) = (c ∘ g) ∘ a := rfl
  rw [he,hder,norm_mul] at hs
  have har : deriv (planeExtension (fun z => (a z : ℂ))) 0 = (r : ℂ) :=
    discDilation_deriv hr.le hr1
  rw [har,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at hs
  have hpoint : (⟨g (a discZero), hmap discZero⟩ : V) = x :=
    Subtype.ext (by
      change g (a discZero) = (x : M)
      rw [ha0,hg0])
  change p.domainDensity V c ⟨g (a discZero), hmap discZero⟩ *
    (‖deriv (planeExtension (c ∘ g)) 0‖ * r) ≤ 2 at hs
  rw [hpoint] at hs
  apply (div_le_div_iff₀ (p.domainDensity_pos U hc hx) hr).mpr
  have hn : 0 < ‖deriv (planeExtension (c ∘ g)) 0‖ := by
    have hnonneg := norm_nonneg (deriv (planeExtension (c ∘ g)) 0)
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) hnonneg
    rw [heq,mul_zero] at hscale
    norm_num at hscale
  nlinarith [hscale]

end AreaDeficit.Surfaces.DiscCover
