/- Copyright (c) 2026 Lasse Rempe. Released under Apache 2.0 licence; see LICENSE. -/
import BoundedWanderingDomains.Surfaces.SmallChartDomain
import BoundedWanderingDomains.Surfaces.DomainRemoteBound
import BoundedWanderingDomains.Surfaces.ChartPunctures
import BoundedWanderingDomains.UnconditionalPointRemoval
import BoundedWanderingDomains.PunctureDensityLimits

/-! # Density divergence at accumulated punctures

Local comparison reduces the statement to the existing planar divergence
theorem. No additional normal-family argument on surfaces is constructed.
-/
open Set Function Filter Metric
open scoped Manifold Topology
namespace AreaDeficit.Surfaces.DiscCover
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [SecondCountableTopology M]

theorem finite_density_le_domainChartDensity (p : DiscCover M)
    (G : FinitePunctureMetricInput) (U : TopologicalSpace.Opens M)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    (hUc : (U : Set M) ⊆ c.source) (Q : Finset ℂ) (hQ : 2 ≤ Q.card)
    (homit : ∀ y ∈ U, c y ∉ Q) {z : ℂ} (hz : z ∈ domainChartSet U c) :
    G.density Q z ≤ p.domainChartDensity U c z := by
  let x : U := ⟨c.symm z,hz.2⟩
  obtain ⟨g,hg,hg0,hgm,he⟩ := p.domainDensity_extremal_disc U hc
    (x := x) (c.map_target hz.1)
  let t := planeExtension (c ∘ g)
  have ht : DifferentiableOn ℂ t (ball 0 1) := by
    apply planeExtension_differentiableOn
    intro v
    exact ((hc _ (hUc (hgm v))).mdifferentiableAt
      (c.open_source.mem_nhds (hUc (hgm v)))).comp v (hg v)
  have ht0 : t 0 = z := by
    change planeExtension (c ∘ g) (discZero : ℂ) = z
    rw [planeExtension_coe]
    dsimp only [comp_apply]
    rw [hg0]
    exact c.right_inv hz.1
  have htm : MapsTo t (ball 0 1) (Q : Set ℂ)ᶜ := by
    intro v hv
    have htv : t v = c (g ⟨v,hv⟩) := planeExtension_coe _ (⟨v,hv⟩ : unitDisc)
    rw [htv]
    exact homit _ (hgm _)
  have hs := G.schwarz Q hQ t ht htm
  rw [ht0] at hs
  have hn : 0 < ‖deriv t 0‖ := by
    have hnn := norm_nonneg (deriv t 0)
    by_contra hn
    have he0 := le_antisymm (le_of_not_gt hn) hnn
    change p.domainDensity U c x * ‖deriv t 0‖ = 2 at he
    rw [he0,mul_zero] at he
    norm_num at he
  rw [p.domainChartDensity_of_mem U c hz]
  exact (mul_le_mul_iff_left₀ hn).mp (hs.trans_eq he.symm)

/-- The other half of finite-puncture metric convergence: at a point in
the closed limit which is never itself punctured, the densities diverge. -/
theorem domainDensity_tendsto_atTop_finite_punctures (p : DiscCover M)
    (P : ℕ → Finset M) (hP : Monotone P)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {x : M} (hxc : x ∈ c.source) (hxP : ∀ n, x ∉ P n)
    (hx : x ∈ closure (⋃ n, (P n : Set M))) :
    Tendsto (fun n => p.domainDensity (finitePunctureDomain (P n)) c ⟨x,hxP n⟩)
      atTop atTop := by
  classical
  obtain ⟨D,hxD,hDc,a,b,hab,ha,hb⟩ := exists_small_chart_domain hxc
  let U := fun n => finitePunctureDomain (P n)
  let W := fun n => U n ⊓ D
  let Q := fun n => insert a (insert b (chartPunctures c (P n)))
  have hQ : Monotone Q := by
    intro i j hij
    exact Finset.insert_subset_insert a (Finset.insert_subset_insert b
      (chartPunctures_mono c (hP hij)))
  have haQ : a ∈ Q 0 := Finset.mem_insert_self _ _
  have hbQ : b ∈ Q 0 := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hxT : c x ∈ domainChartSet D c :=
    ⟨c.map_source hxc,by
      change c.symm (c x) ∈ D
      rwa [c.left_inv hxc]⟩
  have hxQ : ∀ n, c x ∉ Q n := by
    intro n h
    rcases Finset.mem_insert.mp h with he | h
    · exact ha (he ▸ hxT)
    rcases Finset.mem_insert.mp h with he | h
    · exact hb (he ▸ hxT)
    · have hm := (mem_chartPunctures_iff c (P n) (c.map_source hxc)).mp h
      rw [c.left_inv hxc] at hm
      exact hxP n hm
  have hxcl : c x ∈ closure (⋃ n, (Q n : Set ℂ)) := by
    apply closure_mono (s := ⋃ n, (chartPunctures c (P n) : Set ℂ)) _
      (chartPunctures_mem_closure c P hxc hx)
    rintro z hz
    obtain ⟨n,hn⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨n,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn)⟩
  let G := canonicalFinitePunctureMetricInput
  have hdiv := G.density_tendsto_atTop hQ hab haQ hbQ hxQ hxcl
  have hCK : Disjoint ({x} : Set M) (D : Set M)ᶜ := by
    rw [disjoint_singleton_left]
    exact not_not.mpr hxD
  obtain ⟨B,hB,hbound⟩ := p.remote_domainDensity_ratio_bound
    D.isOpen.isClosed_compl isCompact_singleton hCK
  apply Tendsto.atTop_of_const_mul₀ (lt_of_lt_of_le zero_lt_one hB)
  apply tendsto_atTop_mono (f := fun n => G.density (Q n) (c x)) _ hdiv
  intro n
  have hxW : x ∈ W n := ⟨hxP n,hxD⟩
  have hxTW : c x ∈ domainChartSet (W n) c :=
    ⟨c.map_source hxc,by
      change c.symm (c x) ∈ W n
      rwa [c.left_inv hxc]⟩
  have hWc : (W n : Set M) ⊆ c.source := fun _ hy => hDc hy.2
  have hcard : 2 ≤ (Q n).card := Finset.one_lt_card.mpr
    ⟨a,hQ (Nat.zero_le n) haQ,b,hQ (Nat.zero_le n) hbQ,hab⟩
  have homit : ∀ y ∈ W n, c y ∉ Q n := by
    intro y hy h
    have hyc := hWc hy
    have hyT : c y ∈ domainChartSet D c :=
      ⟨c.map_source hyc,by simpa only [mem_preimage,c.left_inv hyc] using hy.2⟩
    rcases Finset.mem_insert.mp h with he | h
    · exact ha (he ▸ hyT)
    rcases Finset.mem_insert.mp h with he | h
    · exact hb (he ▸ hyT)
    · have hm := (mem_chartPunctures_iff c (P n) (c.map_source hyc)).mp h
      rw [c.left_inv hyc] at hm
      exact hy.1 hm
  have hlo := p.finite_density_le_domainChartDensity G (W n) hc hWc (Q n) hcard homit hxTW
  have hratio := hbound (U n) (W n) inf_le_left
    (fun y hy hDy => ⟨hy,not_not.mp hDy⟩) c hc ⟨x,hxW⟩ (mem_singleton x) hxc
  have hupp := (div_le_iff₀ (p.domainDensity_pos (U n) hc (x := ⟨x,hxP n⟩) hxc)).mp hratio
  have he : p.domainChartDensity (W n) c (c x) = p.domainDensity (W n) c ⟨x,hxW⟩ := by
    rw [p.domainChartDensity_of_mem (W n) c hxTW]
    congr 1
    exact Subtype.ext (c.left_inv hxc)
  rw [he] at hlo
  exact hlo.trans hupp

theorem domainChartDensity_tendsto_atTop_finite_punctures (p : DiscCover M)
    (P : ℕ → Finset M) (hP : Monotone P)
    {c : OpenPartialHomeomorph M ℂ}
    (hc : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) c c.source)
    {z : ℂ} (hz : z ∈ c.target) (hzP : ∀ n, c.symm z ∉ P n)
    (hzA : c.symm z ∈ closure (⋃ n, (P n : Set M))) :
    Tendsto (fun n => p.domainChartDensity (finitePunctureDomain (P n)) c z)
      atTop atTop := by
  have hm : ∀ n, z ∈ domainChartSet (finitePunctureDomain (P n)) c :=
    fun n => ⟨hz,hzP n⟩
  simp_rw [p.domainChartDensity_of_mem _ c (hm _)]
  exact p.domainDensity_tendsto_atTop_finite_punctures P hP hc
    (c.map_target hz) hzP hzA

end AreaDeficit.Surfaces.DiscCover
