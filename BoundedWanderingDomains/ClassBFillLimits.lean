/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 licence; see LICENSE.
-/
import BoundedWanderingDomains.HolomorphicFilling
import BoundedWanderingDomains.TractFillingObstruction
import BoundedWanderingDomains.UniformSphericalConstants

/-! # Extending constant limits across compact fillings in class B -/

open Set Metric Function Filter OnePoint
open scoped Topology

namespace AreaDeficit

theorem isOpenMap_of_transcendentalEntire {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) : IsOpenMap f := by
  apply (hf.1.differentiableOn.analyticOnNhd isOpen_univ).is_constant_or_isOpenMap.resolve_left
  rintro ⟨c, hc⟩
  exact hf.2 ⟨Polynomial.C c, funext (fun z => by simpa using hc z)⟩

theorem isOpenMap_iterate_of_transcendentalEntire {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) (n : ℕ) : IsOpenMap (f^[n]) := by
  induction n with
  | zero => intro S hS; simpa using hS
  | succ n ih => simpa only [iterate_succ'] using (isOpenMap_of_transcendentalEntire hf).comp ih

/-- High modulus on a compact continuum extends to its filling for positive
iterates of a transcendental entire exterior covering. -/
theorem iterate_norm_gt_on_fill {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) {R : ℝ} (hR : 0 < R)
    (hc : IsCoveringMapOn f {w : ℂ | R < ‖w‖})
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (n : ℕ)
    (hb : ∀ z ∈ K, R < ‖(f^[n+1]) z‖) :
    ∀ z ∈ ComplexApproximation.fill K, R < ‖(f^[n+1]) z‖ := by
  have hI := hK.image (hf.1.iterate n).continuous
  have hIc := hKc.image (f^[n]) (hf.1.iterate n).continuous.continuousOn
  have hIR : ∀ w ∈ (f^[n]) '' K, R < ‖f w‖ := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [iterate_succ_apply'] using hb z hz
  intro z hz
  rw [iterate_succ_apply']
  exact exterior_fill_subset hf hR hc hI hIc hIR _
    (image_fill_subset_fill_image (hf.1.iterate n).continuous
      (isOpenMap_iterate_of_transcendentalEntire hf n) hK (mem_image_of_mem _ hz))

/-- A finite constant limit of entire functions extends uniformly to the
filled compactum, by the maximum-modulus principle. -/
theorem uniform_spherical_finite_on_fill {F : ℕ → ℂ → ℂ} {K : Set ℂ} {a : ℂ}
    (hK : IsCompact K) (hF : ∀ n, Differentiable ℂ (F n))
    (hlim : TendstoUniformlyOn (fun n z => (F n z : OnePoint ℂ))
      (fun _ => (a : OnePoint ℂ)) atTop K) :
    TendstoUniformlyOn (fun n z => (F n z : OnePoint ℂ))
      (fun _ => (a : OnePoint ℂ)) atTop (ComplexApproximation.fill K) := by
  apply uniform_spherical_finite_iff.mpr
  have h := uniform_spherical_finite_iff.mp hlim
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn z hz
  have hb : ∀ w ∈ K, ‖F n w - a‖ ≤ ε / 2 := by
    intro w hw
    simpa only [dist_eq_norm, norm_sub_rev] using (hn w hw).le
  have hf := norm_le_on_fill hK ((hF n).sub_const a) hb z hz
  rw [dist_eq_norm, norm_sub_rev]
  exact hf.trans_lt (half_lt_self hε)

/-- In class B, an infinite constant limit of positive iterates also extends
to the filled compactum, using simple connectivity of the exterior tracts. -/
theorem uniform_spherical_infty_on_fill {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) (hB : ComplexDynamics.MemClassB f)
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) {ns : ℕ → ℕ}
    (hlim : TendstoUniformlyOn (fun n z => ((f^[ns n + 1]) z : OnePoint ℂ))
      (fun _ => ∞) atTop K) :
    TendstoUniformlyOn (fun n z => ((f^[ns n + 1]) z : OnePoint ℂ))
      (fun _ => ∞) atTop (ComplexApproximation.fill K) := by
  apply uniform_spherical_infty_iff.mpr
  obtain ⟨M, hM, hb⟩ := ((ComplexDynamics.memClassB_iff f).mp hB).exists_pos_norm_le
  intro R
  let B := max M R
  have hBp : 0 < B := hM.trans_le (le_max_left _ _)
  have hc : IsCoveringMapOn f {w : ℂ | B < ‖w‖} :=
    (ComplexDynamics.isCoveringMapOn_compl_singularValues f).mono (by
      intro w hw hws
      exact (not_lt_of_ge ((hb w hws).trans (le_max_left M R))) hw)
  filter_upwards [uniform_spherical_infty_iff.mp hlim B] with n hn z hz
  exact (le_max_right M R).trans_lt (iterate_norm_gt_on_fill hf hBp hc hK hKc (ns n) hn z hz)

/-- Both possible constant spherical limits extend uniformly across the holes. -/
theorem uniform_spherical_constant_on_fill {f : ℂ → ℂ}
    (hf : FunctionTheory.IsTranscendentalEntire f) (hB : ComplexDynamics.MemClassB f)
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) {ns : ℕ → ℕ}
    {a : OnePoint ℂ}
    (hlim : TendstoUniformlyOn (fun n z => ((f^[ns n + 1]) z : OnePoint ℂ))
      (fun _ => a) atTop K) :
    TendstoUniformlyOn (fun n z => ((f^[ns n + 1]) z : OnePoint ℂ))
      (fun _ => a) atTop (ComplexApproximation.fill K) := by
  cases a with
  | infty => exact uniform_spherical_infty_on_fill hf hB hK hKc hlim
  | coe a => exact uniform_spherical_finite_on_fill hK (fun n => hf.1.iterate (ns n + 1)) hlim

end AreaDeficit

#print axioms AreaDeficit.uniform_spherical_constant_on_fill
