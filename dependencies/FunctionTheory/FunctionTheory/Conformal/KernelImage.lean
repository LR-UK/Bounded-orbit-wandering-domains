import FunctionTheory.Conformal.KernelSeparation
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping

/-! # Images of nondegenerate conformal limits

A nonconstant holomorphic limit takes values in the interior of every closed
constraint eventually satisfied by its approximants. A positive lower bound on
the derivative at one fixed point excludes degeneration to a constant map.
These are the kernel-identification steps, independent of the existence of
Riemann maps or of a convergent subsequence.
-/

open Set Filter Metric
open scoped Topology

namespace FunctionTheory

theorem image_subset_interior_iInter_of_holomorphic_limit
    {ι κ : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {D : Set ℂ} {C : κ → Set ℂ}
    (hDo : IsOpen D) (hDc : IsPreconnected D) (hg : DifferentiableOn ℂ g D)
    (hnc : ¬ ∃ c, ∀ z ∈ D, g z = c)
    (hconv : TendstoLocallyUniformlyOn F g l D)
    (hC : ∀ k, IsClosed (C k))
    (hmem : ∀ k, ∀ᶠ n in l, MapsTo (F n) D (C k)) :
    g '' D ⊆ interior (⋂ k, C k) := by
  have hopen : IsOpen (g '' D) :=
    ((hg.analyticOnNhd hDo).is_constant_or_isOpen hDc).resolve_left hnc D subset_rfl hDo
  apply interior_maximal _ hopen
  rintro _ ⟨z, hz, rfl⟩
  apply mem_iInter.mpr
  intro k
  exact (hC k).mem_of_tendsto (hconv.tendsto_at hz) ((hmem k).mono fun n hn => hn hz)

theorem nonconstant_of_derivative_lower_bound_of_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ} {c : ℝ}
    (hDo : IsOpen D) (hz₀ : z₀ ∈ D) (hc : 0 < c)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F g atTop D)
    (hderiv : ∀ᶠ n in atTop, c ≤ ‖deriv (F n) z₀‖) :
    ¬ ∃ a, ∀ z ∈ D, g z = a := by
  have hbound : c ≤ ‖deriv g z₀‖ :=
    ge_of_tendsto ((hconv.deriv hF hDo).tendsto_at hz₀).norm hderiv
  rintro ⟨a, ha⟩
  have heq : g =ᶠ[𝓝 z₀] fun _ => a := by
    filter_upwards [hDo.mem_nhds hz₀] with z hz
    exact ha z hz
  have hd : deriv g z₀ = 0 := by rw [heq.deriv_eq]; simp
  rw [hd, norm_zero] at hbound
  exact hc.not_ge hbound

/-- The closed sets can be closures of a decreasing family of domains. The
interior of their intersection is then the candidate kernel. -/
theorem image_subset_kernel_of_derivative_lower_bound
    {κ : Type*} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {D : Set ℂ}
    {C : κ → Set ℂ} {z₀ : ℂ} {c : ℝ}
    (hDo : IsOpen D) (hDc : IsPreconnected D) (hz₀ : z₀ ∈ D) (hc : 0 < c)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F g atTop D)
    (hderiv : ∀ᶠ n in atTop, c ≤ ‖deriv (F n) z₀‖)
    (hC : ∀ k, IsClosed (C k))
    (hmem : ∀ k, ∀ᶠ n in atTop, MapsTo (F n) D (C k)) :
    g '' D ⊆ interior (⋂ k, C k) :=
  image_subset_interior_iInter_of_holomorphic_limit hDo hDc
    (hconv.differentiableOn hF hDo)
    (nonconstant_of_derivative_lower_bound_of_tendstoLocallyUniformlyOn
      hDo hz₀ hc hF hconv hderiv) hconv hC hmem

end FunctionTheory
