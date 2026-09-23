import FunctionTheory.Conformal.UnivalentCompositionStability

open Set Function Filter Metric
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- Shrink a prescribed target neighbourhood so its inverse-coordinate image
has room for every step of a finite orbit. This supplies the collars required
by forward-coordinate approximation before any error tolerance is chosen. -/
theorem exists_compact_target_collar_for_finite_orbit
    (g : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (N : ℕ)
    {K W : Set ℂ} (hK : IsCompact K)
    (hU : ∀ k<N, IsOpen (U k)) (hg : ∀ k<N, ContinuousOn (g k) (U k))
    (horbit : ∀ k<N, MapsTo (finiteComposition g k) K (U k))
    (e : OpenPartialHomeomorph ℂ ℂ) (hKS : K⊆e.source)
    (hW : IsOpen W) (heKW : e '' K⊆W) :
    ∃ V : Set ℂ, IsOpen V ∧ IsCompact (closure V) ∧ e '' K⊆V ∧
      closure V⊆W ∧ closure V⊆e.target ∧
      ∀ k<N, MapsTo (finiteComposition g k) (e.symm '' closure V) (U k) := by
  let D := finiteOrbitDomain g U N
  have hD : IsOpen D := isOpen_finiteOrbitDomain g U N hU hg
  have hKD : K⊆D := fun z hz k hk => horbit k hk hz
  let S := (e.target∩e.symm ⁻¹' D)∩W
  have hS : IsOpen S := (e.isOpen_inter_preimage_symm hD).inter hW
  have hAS : e '' K⊆S := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨⟨e.map_source (hKS hx),by change e.symm (e x)∈D; rw [e.left_inv (hKS hx)]; exact hKD hx⟩,
      heKW ⟨x,hx,rfl⟩⟩
  have hA : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKS)
  obtain ⟨V,hV,hAV,hVS,hVc⟩ := exists_open_between_and_isCompact_closure hA hS hAS
  refine ⟨V,hV,hVc,hAV,fun z hz => (hVS hz).2,fun z hz => (hVS hz).1.1,?_⟩
  intro k hk z hz
  obtain ⟨w,hw,rfl⟩ := hz
  exact (hVS hw).1.2 k hk

end FunctionTheory
