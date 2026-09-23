import EremenkosConjecture.UnivalentIterates
import EremenkosConjecture.OrbitControl

/-! # A persistent conformal-chart invariant for the induction -/

open Set Metric Function
open Filter
open scoped Topology

namespace EremenkosConjecture

def HasAmbientConformalChart (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∃ (H : ℂ ≃ₜ ℂ) (V : Set ℂ), IsOpen V ∧ K ⊆ V ∧
    EqOn f H V ∧ DifferentiableOn ℂ H V ∧ DifferentiableOn ℂ H.symm (H '' V)

theorem HasAmbientConformalChart.mono {f : ℂ → ℂ} {K L : Set ℂ}
    (h : HasAmbientConformalChart f K) (hLK : L ⊆ K) : HasAmbientConformalChart f L := by
  obtain ⟨H, V, hV, hKV, heq, hd, hdi⟩ := h
  exact ⟨H, V, hV, hLK.trans hKV, heq, hd, hdi⟩

theorem HasAmbientConformalChart.injOn {f : ℂ → ℂ} {K : Set ℂ}
    (h : HasAmbientConformalChart f K) : InjOn f K := by
  obtain ⟨H, V, hV, hKV, heq, hd, hdi⟩ := h
  intro x hx y hy hxy
  apply H.injective
  rwa [← heq (hKV hx), ← heq (hKV hy)]

theorem HasAmbientConformalChart.isFull_image {f : ℂ → ℂ} {K : Set ℂ}
    (h : HasAmbientConformalChart f K) (hfull : IsConnected Kᶜ) : IsConnected (f '' K)ᶜ := by
  obtain ⟨H, V, hV, hKV, heq, hd, hdi⟩ := h
  have himage : f '' K = H '' K := Set.image_congr (fun z hz => heq (hKV hz))
  rw [himage]
  exact isConnected_compl_image_homeomorph H hfull

theorem hasAmbientConformalChart_id (K : Set ℂ) : HasAmbientConformalChart id K := by
  exact ⟨Homeomorph.refl ℂ, univ, isOpen_univ, subset_univ _, fun _ _ => rfl,
    differentiableOn_id, differentiableOn_id⟩

theorem HasAmbientConformalChart.congr_near {f g : ℂ → ℂ} {K O : Set ℂ}
    (h : HasAmbientConformalChart f K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hfg : EqOn f g O) : HasAmbientConformalChart g K := by
  obtain ⟨H, V, hV, hKV, heq, hd, hdi⟩ := h
  exact ⟨H, V ∩ O, hV.inter hO, fun z hz => ⟨hKV hz, hKO hz⟩,
    fun z hz => (hfg hz.2).symm.trans (heq hz.1), hd.mono inter_subset_left,
    hdi.mono (image_mono inter_subset_left)⟩

theorem HasAmbientConformalChart.add_const {f : ℂ → ℂ} {K : Set ℂ}
    (h : HasAmbientConformalChart f K) (c : ℂ) :
    HasAmbientConformalChart (fun z => f z + c) K := by
  obtain ⟨H, V, hV, hKV, heq, hd, hdi⟩ := h
  let G := H.trans (Homeomorph.addRight c)
  refine ⟨G, V, hV, hKV, fun z hz => ?_, ?_, ?_⟩
  · change f z + c = H z + c
    rw [heq hz]
  · exact hd.add_const c
  · have hm : MapsTo (fun z : ℂ => z - c) (G '' V) (H '' V) := by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, hw, by change H w = H w + c - c; simp⟩
    exact hdi.comp (differentiableOn_id.sub_const c) hm

theorem HasAmbientConformalChart.congr_nhds {f g : ℂ → ℂ} {K : Set ℂ}
    (h : HasAmbientConformalChart f K) (hfg : ∀ z ∈ K, f =ᶠ[𝓝 z] g) :
    HasAmbientConformalChart g K := by
  apply h.congr_near (O := interior {z | f z = g z}) isOpen_interior
  · intro z hz
    exact mem_interior_iff_mem_nhds.mpr (hfg z hz)
  · intro z hz
    exact (show z ∈ {w | f w = g w} from interior_subset hz)

theorem approximationStable_ambient_conformal_iterate
    (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (n : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hchart : HasAmbientConformalChart (g^[n]) K)
    (horbit : ∀ k < n, MapsTo (g^[k]) K U) :
    ApproximationStable g U (fun f => HasAmbientConformalChart (f^[n]) K) := by
  obtain ⟨H, V, hV, hKV, heq, hd, hdi⟩ := hchart
  let W := V ∩ ComplexDynamics.iterateDomain g U n
  have hW : IsOpen W := hV.inter (ComplexDynamics.isOpen_iterateDomain g U hU hg.continuousOn n)
  have hKW : K ⊆ W := fun z hz => ⟨hKV hz,
    (ComplexDynamics.mem_iterateDomain_iff g U n z).mpr (fun k hk => horbit k hk hz)⟩
  let e := H.toOpenPartialHomeomorph.restrOpen W hW
  have hKe : K ⊆ e.source := fun z hz => ⟨mem_univ z, hKW hz⟩
  have hei : DifferentiableOn ℂ e.symm e.target := by
    apply hdi.mono
    intro z hz
    refine ⟨H.symm z, hz.2.1, H.apply_symm_apply z⟩
  have he : EqOn (g^[n]) e e.source := fun z hz => heq hz.2.1
  have heH : EqOn e H e.source := fun _ _ => rfl
  have hdom : ∀ k < n, MapsTo (g^[k]) e.source U := fun k hk z hz =>
    ComplexDynamics.mapsTo_iterateDomain g U hk hz.2.2
  obtain ⟨δ, hδ, Hδ⟩ := approximate_ambient_conformal_iterates_on_compact
    g U hU hg n e he hei H heH hdom K hK hKe 1 zero_lt_one
  refine ⟨δ, hδ, fun f hf hc => ?_⟩
  obtain ⟨⟨G, O, hO, hKO, hOe, hfg, hG, hGi⟩, _⟩ := Hδ f hf hc
  exact ⟨G, O, hO, hKO, hfg, hG, hGi⟩

end EremenkosConjecture
