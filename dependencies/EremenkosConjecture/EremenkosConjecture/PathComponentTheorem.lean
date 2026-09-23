import EremenkosConjecture.BarrierScaling
import EremenkosConjecture.SingletonContinuum
import ComplexDynamics.CurvesToInfinity

open Set Metric Filter Function ComplexDynamics

namespace EremenkosConjecture

private theorem singleton_pathComponent {S : Set ℂ} {a : ℂ} (ha : a ∈ S)
    (hsub : pathComponentIn S a ⊆ {a}) : pathComponentIn S a = {a} :=
  Subset.antisymm hsub (singleton_subset_iff.mpr (mem_pathComponentIn_self ha))

/-- Theorem 3.4 with the fast-escape strengthening of Remark 3.5, including singleton continua. -/
theorem fast_escaping_path_components (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ K ⊆ fastEscapingSet f ∧
      (∀ x ∈ K, pathComponentIn (escapingSet f) x = pathComponentIn K x) ∧
      (∀ x ∈ frontier K, pathComponentIn (juliaSet f) x = pathComponentIn (frontier K) x) := by
  by_cases hnt : K.Nontrivial
  · exact fast_escaping_path_components_nontrivial K hK hconn hfull hnt
  · have hsingle : K.Subsingleton := not_nontrivial_iff.mp hnt
    obtain ⟨a, ha⟩ := hconn.nonempty
    have hKeq : K = {a} := hsingle.eq_singleton_of_mem ha
    obtain ⟨L, hLc, hLconn, hLfull, hLnt, haL, hpathL⟩ :=
      exists_full_continuum_singleton_pathComponent a
    obtain ⟨f, hf, hfast, hI, hJ⟩ :=
      fast_escaping_path_components_nontrivial L hLc hLconn hLfull hLnt
    have haL' : a ∈ L := frontier_subset_iff_isClosed.mpr hLc.isClosed haL
    have hpathFront : pathComponentIn (frontier L) a = {a} :=
      singleton_pathComponent haL (hpathL ▸ pathComponentIn_mono
        (frontier_subset_iff_isClosed.mpr hLc.isClosed))
    have hsinglePath : pathComponentIn ({a} : Set ℂ) a = {a} :=
      singleton_pathComponent (mem_singleton a) pathComponentIn_subset
    have hfrontSingle : frontier ({a} : Set ℂ) = {a} := by
      rw [frontier, closure_singleton, interior_singleton, sdiff_empty]
    refine ⟨f, hf, ?_, ?_, ?_⟩
    · rw [hKeq]
      exact singleton_subset_iff.mpr (hfast haL')
    · intro x hx
      have hxa : x = a := by simpa only [hKeq, mem_singleton_iff] using hx
      subst x
      rw [hI a haL', hpathL, hKeq, hsinglePath]
    · rw [hKeq, hfrontSingle]
      intro x hx
      have hxa : x = a := hx
      subst x
      rw [hJ a haL, hpathFront, hsinglePath]

/-- Every full continuum occurs with the path components asserted in Theorem 3.4,
and no curve in the escaping set connects any of its points to infinity. -/
theorem strong_eremenko_counterexamples (K : Set ℂ) (hK : IsCompact K)
    (hconn : IsConnected K) (hfull : IsConnected Kᶜ) :
    ∃ f : ℂ → ℂ, IsTranscendentalEntire f ∧ K ⊆ fastEscapingSet f ∧
      (∀ x ∈ K, pathComponentIn (escapingSet f) x = pathComponentIn K x) ∧
      (∀ x ∈ frontier K, pathComponentIn (juliaSet f) x = pathComponentIn (frontier K) x) ∧
      (∀ γ : ℝ → ℂ, ContinuousOn γ (Ici 0) → γ 0 ∈ K → MapsTo γ (Ici 0) (escapingSet f) →
        ¬ Tendsto (fun t => ‖γ t‖) atTop atTop) := by
  obtain ⟨f, hf, hfast, hI, hJ⟩ := fast_escaping_path_components K hK hconn hfull
  refine ⟨f, hf, hfast, hI, hJ, ?_⟩
  intro γ hγ hstart hmem
  apply not_curve_to_infinity_of_bounded_pathComponent (x := γ 0) _ hγ rfl hmem
  rw [hI _ hstart]
  exact hK.isBounded.subset pathComponentIn_subset

end EremenkosConjecture
