import FunctionTheory.Conformal.BlaschkeDiscMap
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

open Set Metric

namespace FunctionTheory.FiniteBlaschkeProduct

set_option autoImplicit false

/-- The disc restriction of a finite Blaschke product is continuous as a
map between the actual open-disc subtypes. -/
theorem continuous_discMap (B : FiniteBlaschkeProduct) : Continuous B.discMap := by
  apply Continuous.subtype_mk
  exact continuousOn_iff_continuous_restrict.mp
    (B.analyticOnNhd_closedBall.continuousOn.mono ball_subset_closedBall)

/-- A positive-degree finite Blaschke product is proper on the open disc.
Compact target sets stay away from the image of the unit circle, so their
preimages are compact already in the open-disc topology. -/
theorem isProperMap_discMap (B : FiniteBlaschkeProduct) : IsProperMap B.discMap := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨B.continuous_discMap,?_⟩
  intro K hK
  let F : closedBall (0:ℂ) 1 → ℂ := fun z => B.eval z
  have hF : Continuous F :=
    continuousOn_iff_continuous_restrict.mp B.analyticOnNhd_closedBall.continuousOn
  let P := F ⁻¹' (((↑) : ball (0:ℂ) 1 → ℂ) '' K)
  haveI : CompactSpace (closedBall (0:ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hP : IsCompact P := ((hK.image continuous_subtype_val).isClosed.preimage hF).isCompact
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have heq : ((↑) : ball (0:ℂ) 1 → ℂ) '' (B.discMap ⁻¹' K) =
      ((↑) : closedBall (0:ℂ) 1 → ℂ) '' P := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,ball_subset_closedBall z.property⟩,?_,rfl⟩
      exact ⟨B.discMap z,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨y,hy,hyz⟩ := hz
      have heval : ‖B.eval z‖<1 := by
        change ‖F z‖<1
        rw [← hyz]
        exact mem_ball_zero_iff.mp y.property
      have hzlt : ‖(z:ℂ)‖<1 := by
        have hzle : ‖(z:ℂ)‖≤1 := mem_closedBall_zero_iff.mp z.property
        rcases hzle.lt_or_eq with hlt | hequal
        · exact hlt
        · exact ((B.norm_eval_sphere hequal).not_lt heval).elim
      let x : ball (0:ℂ) 1 := ⟨z,mem_ball_zero_iff.mpr hzlt⟩
      have hx : B.discMap x=y := Subtype.ext hyz.symm
      refine ⟨x,?_,rfl⟩
      change B.discMap x∈K
      rwa [hx]
  rw [heq]
  exact hP.image continuous_subtype_val

/-- Properness is retained in actual-domain charts. This applies to the
one-step maps of realised wandering domains with prescribed Blaschke maps. -/
theorem isProperMap_of_disc_charts (B : FiniteBlaschkeProduct)
    {U V : Set ℂ} (σ : ball (0:ℂ) 1 ≃ₜ U) (τ : ball (0:ℂ) 1 ≃ₜ V)
    (f : U → V) (hconj : ∀ z, f (σ z)=τ (B.discMap z)) :
    IsProperMap f := by
  have heq : f=(fun z => τ (B.discMap (σ.symm z))) := by
    funext z
    simpa only [σ.apply_symm_apply] using hconj (σ.symm z)
  rw [heq]
  exact τ.isProperMap.comp (B.isProperMap_discMap.comp σ.symm.isProperMap)

end FunctionTheory.FiniteBlaschkeProduct
