import FunctionTheory.Conformal.ReflectionBounds
import FunctionTheory.Conformal.AnalyticContinuationConvergence

/-! # Convergence across a circle arc by reflection and Vitali

A uniform lower bound on the inner values bounds the reflected family.
Vitali and the identity theorem continue convergence from an inner accumulation
set to the symmetric neighbourhood, including its original closed inner side.
-/

open Set Metric Filter EuclideanGeometry
open scoped Topology

namespace FunctionTheory

theorem reflected_maps_tendsto_of_inner_convergence
    {Ω A : Set ℂ} {F : ℕ → ℂ → ℂ} {δ : ℝ} {z₀ : ℂ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hδ : 0 < δ)
    (hsymm : MapsTo (inversion (0 : ℂ) 1) Ω Ω)
    (hFc : ∀ n, ContinuousOn (F n) (Ω ∩ closedBall (0 : ℂ) 1))
    (hFd : ∀ n, DifferentiableOn ℂ (F n) (Ω ∩ ball (0 : ℂ) 1))
    (hboundary : ∀ n, MapsTo (F n) (Ω ∩ sphere (0 : ℂ) 1) (sphere 0 1))
    (hupper : ∀ n, ∀ z ∈ Ω ∩ closedBall (0 : ℂ) 1, ‖F n z‖ ≤ 1)
    (hlower : ∀ n, ∀ z ∈ Ω ∩ ball (0 : ℂ) 1, z ≠ 0 → δ ≤ ‖F n z‖)
    (hA : A ⊆ Ω ∩ ball (0 : ℂ) 1) (hz₀ : z₀ ∈ Ω)
    (hacc : AccPt z₀ (𝓟 A))
    (hpoint : ∀ z ∈ A, Tendsto (fun n => F n z) atTop (𝓝 z)) :
    TendstoLocallyUniformlyOn
      (fun n => TauCeti.circleSchwarzReflection 0 1 0 1 (F n))
      (fun z => z) atTop Ω := by
  have hd (n : ℕ) : DifferentiableOn ℂ
      (TauCeti.circleSchwarzReflection 0 1 0 1 (F n)) Ω := by
    apply TauCeti.differentiableOn_circleSchwarzReflection_of_symmetric
      one_pos one_pos hΩ hsymm (hFc n) (hFd n) (hboundary n)
    intro z hz hz0 heq
    have h := hlower n z hz hz0
    rw [heq, norm_zero] at h
    exact hδ.not_ge h
  have hb : TauCeti.IsLocallyBoundedOn
      (fun n => TauCeti.circleSchwarzReflection 0 1 0 1 (F n)) Ω := by
    apply TauCeti.isLocallyBoundedOn_def.mpr
    intro K hK _
    exact ⟨max 1 (1 / δ), fun n z hz =>
      norm_circleSchwarzReflection_le hδ hsymm (hupper n) (hlower n) z (hK hz)⟩
  apply locallyUniform_of_vitali_with_holomorphic_limit hΩ hconn hd hb
    differentiable_id.differentiableOn (hA.trans inter_subset_left) hz₀ hacc
  intro z hz
  have heq : (fun n => TauCeti.circleSchwarzReflection 0 1 0 1 (F n) z) =
      (fun n => F n z) := by
    funext n
    exact TauCeti.circleSchwarzReflection_of_mem_closedBall 0 1 (F n)
      (ball_subset_closedBall (hA hz).2)
  rw [heq]
  exact hpoint z hz

theorem locallyUniformOn_closedSide_of_reflected_convergence
    {ι : Type*} {l : Filter ι} {Ω : Set ℂ} {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn
      (fun n => TauCeti.circleSchwarzReflection 0 1 0 1 (F n)) g l Ω) :
    TendstoLocallyUniformlyOn F g l (Ω ∩ closedBall (0 : ℂ) 1) :=
  (hconv.mono inter_subset_left).congr fun n _ hz =>
    TauCeti.circleSchwarzReflection_of_mem_closedBall 0 1 (F n) hz.2

end FunctionTheory
