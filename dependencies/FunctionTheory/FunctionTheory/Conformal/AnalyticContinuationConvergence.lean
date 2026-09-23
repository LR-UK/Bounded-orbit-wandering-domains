import TauCeti.Analysis.Complex.Conformal.Vitali

/-! # Continuing convergence to a known holomorphic limit

Vitali's theorem supplies convergence from a set with an accumulation point.
The identity theorem identifies the limit with a prescribed holomorphic map
on the whole connected domain.
-/

open Set Filter
open scoped Topology

namespace FunctionTheory

theorem locallyUniform_of_vitali_with_holomorphic_limit
    {Ω A : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {z₀ : ℂ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : TauCeti.IsLocallyBoundedOn F Ω)
    (hg : DifferentiableOn ℂ g Ω) (hAΩ : A ⊆ Ω) (hz₀ : z₀ ∈ Ω)
    (hacc : AccPt z₀ (𝓟 A))
    (hpoint : ∀ z ∈ A, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    TendstoLocallyUniformlyOn F g atTop Ω := by
  obtain ⟨q, hq, hqgA, hconv⟩ :=
    TauCeti.vitali_of_tendsto hΩ hconn hF hb hAΩ hz₀ hacc hpoint
  have hqg : EqOn q g Ω :=
    (hq.analyticOnNhd hΩ).eqOn_of_preconnected_of_frequently_eq
      (hg.analyticOnNhd hΩ) hconn hz₀
      ((accPt_iff_frequently_nhdsNE.mp hacc).mono fun z hz => hqgA hz)
  exact hconv.congr_right hqg

end FunctionTheory
