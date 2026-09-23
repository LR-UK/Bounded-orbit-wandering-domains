import FunctionTheory.Conformal.RegularAnalyticArc
import FunctionTheory.Conformal.CompactConformalInverse

open Set Metric Complex Filter
open scoped Topology
namespace FunctionTheory
set_option autoImplicit false

/-- A Euclidean circle is a regular analytic arc near every one of its
points. The actual local conformal coordinate is an affine Cayley map. -/
theorem hasRegularAnalyticArcAt_sphere {c p : ℂ} {r : ℝ}
    (hr : 0<r) (hp : p∈sphere c r) : HasRegularAnalyticArcAt (sphere c r) p := by
  have hpn : ‖p-c‖=r := by simpa only [mem_sphere,dist_eq_norm] using hp
  have hpc : p-c≠0 := norm_ne_zero_iff.mp (by rw [hpn]; exact hr.ne')
  let A := fun z => (z-c)/(p-c)
  let T := fun z => cayleyCoordinate (A z)
  let S : Set ℂ := {z | 1+A z≠0}
  have hS : IsOpen S := isOpen_ne_fun
    (continuous_const.add ((continuous_id.sub continuous_const).div_const (p-c))) continuous_const
  have hd : DifferentiableOn ℂ T S := by
    intro z hz
    exact ((differentiableAt_cayleyCoordinate hz).comp z
      ((differentiableAt_id.sub_const c).div_const (p-c))).differentiableWithinAt
  have hi : InjOn T S := by
    intro z hz w hw H
    have hA := cayleyCoordinate_injOn hz hw H
    exact sub_left_inj.mp ((div_left_inj' hpc).mp hA)
  let e := hd.toOpenPartialHomeomorph hS hi
  have hpS : p∈S := by simp [S,A,div_self hpc]
  refine ⟨e,hpS,hd.analyticOnNhd hS,
    (hd.differentiableOn_toOpenPartialHomeomorph_symm hS hi).analyticOnNhd e.open_target,?_,?_⟩
  · change cayleyCoordinate ((p-c)/(p-c))=0
    simp [div_self hpc]
  · intro z hz
    change z∈sphere c r ↔ (cayleyCoordinate (A z)).re=0
    have hden : normSq (1+A z)≠0 := by
      rw [normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    rw [re_cayleyCoordinate,div_eq_zero_iff]
    rw [or_iff_left hden]
    constructor
    · intro hzr
      have hzn : ‖z-c‖=r := by simpa only [mem_sphere,dist_eq_norm] using hzr
      simp [A,normSq_eq_norm_sq,norm_div,hpn,hzn,hr.ne']
    · intro H
      have hn : ‖A z‖=1 := by
        rw [normSq_eq_norm_sq] at H
        nlinarith [norm_nonneg (A z)]
      have heq : ‖z-c‖=r := (div_eq_one_iff_eq hr.ne').mp (by
        simpa only [A,norm_div,hpn] using hn)
      simpa only [mem_sphere,dist_eq_norm] using heq

end FunctionTheory
