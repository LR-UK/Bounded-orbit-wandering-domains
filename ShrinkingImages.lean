import NormalFamilies

open Set Metric Function Filter
open scoped Topology Uniformity UniformConvergence

namespace AreaDeficit

theorem disjoint_images_eventually_omit {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hdis : Pairwise (fun n m => Disjoint (f n '' U) (f m '' U))) :
    ∀ a ∈ ⋃ n, f n '' U, ∀ᶠ n in atTop, ∀ z ∈ U, f n z ≠ a := by
  intro a ha
  obtain ⟨m, hm⟩ := mem_iUnion.mp ha
  filter_upwards [eventually_gt_atTop m] with n hn z hz he
  exact disjoint_left.mp (hdis (ne_of_gt hn))
    (by simpa only [he] using mem_image_of_mem (f n) hz) hm

/-- For uniformly bounded holomorphic maps with disjoint images,
the images of each compact source set shrink relative to any fixed
source point. No injectivity or Riemann mapping is needed here. -/
theorem disjoint_bounded_images_shrink {U L : Set ℂ} {x : ℂ}
    {f : ℕ → ℂ → ℂ} {M : ℝ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hd : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ n z, z ∈ U → ‖f n z‖ ≤ M)
    (hdis : Pairwise (fun n m => Disjoint (f n '' U) (f m '' U))) :
    TendstoUniformlyOn (fun n z => f n z - f n x) (fun _ => 0) atTop L := by
  let q : ℕ → (ℂ →ᵤ[{L}] ℂ) :=
    fun n => UniformOnFun.ofFun {L} (fun z => f n z - f n x)
  suffices Tendsto q atTop (𝓝 (UniformOnFun.ofFun {L} (fun _ => (0 : ℂ)))) by
    simpa [UniformOnFun.tendsto_iff_tendstoUniformlyOn, q, Function.comp_def] using this
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, g, hφ, hl, _⟩ := bounded_holomorphic_subsequence hU
    (fun n => hd (ns n)) (fun n => hb (ns n))
  have hseq : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hbase : g x ∈ closure (⋃ n, f n '' U) :=
    isClosed_closure.mem_of_tendsto (hl.tendsto_at hx)
      (Eventually.of_forall (fun n => subset_closure
        (mem_iUnion_of_mem (ns (φ n)) (mem_image_of_mem _ hx))))
  obtain ⟨c, hc⟩ := limit_constant_at_omitted_closure hU hUc hx
    (fun n => hd (ns (φ n))) hl
    (fun a ha => hseq.eventually (disjoint_images_eventually_omit hdis a ha)) hbase
  have hu : TendstoUniformlyOn (fun n => f (ns (φ n))) g atTop L :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hL).mp (hl.mono hLU)
  have hz : TendstoUniformlyOn (fun n z => f (ns (φ n)) z - f (ns (φ n)) x)
      (fun z => (0 : ℂ)) atTop L := by
    apply (hu.fun_sub ((hl.tendsto_at hx).tendstoUniformlyOn_const L)).congr_right
    intro z hz
    simp only [hc z (hLU hz), hc x hx, sub_self]
  exact ⟨φ, by simpa [UniformOnFun.tendsto_iff_tendstoUniformlyOn, q, Function.comp_def] using hz⟩

end AreaDeficit
