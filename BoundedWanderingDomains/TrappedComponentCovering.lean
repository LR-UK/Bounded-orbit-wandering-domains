import BoundedWanderingDomains.HolomorphicLifting
import BoundedWanderingDomains.LocalTrappedTopology

open Set Metric Function Filter
open scoped Topology

namespace AreaDeficit

/-- A finite set can meet only finitely many members of a disjoint sequence. -/
theorem eventually_disjoint_finite {α : Type*} {U : ℕ → Set α}
    (hU : Pairwise (fun n m => Disjoint (U n) (U m)))
    {E : Set α} (hE : E.Finite) : ∀ᶠ n in atTop, Disjoint (U n) E := by
  classical
  have hpoint : ∀ x, ∀ᶠ n in atTop, x ∉ U n := by
    intro x
    by_cases hx : ∃ m, x ∈ U m
    · obtain ⟨m, hm⟩ := hx
      filter_upwards [eventually_gt_atTop m] with n hn hx
      exact disjoint_left.mp (hU (ne_of_gt hn)) hx hm
    · exact Eventually.of_forall (by simpa only [not_exists] using hx)
  have hh := hE.eventually_all.mpr (fun x _ => hpoint x)
  filter_upwards [hh] with n hn
  exact disjoint_left.mpr (fun x hx he => hn x he hx)

/-- Compactness and local nonconstancy make the wandering tail unramified. -/
theorem eventually_deriv_ne_zero_on_disjoint_domains {f : ℂ → ℂ}
    {K : Set ℂ} {U : ℕ → Set ℂ} (hK : IsCompact K)
    (hf : AnalyticOnNhd ℂ f K) (hn : ∀ x ∈ K, ¬EventuallyConst f (𝓝 x))
    (hUK : ∀ n, U n ⊆ K)
    (hU : Pairwise (fun n m => Disjoint (U n) (U m))) :
    ∀ᶠ n in atTop, ∀ x ∈ U n, deriv f x ≠ 0 := by
  filter_upwards [eventually_disjoint_finite hU (finite_local_critical_points hK hf hn)]
    with n h x hx hd
  exact disjoint_left.mp h hx ⟨hUK n hx, hd⟩

/-- The trapped interior is backward invariant as long as the preimage stays in V. -/
theorem trapped_interior_backward {f : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V) (hf : ContinuousOn f V) :
    V ∩ f ⁻¹' interior (trappedSet f V) ⊆ interior (trappedSet f V) := by
  have hopen : IsOpen (V ∩ f ⁻¹' interior (trappedSet f V)) :=
    hf.isOpen_inter_preimage hV isOpen_interior
  apply hopen.subset_interior_iff.mpr
  rintro x ⟨hx, hfx⟩ n
  cases n with
  | zero => exact hx
  | succ n => simpa only [iterate_succ_apply] using interior_subset hfx n

/-- A component is relatively closed in its ambient set. -/
theorem closure_component_inter_subset {S : Set ℂ} {z : ℂ} (hz : z ∈ S) :
    closure (connectedComponentIn S z) ∩ S ⊆ connectedComponentIn S z := by
  rintro x ⟨hxc, hxS⟩
  have hc : IsPreconnected (insert x (connectedComponentIn S z)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hxc subset_closure)
  exact hc.subset_connectedComponentIn
    (mem_insert_of_mem _ (mem_connectedComponentIn hz))
    (insert_subset hxS (connectedComponentIn_subset _ _)) (mem_insert _ _)

/-- No boundary point of a compactly contained trapped component maps into
the trapped interior. This supplies the properness needed for covering theory. -/
theorem closure_component_preimage_trapped {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ}
    (hV : IsOpen V) (hf : ContinuousOn f V) (hK : IsClosed K) (hKV : K ⊆ V)
    (hz : z ∈ interior (trappedSet f V))
    (hUK : connectedComponentIn (interior (trappedSet f V)) z ⊆ K) :
    ∀ x ∈ closure (connectedComponentIn (interior (trappedSet f V)) z),
      f x ∈ interior (trappedSet f V) →
      x ∈ connectedComponentIn (interior (trappedSet f V)) z := by
  intro x hxc hfx
  exact closure_component_inter_subset hz ⟨hxc,
    trapped_interior_backward hV hf ⟨hKV (closure_minimal hUK hK hxc), hfx⟩⟩

/-- A covering is injective on a simply connected source domain whose
image lies in a simply connected target domain, by uniqueness of lifts. -/
theorem covering_injOn_domain {f : ℂ → ℂ} {U W K : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hW : IsOpen W) (hWc : IsSimplyConnected W)
    (hz : z ∈ U) (hUK : U ⊆ K) (hf : ContinuousOn f U)
    (hm : MapsTo f U W) (hcov : IsCoveringMapOn (fun x : K => f x) W) :
    InjOn f U := by
  let := hUc.simplyConnectedSpace
  let := hWc.simplyConnectedSpace
  let := hU.locallyPathConnectedSpace
  let := hW.locallyPathConnectedSpace
  obtain ⟨H, ⟨hH0, hH⟩, _⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨Subtype.val, continuous_subtype_val⟩ : C(W, ℂ))
    (a₀ := ⟨f z, hm hz⟩) (e₀ := ⟨z, hUK hz⟩) rfl (fun x => x.2)
  let F : C(U, K) := H.comp ⟨fun x => ⟨f x, hm x.2⟩,
    hf.domRestrict.subtype_mk _⟩
  let I : C(U, K) := ⟨fun x => ⟨x, hUK x.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  obtain ⟨L, _, huniq⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨U.domRestrict f, hf.domRestrict⟩ : C(U, ℂ))
    (a₀ := ⟨z, hz⟩) (e₀ := ⟨z, hUK hz⟩) rfl (fun x => hm x.2)
  have hF : F = L := huniq F ⟨hH0, by
    funext x
    exact congrFun hH ⟨f x, hm x.2⟩⟩
  have hI : I = L := huniq I ⟨rfl, rfl⟩
  have hFI := hF.trans hI.symm
  intro x hx y hy hxy
  have hFx : H ⟨f x, hm hx⟩ = (⟨x, hUK hx⟩ : K) :=
    congrArg (fun M : C(U, K) => M ⟨x, hx⟩) hFI
  have hFy : H ⟨f y, hm hy⟩ = (⟨y, hUK hy⟩ : K) :=
    congrArg (fun M : C(U, K) => M ⟨y, hy⟩) hFI
  exact congrArg Subtype.val (hFx.symm.trans
    ((congrArg H (Subtype.ext hxy)).trans hFy))

/-- An unramified, compactly contained trapped component maps injectively
to a simply connected successor component. -/
theorem trapped_component_injOn {f : ℂ → ℂ} {V K : Set ℂ} {z : ℂ}
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : AnalyticOnNhd ℂ f V)
    (hz : z ∈ interior (trappedSet f V))
    (hUK : connectedComponentIn (interior (trappedSet f V)) z ⊆ K)
    (hsc : IsSimplyConnected (connectedComponentIn (interior (trappedSet f V)) z))
    (hsc' : IsSimplyConnected (connectedComponentIn (interior (trappedSet f V)) (f z)))
    (hm : MapsTo f (connectedComponentIn (interior (trappedSet f V)) z)
      (connectedComponentIn (interior (trappedSet f V)) (f z)))
    (hreg : ∀ x ∈ connectedComponentIn (interior (trappedSet f V)) z, deriv f x ≠ 0) :
    InjOn f (connectedComponentIn (interior (trappedSet f V)) z) := by
  let U := connectedComponentIn (interior (trappedSet f V)) z
  let W := connectedComponentIn (interior (trappedSet f V)) (f z)
  have hU : IsOpen U := isOpen_interior.connectedComponentIn
  have hW : IsOpen W := isOpen_interior.connectedComponentIn
  have hclK : closure U ⊆ K := closure_minimal hUK hK.isClosed
  have hc : IsCompact (closure U) := hK.of_isClosed_subset isClosed_closure hclK
  have hfa : AnalyticOnNhd ℂ f (closure U) := hf.mono (hclK.trans hKV)
  have hback : ∀ x ∈ closure U, f x ∈ W → x ∈ U := by
    intro x hx hfx
    exact closure_component_preimage_trapped hV hf.continuousOn hK.isClosed hKV hz
      hUK x hx (connectedComponentIn_subset _ _ hfx)
  have hcov : IsCoveringMapOn (fun x : closure U => f x) W := by
    apply compact_analytic_covering hc hfa
    · intro x hx hfx
      exact (hU.subset_interior_iff.mpr subset_closure) (hback x hx hfx)
    · intro x hx hfx
      exact hreg x (hback x hx hfx)
  exact covering_injOn_domain hU hsc hW hsc' (mem_connectedComponentIn hz)
    subset_closure (hfa.continuousOn.mono subset_closure) hm hcov

end AreaDeficit

#print axioms AreaDeficit.eventually_deriv_ne_zero_on_disjoint_domains
#print axioms AreaDeficit.closure_component_preimage_trapped
