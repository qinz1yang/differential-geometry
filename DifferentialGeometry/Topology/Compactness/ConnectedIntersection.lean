import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Set

theorem IsCompact.isPreconnected_iInter_of_directed {X ι : Type*}
    [TopologicalSpace X] [T2Space X] {K : ι → Set X} {i₀ : ι}
    (hcompact : IsCompact (K i₀)) (hclosed : ∀ i, IsClosed (K i))
    (hdir : Directed (· ⊇ ·) K)
    (hconn : ∀ i, IsPreconnected (K i)) : IsPreconnected (⋂ i, K i) := by
  classical
  let S := ⋂ i, K i
  let : Nonempty ι := ⟨i₀⟩
  have hSc : IsCompact S := hcompact.of_isClosed_subset
    (isClosed_iInter hclosed) (iInter_subset K i₀)
  apply isPreconnected_closed_iff.mpr
  intro F G hF hG hcover hSF hSG
  by_contra hmeet
  have hdisj : Disjoint (S ∩ F) (S ∩ G) := by
    apply disjoint_left.mpr
    intro x hxF hxG
    exact hmeet ⟨x, hxF.1, hxF.2, hxG.2⟩
  obtain ⟨U, V, hU, hV, hSFU, hSGV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hSc.inter_right hF) (hSc.inter_right hG) hdisj
  have hScover : S ⊆ U ∪ V := by
    intro x hx
    rcases hcover hx with hxF | hxG
    · exact Or.inl (hSFU ⟨hx, hxF⟩)
    · exact Or.inr (hSGV ⟨hx, hxG⟩)
  have hex : ∃ i, K i ⊆ U ∪ V := by
    have hempty : (K i₀ ∩ (U ∪ V)ᶜ) ∩ ⋂ i, K i = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxS⟩
      exact hx.2 (hScover hxS)
    obtain ⟨i, hi⟩ :=
      (hcompact.inter_right (hU.union hV).isClosed_compl).elim_directed_family_closed
        K hclosed (disjoint_iff_inter_eq_empty.mpr hempty) hdir
    obtain ⟨k, hk₀, hki⟩ := hdir i₀ i
    refine ⟨k, ?_⟩
    intro x hx
    by_contra hxUV
    have hm : x ∈ (K i₀ ∩ (U ∪ V)ᶜ) ∩ K i := ⟨⟨hk₀ hx, hxUV⟩, hki hx⟩
    exact hi.le_bot hm
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x, hxS, hxF⟩ := hSF
  obtain ⟨y, hyS, hyG⟩ := hSG
  obtain ⟨z, _, hzU, hzV⟩ := hconn i U V hU hV hi
    ⟨x, mem_iInter.mp hxS i, hSFU ⟨hxS, hxF⟩⟩
    ⟨y, mem_iInter.mp hyS i, hSGV ⟨hyS, hyG⟩⟩
  exact disjoint_left.mp hUV hzU hzV

theorem IsCompact.isConnected_iInter_of_directed {X ι : Type*}
    [TopologicalSpace X] [T2Space X] {K : ι → Set X} {i₀ : ι}
    (hcompact : IsCompact (K i₀)) (hclosed : ∀ i, IsClosed (K i))
    (hdir : Directed (· ⊇ ·) K)
    (hconn : ∀ i, IsConnected (K i)) : IsConnected (⋂ i, K i) := by
  let : Nonempty ι := ⟨i₀⟩
  refine ⟨?_, hcompact.isPreconnected_iInter_of_directed hclosed hdir
    (fun i => (hconn i).isPreconnected)⟩
  by_contra h
  have hempty : K i₀ ∩ ⋂ i, K i = ∅ := by rw [not_nonempty_iff_eq_empty.mp h, inter_empty]
  obtain ⟨i, hi⟩ := hcompact.elim_directed_family_closed K hclosed
    (disjoint_iff_inter_eq_empty.mpr hempty) hdir
  obtain ⟨k, hk₀, hki⟩ := hdir i₀ i
  obtain ⟨x, hx⟩ := (hconn k).nonempty
  have hm : x ∈ K i₀ ∩ K i := ⟨hk₀ hx, hki hx⟩
  exact hi.le_bot hm

theorem Continuous.isPreconnected_ge_of_isPreconnected_gt {X α : Type*}
    [TopologicalSpace X] [T2Space X] [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderClosedTopology α] {f : X → α} (hf : Continuous f)
    {b c : α} (hbc : b < c) (hb : IsCompact {x | b ≤ f x})
    (hc : ∀ t ∈ Ioo b c, IsPreconnected {x | t < f x}) :
    IsPreconnected {x | c ≤ f x} := by
  let K : Ioo b c → Set X := fun t => closure {x | t.val < f x}
  obtain ⟨t₀, ht₀b, ht₀c⟩ := exists_between hbc
  have hK (t : Ioo b c) : IsCompact (K t) := hb.of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx => le_trans t.property.1.le hx.le)
      (isClosed_le continuous_const hf))
  have hdir : Directed (· ⊇ ·) K := by
    intro u v
    refine ⟨⟨max u.val v.val, lt_max_of_lt_left u.property.1,
      max_lt u.property.2 v.property.2⟩, ?_, ?_⟩
    · exact closure_mono (fun x hx => lt_of_le_of_lt (le_max_left _ _) hx)
    · exact closure_mono (fun x hx => lt_of_le_of_lt (le_max_right _ _) hx)
  have heq : (⋂ t, K t) = {x | c ≤ f x} := by
    ext x
    constructor
    · intro hx
      by_contra hcx
      obtain ⟨t, ht, htc⟩ := exists_between (max_lt hbc (lt_of_not_ge hcx))
      have htb : b < t := lt_of_le_of_lt (le_max_left _ _) ht
      have htfx : t ≤ f x :=
        closure_minimal (fun y hy => hy.le) (isClosed_le continuous_const hf)
          (mem_iInter.mp hx ⟨t, htb, htc⟩)
      exact (lt_of_le_of_lt (le_max_right _ _) ht).not_ge htfx
    · intro hx
      exact mem_iInter.mpr fun t => subset_closure (lt_of_lt_of_le t.property.2 hx)
  rw [← heq]
  exact (hK ⟨t₀, ht₀b, ht₀c⟩).isPreconnected_iInter_of_directed
    (fun _ => isClosed_closure) hdir (fun t => (hc t.val t.property).closure)

theorem Continuous.isPreconnected_le_of_isPreconnected_lt {X α : Type*}
    [TopologicalSpace X] [T2Space X] [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderClosedTopology α] {f : X → α} (hf : Continuous f)
    {b c : α} (hcb : c < b) (hb : IsCompact {x | f x ≤ b})
    (hc : ∀ t ∈ Ioo c b, IsPreconnected {x | f x < t}) :
    IsPreconnected {x | f x ≤ c} := by
  exact Continuous.isPreconnected_ge_of_isPreconnected_gt (α := OrderDual α)
    (f := f) (b := b) (c := c) hf hcb hb (fun t ht => hc t ⟨ht.2, ht.1⟩)

open Topology

namespace DifferentialGeometry.Topology

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]

theorem isPreconnected_iInter_of_directed_isCompact [Nonempty ι] (C : ι → Set X)
    (hdir : Directed (· ⊇ ·) C) (hcompact : ∀ i, IsCompact (C i))
    (hconn : ∀ i, IsPreconnected (C i)) : IsPreconnected (⋂ i, C i) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact (hcompact i₀).isPreconnected_iInter_of_directed
    (fun i => (hcompact i).isClosed) hdir hconn

theorem isPreconnected_inter_le_of_isCompact_of_forall_inter_lt
    {S : Set X} (hS : IsCompact S) {f : X → ℝ} (hf : ContinuousOn f S) (r : ℝ)
    (hconn : ∀ t, r < t → IsPreconnected (S ∩ {x | f x < t})) :
    IsPreconnected (S ∩ {x | f x ≤ r}) := by
  let C := fun t : Ioi r => closure (S ∩ {x | f x < t})
  have hnonempty : Nonempty (Ioi r) := ⟨⟨r + 1, by change r < r + 1; linarith⟩⟩
  let _ := hnonempty
  have hsub (t : Ioi r) : C t ⊆ S ∩ {x | f x ≤ t} :=
    closure_minimal (fun _ hx => ⟨hx.1, le_of_lt (show f _ < t from hx.2)⟩)
      (hf.preimage_isClosed_of_isClosed hS.isClosed isClosed_Iic)
  have heq : (⋂ t, C t) = S ∩ {x | f x ≤ r} := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨(hsub ⟨r + 1, by change r < r + 1; linarith⟩ (mem_iInter.mp hx _)).1, ?_⟩
      change f x ≤ r
      apply le_of_forall_gt_imp_ge_of_dense
      intro t ht
      exact (hsub ⟨t, ht⟩ (mem_iInter.mp hx _)).2
    · intro x hx
      exact mem_iInter.mpr fun t => subset_closure
        ⟨hx.1, lt_of_le_of_lt (show f x ≤ r from hx.2) t.2⟩
  rw [← heq]
  apply isPreconnected_iInter_of_directed_isCompact C
  · intro s t
    refine ⟨⟨min s t, (show r < min (s : ℝ) (t : ℝ) from lt_min (show r < s from s.2) (show r < t
        from t.2))⟩, ?_, ?_⟩
    · exact closure_mono (fun _ hx => ⟨hx.1, lt_of_lt_of_le (show f _ < min s t from hx.2)
        (min_le_left _ _)⟩)
    · exact closure_mono (fun _ hx => ⟨hx.1, lt_of_lt_of_le (show f _ < min s t from hx.2)
        (min_le_right _ _)⟩)
  · intro t
    exact hS.of_isClosed_subset isClosed_closure ((hsub t).trans inter_subset_left)
  · intro t
    exact (hconn t t.2).closure

theorem isPreconnected_inter_ge_of_isCompact_of_forall_inter_gt
    {S : Set X} (hS : IsCompact S) {f : X → ℝ} (hf : ContinuousOn f S) (r : ℝ)
    (hconn : ∀ t, t < r → IsPreconnected (S ∩ {x | t < f x})) :
    IsPreconnected (S ∩ {x | r ≤ f x}) := by
  have h := isPreconnected_inter_le_of_isCompact_of_forall_inter_lt hS hf.neg (-r) (by
    intro t ht
    have ht' : -t < r := by linarith
    change IsPreconnected (S ∩ {x | -f x < t})
    simpa only [neg_lt] using hconn (-t) ht')
  change IsPreconnected (S ∩ {x | -f x ≤ -r}) at h
  simpa only [neg_le_neg_iff] using h

end DifferentialGeometry.Topology
