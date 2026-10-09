/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]

theorem isPreconnected_iInter_of_directed_isCompact [Nonempty ι] (C : ι → Set X)
    (hdir : Directed (· ⊇ ·) C) (hcompact : ∀ i, IsCompact (C i))
    (hconn : ∀ i, IsPreconnected (C i)) : IsPreconnected (⋂ i, C i) := by
  classical
  have hclosed : IsClosed (⋂ i, C i) := isClosed_iInter fun i => (hcompact i).isClosed
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hcap : IsCompact (⋂ i, C i) :=
    (hcompact i₀).of_isClosed_subset hclosed (iInter_subset C i₀)
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hclosed).mpr
  intro A B hA hB hcover hdis
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hcap.inter_right hA) (hcap.inter_right hB)
      (hdis.mono inter_subset_right inter_subset_right)
  have hcover' : (⋂ i, C i) ⊆ U ∪ V := by
    intro x hx
    exact (hcover hx).elim (fun h => Or.inl (hAU ⟨hx, h⟩))
      (fun h => Or.inr (hBV ⟨hx, h⟩))
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact' hdir hcompact
    (fun i => (hcompact i).isClosed)
    (mem_nhdsSet_iff_forall.mpr fun x hx => (hU.union hV).mem_nhds (hcover' hx))
  rcases (hconn i).subset_or_subset hU hV hUV hi with hCU | hCV
  · refine Or.inl fun x hx => (hcover hx).resolve_right ?_
    intro hxB
    exact hUV.le_bot ⟨hCU (iInter_subset C i hx), hBV ⟨hx, hxB⟩⟩
  · refine Or.inr fun x hx => (hcover hx).resolve_left ?_
    intro hxA
    exact hUV.le_bot ⟨hAU ⟨hx, hxA⟩, hCV (iInter_subset C i hx)⟩

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
