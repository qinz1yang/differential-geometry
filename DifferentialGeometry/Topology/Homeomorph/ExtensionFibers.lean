import DifferentialGeometry.Topology.Compactness.ConnectedIntersection
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas

section

open Set

namespace Homeomorph

private theorem denseRange_inclusion_closure
    {E : Type*} [TopologicalSpace E] {s K : Set E} (hclosure : closure s = K) :
    DenseRange (Set.inclusion (subset_closure.trans_eq hclosure) : s → K) := by
  apply (denseRange_inclusion_iff _).mpr
  rw [hclosure]

theorem surjective_extension_to_closure
    {E : Type*} [TopologicalSpace E] [T2Space E] {s K : Set E}
    (h : s ≃ₜ s) (hK : IsCompact K) (hclosure : closure s = K)
    (F : C(K, K))
    (hF : ∀ z : s, F (Set.inclusion (subset_closure.trans_eq hclosure) z) =
      Set.inclusion (subset_closure.trans_eq hclosure) (h z)) :
    Function.Surjective F := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let i : s → K := Set.inclusion (subset_closure.trans_eq hclosure)
  have hi : DenseRange i := denseRange_inclusion_closure hclosure
  have hsub : range i ⊆ range F := by
    rintro _ ⟨z, rfl⟩
    refine ⟨i (h.symm z), ?_⟩
    exact (hF (h.symm z)).trans (congrArg i (h.apply_symm_apply z))
  have hclosed : IsClosed (range F) := (isCompact_range F.continuous).isClosed
  intro y
  exact closure_minimal hsub hclosed (hi y)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s K : Set E}

theorem isPreconnected_fiber_extension_to_convex_closure
    (h : s ≃ₜ s) (hs : Convex ℝ s) (hK : IsCompact K) (hclosure : closure s = K)
    (F : C(K, K))
    (hF : ∀ z : s, F (Set.inclusion (subset_closure.trans_eq hclosure) z) =
      Set.inclusion (subset_closure.trans_eq hclosure) (h z)) (y : K) :
    IsPreconnected (F ⁻¹' {y}) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let i : s → K := Set.inclusion (subset_closure.trans_eq hclosure)
  have hi : DenseRange i := denseRange_inclusion_closure hclosure
  let f : K → ℝ := fun x => dist (F x) y
  have hf : Continuous f := F.continuous.dist continuous_const
  have hstrict (ε : ℝ) : IsPreconnected {x : K | f x < ε} := by
    have hlens : IsPreconnected ((Subtype.val : s → E) ⁻¹' Metric.ball (y : E) ε) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe]
      exact (hs.inter (convex_ball (y : E) ε)).isPreconnected
    have hpre : i ⁻¹' {x : K | f x < ε} =
        h ⁻¹' ((Subtype.val : s → E) ⁻¹' Metric.ball (y : E) ε) := by
      ext z
      change dist (F (i z)) y < ε ↔ dist (h z : E) (y : E) < ε
      rw [hF z]
      rfl
    have hpreconn : IsPreconnected (i ⁻¹' {x : K | f x < ε}) := by
      rw [hpre]
      exact h.isPreconnected_preimage.mpr hlens
    have himage : IsPreconnected (i '' (i ⁻¹' {x : K | f x < ε})) :=
      hpreconn.image i (continuous_inclusion _).continuousOn
    exact himage.subset_closure (image_preimage_subset _ _)
      (hi.subset_closure_image_preimage_of_isOpen (isOpen_lt hf continuous_const))
  have hzero : IsPreconnected {x : K | f x ≤ 0} :=
    hf.isPreconnected_le_of_isPreconnected_lt (by norm_num : (0 : ℝ) < 1)
      (isClosed_le hf continuous_const).isCompact (fun ε _ => hstrict ε)
  convert hzero using 1
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, f, dist_le_zero]

theorem isConnected_fiber_extension_to_convex_closure
    (h : s ≃ₜ s) (hs : Convex ℝ s) (hK : IsCompact K) (hclosure : closure s = K)
    (F : C(K, K))
    (hF : ∀ z : s, F (Set.inclusion (subset_closure.trans_eq hclosure) z) =
      Set.inclusion (subset_closure.trans_eq hclosure) (h z)) (y : K) :
    IsConnected (F ⁻¹' {y}) := by
  obtain ⟨x, hx⟩ := h.surjective_extension_to_closure hK hclosure F hF y
  exact ⟨⟨x, hx⟩, h.isPreconnected_fiber_extension_to_convex_closure hs hK hclosure F hF y⟩

theorem isConnected_fiber_extension_to_closedBall
    {c : E} {r : ℝ} (h : Metric.ball c r ≃ₜ Metric.ball c r)
    (hK : IsCompact (Metric.closedBall c r))
    (F : C(Metric.closedBall c r, Metric.closedBall c r))
    (hF : ∀ z : Metric.ball c r, F ⟨z, Metric.ball_subset_closedBall z.2⟩ =
      ⟨h z, Metric.ball_subset_closedBall (h z).2⟩) (y : Metric.closedBall c r) :
    IsConnected (F ⁻¹' {y}) := by
  by_cases hr : r = 0
  · subst r
    let : Subsingleton (Metric.closedBall c (0 : ℝ)) :=
      (Metric.subsingleton_closedBall c le_rfl).coe_sort
    have heq : F ⁻¹' {y} = univ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [heq]
    exact ⟨⟨y, mem_univ _⟩, isPreconnected_univ⟩
  · exact h.isConnected_fiber_extension_to_convex_closure (convex_ball c r)
      hK (closure_ball c hr) F hF y

end Homeomorph

end
