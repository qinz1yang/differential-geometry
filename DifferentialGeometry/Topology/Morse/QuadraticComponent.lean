import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen

open Set Metric

namespace OpenPartialHomeomorph

theorem closedBall_image_eq_connectedComponentIn_sublevel
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [T2Space M]
    (χ : OpenPartialHomeomorph E M) {r : ℝ} (hr : 0 ≤ r)
    (hcompact : IsCompact (closedBall (0 : E) r))
    (hsource : closedBall 0 r ⊆ χ.source)
    {f : M → ℝ} {α : ℝ} (hα : 0 < α)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = f (χ 0) + α / 2 * ‖y‖ ^ 2) :
    χ '' closedBall 0 r =
      connectedComponentIn (f ⁻¹' Iic (f (χ 0) + α / 2 * r ^ 2)) (χ 0) := by
  let S := f ⁻¹' Iic (f (χ 0) + α / 2 * r ^ 2)
  let K := χ '' closedBall 0 r
  have hK : K = S ∩ χ.target := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨?_, χ.map_source (hsource hy)⟩
      change f (χ y) ≤ f (χ 0) + α / 2 * r ^ 2
      rw [hnormal y (hsource hy)]
      have hy' := (sq_le_sq₀ (norm_nonneg y) hr).mpr (mem_closedBall_zero_iff.mp hy)
      exact add_le_add_right (mul_le_mul_of_nonneg_left hy' (half_pos hα).le) _
    · intro x hx
      refine ⟨χ.symm x, ?_, χ.right_inv hx.2⟩
      rw [mem_closedBall_zero_iff]
      have hn := hnormal (χ.symm x) (χ.map_target hx.2)
      rw [χ.right_inv hx.2] at hn
      apply (sq_le_sq₀ (norm_nonneg _) hr).mp
      apply (mul_le_mul_iff_right₀ (half_pos hα)).mp
      have hxle : f x ≤ f (χ 0) + α / 2 * r ^ 2 := hx.1
      linarith
  have hKclosed : IsClosed K :=
    (hcompact.image_of_continuousOn (χ.continuousOn.mono hsource)).isClosed
  have hKpre : IsPreconnected K :=
    (convex_closedBall (0 : E) r).isPreconnected.image χ (χ.continuousOn.mono hsource)
  have hzero : χ 0 ∈ K := mem_image_of_mem χ (mem_closedBall_self hr)
  have hKS : K ⊆ S := hK ▸ inter_subset_left
  have hclopen : IsClopen ((Subtype.val : S → M) ⁻¹' K) := by
    refine ⟨hKclosed.preimage continuous_subtype_val, ?_⟩
    have heq : (Subtype.val : S → M) ⁻¹' K = (Subtype.val : S → M) ⁻¹' χ.target := by
      ext x
      simp only [mem_preimage, hK, mem_inter_iff, x.property, true_and]
    rw [heq]
    exact χ.open_target.preimage continuous_subtype_val
  apply Subset.antisymm (hKpre.subset_connectedComponentIn hzero hKS)
  rw [connectedComponentIn_eq_image (hKS hzero)]
  rintro x ⟨y, hy, rfl⟩
  exact hclopen.connectedComponent_subset hzero hy

theorem closedBall_image_eq_connectedComponentIn_superlevel
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [T2Space M]
    (χ : OpenPartialHomeomorph E M) {r : ℝ} (hr : 0 ≤ r)
    (hcompact : IsCompact (closedBall (0 : E) r))
    (hsource : closedBall 0 r ⊆ χ.source)
    {f : M → ℝ} {α : ℝ} (hα : α < 0)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = f (χ 0) + α / 2 * ‖y‖ ^ 2) :
    χ '' closedBall 0 r =
      connectedComponentIn (f ⁻¹' Ici (f (χ 0) + α / 2 * r ^ 2)) (χ 0) := by
  have h := χ.closedBall_image_eq_connectedComponentIn_sublevel hr hcompact hsource
    (neg_pos.mpr hα) (f := -f) (fun y hy => by
      simp only [Pi.neg_apply, hnormal y hy]
      ring)
  have heq : (-f) ⁻¹' Iic (-f (χ 0) + -α / 2 * r ^ 2) =
      f ⁻¹' Ici (f (χ 0) + α / 2 * r ^ 2) := by
    ext x
    change -f x ≤ -f (χ 0) + -α / 2 * r ^ 2 ↔ f (χ 0) + α / 2 * r ^ 2 ≤ f x
    constructor <;> intro hx <;> linarith
  exact h.trans (congrArg (fun S => connectedComponentIn S (χ 0)) heq)

end OpenPartialHomeomorph
