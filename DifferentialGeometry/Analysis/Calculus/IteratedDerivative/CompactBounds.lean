import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded








open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]


theorem iteratedFDeriv_comp_affine
    {f : E → F} {s : Set E} {k : ℕ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ k f s) (a : E) (L : G →L[ℝ] E)
    {x : G} (hx : a + L x ∈ s) :
    iteratedFDeriv ℝ k (fun y => f (a + L y)) x =
      (iteratedFDeriv ℝ k f (a + L x)).compContinuousLinearMap
        (fun _ : Fin k => L) := by
  let t := (fun y : E => a + y) ⁻¹' s
  have ht : IsOpen t := hs.preimage (continuous_const.add continuous_id)
  have hg : ContDiffOn ℝ k (fun y => f (a + y)) t :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun _ hy => hy)
  have h := L.iteratedFDerivWithin_comp_right hg ht.uniqueDiffOn
    (ht.preimage L.continuous).uniqueDiffOn hx (le_refl (k : ℕ∞ω))
  rw [iteratedFDerivWithin_of_isOpen k (ht.preimage L.continuous) hx,
    iteratedFDerivWithin_of_isOpen k ht hx,
    iteratedFDeriv_comp_add_left] at h
  exact h



theorem exists_bound_iteratedFDeriv_on_compact
    {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hK : IsCompact K) (hKs : K ⊆ s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k f) s :=
    (hf.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast le_top)
      hs.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen k hs hx).symm)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKs)
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩



theorem exists_bound_iteratedFDeriv_comp_affine_on_compact
    {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hK : IsCompact K) (hKs : K ⊆ s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E) (L : G →L[ℝ] E) (x : G), a + L x ∈ K →
      ‖iteratedFDeriv ℝ k (fun y => f (a + L y)) x‖ ≤ C * ‖L‖ ^ k := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_iteratedFDeriv_on_compact hs hf hK hKs k
  refine ⟨C, hC, fun a L x hx => ?_⟩
  rw [iteratedFDeriv_comp_affine (k := k) hs (hf.of_le (by exact_mod_cast le_top)) a L (hKs hx)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (a + L x)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k f (a + L x)‖ * ‖L‖ ^ k := by simp
    _ ≤ C * ‖L‖ ^ k := mul_le_mul_of_nonneg_right (hbound _ hx) (by positivity)

end DifferentialGeometry.Analysis
