import DifferentialGeometry.Analysis.Convex.SupConvolution
import DifferentialGeometry.Analysis.Calculus.Taylor

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis.Viscosity

open DifferentialGeometry.Analysis.Convex

theorem le_zero_of_upper_test_supConvolutionOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} {K : ℝ≥0} (hs : IsCompact s) (hu : LipschitzOnWith K u s)
    {ε : ℝ} (hε : 0 < ε) {x : E} (hx : Metric.closedBall x (2 * ε * K) ⊆ interior s)
    {H : ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}
    (hH : ∀ p B, Monotone (fun r => H r p B))
    (hsub : ∀ y ∈ interior s, ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun z => u z - ψ z) y → H (u y) (fderiv ℝ ψ y) (fderiv ℝ (fderiv ℝ ψ) y) ≤ 0)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hm : IsLocalMax (fun z => supConvolutionOn s u ε z - φ z) x) :
    H (supConvolutionOn s u ε x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0 := by
  have hxs : x ∈ s := interior_subset (hx (Metric.mem_closedBall_self (by positivity)))
  obtain ⟨y, hy, hmax⟩ := exists_supConvolutionOn_eq_of_isCompact hs ⟨x, hxs⟩
    hu.continuousOn.upperSemicontinuousOn ε x
  have hyi : y ∈ interior s := by
    apply hx
    rw [Metric.mem_closedBall, dist_comm]
    exact dist_le_of_supConvolutionOn_eq hu hε hxs hy hmax
  have hbound : BddAbove (u '' s) := hs.bddAbove_image hu.continuousOn
  have htest := isLocalMax_sub_translate_of_supConvolutionOn hbound hε hyi hmax hm
  have htranslate (z : E) : x + (z - y) = z + (x - y) := by abel
  simp_rw [htranslate] at htest
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => φ (z + (x - y))) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have hle := hsub y hyi _ hsmooth htest
  have hxy : y + (x - y) = x := by abel
  have hD : fderiv ℝ (fun z => φ (z + (x - y))) y = fderiv ℝ φ x := by
    rw [DifferentialGeometry.Analysis.fderiv_translate φ (x - y) y
      (hφ.differentiable (by simp) _), hxy]
  have hDD : fderiv ℝ (fderiv ℝ (fun z => φ (z + (x - y)))) y =
      fderiv ℝ (fderiv ℝ φ) x := by
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    rw [DifferentialGeometry.Analysis.fderiv_fderiv_translate φ hφ2 (x - y) y, hxy]
  rw [hD, hDD] at hle
  apply le_trans (hH _ _ ?_) hle
  rw [hmax]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

end DifferentialGeometry.Analysis.Viscosity
