import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem hasDerivAt_normalized_branch_power (a z : ℂ) (m : ℕ) :
    HasDerivAt (fun w : ℂ => (w - a) ^ (m + 1) / ((m + 1 : ℕ) : ℂ))
      ((z - a) ^ m) z := by
  have hn : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  have hd := (((hasDerivAt_id z).sub_const a).pow (m + 1)).div_const
    ((m + 1 : ℕ) : ℂ)
  simpa only [Nat.add_sub_cancel, mul_one, mul_div_cancel_left₀ _ hn] using! hd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original chart map, projected using its original metric leading
plane, has its normalized power as first nonzero term. The remainder bound
comes from the actual derivative and the existing convex mean-value theorem. -/
theorem chartComplexGradient_leading_projection_expansion
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContDiffAt ℝ 1 B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z) :
    let proj := chartLeadingPlaneProjection g p (U a) (B a)
    let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (U z))
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ Metric.ball a r ⊆ s ∧
      (∀ z ∈ Metric.ball a r, U z ∈ (chartAt E p).source) ∧
      ∀ z ∈ Metric.ball a r,
        ‖F z - F a - (z - a) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖ ≤
          C * ‖z - a‖ ^ (m + 2) := by
  let proj := chartLeadingPlaneProjection g p (U a) (B a)
  let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (U z))
  let H : ℂ → ℂ := fun z => (z - a) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
  let J : ℂ → ℂ := fun z => F z - H z
  obtain ⟨C, r, hC, hr, hrs, hchart, herror⟩ :=
    chartComplexGradient_leading_projection_fderiv_error g hs hU hconformal ha hsrc
      hB hBne hfactor
  change ∀ z ∈ Metric.ball a r, ∀ v : ℂ,
    ‖fderiv ℝ F z v - (z - a) ^ m * v‖ ≤ C * ‖z - a‖ ^ (m + 1) * ‖v‖ at herror
  have hF (z : ℂ) (hz : z ∈ Metric.ball a r) : DifferentiableAt ℝ F z := by
    have hX : ContDiffAt ℝ 1 (fun w => extChartAt 𝓘(ℝ, E) p (U w)) z :=
      ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) (hchart z hz)).comp z
        (hU.contMDiffAt (hs.mem_nhds (hrs hz)))).contDiffAt
    exact proj.differentiableAt.comp z (hX.differentiableAt (by norm_num))
  have hH (z : ℂ) : DifferentiableAt ℝ H z :=
    (hasDerivAt_normalized_branch_power a z m).differentiableAt.restrictScalars ℝ
  have hHd (z v : ℂ) : fderiv ℝ H z v = (z - a) ^ m * v := by
    rw [((hasDerivAt_normalized_branch_power a z m).hasFDerivAt.restrictScalars ℝ).fderiv]
    change v * (z - a) ^ m = (z - a) ^ m * v
    exact mul_comm _ _
  have hJ (z : ℂ) (hz : z ∈ Metric.ball a r) : DifferentiableAt ℝ J z :=
    (hF z hz).sub (hH z)
  have hJd (z : ℂ) (hz : z ∈ Metric.ball a r) (v : ℂ) :
      fderiv ℝ J z v = fderiv ℝ F z v - (z - a) ^ m * v := by
    have hd : fderiv ℝ J z = fderiv ℝ F z - fderiv ℝ H z :=
      ((hF z hz).hasFDerivAt.sub (hH z).hasFDerivAt).fderiv
    rw [hd, sub_apply, hHd]
  refine ⟨C, r, hC, hr, hrs, hchart, ?_⟩
  intro z hz
  let K := Metric.closedBall a ‖z - a‖
  have hzlt : ‖z - a‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hK : K ⊆ Metric.ball a r := Metric.closedBall_subset_ball hzlt
  have haK : a ∈ K := Metric.mem_closedBall_self (norm_nonneg _)
  have hzK : z ∈ K := by simp only [K, Metric.mem_closedBall, dist_eq_norm, le_refl]
  have hnorm (w : ℂ) (hw : w ∈ K) :
      ‖fderiv ℝ J w‖ ≤ C * ‖z - a‖ ^ (m + 1) := by
    apply (fderiv ℝ J w).opNorm_le_bound
      (mul_nonneg hC.le (pow_nonneg (norm_nonneg _) _))
    intro v
    have hdist : ‖w - a‖ ≤ ‖z - a‖ := by
      simpa only [K, Metric.mem_closedBall, dist_eq_norm] using hw
    calc
      ‖fderiv ℝ J w v‖ = ‖fderiv ℝ F w v - (w - a) ^ m * v‖ := by
        rw [hJd w (hK hw)]
      _ ≤ C * ‖w - a‖ ^ (m + 1) * ‖v‖ := herror w (hK hw) v
      _ ≤ C * ‖z - a‖ ^ (m + 1) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hdist _) hC.le) (norm_nonneg _)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => hJ w (hK hw)) hnorm (convex_closedBall a ‖z - a‖) haK hzK
  have hHa : H a = 0 := by simp [H]
  have heq : J z - J a = F z - F a - H z := by
    dsimp only [J]
    rw [hHa]
    ring
  rw [heq] at hmv
  simpa only [mul_assoc, ← pow_succ] using hmv

end DifferentialGeometry.Geometry
