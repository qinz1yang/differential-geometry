import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralSmoothRepresentative
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open Parabolic.TensorHeatEquation
open MetricRealization
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem summable_weighted_heat_trace
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (htail : EigenvalueTailSummable (I := I) (M := M) g r s)
    (σ : ℝ) (hσ : 0 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        Real.exp (-(2 * (TensorEigenIdx.lambda (I := I) (M := M) i) * ε))) := by
  obtain ⟨p, hp_pos, htp⟩ := htail
  set C : ℝ := tensorSmoothingConst (σ + p) * (min ε 1) ^ (-(σ + p)) with hC
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (htp.mul_left C)
  · exact mul_nonneg (tensorSobolevWeight_nonneg _ _) (Real.exp_pos _).le
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
        ((1 + lam) ^ (σ + p)) * ((1 + lam) ^ (-p)) := by
      unfold tensorSobolevWeight
      rw [hlam, ← Real.rpow_add hbase_pos]; congr 1; ring
    have hbound := tensorSmoothingScalarBound_of_pos
      (μ := σ + p) (by linarith) (t := ε) hε (lam := lam) hlam_nn
    calc tensorSobolevWeight (I := I) (M := M) i σ *
            Real.exp (-(2 * lam * ε))
        = ((1 + lam) ^ (σ + p) * Real.exp (-(2 * lam * ε))) * ((1 + lam) ^ (-p)) := by
          rw [hsplit]; ring
      _ ≤ C * ((1 + lam) ^ (-p)) := by
          apply mul_le_mul_of_nonneg_right hbound
          exact Real.rpow_nonneg hbase_pos.le _

end DifferentialGeometry.Analysis.Spectral
