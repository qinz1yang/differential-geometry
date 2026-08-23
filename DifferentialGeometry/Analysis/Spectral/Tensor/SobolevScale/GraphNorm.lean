import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorSobolevWeight_mul_one_add_lambda_sq
    (τ : ℝ) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i τ *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (τ + 2) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  rw [tensorSobolevWeight, tensorSobolevWeight,
    ← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) 2,
    ← Real.rpow_add hbase_pos]
  norm_num

def tensorHsAddTwoOfOneAddLambdaMul (τ : ℝ)
    (u z : tensorHs (I := I) (M := M) g r s τ)
    (hz : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      z.coeff i =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) * u.coeff i) :
    tensorHs (I := I) (M := M) g r s (τ + 2) where
  coeff := u.coeff
  weighted_summable := by
    have hmass :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (τ + 2) *
            (u.coeff i) ^ 2) =
        (fun i => tensorSobolevWeight (I := I) (M := M) i τ *
          (z.coeff i) ^ 2) := by
      funext i
      rw [hz i, mul_pow, ← mul_assoc,
        tensorSobolevWeight_mul_one_add_lambda_sq (I := I) (M := M) τ i]
    rw [hmass]
    exact z.weighted_summable

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsAddTwoOfOneAddLambdaMul_coeff (τ : ℝ)
    (u z : tensorHs (I := I) (M := M) g r s τ)
    (hz : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      z.coeff i =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) * u.coeff i)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsAddTwoOfOneAddLambdaMul (I := I) (M := M) τ u z hz).coeff i =
      u.coeff i :=
  rfl

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
