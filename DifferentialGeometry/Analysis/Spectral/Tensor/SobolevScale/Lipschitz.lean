import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

open scoped Manifold ContDiff NNReal BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}
  {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}

theorem TensorHs.lipschitzWith_of_coeff_bound
    (f : X → TensorHs (I := I) (M := M) g r s σ)
    (hbound : ∀ x y, (∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
      ((f x).coeff i - (f y).coeff i) ^ 2) ≤ ((K : ℝ) * dist x y) ^ 2) :
    LipschitzWith K f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hnorm : ‖f x - f y‖ ^ 2 ≤ ((K : ℝ) * dist x y) ^ 2 := by
    rw [TensorHs.norm_sq_eq_tsum]
    simpa only [sub_eq_add_neg, TensorHs.add_coeff, TensorHs.neg_coeff] using hbound x y
  rw [dist_eq_norm]
  calc
    ‖f x - f y‖ = Real.sqrt (‖f x - f y‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((K : ℝ) * dist x y) ^ 2) := Real.sqrt_le_sqrt hnorm
    _ = (K : ℝ) * dist x y := Real.sqrt_sq (mul_nonneg K.coe_nonneg dist_nonneg)

theorem TensorHs.lipschitzWith_of_l2_coeff_bound
    (f : X → TensorHs (I := I) (M := M) g r s σ)
    (F : X → TensorL2 r s g)
    (hcompact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (hcoeff : ∀ x i, (f x).coeff i = tensorL2Coeff (I := I) (M := M) hcompact (F x) i)
    (hbound : ∀ x y, (∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
      (tensorL2Coeff (I := I) (M := M) hcompact (F x - F y) i) ^ 2) ≤
        ((K : ℝ) * dist x y) ^ 2) :
    LipschitzWith K f := by
  have hsub (x y : X) (i : TensorEigenIdx (I := I) (M := M) g r s) :
      tensorL2Coeff (I := I) (M := M) hcompact (F x - F y) i =
        tensorL2Coeff (I := I) (M := M) hcompact (F x) i -
          tensorL2Coeff (I := I) (M := M) hcompact (F y) i := by
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  refine TensorHs.lipschitzWith_of_coeff_bound f fun x y => ?_
  simpa only [hcoeff, hsub] using hbound x y

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
