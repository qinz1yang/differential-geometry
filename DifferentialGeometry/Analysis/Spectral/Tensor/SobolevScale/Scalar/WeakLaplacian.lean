import DifferentialGeometry.Analysis.Heat.Smoothing.Scalar.SpectralIdentification

noncomputable section
open scoped Manifold ContDiff InnerProductSpace RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem tensorHs_coeff_eq_of_weak_laplacian
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (u : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs g 0 0 σ)
    (f : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs g 0 0 τ)
    (hweak : ∀ T : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 0,
      ⟪DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 T,
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsToL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) hτ f)⟫_ℝ =
      ⟪DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2
          (DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth g 0 0 T),
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsToL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) hσ u)⟫_ℝ)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx g 0 0) :
    f.coeff i =
      -DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda i * u.coeff i := by
  have h := hweak
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth g 0 0 i)
  rw [DifferentialGeometry.Analysis.HeatEquation.tensorEigen00_rawLap_eq,
    real_inner_smul_left] at h
  rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_apply,
    DifferentialGeometry.Analysis.HeatEquation.eigenvectorSmooth00_eq_basis,
    ← DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
    ← DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsToL2_tensorL2Coeff,
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsToL2_tensorL2Coeff] at h
  exact h

end DifferentialGeometry.Analysis.Spectral
