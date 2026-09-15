import DifferentialGeometry.Analysis.Heat.Smoothing.Scalar.HeatFlow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section

open MeasureTheory
open scoped ENNReal Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

def scalarH0EquivLp (g : SmoothRiemannianMetric I M) :
    TensorHs g 0 0 0 ≃ₗᵢ[ℝ] Lp ℝ 2 (riemannianVolumeMeasure I M g) :=
  (tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)).trans
    (tensor00ScalarL2Equiv g)

def scalarH0ContinuousMul (g : SmoothRiemannianMetric I M) :
    C(M, ℝ) →L[ℝ] TensorHs g 0 0 0 →L[ℝ] TensorHs g 0 0 0 :=
  let e := (scalarH0EquivLp g).symm.toContinuousLinearEquiv
  (ContinuousLinearEquiv.arrowCongr e e).toContinuousLinearMap.comp
    ((ContinuousLinearMap.holderL (riemannianVolumeMeasure I M g) ∞ 2 2 (ContinuousLinearMap.mul ℝ ℝ)).comp
      (ContinuousMap.toLp ∞ (riemannianVolumeMeasure I M g) ℝ))

theorem scalarH0EquivLp_scalarH0ContinuousMul (g : SmoothRiemannianMetric I M)
    (a : C(M, ℝ)) (u : TensorHs g 0 0 0) :
    scalarH0EquivLp g (scalarH0ContinuousMul g a u) =ᵐ[riemannianVolumeMeasure I M g]
      fun x => a x * scalarH0EquivLp g u x := by
  change (scalarH0EquivLp g)
    ((scalarH0EquivLp g).symm
      ((ContinuousLinearMap.mul ℝ ℝ).holder 2
        (ContinuousMap.toLp ∞ (riemannianVolumeMeasure I M g) ℝ a)
        (scalarH0EquivLp g u))) =ᵐ[_] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  filter_upwards [(ContinuousLinearMap.coeFn_holder (μ := riemannianVolumeMeasure I M g) (p := ∞) (q := 2) (r := 2) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousMap.toLp ∞ (riemannianVolumeMeasure I M g) ℝ a) (scalarH0EquivLp g u)),
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := ∞) (riemannianVolumeMeasure I M g) a] with x hx ha
  simpa only [ContinuousLinearMap.mul_apply', ha] using hx

theorem norm_scalarH0ContinuousMul_apply_le (g : SmoothRiemannianMetric I M)
    (a : C(M, ℝ)) (u : TensorHs g 0 0 0) :
    ‖scalarH0ContinuousMul g a u‖ ≤ ‖a‖ * ‖u‖ := by
  rw [← (scalarH0EquivLp g).norm_map (scalarH0ContinuousMul g a u),
    ← (scalarH0EquivLp g).norm_map u]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarH0EquivLp_scalarH0ContinuousMul g a u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm a x) (norm_nonneg _)

theorem norm_scalarH0ContinuousMul_le (g : SmoothRiemannianMetric I M) :
    ‖scalarH0ContinuousMul g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  simpa only [one_mul] using norm_scalarH0ContinuousMul_apply_le g a u

theorem scalarH0EquivLp_ccTensorToHs (g : SmoothRiemannianMetric I M)
    (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 0) :
    scalarH0EquivLp g (ccTensorToHs g 0 0 S) =ᵐ[riemannianVolumeMeasure I M g]
      DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0 S.toSection := by
  have h : tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)
      (ccTensorToHs g 0 0 S) = DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 S := by
    apply (tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)).symm.injective
    rw [LinearIsometryEquiv.symm_apply_apply]
    apply TensorHs.ext
    funext i
    rw [tensorHsZeroEquivL2_symm_coeff, ccTensorToHs_coeff]
  change (tensor00ScalarL2Equiv g
    (tensorHsZeroEquivL2 (tensorResolventL2_isCompactOperator g 0 0)
      (ccTensorToHs g 0 0 S)) : M → ℝ) =ᵐ[_] _
  rw [h]
  change (tensor00ToScalarL2 g
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 S) : M → ℝ) =ᵐ[_] _
  rw [tensor00ToScalarL2_toL2]
  exact (scalar0Cc g S).memLp_two.coeFn_toLp

theorem scalarH0ContinuousMul_ccTensorToHs (g : SmoothRiemannianMetric I M)
    (a : C^∞⟮I, M; ℝ⟯) (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 0) :
    scalarH0ContinuousMul g ⟨a, a.2.continuous⟩ (ccTensorToHs g 0 0 S) =
      ccTensorToHs g 0 0
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul g 0 0 a S) := by
  apply (scalarH0EquivLp g).injective
  apply Lp.ext
  filter_upwards [scalarH0EquivLp_scalarH0ContinuousMul g ⟨a, a.2.continuous⟩
      (ccTensorToHs g 0 0 S), scalarH0EquivLp_ccTensorToHs g S,
    scalarH0EquivLp_ccTensorToHs g
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul g 0 0 a S)]
      with x hx hu hv
  rw [hx, hu, hv]
  exact (DifferentialGeometry.Analysis.Sobolev.scalar0_smul_cc g a S x).symm

end DifferentialGeometry.Analysis.Spectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal Manifold ContDiff
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

theorem scalarH0ContinuousMul_const (g : SmoothRiemannianMetric I M)
    (c : ℝ) (u : TensorHs g 0 0 0) :
    scalarH0ContinuousMul g (ContinuousMap.const M c) u = c • u := by
  apply (scalarH0EquivLp g).injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [scalarH0EquivLp_scalarH0ContinuousMul g (ContinuousMap.const M c) u,
    Lp.coeFn_smul c (scalarH0EquivLp g u)] with x hx hs
  simpa only [ContinuousMap.const_apply, Pi.smul_apply, smul_eq_mul] using hx.trans hs.symm

end DifferentialGeometry.Analysis.Spectral
end
