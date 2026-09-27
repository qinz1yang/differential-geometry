import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCoreL2
import DifferentialGeometry.Analysis.Heat.Smoothing.Scalar.HeatFlow
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Spectral

open MeasureTheory
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  infer_instance

theorem scalarHsToContinuous_toLp (g : SmoothRiemannianMetric I M)
    (u : TensorHs (I := I) (M := M) g 0 0
      ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)) :
    ContinuousMap.toLp 2 (riemannianVolumeMeasure (I := I) (M := M) g) ℝ
      (scalarHsToContinuous g u) =
    tensor00ToScalarL2LI g
      (tensorHsToL2 (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        (by positivity : (0 : ℝ) ≤ ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)) u) := by
  let hσ : (0 : ℝ) ≤ ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) := by positivity
  let lhs := (ContinuousMap.toLp 2 (riemannianVolumeMeasure (I := I) (M := M) g) ℝ).comp
    (scalarHsToContinuous g)
  let rhs := (tensor00ToScalarL2LI g).toContinuousLinearMap.comp
    (tensorHsToL2 (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) hσ)
  have heq : (lhs : _ → _) = rhs := by
    apply (ccToHsLin_dense (I := I) (M := M) g 0 hσ).equalizer lhs.continuous rhs.continuous
    funext S
    change ContinuousMap.toLp 2 (riemannianVolumeMeasure (I := I) (M := M) g) ℝ
      (scalarHsToContinuous g (ccTensorToHs g 0 _ S)) =
      tensor00ToScalarL2 g (tensorHsToL2 _ hσ (ccTensorToHs g 0 _ S))
    rw [tensorHsToL2_ccTensorToHs, tensor00ToScalarL2_toL2]
    apply Lp.ext
    refine (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ _).trans ?_
    have hpoint : (scalarHsToContinuous g (ccTensorToHs g 0 _ S) : M → ℝ) =
        (scalar0Cc g S).toFun := by
      funext x
      exact scalarHsToContinuous_apply_ccTensorToHs g S x
    rw [hpoint]
    exact (MemLp.coeFn_toLp (scalar0Cc g S).memLp_two).symm
  exact congrFun heq u

end DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance (g : SmoothRiemannianMetric I M) :
    MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  infer_instance

theorem scalarHsToContinuous_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (scalarHsToContinuous (I := I) (M := M) g) := by
  intro u v huv
  apply tensorHsToL2_injective
    (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
    (by positivity : (0 : ℝ) ≤ ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ))
  apply (tensor00ToScalarL2LI g).injective
  rw [← scalarHsToContinuous_toLp, ← scalarHsToContinuous_toLp, huv]

end DifferentialGeometry.Analysis.Spectral

namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

theorem scalarH1ToContinuous_injective
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) : Function.Injective (scalarH1ToContinuous g) := by
  intro u v huv
  apply (tensorHsCongr g 0 0 (by norm_num : (1 : ℝ) = ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ))).injective
  exact scalarHsToContinuous_injective g huv

theorem scalarH1PiToContinuous_injective {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    Function.Injective (scalarH1PiToContinuous (ι := ι) g) := by
  intro u v huv
  apply PiLp.ext
  intro i
  apply scalarH1ToContinuous_injective g
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : C(M, ι → ℝ) => f x i) huv

end DifferentialGeometry.Analysis.Spectral
