import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.ChristoffelDecomp
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def chartChristoffelBilin
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.smulRight
          (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.smulRight
            (chartChristoffel (I := I) g α i j k (extChartAt I α b) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) i *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k := by
  classical
  unfold chartChristoffelBilin
  rw [sum_apply]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sum_apply]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sum_apply]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rw [smul_apply]
  rw [ContinuousLinearMap.smulRight_apply]
  have hcoord_i : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap v =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) i := rfl
  have hcoord_j : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap w =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) j := rfl
  rw [hcoord_i, hcoord_j]
  rw [smul_smul, smul_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_add_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v₁ v₂ w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) w =
      chartChristoffelBilin (I := I) (M := M) g α b v₁ w +
        chartChristoffelBilin (I := I) (M := M) g α b v₂ w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) =
        chartChristoffelBilin (I := I) (M := M) g α b v₁ +
          chartChristoffelBilin (I := I) (M := M) g α b v₂ from map_add _ _ _,
      add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_smul_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (c : ℝ) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (c • v) w =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (c • v) =
        c • chartChristoffelBilin (I := I) (M := M) g α b v from map_smul _ _ _,
      smul_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_add_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w₁ w₂ : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (w₁ + w₂) =
      chartChristoffelBilin (I := I) (M := M) g α b v w₁ +
        chartChristoffelBilin (I := I) (M := M) g α b v w₂ :=
  map_add _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartChristoffelBilin_smul_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v : E) (c : ℝ) (w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (c • w) =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w :=
  map_smul _ _ _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
