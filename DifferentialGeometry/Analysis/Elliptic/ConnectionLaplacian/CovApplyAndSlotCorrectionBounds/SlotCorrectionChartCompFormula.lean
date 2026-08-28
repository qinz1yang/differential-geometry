import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section


open Bundle Manifold Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartTensorRSInputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun i : Fin r =>
                (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                  (tangentLinearMapToModel
                    (tangentSlotCLM (I := I) r k
                      (chartLeviCivitaParallelCLM (I := I) g α b B) i))))))
        (fun j : Fin s =>
          chartTrivializationLinearMapSymm (I := I) (M := M) α b
            ((chartModelBasis E) (Jdx j))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((chartModelBasis E) (Jdx j))) = _
  rw [Tensor0SSpace.toModel_apply_model_vector]
  change Tensor0SSpace.eval
      (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b
            ((chartModelBasis E) (Jdx j)))) = _
  rw [chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
    (Tensor0SSpace.ofModel
      ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
    (fun j : Fin s =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((chartModelBasis E) (Jdx j))))]
  have hsubst :
      tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))) =
        Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun i : Fin r =>
              (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                (tangentLinearMapToModel
                  (tangentSlotCLM (I := I) r k
                    (chartLeviCivitaParallelCLM (I := I) g α b B) i)))) := by
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext ?_
    intro v
    change Tensor0SSpace.eval
        (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i)) =
      ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun i : Fin r =>
          (chartTrivializationLinearMap (I := I) (M := M) α b).comp
            (tangentLinearMapToModel
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i)))) v
    rw [tensorSlotSubstCLM_apply (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b B))
      (Tensor0SSpace.ofModel
        ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
      (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i))]
    change ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B) i
            ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i)))) = _
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
  rw [hsubst, Tensor0SSpace.toModel_apply_model_vector]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartTensorRSOutputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
        (fun j : Fin s =>
          tangentLinearMapToModel
            (tangentSlotCLM (I := I) s l
              (chartLeviCivitaParallelCLM (I := I) g α b B) j)
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b
              ((chartModelBasis E) (Jdx j)))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((chartModelBasis E) (Jdx j))) = _
  rw [Tensor0SSpace.toModel_apply_model_vector]
  change Tensor0SSpace.eval
      (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b
            ((chartModelBasis E) (Jdx j)))) = _
  rw [chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l]
  change Tensor0SSpace.eval
      (T b (Tensor0SSpace.ofModel
        ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j => tangentSlotCLM (I := I) s l
        (chartLeviCivitaParallelCLM (I := I) g α b B) j
          ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b
              ((chartModelBasis E) (Jdx j))))) = _
  rw [Tensor0SSpace.toModel_apply_model_vector]
  congr 1

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin 1)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) 1 2 g α T B b k)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) 1 Idx).compContinuousLinearMap
              (fun i : Fin 1 =>
                (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                  (tangentLinearMapToModel
                    (tangentSlotCLM (I := I) 1 k
                      (chartLeviCivitaParallelCLM (I := I) g α b B) i))))))
        (fun j : Fin 2 =>
          chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) :=
  chartTensorRSInputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb k Idx Jdx

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin 2)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) 1 2 g α T B b l)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) 1 Idx).compContinuousLinearMap
              (fun _ : Fin 1 => chartTrivializationLinearMap (I := I) (M := M) α b))))
        (fun j : Fin 2 =>
          tangentLinearMapToModel
            (tangentSlotCLM (I := I) 2 l
              (chartLeviCivitaParallelCLM (I := I) g α b B) j)
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b
              ((chartModelBasis E) (Jdx j)))) :=
  chartTensorRSOutputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb l Idx Jdx

end Elliptic
end Analysis
end DifferentialGeometry
