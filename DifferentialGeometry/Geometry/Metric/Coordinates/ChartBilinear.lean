import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.InnerBridge
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry.Tensor.Coordinates

open DifferentialGeometry.TensorMetric (modelInnerAt)
open DifferentialGeometry.Tensor.Tensor0SRiemannian
  (chartTrivializationLinearMap chartTrivializationLinearMapSymm chartGramMatrix_eq_innerJinv
    chartJinv_chartJ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartCoordCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) => ℝ) i).comp
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFunL.toContinuousLinearMap

@[simp]
lemma chartCoordCLM_apply (i : Fin (Module.finrank ℝ E)) (u : E) :
    chartCoordCLM E i u = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u i := by
  unfold chartCoordCLM
  rfl

def chartGramBilin (g : SmoothRiemannianMetric I M) (α b : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b j k • (chartCoordCLM E j).smulRight (chartCoordCLM E k)

@[simp]
lemma chartGramBilin_apply
    (g : SmoothRiemannianMetric I M) (α b : M) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b u w =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b j k *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k := by
  unfold chartGramBilin
  simp [sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_assoc]

lemma chartGramBilin_eq_innerJinv
    (g : SmoothRiemannianMetric I M) (α b : M) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b u w =
      modelInnerAt (I := I) (M := M) g b
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b u)
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b w) := by
  classical
  rw [chartGramBilin_apply]
  have hrewrite :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b j k *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k)
        = ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k *
                modelInnerAt (I := I) (M := M) g b
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartGramMatrix_eq_innerJinv (I := I) (M := M) g α b j k]
    ring
  rw [hrewrite]
  have hcollapse_inner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)))
        = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
              (∑ k : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k •
                  chartTrivializationLinearMapSymm (I := I) (M := M) α b
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) := by
    intro j
    have hRHS_unfold :
        ((modelInnerAt (I := I) (M := M) g b
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)))
            (∑ k : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k •
                chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)))
          = ∑ k : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k *
                modelInnerAt (I := I) (M := M) g b
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hRHS_unfold]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)))
        = ∑ j : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
              modelInnerAt (I := I) (M := M) g b
                (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
                (∑ k : Fin (Module.finrank ℝ E),
                  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k •
                    chartTrivializationLinearMapSymm (I := I) (M := M) α b
                      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) from
      Finset.sum_congr rfl (fun j _ => hcollapse_inner j)]
  have hwsum :
      (∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k •
            chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) =
        chartTrivializationLinearMapSymm (I := I) (M := M) α b w := by
    have hsum_eq :
        (∑ k : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k •
              chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k))
          = chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (∑ k : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_equivFun w]
  rw [hwsum]
  have hcollapse_outer :
      (∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b w))
        = modelInnerAt (I := I) (M := M) g b
            (∑ j : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j •
                chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b w) := by
    rw [map_sum]
    rw [sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  rw [hcollapse_outer]
  have husum :
      (∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j •
            chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
        = chartTrivializationLinearMapSymm (I := I) (M := M) α b u := by
    have hsum_eq :
        (∑ j : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j •
              chartTrivializationLinearMapSymm (I := I) (M := M) α b ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
          = chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (∑ j : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_equivFun u]
  rw [husum]

lemma chartGramBilin_chartJ_chartJ
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b
        (chartTrivializationLinearMap (I := I) (M := M) α b u)
        (chartTrivializationLinearMap (I := I) (M := M) α b w) =
      modelInnerAt (I := I) (M := M) g b u w := by
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g α b]
  rw [chartJinv_chartJ (I := I) (M := M) α hb u]
  rw [chartJinv_chartJ (I := I) (M := M) α hb w]

end DifferentialGeometry.Tensor.Coordinates

end
