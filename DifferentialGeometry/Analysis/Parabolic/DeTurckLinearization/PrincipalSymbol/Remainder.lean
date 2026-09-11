import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.PrincipalSymbol.SecondOrder
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Symbol.Basic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]


def chartDeTurckCorrectionHessBlock (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α k l y *
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b)) y +
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a)) y -
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b)) y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrectionHessBlock_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionHessBlock (I := I) g α h d a b k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b)) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a)) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b)) y) := rfl


def chartDeTurckCorrectionGramDerivBlock (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y -
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrectionGramDerivBlock_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionGramDerivBlock (I := I) g α h d a b k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y) := rfl

def chartDeTurckCorrectionPrincipalSymbolExpr (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionHessBlock (I := I) g α h i a b k y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionHessBlock (I := I) g α h j a b k y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrectionPrincipalSymbolExpr_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionHessBlock (I := I) g α h i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionHessBlock (I := I) g α h j a b k y) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionPrincipalSymbolExpr_eq_explicit
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α k l y *
                    (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b)) y +
                     DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a)) y -
                     DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b)) y))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α k l y *
                    (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b)) y +
                     DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a)) y -
                     DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b)) y))) := by
  rw [chartDeTurckCorrectionPrincipalSymbolExpr_def]
  simp only [chartDeTurckCorrectionHessBlock_def]

def chartDeTurckCorrectionFirstOrderRemainder (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionGramDerivBlock (I := I) g α h i a b k y))) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionGramDerivBlock (I := I) g α h j a b k y)))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrectionFirstOrderRemainder_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionFirstOrderRemainder (I := I) g α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                  chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
              (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrectionGramDerivBlock (I := I) g α h i a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                  chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
              (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrectionGramDerivBlock (I := I) g α h j a b k y))) := rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
        (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g α h k y') y =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
      ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionGramDerivBlock (I := I) g α h d a b k y) +
       (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionHessBlock (I := I) g α h d a b k y)) := by
  classical
  rw [partialDeriv_chartLinearizedDeTurckVFPrincipal (I := I) g α h k d hy]
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y +
          chartInvGramOnE (I := I) g α a b y *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [partialDeriv_chartLinearizedChristoffelPrincipal (I := I) g α h a b k d hy,
    chartDeTurckCorrectionGramDerivBlock_def, chartDeTurckCorrectionHessBlock_def]
  rw [show ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y -
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y) +
            chartInvGramOnE (I := I) g α k l y *
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b)) y +
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a)) y -
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b)) y))) =
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y -
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y)) +
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l y *
              (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b)) y +
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a)) y -
               DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b)) y)) from by
    rw [Finset.sum_add_distrib, mul_add]]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckCorrectionSecondOrderPart_eq_principalSymbol_add_remainder
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartDeTurckCorrectionSecondOrderPart (I := I) g α h i j y =
      chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h i j y +
        chartDeTurckCorrectionFirstOrderRemainder (I := I) g α h i j y := by
  classical
  rw [chartDeTurckCorrectionSecondOrderPart_def, chartDeTurckCorrectionPrincipalSymbolExpr_def,
    chartDeTurckCorrectionFirstOrderRemainder_def]
  have hexp : ∀ (d k : Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g α h k y') y =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionGramDerivBlock (I := I) g α h d a b k y) +
         (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h d a b k y)) :=
    fun d k => partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded
      (I := I) g α h k d hy
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g α h k y') y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h i a b k y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hexp i k]
    ring
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g α h k y') y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h j a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h j a b k y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hexp j k]
    ring
  rw [hsum1, hsum2]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckCorrectionSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartDeTurckCorrectionSecondOrderPart (I := I) g α h i j (extChartAt I α x) =
      chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h i j (extChartAt I α x) +
        chartDeTurckCorrectionFirstOrderRemainder (I := I) g α h i j (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartDeTurckCorrectionSecondOrderPart_eq_principalSymbol_add_remainder
    (I := I) g α h i j hx_int

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrectionFirstOrderRemainder_eq_first_order_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionFirstOrderRemainder (I := I) g α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y)))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y)))) := by
  classical
  rw [chartDeTurckCorrectionFirstOrderRemainder_def]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartLinearizedChristoffelPrincipal_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartDeTurckCorrectionGramDerivBlock_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartLinearizedChristoffelPrincipal_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartDeTurckCorrectionGramDerivBlock_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring

section BlockLinearity

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_zero
    (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b)) y = 0 := by
  have hinner : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b) =
      fun _ : E => (0 : ℝ) := by
    funext y'
    have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
    rw [hconst, partialDeriv_const]
  rw [hinner, partialDeriv_const]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_zero_apply
    (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p ((0 : ChartMetricPerturbation E) a b) y = 0 := by
  have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
  rw [hconst, partialDeriv_const]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q ((h₁ + h₂) a b)) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h₁ a b)) y +
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h₂ a b)) y := by
  have hinner : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q ((h₁ + h₂) a b) =
      fun y' => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h₁ a b) y' +
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h₂ a b) y' := by
    funext y'
    have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
    rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
          (h₁.differentiableAt a b y') (h₂.differentiableAt a b y')]
  rw [hinner, partialDeriv_add (E := E)
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h₁ a b)) (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h₂ a b))
        (partialDeriv_perturbation_differentiableAt h₁ q a b y)
        (partialDeriv_perturbation_differentiableAt h₂ q a b y)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p ((h₁ + h₂) a b) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (h₁ a b) y + DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (h₂ a b) y := by
  have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
  rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
        (h₁.differentiableAt a b y) (h₂.differentiableAt a b y)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q ((c • h) a b)) y =
      c * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h a b)) y := by
  have hinner : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q ((c • h) a b) =
      fun y' => c • DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h a b) y' := by
    funext y'
    have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
    rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y')]
  rw [hinner, partialDeriv_const_smul (E := E) c
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (h a b))
        (partialDeriv_perturbation_differentiableAt h q a b y), smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p ((c • h) a b) y =
      c * DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p (h a b) y := by
  have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
  rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y),
    smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionHessBlock_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionHessBlock (I := I) g α
      (0 : ChartMetricPerturbation E) d a b k y = 0 := by
  classical
  rw [chartDeTurckCorrectionHessBlock_def]
  have hzero : (∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a ((0 : ChartMetricPerturbation E) l b)) y +
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b ((0 : ChartMetricPerturbation E) l a)) y -
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) a b)) y)) = 0 := by
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_zero d a l b y,
      partialDeriv_partialDeriv_zero d b l a y,
      partialDeriv_partialDeriv_zero d l a b y]
    ring
  rw [hzero, mul_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionHessBlock_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionHessBlock (I := I) g α (h₁ + h₂) d a b k y =
      chartDeTurckCorrectionHessBlock (I := I) g α h₁ d a b k y +
        chartDeTurckCorrectionHessBlock (I := I) g α h₂ d a b k y := by
  classical
  rw [chartDeTurckCorrectionHessBlock_def, chartDeTurckCorrectionHessBlock_def,
    chartDeTurckCorrectionHessBlock_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_partialDeriv_add_apply h₁ h₂ d a l b y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ d b l a y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ d l a b y]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionHessBlock_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionHessBlock (I := I) g α (c • h) d a b k y =
      c * chartDeTurckCorrectionHessBlock (I := I) g α h d a b k y := by
  classical
  rw [chartDeTurckCorrectionHessBlock_def, chartDeTurckCorrectionHessBlock_def]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a ((c • h) l b)) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b ((c • h) l a)) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((c • h) a b)) y)) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b)) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a)) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b)) y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_smul_apply c h d a l b y,
      partialDeriv_partialDeriv_smul_apply c h d b l a y,
      partialDeriv_partialDeriv_smul_apply c h d l a b y]
    ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionGramDerivBlock_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionGramDerivBlock (I := I) g α
      (0 : ChartMetricPerturbation E) d a b k y = 0 := by
  classical
  rw [chartDeTurckCorrectionGramDerivBlock_def]
  have hzero : (∑ l : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a ((0 : ChartMetricPerturbation E) l b) y +
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b ((0 : ChartMetricPerturbation E) l a) y -
         DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) a b) y)) = 0 := by
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [partialDeriv_zero_apply a l b y, partialDeriv_zero_apply b l a y,
      partialDeriv_zero_apply l a b y]
    ring
  rw [hzero, mul_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionGramDerivBlock_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionGramDerivBlock (I := I) g α (h₁ + h₂) d a b k y =
      chartDeTurckCorrectionGramDerivBlock (I := I) g α h₁ d a b k y +
        chartDeTurckCorrectionGramDerivBlock (I := I) g α h₂ d a b k y := by
  classical
  rw [chartDeTurckCorrectionGramDerivBlock_def, chartDeTurckCorrectionGramDerivBlock_def,
    chartDeTurckCorrectionGramDerivBlock_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_add_apply h₁ h₂ a l b y, partialDeriv_add_apply h₁ h₂ b l a y,
    partialDeriv_add_apply h₁ h₂ l a b y]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionGramDerivBlock_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionGramDerivBlock (I := I) g α (c • h) d a b k y =
      c * chartDeTurckCorrectionGramDerivBlock (I := I) g α h d a b k y := by
  classical
  rw [chartDeTurckCorrectionGramDerivBlock_def, chartDeTurckCorrectionGramDerivBlock_def]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a ((c • h) l b) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b ((c • h) l a) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l ((c • h) a b) y)) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (h l b) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) b (h l a) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (h a b) y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_smul_apply c h a l b y, partialDeriv_smul_apply c h b l a y,
      partialDeriv_smul_apply c h l a b y]
    ring]
  ring

end BlockLinearity

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionPrincipalSymbolExpr_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrectionPrincipalSymbolExpr_def]
  have hzero : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionHessBlock (I := I) g α
              (0 : ChartMetricPerturbation E) d a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartDeTurckCorrectionHessBlock_zero, mul_zero]
  rw [Finset.sum_eq_zero (fun k _ => by rw [hzero i k, mul_zero]),
    Finset.sum_eq_zero (fun k _ => by rw [hzero j k, mul_zero]), add_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrectionPrincipalSymbolExpr_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α (h₁ + h₂) i j y =
      chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h₁ i j y +
        chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h₂ i j y := by
  classical
  rw [chartDeTurckCorrectionPrincipalSymbolExpr_def, chartDeTurckCorrectionPrincipalSymbolExpr_def,
    chartDeTurckCorrectionPrincipalSymbolExpr_def]
  have hsplit : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionHessBlock (I := I) g α (h₁ + h₂) d a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h₁ d a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h₂ d a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrectionHessBlock_add]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α (h₁ + h₂) i a b k y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h₁ i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h₂ i a b k y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsplit i k, mul_add]]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α (h₁ + h₂) j a b k y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h₁ j a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h₂ j a b k y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsplit j k, mul_add]]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrectionPrincipalSymbolExpr_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α (c • h) i j y =
      c • chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h i j y := by
  classical
  rw [chartDeTurckCorrectionPrincipalSymbolExpr_def, chartDeTurckCorrectionPrincipalSymbolExpr_def,
    smul_eq_mul]
  have hscale : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionHessBlock (I := I) g α (c • h) d a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionHessBlock (I := I) g α h d a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrectionHessBlock_smul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α (c • h) i a b k y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h i a b k y from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hscale i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α (c • h) j a b k y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionHessBlock (I := I) g α h j a b k y from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hscale j k]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartDeTurckCorrectionFirstOrderRemainder_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionFirstOrderRemainder (I := I) g α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrectionFirstOrderRemainder_def]
  have hbranchA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α
              (0 : ChartMetricPerturbation E) a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_zero, mul_zero]
  have hbranchB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionGramDerivBlock (I := I) g α
              (0 : ChartMetricPerturbation E) d a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartDeTurckCorrectionGramDerivBlock_zero, mul_zero]
  rw [Finset.sum_eq_zero (fun k _ => by rw [hbranchA i k, hbranchB i k]; ring),
    Finset.sum_eq_zero (fun k _ => by rw [hbranchA j k, hbranchB j k]; ring), add_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrectionFirstOrderRemainder_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionFirstOrderRemainder (I := I) g α (h₁ + h₂) i j y =
      chartDeTurckCorrectionFirstOrderRemainder (I := I) g α h₁ i j y +
        chartDeTurckCorrectionFirstOrderRemainder (I := I) g α h₂ i j y := by
  classical
  rw [chartDeTurckCorrectionFirstOrderRemainder_def, chartDeTurckCorrectionFirstOrderRemainder_def,
    chartDeTurckCorrectionFirstOrderRemainder_def]
  have hA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_add]
    ring
  have hB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionGramDerivBlock (I := I) g α (h₁ + h₂) d a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionGramDerivBlock (I := I) g α h₁ d a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrectionGramDerivBlock (I := I) g α h₂ d a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrectionGramDerivBlock_add]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α (h₁ + h₂) i a b k y))) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h₁ i a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h₂ i a b k y))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA i k, hB i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α (h₁ + h₂) j a b k y))) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h₁ j a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h₂ j a b k y))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA j k, hB j k]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrectionFirstOrderRemainder_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionFirstOrderRemainder (I := I) g α (c • h) i j y =
      c • chartDeTurckCorrectionFirstOrderRemainder (I := I) g α h i j y := by
  classical
  rw [chartDeTurckCorrectionFirstOrderRemainder_def, chartDeTurckCorrectionFirstOrderRemainder_def,
    smul_eq_mul]
  have hA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_smul, smul_eq_mul]
    ring
  have hB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionGramDerivBlock (I := I) g α (c • h) d a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrectionGramDerivBlock (I := I) g α h d a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrectionGramDerivBlock_smul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α (c • h) i a b k y))) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h i a b k y)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA i k, hB i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α (c • h) j a b k y))) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrectionGramDerivBlock (I := I) g α h j a b k y)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA j k, hB j k]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartDeTurckCorrectionPrincipalSymbolExpr_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h i j y =
      chartDeTurckCorrectionPrincipalSymbolExpr (I := I) g α h j i y := by
  classical
  rw [chartDeTurckCorrectionPrincipalSymbolExpr_def, chartDeTurckCorrectionPrincipalSymbolExpr_def]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g α i k y]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g α k j y]

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
