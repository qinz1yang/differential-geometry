import DifferentialGeometry.Geometry.Operator.VossWeyl

noncomputable section

open Set
open scoped BigOperators ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartChristoffel (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartChristoffel_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      chartChristoffel (I := I) g α j i k y := by
  classical
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  congr 1
  have hsym : chartGramOnE (I := I) g α i j =
      chartGramOnE (I := I) g α j i :=
    funext (fun y' => chartGramOnE_symm (I := I) g α i j y')
  rw [show partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y =
        partialDeriv (E := E) l (chartGramOnE (I := I) g α j i) y from by
    rw [hsym]]
  ring

end DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartChristoffelBracket (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
    partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
    partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y

def chartChristoffelBracketDeriv (g : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y +
    partialDeriv (E := E) m (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) y -
    partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y

def chartChristoffelBracketSecondDeriv (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j))) y +
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))) y -
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))) y

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          chartChristoffelBracket (I := I) g α i j l y := by
  rw [chartChristoffel_def]
  rfl

end DifferentialGeometry.Geometry.Connection
