import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.Christoffel
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section

open Set
open DifferentialGeometry.Geometry.Operator
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma chartChristoffelBracket_differentiableAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (i j l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartChristoffelBracket (I := I) g α i j l) y := by
  have h1 := partialDeriv_chartGramOnE_differentiableAt_interior (I := I) g α i l j hy
  have h2 := partialDeriv_chartGramOnE_differentiableAt_interior (I := I) g α j l i hy
  have h3 := partialDeriv_chartGramOnE_differentiableAt_interior (I := I) g α l i j hy
  exact (h1.add h2).sub h3

lemma partialDeriv_chartChristoffelBracket_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffelBracket (I := I) g α i j l) y =
      chartChristoffelBracketDeriv (I := I) g α m i j l y := by
  have h1 := partialDeriv_chartGramOnE_differentiableAt_interior (I := I) g α i l j hy
  have h2 := partialDeriv_chartGramOnE_differentiableAt_interior (I := I) g α j l i hy
  have h3 := partialDeriv_chartGramOnE_differentiableAt_interior (I := I) g α l i j hy
  unfold chartChristoffelBracket chartChristoffelBracketDeriv
  change (fderiv ℝ (fun z =>
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
        (chartGramOnE (I := I) g α l j) z +
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
        (chartGramOnE (I := I) g α l i) z -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l
        (chartGramOnE (I := I) g α i j) z) y)
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E m) = _
  rw [fderiv_fun_sub (h1.add h2) h3, fderiv_fun_add h1 h2]
  rfl

theorem partialDeriv_chartChristoffel_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            chartChristoffelBracket (I := I) g α i j l y +
          chartInvGramOnE (I := I) g α k l y *
            chartChristoffelBracketDeriv (I := I) g α m i j l y) := by
  classical
  have heq : chartChristoffel (I := I) g α i j k =
      fun z : E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l z * chartChristoffelBracket (I := I) g α i j l z := by
    funext z
    exact chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket (I := I) g α i j k z
  have hsum_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun z : E => chartInvGramOnE (I := I) g α k l z *
          chartChristoffelBracket (I := I) g α i j l z) y :=
    fun l => (chartInvGramOnE_differentiableAt_interior (I := I) g α k l hy).mul
      (chartChristoffelBracket_differentiableAt_int (I := I) g α i j l hy)
  have hprod (l : Fin (Module.finrank ℝ E)) :
      (fderiv ℝ (fun z : E => chartInvGramOnE (I := I) g α k l z *
        chartChristoffelBracket (I := I) g α i j l z) y)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E m) =
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
            (chartInvGramOnE (I := I) g α k l) y *
          chartChristoffelBracket (I := I) g α i j l y +
        chartInvGramOnE (I := I) g α k l y *
          chartChristoffelBracketDeriv (I := I) g α m i j l y := by
    rw [fderiv_fun_mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g α k l hy)
      (chartChristoffelBracket_differentiableAt_int (I := I) g α i j l hy)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    change chartInvGramOnE (I := I) g α k l y *
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
          (chartChristoffelBracket (I := I) g α i j l) y +
      chartChristoffelBracket (I := I) g α i j l y *
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
          (chartInvGramOnE (I := I) g α k l) y = _
    rw [partialDeriv_chartChristoffelBracket_eq (I := I) g α m i j l hy]
    ring
  rw [heq]
  change (fderiv ℝ (fun z : E => (1 / 2 : ℝ) *
    ∑ l : Fin (Module.finrank ℝ E), chartInvGramOnE (I := I) g α k l z *
      chartChristoffelBracket (I := I) g α i j l z) y)
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E m) = _
  rw [fderiv_const_mul (DifferentiableAt.fun_sum (fun l _ => hsum_diff l)) (1 / 2 : ℝ),
    fderiv_fun_sum (fun l _ => hsum_diff l)]
  simp only [smul_apply, smul_eq_mul, sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun l _ => hprod l)

end DifferentialGeometry.Geometry.Connection

end
