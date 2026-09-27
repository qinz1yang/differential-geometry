import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.UniformConvergence
import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic

noncomputable section

open Set Filter
open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace DifferentialGeometry.Integral.Measure

open Geometry.Curvature Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartDensity_eq_sqrt_det_chartGramOp {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M) (p : ℝ × E) :
    chartDensity (G.metric p.1) alpha ((extChartAt I alpha).symm p.2) =
      Real.sqrt (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        inner ℝ (chartGramOp G alpha p (chartModelBasis E i)) (chartModelBasis E j)).det := by
  unfold chartDensity
  congr 1
  apply congrArg Matrix.det
  ext i j
  rw [Matrix.of_apply, chartGramOp_inner]
  exact Tensor.Tensor0SRiemannian.chartGramMatrix_eq_innerJinv
    (G.metric p.1) alpha ((extChartAt I alpha).symm p.2) i j

theorem tendstoUniformly_chartDensity_of_chartGramOp
    {ι Q : Type*} {l : Filter ι} {D D' : RealTimeInterval}
    (G : ι → MetricConnectionFamilyOn (I := I) (M := M) D)
    (G' : MetricConnectionFamilyOn (I := I) (M := M) D') (alpha : M)
    {p : ι → Q → ℝ × E} {q : Q → ℝ × E}
    (h : TendstoUniformly (fun k x => chartGramOp (G k) alpha (p k x))
      (fun x => chartGramOp G' alpha (q x)) l)
    (hb : Bornology.IsBounded (range (fun x => chartGramOp G' alpha (q x)))) :
    TendstoUniformly
      (fun k x => chartDensity ((G k).metric (p k x).1) alpha
        ((extChartAt I alpha).symm (p k x).2))
      (fun x => chartDensity (G'.metric (q x).1) alpha
        ((extChartAt I alpha).symm (q x).2)) l := by
  let L : (E →L[ℝ] E) →L[ℝ] Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
      (innerSLFlip ℝ (chartModelBasis E j)).comp
        (ContinuousLinearMap.apply ℝ E (chartModelBasis E i))
  have hL := L.uniformContinuous.comp_tendstoUniformly h
  have hbL : Bornology.IsBounded (range (fun x => L (chartGramOp G' alpha (q x)))) := by
    exact (L.lipschitz.isBounded_image hb).subset (by
      rintro A ⟨x, rfl⟩
      exact ⟨chartGramOp G' alpha (q x), mem_range_self x, rfl⟩)
  have hsqrt := hL.sqrt_det hbL
  have hLA (A : E →L[ℝ] E) : L A = Matrix.of fun i j =>
      inner ℝ (A (chartModelBasis E i)) (chartModelBasis E j) := by
    ext i j
    rfl
  convert hsqrt using 1
  · funext k x
    rw [chartDensity_eq_sqrt_det_chartGramOp]
    exact congrArg (fun A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ => Real.sqrt A.det) (hLA _).symm
  · funext x
    rw [chartDensity_eq_sqrt_det_chartGramOp]
    exact congrArg (fun A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ => Real.sqrt A.det) (hLA _).symm

end DifferentialGeometry.Integral.Measure
