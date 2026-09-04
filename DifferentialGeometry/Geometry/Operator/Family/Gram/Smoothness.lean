import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Curvature

open Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem chartGramOp_smooth {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I alpha).target) :
    ContDiffOn Real ∞ (chartGramOp (I := I) G alpha) (D.regular ×ˢ K) := by
  classical
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      ContDiffOn Real ∞
        (fun p : Real × E =>
          chartGramOnE (I := I) (G.metric p.1) alpha i j p.2)
        (D.regular ×ˢ K) := by
    intro i j
    exact (hG.chartGramOnE_contDiffOn Subset.rfl alpha i j).mono
      (prod_mono_right hK)
  have hbilin : ContDiffOn Real ∞
      (fun p : Real × E =>
        chartGramBilin (E := E) (I := I) (M := M) (G.metric p.1) alpha
          ((extChartAt I alpha).symm p.2))
      (D.regular ×ˢ K) := by
    rw [contDiffOn_clm_apply]
    intro v
    rw [contDiffOn_clm_apply]
    intro w
    have hscalar : ContDiffOn Real ∞
        (fun p : Real × E =>
          ∑ j : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
            chartGramOnE (I := I) (G.metric p.1) alpha j k p.2 *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun v j *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k)
        (D.regular ×ˢ K) := by
      exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
        ((hentry j k).mul contDiffOn_const).mul contDiffOn_const
    simpa only [chartGramBilin_apply, chartGramOnE_def] using hscalar
  exact (IsCoercive.gramCLM (F := E)).contDiff.comp_contDiffOn hbilin

end DifferentialGeometry.Geometry.Curvature
