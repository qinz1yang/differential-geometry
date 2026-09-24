import DifferentialGeometry.Geometry.Metric.Family.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

theorem tensor0SFamilyContinuousOnSet.continuousOn_chartGram
    {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet 2 J (fun t x => metricTensorField (g t) x))
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × M => chartGramMatrix (g q.1) α q.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  let Q := ↥(J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
  have hframe (l : Fin 2) : Continuous (fun q : Q =>
      TotalSpace.mk' E q.1.2
        (chartBasisVecFiber (I := I) α (![i, j] l) q.1.2)) :=
    (chartBasisVec_contMDiffOn (I := I) α (![i, j] l)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun q : Q => q.2.2)
  have heval := hg.eval_continuous (P := Q)
    (τ := fun q : Q => q.1.1) (b := fun q : Q => q.1.2)
    (v := fun l (q : Q) => chartBasisVecFiber (I := I) α (![i, j] l) q.1.2)
    (continuous_fst.comp continuous_subtype_val) (fun q : Q => q.2.1)
    (continuous_snd.comp continuous_subtype_val) hframe
  rw [continuousOn_iff_continuous_domRestrict]
  exact heval.congr (fun q => by
    simp only [metricTensorField_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      chartGramMatrix_apply]
    rfl)

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.SolutionOn

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem continuousOn_chartGram (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × M => chartGramMatrix (S.family.metric q.1) α q.2 i j)
      (D.carrier ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
  hS.smoothMetric.metricTensor_cont.continuousOn_chartGram α i j

end DifferentialGeometry.PDE.RicciFlow.SolutionOn
