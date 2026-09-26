import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.C1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1RegularityAbsolutelyContinuous
set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace.PseudoMetrizableSpace M] {D : RealTimeInterval}

theorem lMinCurve_c1_of_absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (hab : a < b) (gamma : ℝ → M)
    (hgamma : Manifold.absolutelyContinuousOnInterval I gamma a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume a b)
    (hreg : ∀ r ∈ Icc a b, T - r ^ 2 ∈ D.regular)
    (hmin : ∀ delta : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b) := by
  apply lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives
    S hS T a b hab gamma hgamma hint D.regular D.regular_subset hreg
    (fun r hr => hreg r (Ioo_subset_Icc_self hr)) _ _ hmin
  · intro p
    have hs := chartGramOp_smooth hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
    have hfd := hs.continuousOn_fderiv_of_isOpen
      (D.regular_isOpen.prod isOpen_interior) (by simp)
    have hc := ((ContinuousLinearMap.compL ℝ E (ℝ × E) (E →L[ℝ] E)).flip
      (ContinuousLinearMap.inr ℝ ℝ E)).continuous.comp_continuousOn hfd
    exact hc.congr fun z hz =>
      chartGramOp_spatial_fderiv_eq S.family hS.smoothMetric p hz.1 hz.2
  · intro p
    exact (chartScalCov_smooth S hS p).continuousOn.congr fun z hz =>
      (chartScalCov_eq S hS p hz.1 hz.2).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
