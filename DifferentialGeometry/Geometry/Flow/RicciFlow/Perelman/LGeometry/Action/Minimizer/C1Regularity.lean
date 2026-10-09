import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Regularity.C1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.StrictRefinement

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem lMinCurve_c1
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b) (p : Fin m → M)
    (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b) := by
  classical
  obtain ⟨k, s, _q, p', u', hs, _hq, hs0, hslast, _hseg, _hp,
      hsrc', hrep'⟩ := exists_strict_chart_partition (I := I) t htmono p u gamma hsrc hrep
  have hs0a : s 0 = a := hs0.trans ht0
  have hslastb : s (Fin.last k) = b := hslast.trans htlast
  have hk : 0 < k := by
    cases k with
    | zero =>
        exfalso
        apply hab.ne
        exact hs0a.symm.trans ((congrArg s (Fin.ext (by simp))).trans hslastb)
    | succ k => omega
  have hpos : ∀ i : Fin k, s i.castSucc < s i.succ := by
    intro i
    exact hs Fin.castSucc_lt_succ
  exact lRegularizedAction_minimizer_contMDiffOn_one_of_chart_partition (I := I) S hS T a b hk s hs0a hslastb p' gamma
    hgamma u' hpos hsrc' hrep' hreg hmin

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

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
