import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance uniformOrdinaryC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem uniform_metric_time_jets_on_compact_closedWindow
    {D : ℕ → RealTimeInterval} {D₀ : RealTimeInterval}
    (S : (n : ℕ) → SolutionOn (I := I) (M := M) (D n)) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : ∀ n, Icc a b ⊆ (D n).carrier) (hregular : ∀ n, Ioo a b ⊆ (D n).regular)
    (hslab₀ : Icc a b ⊆ D₀.carrier) (hregular₀ : Ioo a b ⊆ D₀.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ Icc c b) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) ((S n).base.metric t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (S₀.base.metric t) p i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I p).symm z)) (Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y -
        iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I p).symm z)) (Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε := by
  let D' := RealTimeInterval.closed a b (hac.trans hcb).le
  exact uniform_ordinary_metric_jets_on_compact_time_of_closed_interval
    (fun n => (S n).timeRestrict D')
    (fun n => isSolutionOn_timeRestrict (hS n) (hslab n) (hregular n))
    (S₀.timeRestrict D') (isSolutionOn_timeRestrict hS₀ hslab₀ hregular₀)
    hac hcb rfl Subset.rfl hJ hJb p hU hUt hgram hK hKU r q slots

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
