import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalChartJets
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.JetOperators
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.DifferentiatedBasisIdentityOffCenter

set_option autoImplicit false
noncomputable section
open Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

export DifferentialGeometry.CheegerGromovCompactness
  (mapCInfConvergence_jet2 mapCInfConvergence_chartJetOperator
    mapCInfConvergence_chartChristoffel_of_gram mapCInfConvergence_chartRicci_of_gram)

section Flow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem solution_chartRicci_jets_tendsto_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p p ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
        TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
          (chartRicciTensor (I := I) (S.base.metric t) p i j))
          (iteratedFDeriv ℝ r (chartRicciTensor (I := I) (S.base.metric b) p i j))
          (𝓝[<] b) K := by
  obtain ⟨W, hW, hpW, hWt, hgram⟩ := solution_chartGram_jets_tendsto_terminal
    S hS hab hslab hreg p
  refine ⟨W, hW, hpW, hWt, ?_⟩
  intro r i j K hK hKW
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro τ hτ
  have hseq (u v : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p u v)
      (chartGramOnE (I := I) (S.base.metric b) p u v) := by
    intro Q _hQ hQW m
    apply mapCPConvergenceOn_of_tendstoUniformlyOn hW hQW
      (fun n => ((chartGramOnE_contDiffOn (I := I) (S.base.metric (τ n)) p u v).mono hWt).of_le
        (by exact_mod_cast le_top))
      (((chartGramOnE_contDiffOn (I := I) (S.base.metric b) p u v).mono hWt).of_le
        (by exact_mod_cast le_top))
    intro q _hq
    exact ((hgram q u v).seq_tendstoUniformlyOn τ hτ).mono hQW
  have hric := mapCInfConvergence_chartRicci_of_gram (fun n => S.base.metric (τ n))
    (S.base.metric b) p hW hWt hseq i j
  exact hric.tendstoUniformlyOn_iteratedFDeriv hW hK hKW
    (fun n => (chartRicciTensor_contDiffOn_interior (I := I) (S.base.metric (τ n)) p i j).mono
      (interior_maximal hWt hW))
    ((chartRicciTensor_contDiffOn_interior (I := I) (S.base.metric b) p i j).mono
      (interior_maximal hWt hW)) r

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
