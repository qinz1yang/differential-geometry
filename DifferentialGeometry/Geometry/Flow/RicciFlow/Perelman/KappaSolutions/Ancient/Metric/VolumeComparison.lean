import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

set_option autoImplicit false
noncomputable section

section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped ContDiff _root_.Manifold _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalFatouTopology : TopologicalSpace F.M := F.topology
private local instance terminalFatouCharted : ChartedSpace H F.M := F.charted
private local instance terminalFatouSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalFatouC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalFatouT2 : T2Space F.M := F.t2
private local instance terminalFatouSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance terminalFatouMeasurable : MeasurableSpace F.M := borel F.M
private local instance terminalFatouBorel : BorelSpace F.M := ⟨rfl⟩

theorem ancient_volumeMeasure_le_of_time_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0) :
    riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric t) ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric s) := by
  have hRic : ∀ q ∈ Ioo s t, ∀ y : F.M, ∀ w : TangentSpace I y,
      0 ≤ F.S.ricciAt q y (vec2 w w) := by
    intro q hq y w
    have hqmem : q ∈ ancientTimeInterval.carrier := hq.2.le.trans ht
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric q) y).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator q hqmem y n c a b
  have hmetric (x : F.M) (v : TangentSpace I x) :
      (F.S.base.metric t).inner x v v ≤ (F.S.base.metric s).inner x v v := by
    have hanti := CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior F.S F.isSolution
      (a := s) (b := t) (fun _ hq => hq.2.trans ht)
      (fun _ hq => hq.2.trans_le ht) hRic x v
    exact hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_smul] using
    volumeMeasure_le (F.S.base.metric s) (F.S.base.metric t) one_pos
      (fun x v => by simpa only [one_mul] using hmetric x v)


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalVolumeTopology : TopologicalSpace F.M := F.topology
local instance terminalVolumeCharted : ChartedSpace H F.M := F.charted
local instance terminalVolumeSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalVolumeT2 : T2Space F.M := F.t2
local instance terminalVolumeSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem exists_ancientKappa_metric_inner_le_exp
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t : ℝ, s ≤ t → t ≤ 0 →
      ∀ x : F.M, ∀ v : TangentSpace I x,
      (F.S.base.metric s).inner x v v ≤
        Real.exp (2 * K * (t - s)) * (F.S.base.metric t).inner x v v := by
  obtain ⟨B, hB⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  let K : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B
  refine ⟨K, mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  intro s t hst ht x v
  have hslab : Icc s t ⊆ ancientTimeInterval.carrier := fun r hr => hr.2.trans ht
  have hreg : Ioo s t ⊆ ancientTimeInterval.regular := fun r hr => hr.2.trans_le ht
  have hpde := metricPDE_Icc F.S F.isSolution hslab hreg
  have hric : ∀ r ∈ Icc s t, ∀ y : F.M, ∀ w : TangentSpace I y,
      |ricciTensor (F.S.base.metric r) y w w| ≤
        K * (F.S.base.metric r).inner y w w :=
    fun r hr y w => ricci_quadratic_form_bound_of_solution_curvature_bound F.S y w
      (hB r (hslab hr) y)
  have hpair := (metricEquiv_Icc F.S.base.metric hpde hric t ⟨hst, le_rfl⟩ x v).1
  calc
    (F.S.base.metric s).inner x v v =
        Real.exp (2 * K * (t - s)) *
          (Real.exp (-(2 * K * (t - s))) * (F.S.base.metric s).inner x v v) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (2 * K * (t - s)) * (F.S.base.metric t).inner x v v :=
      mul_le_mul_of_nonneg_left hpair (Real.exp_pos _).le

theorem exists_ancientKappa_volumeMeasure_le_exp
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t : ℝ, s ≤ t → t ≤ 0 →
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric s) ≤
        ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (t - s)) ^ Module.finrank ℝ E)) •
          riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric t) := by
  obtain ⟨K, hK, hmetric⟩ := exists_ancientKappa_metric_inner_le_exp F hF
  exact ⟨K, hK, fun s t hst ht =>
    volumeMeasure_le _ _ (Real.exp_pos _) (hmetric s t hst ht)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
