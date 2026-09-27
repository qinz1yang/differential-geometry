import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientUniformWeightedDensityTail
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Metric.Distance.Ball


noncomputable section

open Set MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance closedBallTailTopology
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    TopologicalSpace F.M := F.topology
private local instance closedBallTailCharted
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    ChartedSpace H F.M := F.charted
private local instance closedBallTailSmooth
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    IsManifold I ∞ F.M := F.smooth
private local instance closedBallTailT2
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    T2Space F.M := F.t2
private local instance closedBallTailSigma
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    SigmaCompactSpace F.M := F.sigmaCompact
private local instance closedBallTailMeasurable
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    MeasurableSpace F.M := borel F.M
private local instance closedBallTailBorel
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    BorelSpace F.M := ⟨rfl⟩

theorem exists_uniform_ancient_sqrt_redLength_mul_redDensity_closedBall_compl_bound
    {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
      ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (p q : F.M) {tau : ℝ}, tau ∈ Icc a b → redLength F.S 0 p q tau ≤ B →
      (∫⁻ x in (riemannianClosedBallOf (I := I) (F.S.base.metric (-tau)) q (N : ℝ))ᶜ,
        ENNReal.ofReal (Real.sqrt (redLength F.S 0 p x tau) * redDensity F.S 0 p x tau)
          ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) < ε := by
  obtain ⟨N, hN⟩ := exists_uniform_ancient_sqrt_redLength_mul_redDensity_tail_bound
    (I := I) (B := B) ha hab hε
  refine ⟨N, ?_⟩
  intro F kappa hF p q tau htau hq
  let _ : ConnectedSpace F.M := hF.connected
  have hsubset :
      (riemannianClosedBallOf (I := I) (F.S.base.metric (-tau)) q (N : ℝ))ᶜ ⊆
        {x : F.M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal} := by
    intro x hx
    change ¬ riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x ≤
      ENNReal.ofReal (N : ℝ) at hx
    change (N : ℝ) ≤
      (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal
    by_contra hsmall
    have hsmall' :
        (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal < (N : ℝ) :=
      lt_of_not_ge hsmall
    have hfinite := riemannianEDistOf_ne_top (I := I) (F.S.base.metric (-tau)) q x
    exact hx ((ENNReal.ofReal_toReal hfinite).symm.trans_le
      (ENNReal.ofReal_le_ofReal hsmall'.le))
  exact (lintegral_mono_set hsubset).trans_lt (hN F hF p q htau hq)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
