import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientFractionalDensityBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set MeasureTheory CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval}
  (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

variable [I.Boundaryless]

theorem exists_poleEndpoint_lintegral_exp_neg_redLength_quarter_bound
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (p : F.M) {kappa A : ℝ} :
    let U := poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
    let Y := poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
    (∀ i, IsAncientKappaSolution kappa (U.term i)) →
    (∀ i, redLength (U.term i).S 0 p (q i) 1 ≤ A) →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ i,
      (∫⁻ x : F.M, ENNReal.ofReal (Real.exp (-redLength (U.term i).S 0 p x 1 / 4))
        ∂riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)) ≤ C := by
  dsimp only
  intro hAncient hbase
  obtain ⟨C, hC, hbound⟩ := exists_uniform_ancient_lintegral_exp_neg_mul_redLength_bound
    (I := I) (η := 1 / 4) (B := A) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro i
  have hmetric := poleEndpointRescaledFlowSeq_metric_eq_shift
    F hcar hreg b hbmem tau q hsigma i 0
  rw [zero_sub] at hmetric
  rw [hmetric]
  have h := hbound
    ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i)
    (hAncient i) p (q i) (hbase i)
  have hexponent (z : ℝ) : -z / 4 = -(1 / 4 : ℝ) * z := by ring
  simp only [hexponent]
  with_unfolding_all exact h

omit [I.Boundaryless] in
theorem poleEndpointRescaledFlowSeq_volume_zero
    (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    @riemannianVolumeMeasure E _ _ _ H _ I F.M
        F.topology F.charted F.smooth F.t2 F.sigmaCompact
        (((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0) =
      ENNReal.ofReal (Real.sqrt ((tau i + b)⁻¹)) ^ Module.finrank ℝ E •
        @riemannianVolumeMeasure E _ _ _ H _ I F.M
        F.topology F.charted F.smooth F.t2 F.sigmaCompact (F.S.base.metric (-tau i)) := by
  rw [poleEndpointRescaledFlowSeq_metric_zero]
  exact volume_scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) (F.S.base.metric (-tau i))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
