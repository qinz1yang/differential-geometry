import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthMultiplicativeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointFractionalDensityBound
import DifferentialGeometry.Analysis.Integration.Integral.ExponentialDistortion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleRescaledReducedLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityMeasurability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩


private theorem measurable_redLength_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T ≤ 0) (htau : 0 < tau) (p : F.M) :
    Measurable (fun x => redLength F.S T p x tau) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hden := ancient_measurable_redDensity F hF hT htau p
  have hlog := hden.log
  have heq : (fun x => redLength F.S T p x tau) = fun x =>
      -Real.log (redDensity F.S T p x tau) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi) := by
    funext x
    rw [redDensity, Real.log_exp]
    ring
  rw [heq]
  exact (hlog.neg.sub measurable_const).sub measurable_const

omit [I.Boundaryless] in
private theorem redLength_nonneg_of_ancient_time
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T ≤ 0) (htau : 0 ≤ tau) (p x : F.M) :
    0 ≤ redLength F.S T p x tau := by
  obtain ⟨R, hR⟩ := hF.globalScalarBound
  exact div_nonneg (lCost_nonneg_of_scalar_nonneg F.S T htau
    (fun s hs z => (hR _ ((sub_le_self T hs.1).trans hT) z).1) p x) (by positivity)

theorem poleEndpoint_integral_exp_redLength_sub_tendsto_zero
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) {b : ℝ} (hb : b < 0)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    (p : F.M) {A : ℝ}
    (hancient : ∀ i, IsAncientKappaSolution kappa
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma).term i))
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma).term i).S
      0 p (q i) 1 ≤ A) :
    let U := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
    let Y := poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
    Tendsto (fun i =>
      (∫ x : F.M, Real.exp (-redLength F.S 0 p x (tau i))
        ∂riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)) -
      ∫ x : F.M, Real.exp (-redLength (U.term i).S 0 p x 1)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0))
      atTop (𝓝 0) := by
  dsimp only
  let U := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
  let Y := poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
  let mu (i : ℕ) : Measure F.M :=
    riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)
  let f (i : ℕ) (x : F.M) := redLength F.S 0 p x (tau i)
  let g (i : ℕ) (x : F.M) := redLength (U.term i).S 0 p x 1
  have hgEq (i : ℕ) (x : F.M) : g i x = redLength F.S b p x (tau i + b) :=
    poleRescaledFlowSeq_redLength_one F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma i p x
  obtain ⟨C, hC, hquarter⟩ := exists_poleEndpoint_lintegral_exp_neg_redLength_quarter_bound
    F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma p hancient hbase
  have hCeq : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hC.ne
  apply DifferentialGeometry.Analysis.Measure.tendsto_integral_exp_neg_sub_integral_exp_neg_zero
    mu f g (C := C.toReal)
  · exact Eventually.of_forall fun i =>
      (measurable_redLength_of_ancient F hF le_rfl (htau i) p).aemeasurable
  · apply Eventually.of_forall
    intro i
    have heq : g i = fun x => redLength F.S b p x (tau i + b) := funext (hgEq i)
    rw [heq]
    exact (measurable_redLength_of_ancient F hF hb.le (hsigma i) p).aemeasurable
  · exact Eventually.of_forall fun i => Eventually.of_forall fun x =>
      redLength_nonneg_of_ancient_time F hF le_rfl (htau i).le p x
  · exact Eventually.of_forall fun i => Eventually.of_forall fun x => by
      rw [hgEq]
      exact redLength_nonneg_of_ancient_time F hF hb.le (hsigma i).le p x
  · apply Eventually.of_forall
    intro i
    rw [hCeq]
    simpa only [mu, g, neg_div] using hquarter i
  · intro delta hdelta
    obtain ⟨D, T, hD, _, hcompare⟩ :=
      exists_ancientKappa_redLength_baseTime_mul_add_bounds F hdim hF
        (d := -b) (neg_pos.mpr hb) hdelta
    let e (i : ℕ) := D / Real.sqrt (tau i)
    have he : Tendsto e atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hescape)
      simpa only [e, div_eq_mul_inv, mul_zero, Function.comp_def] using h.const_mul D
    have hpair : ∀ᶠ i in atTop, ∀ x : F.M,
        f i x ≤ (1 + delta) * g i x + e i ∧
        g i x ≤ (1 + delta) * f i x + e i := by
      filter_upwards [hescape.eventually_gt_atTop T] with i hi x
      have h := hcompare (tau i) hi p x
      simpa only [f, hgEq, e, neg_neg, sub_neg_eq_add] using And.intro h.2 h.1
    refine ⟨e, he, Eventually.of_forall (fun i => div_nonneg hD (Real.sqrt_nonneg _)), ?_, ?_⟩
    · exact hpair.mono fun i hi => Eventually.of_forall fun x => (hi x).1
    · exact hpair.mono fun i hi => Eventually.of_forall fun x => (hi x).2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
