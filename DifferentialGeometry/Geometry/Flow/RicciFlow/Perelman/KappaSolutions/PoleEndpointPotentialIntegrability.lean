import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointPotentialMassComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPotentialMeasurability

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


theorem poleEndpoint_exp_redLength_integrable
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
    (∀ i, Integrable (fun x : F.M => Real.exp (-redLength (U.term i).S 0 p x 1))
      (riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0))) ∧
    ∀ᶠ i in atTop, Integrable (fun x : F.M => Real.exp (-redLength F.S 0 p x (tau i)))
      (riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)) := by
  dsimp only
  let U := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
  let Y := poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma
  let mu (i : ℕ) : Measure F.M :=
    riemannianVolumeMeasure (I := I) (M := F.M) ((Y.term i).S.base.metric 0)
  let g (i : ℕ) (x : F.M) := redLength (U.term i).S 0 p x 1
  have hgEq (i : ℕ) (x : F.M) : g i x = redLength F.S b p x (tau i + b) :=
    poleRescaledFlowSeq_redLength_one F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma i p x
  have hg0 (i : ℕ) (x : F.M) : 0 ≤ g i x := by
    rw [hgEq]
    obtain ⟨R, hR⟩ := hF.globalScalarBound
    exact div_nonneg (lCost_nonneg_of_scalar_nonneg F.S b (hsigma i).le
      (fun s hs z => (hR _ ((sub_le_self b hs.1).trans hb.le) z).1) p x) (by positivity)
  obtain ⟨C, hC, hQ⟩ := exists_poleEndpoint_lintegral_exp_neg_redLength_quarter_bound
    F hF.carrier_eq hF.regular_eq b hb.le tau q hsigma p hancient hbase
  have hquarter (i : ℕ) : Integrable (fun x => Real.exp (-(g i x / 4))) (mu i) := by
    have hmeas : Measurable (fun x => Real.exp (-(g i x / 4))) := by
      have h := (measurable_exp_neg_redLength F hF hb.le (hsigma i) p).log
      have heq : (fun x => Real.exp (-(g i x / 4))) = fun x =>
          Real.exp (Real.log (Real.exp (-redLength F.S b p x (tau i + b))) / 4) := by
        funext x
        rw [Real.log_exp, hgEq, neg_div]
      rw [heq]
      exact (h.div_const 4).exp
    apply (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp
    exact ne_top_of_le_ne_top hC.ne (by simpa only [g, mu, neg_div] using hQ i)
  constructor
  · intro i
    apply (hquarter i).mono'
      (by
        have heq : (fun x => Real.exp (-g i x)) =
            (fun x => Real.exp (-redLength F.S b p x (tau i + b))) := by
          funext x
          rw [hgEq]
        rw [heq]
        exact (measurable_exp_neg_redLength F hF hb.le (hsigma i) p).aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.exp_le_exp.mpr (by linarith [hg0 i x])
  · obtain ⟨D, T, _, _, hcompare⟩ := exists_ancientKappa_redLength_baseTime_mul_add_bounds
      F hdim hF (d := -b) (neg_pos.mpr hb) (delta := 1) zero_lt_one
    filter_upwards [hescape.eventually_gt_atTop T] with i hi
    let e : ℝ := D / Real.sqrt (tau i)
    apply ((hquarter i).const_mul (Real.exp (e / 2))).mono'
      (measurable_exp_neg_redLength F hF le_rfl (htau i) p).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
    have h := (hcompare (tau i) hi p x).1
    have h' : g i x ≤ 2 * redLength F.S 0 p x (tau i) + e := by
      simpa only [hgEq, e, neg_neg, sub_neg_eq_add, one_add_one_eq_two] using h
    apply Real.exp_le_exp.mpr
    linarith [hg0 i x]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
