import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostTwoPoint
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped ContDiff ENNReal _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

theorem ancientKappaThree_redLength_ge_rescaled_distance_sq
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 3) (p q x : F.M) {tau A : ℝ}
    (htau : 0 < tau) (hbase : redLength F.S 0 p q tau ≤ A) :
    let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
    collapsedVolumeChi * (riemannianEDistOf g q x).toReal ^ 2 - 1 - A ≤
      redLength F.S 0 p x tau := by
  have h := ancientKappaThree_reducedCost_two_point_between F hF hdim p q x htau
  change collapsedVolumeChi * (riemannianEDistOf _ q x).toReal ^ 2 / tau - 1 -
    redLength F.S 0 p q tau ≤ redLength F.S 0 p x tau at h
  dsimp only
  rw [edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_inv, mul_pow, inv_pow,
    Real.sq_sqrt htau.le]
  have heq : collapsedVolumeChi *
      (tau⁻¹ * (riemannianEDistOf (F.S.base.metric (-tau)) q x).toReal ^ 2) =
      collapsedVolumeChi * (riemannianEDistOf (F.S.base.metric (-tau)) q x).toReal ^ 2 / tau := by
    ring
  rw [heq]
  linarith

private theorem rescaled_ricci_nonnegative
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) :
    RicciBoundedBelow (I := I)
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro x v
  rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
  apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
  rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
  apply algebraicCurvatureOperatorNonnegativeCone.smul_mem ?_ (inv_pos.mpr htau).le
  apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (F.S.base.metric (-tau)) x).mpr
  intro n c a b
  simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
    hF.nonnegativeCurvatureOperator (-tau) (neg_nonpos.mpr htau.le) x n c a b

theorem ancientKappaThree_lintegral_exp_neg_redLength_tail_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 3) (p q : F.M) {tau A : ℝ}
    (htau : 0 < tau) (hbase : redLength F.S 0 p q tau ≤ A) (N : ℕ) :
    let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
    ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
        ENNReal.ofReal (Real.exp (-redLength F.S 0 p x tau)) ∂riemannianVolumeMeasure (I := I) (M := F.M) g ≤
      ENNReal.ofReal (Real.exp (1 + A)) *
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere univ) *
          ENNReal.ofReal ((3 : ℝ)⁻¹)) * gaussianTail 3 collapsedVolumeChi N := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hF.connected
  let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
  have hc : RiemannianMetricComplete (I := I) (F.S.base.metric (-tau)) :=
    ⟨hF.complete (-tau) (neg_nonpos.mpr htau.le)⟩
  have hcomplete : RiemannianMetricComplete (I := I) g :=
    hc.of_lower (inv_pos.mpr htau) (fun _ _ => le_rfl)
  have hchi : 0 < collapsedVolumeChi := by norm_num [collapsedVolumeChi]
  have hg := lintegral_gaussian_riemannianEDistOf_le g hcomplete q hchi
    (rescaled_ricci_nonnegative F hF htau) N
  rw [hdim] at hg
  norm_num only [Nat.cast_ofNat] at hg
  calc
    _ ≤ ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
        ENNReal.ofReal (Real.exp (1 + A)) * ENNReal.ofReal
          (Real.exp (-collapsedVolumeChi * (riemannianEDistOf g q x).toReal ^ 2))
          ∂riemannianVolumeMeasure (I := I) (M := F.M) g := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := ancientKappaThree_redLength_ge_rescaled_distance_sq F hF hdim p q x htau hbase
      change collapsedVolumeChi * (riemannianEDistOf g q x).toReal ^ 2 - 1 - A ≤ _ at h
      linarith
    _ = ENNReal.ofReal (Real.exp (1 + A)) *
        ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
          ENNReal.ofReal (Real.exp (-collapsedVolumeChi *
            (riemannianEDistOf g q x).toReal ^ 2)) ∂riemannianVolumeMeasure (I := I) (M := F.M) g :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      simpa only [mul_assoc, one_div] using mul_le_mul_of_nonneg_left hg
        (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (1 + A)))

theorem ancientKappaThree_exp_neg_redLength_uniform_tightness
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 3) (A : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p q : F.M) (tau : ℝ) (htau : 0 < tau),
      redLength F.S 0 p q tau ≤ A →
      let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
      ∫⁻ x in {x : F.M | (N : ℝ) ≤ (riemannianEDistOf g q x).toReal},
          ENNReal.ofReal (Real.exp (-redLength F.S 0 p x tau))
          ∂riemannianVolumeMeasure (I := I) (M := F.M) g ≤ ε := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (1 + A)) *
    (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere univ) *
      ENNReal.ofReal ((3 : ℝ)⁻¹))
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (measure_ne_top volume.toSphere univ) ENNReal.ofReal_ne_top)
  have htail : Tendsto (fun N => C * gaussianTail 3 collapsedVolumeChi N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul
        (tendsto_gaussianTail 3 (by norm_num [collapsedVolumeChi])) (Or.inr hC)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htail.eventually (gt_mem_nhds hε))
  refine ⟨N, fun p q tau htau hbase => ?_⟩
  exact (ancientKappaThree_lintegral_exp_neg_redLength_tail_le F hF hdim p q htau hbase N).trans
    (hN N le_rfl).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
