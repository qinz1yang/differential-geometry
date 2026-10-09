import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAsymptoticReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Scaling
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityIntegrability
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure Entropy
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem integrable_ancient_perelmanDensity
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (μ : Measure (Icc a b)) [IsFiniteMeasure μ]
    (R : SmoothRiemannianMetric I F.M) :
    Integrable (fun z : Icc a b × F.M =>
      riemannianVolumeDensity R (F.S.base.metric (-z.1)) z.2 *
        perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1) z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) := by
  have hρ := riemannianVolumeDensity_family_continuousOn R F.S.base.metric
    F.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier
  have hρc : Continuous (fun z : Icc a b × F.M =>
      riemannianVolumeDensity R (F.S.base.metric (-z.1)) z.2) :=
    hρ.comp_continuous ((continuous_subtype_val.comp continuous_fst).neg.prodMk continuous_snd)
      (fun z => ⟨show -(z.1 : ℝ) ≤ 0 from neg_nonpos.mpr (ha.le.trans z.1.property.1), mem_univ _⟩)
  have hl : Continuous (fun z : Icc a b × F.M => redLength F.S 0 p z.2 z.1) :=
    (continuousOn_redLength_space_time_of_ancient F hF p).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨ha.trans_le z.1.property.1, mem_univ _⟩)
  have hu : Continuous (fun z : Icc a b × F.M =>
      perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1) z.2) := by
    unfold perelmanDensity perelmanDensityPrefactor
    apply Continuous.mul
    · apply Continuous.rpow_const (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      intro z
      exact Or.inl (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (ne_of_gt (ha.trans_le z.1.property.1)))
    · exact Real.continuous_exp.comp hl.neg
  have hw := (hρc.mul hu).aestronglyMeasurable
    (μ := μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R))
  apply integrable_prod_volumeDensity_smul_of_lintegral_norm_le μ R
    (fun tau => F.S.base.metric (-tau))
    (fun z => perelmanDensity (Module.finrank ℝ E) z.1 (fun y => redLength F.S 0 p y z.1) z.2)
    hw (C := 1) ENNReal.one_ne_top
  filter_upwards [] with tau
  have htau : 0 < (tau : ℝ) := ha.trans_le tau.property.1
  have hnonneg (x : F.M) : 0 ≤ perelmanDensity (Module.finrank ℝ E) tau
      (fun y => redLength F.S 0 p y tau) x :=
    (mul_pos (prefactor_pos _ htau) (Real.exp_pos _)).le
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
  have hmass := intrinsicReducedVolume_eq_normalizedShrinkerMass F.S 0 p htau
  rw [normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity _ htau, zero_sub] at hmass
  rw [← hmass]
  exact ancient_reducedVolume_le_one F hF le_rfl p htau

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
