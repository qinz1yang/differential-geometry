import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostTwoPoint

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set MeasureTheory CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance tailTopology : TopologicalSpace F.M := F.topology
private local instance tailCharted : ChartedSpace H F.M := F.charted
private local instance tailSmooth : IsManifold I ∞ F.M := F.smooth
private local instance tailT2 : T2Space F.M := F.t2
private local instance tailSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance tailMeasurable : MeasurableSpace F.M := borel F.M
private local instance tailBorel : BorelSpace F.M := ⟨rfl⟩

theorem ancient_lintegral_exp_neg_mul_redLength_le
    {kappa η B : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hη : 0 < η) (p q : F.M)
    (hq : redLength F.S 0 p q 1 ≤ B) :
      (∫⁻ x : F.M, ENNReal.ofReal
        (Real.exp (-η * redLength F.S 0 p x 1))
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-1))) ≤
      ENNReal.ofReal (Real.exp (η * (1 + B))) *
        (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
          ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
          gaussianTail (Module.finrank ℝ E)
            (η / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by norm_num : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let g := F.S.base.metric (-1)
  have htime : (-1 : ℝ) ∈ ancientTimeInterval.carrier := by
    change (-1 : ℝ) ≤ 0
    norm_num
  have hcomplete : RiemannianMetricComplete (I := I) g := ⟨hF.complete (-1) htime⟩
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    intro x v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric (-1)) x).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator (-1) htime x n c a b
  have hdecay : 0 < η / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2) :=
    div_pos hη (by positivity)
  have hlower : ∀ x : F.M,
      (η / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) *
          (riemannianEDistOf (I := I) g q x).toReal ^ 2 - η * (1 + B) ≤
        η * redLength F.S 0 p x 1 := by
    intro x
    have htwo := ancientKappa_reducedCost_two_point_between F hF p q x (by norm_num : (0 : ℝ) < 1)
    have hbase :
        (1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) *
            (riemannianEDistOf (I := I) (F.S.base.metric (-1)) q x).toReal ^ 2 -
          (1 + B) ≤ redLength F.S 0 p x 1 := by
      change _ - 1 - redLength F.S 0 p q 1 ≤ redLength F.S 0 p x 1 at htwo
      simp only [div_one] at htwo
      linarith
    calc
      _ = η * ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) *
          (riemannianEDistOf (I := I) (F.S.base.metric (-1)) q x).toReal ^ 2 -
          (1 + B)) := by dsimp only [g]; ring
      _ ≤ η * redLength F.S 0 p x 1 := mul_le_mul_of_nonneg_left hbase hη.le
  have hgauss := lintegral_exp_neg_le_gaussianTail_of_quadratic_lower_bound
    g hcomplete hRic q hdecay (by positivity : 0 ≤ (1 : ℝ)) hlower 0
  simpa only [g, neg_mul, Nat.cast_zero, ENNReal.toReal_nonneg, one_mul, Set.ofPred_true,
    Measure.restrict_univ] using hgauss

omit F in
theorem exists_uniform_ancient_lintegral_exp_neg_mul_redLength_bound
    {η B : ℝ} (hη : 0 < η) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
        ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
        ∀ p q : F.M, redLength F.S 0 p q 1 ≤ B →
          (∫⁻ x : F.M, ENNReal.ofReal
            (Real.exp (-η * redLength F.S 0 p x 1))
            ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-1))) ≤ C := by
  let decay : ℝ := η / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)
  have hdecay : 0 < decay := by dsimp only [decay]; positivity
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (η * (1 + B))) *
    (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
      gaussianTail (Module.finrank ℝ E) decay 0)
  have hseries : gaussianTail (Module.finrank ℝ E) decay 0 < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    simpa only [gaussianTail, Nat.add_zero] using
      (summable_gaussianShell (Module.finrank ℝ E) hdecay).tsum_ofReal_ne_top
  have hC : C < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (measure_lt_top volume.toSphere univ) ENNReal.ofReal_lt_top)
      hseries)
  refine ⟨C, hC, ?_⟩
  intro F kappa hF p q hq
  let _ : TopologicalSpace F.M := F.topology
  let _ : ChartedSpace H F.M := F.charted
  let _ : IsManifold I ∞ F.M := F.smooth
  let _ : T2Space F.M := F.t2
  let _ : SigmaCompactSpace F.M := F.sigmaCompact
  let _ : MeasurableSpace F.M := borel F.M
  let _ : BorelSpace F.M := ⟨rfl⟩
  exact ancient_lintegral_exp_neg_mul_redLength_le F hF hη p q hq

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
