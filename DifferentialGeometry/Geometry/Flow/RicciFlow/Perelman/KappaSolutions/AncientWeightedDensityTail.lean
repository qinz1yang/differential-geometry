import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostTwoPoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero

noncomputable section

open Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

private theorem sqrt_mul_exp_neg_le_exp_neg_half (x : ℝ) :
    Real.sqrt x * Real.exp (-x) ≤ Real.exp (-x / 2) := by
  have hx : x ≤ Real.exp x :=
    (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
      (Real.add_one_le_exp x)
  calc
    Real.sqrt x * Real.exp (-x) ≤ Real.sqrt (Real.exp x) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx) (Real.exp_nonneg _)
    _ = Real.exp (x / 2) * Real.exp (-x) := by rw [← Real.exp_half x]
    _ = Real.exp (-x / 2) := by rw [← Real.exp_add]; congr 1; ring

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance weightedTailTopology : TopologicalSpace F.M := F.topology
private local instance weightedTailCharted : ChartedSpace H F.M := F.charted
private local instance weightedTailSmooth : IsManifold I ∞ F.M := F.smooth
private local instance weightedTailT2 : T2Space F.M := F.t2
private local instance weightedTailSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem ancient_sqrt_redLength_mul_redDensity_tail_le_of_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau B : ℝ} (htau : 0 < tau)
    (hq : redLength F.S 0 p q tau ≤ B) (N : ℕ) :
    (∫⁻ x in {x : F.M | (N : ℝ) ≤
        (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal},
      ENNReal.ofReal (Real.sqrt (redLength F.S 0 p x tau) * redDensity F.S 0 p x tau)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) ≤
    ENNReal.ofReal (Real.exp
      (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      Real.exp ((1 + B) / 2)) *
      (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
        gaussianTail (Module.finrank ℝ E)
          (((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) / 2) N) := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by norm_num : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  let g := F.S.base.metric (-tau)
  let A : ℝ := Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have htime : -tau ∈ ancientTimeInterval.carrier := by
    change -tau ≤ 0
    exact neg_nonpos.mpr htau.le
  have hcomplete : RiemannianMetricComplete (I := I) g := ⟨hF.complete (-tau) htime⟩
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    intro x v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric (-tau)) x).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator (-tau) htime x n c a b
  have hdecay : 0 < ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) / 2 := by
    positivity
  have hlower (x : F.M) :
      (((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) / 2) *
        (riemannianEDistOf (I := I) g q x).toReal ^ 2 - (1 + B) / 2 ≤
      redLength F.S 0 p x tau / 2 := by
    have h := ancientKappa_reducedCost_two_point_between F hF p q x htau
    change _ - 1 - redLength F.S 0 p q tau ≤ redLength F.S 0 p x tau at h
    have hbase :
        ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) *
          (riemannianEDistOf (I := I) g q x).toReal ^ 2 - (1 + B) ≤
        redLength F.S 0 p x tau := by
      dsimp only [g]
      have heq : ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) *
          (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal ^ 2 =
        (1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) *
          (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal ^ 2 / tau := by
        ring
      rw [heq]
      linarith
    linarith
  have hpoint (x : F.M) :
      ENNReal.ofReal (Real.sqrt (redLength F.S 0 p x tau) * redDensity F.S 0 p x tau) ≤
        ENNReal.ofReal (A * Real.exp (-(redLength F.S 0 p x tau / 2))) := by
    have hdensity : redDensity F.S 0 p x tau = A * Real.exp (-redLength F.S 0 p x tau) := by
      dsimp only [A]
      rw [redDensity, ← Real.exp_add]
      congr 1
      ring
    apply ENNReal.ofReal_le_ofReal
    rw [hdensity, mul_left_comm]
    simpa only [neg_div] using mul_le_mul_of_nonneg_left
      (sqrt_mul_exp_neg_le_exp_neg_half (redLength F.S 0 p x tau))
      (show 0 ≤ A from Real.exp_nonneg _)
  exact (lintegral_mono hpoint).trans
    (lintegral_exp_neg_le_gaussianTail_of_quadratic_lower_bound
      g hcomplete hRic q hdecay (Real.exp_nonneg _) hlower N)

theorem lintegral_sqrt_redLength_mul_redDensity_lt_top_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    (∫⁻ x : F.M,
      ENNReal.ofReal (Real.sqrt (redLength F.S 0 p x tau) * redDensity F.S 0 p x tau)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) < ⊤ := by
  have hdecay : 0 < ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) / 2 := by
    positivity
  have hseries : gaussianTail (Module.finrank ℝ E)
      (((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) / 2) 0 < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    simpa only [gaussianTail, Nat.add_zero] using
      (summable_gaussianShell (Module.finrank ℝ E) hdecay).tsum_ofReal_ne_top
  have hbound := ancient_sqrt_redLength_mul_redDensity_tail_le_of_redLength_le
    F hF p p htau (le_refl (redLength F.S 0 p p tau)) 0
  simp only [Nat.cast_zero, ENNReal.toReal_nonneg, Set.ofPred_true,
    Measure.restrict_univ] at hbound
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (measure_lt_top volume.toSphere univ) ENNReal.ofReal_lt_top)
      hseries))

theorem integrable_sqrt_redLength_mul_redDensity_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    Integrable (fun x : F.M =>
      Real.sqrt (redLength F.S 0 p x tau) * redDensity F.S 0 p x tau)
      (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) := by
  have hell := continuous_redLength_of_ancient F hF p htau
  have hdensity : Continuous (fun x : F.M => redDensity F.S 0 p x tau) := by
    unfold redDensity
    exact ((hell.neg.sub continuous_const).sub continuous_const).rexp
  refine ⟨(hell.sqrt.mul hdensity).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)))).2
  exact lintegral_sqrt_redLength_mul_redDensity_lt_top_of_ancient F hF p htau

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
