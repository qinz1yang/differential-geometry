import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimTerminalDerivativeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.DifferentialGeometry.Manifold Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

private local instance flatThreeSpaceMeasurable : MeasurableSpace ThreeSpace := borel ThreeSpace
private local instance flatThreeSpaceBorel : BorelSpace ThreeSpace := ⟨rfl⟩

abbrev euclideanFlatFlow : PointedFlowData.{0, 0, 0} (I := I3) ancientTimeInterval where
  M := ThreeSpace
  basepoint := 0
  S := SolutionOn.const (euclideanMetric (E := ThreeSpace)) ancientTimeInterval
  isSolution := isSolutionOn_const_of_ricciTensor_eq_zero (euclideanMetric (E := ThreeSpace))
    (fun x v w => DifferentialGeometry.Geometry.euclideanMetric_ricciTensor x v w)
    ancientTimeInterval

theorem euclideanFlatFlow_rm04 (t : ℝ) (x : ThreeSpace) :
    euclideanFlatFlow.S.base.rm04 t x =
      metricRm04At (I := I3) (euclideanMetric (E := ThreeSpace)) x := by
  simp only [SolutionFamily.rm04, SolutionOn.const_metric, metricRm04_apply]

theorem euclideanFlatFlow_metric (t : ℝ) :
    euclideanFlatFlow.S.base.metric t = euclideanMetric (E := ThreeSpace) :=
  SolutionOn.const_metric (euclideanMetric (E := ThreeSpace)) ancientTimeInterval t

theorem euclideanFlatFlow_rmNormSq (t : ℝ) (x : ThreeSpace) :
    euclideanFlatFlow.rmNormSq (I := I3) t x = 0 := by
  have h : euclideanFlatFlow.rmNormSq (I := I3) t x =
      Tensor0SBundle.normSq0S (I := I3) (euclideanMetric (E := ThreeSpace)) x 4
        (0 : Tensor0SSpace 4 I3 x) := by
    rw [PointedFlowData.rmNormSq, SolutionOn.family_metric, euclideanFlatFlow_metric,
      euclideanFlatFlow_rm04,
      DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero]
  rw [h]
  simp only [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S]
  exact (MetricFiberData.inner_self_eq_zero_iff _ (0 : Tensor0SSpace 4 I3 x)).2 rfl

theorem euclideanFlatFlow_not_notFlat :
    ¬ PointedFlowNotFlat (I := I3) euclideanFlatFlow := by
  rintro ⟨t, _ht, x, hx⟩
  exact hx (euclideanFlatFlow_rmNormSq t x)

theorem euclideanFlatFlow_nonnegativeCurvatureOperator (t : ℝ) :
    PointedFlowNonnegativeCurvatureOperator (I := I3) euclideanFlatFlow t := by
  intro x n c v w
  rw [euclideanFlatFlow_rm04,
    DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero]
  simp only [Tensor0SSpace.zero_apply, mul_zero, Finset.sum_const_zero, le_refl]

theorem riemannianEDistOf_euclideanMetric (x y : ThreeSpace) :
    riemannianEDistOf (I := I3) (euclideanMetric (E := ThreeSpace)) x y = edist x y := by
  have hmetric : euclideanMetric (E := ThreeSpace) =
      DifferentialGeometry.Geometry.standardEuclideanMetric ThreeSpace := rfl
  rw [hmetric]
  exact DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric x y

theorem riemannianBallOf_euclideanMetric (c : ThreeSpace) {r : ℝ} (hr : 0 < r) :
    riemannianBallOf (I := I3) (euclideanMetric (E := ThreeSpace)) c r = Metric.ball c r := by
  ext x
  simp only [riemannianBallOf, Set.mem_ofPred_eq, Metric.mem_ball]
  rw [riemannianEDistOf_euclideanMetric, edist_dist]
  rw [ENNReal.ofReal_lt_ofReal_iff hr, dist_comm]

theorem euclideanUnitBallVolume_three :
    euclideanUnitBallVolume 3 = ENNReal.ofReal (4 * Real.pi / 3) := by
  simp only [euclideanUnitBallVolume, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one, one_pow, one_mul, mul_comm Real.pi 4]

theorem euclideanUnitBallVolume_three_ge_one_half :
    ENNReal.ofReal (1 / 2) ≤ euclideanUnitBallVolume 3 := by
  rw [euclideanUnitBallVolume_three]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_gt_three])

theorem flatUnitBallVolume_three :
    (MeasureTheory.volume : MeasureTheory.Measure ThreeSpace) (Metric.ball (0 : ThreeSpace) 1)
      = euclideanUnitBallVolume 3 := by
  rw [euclideanUnitBallVolume_three]
  have h := InnerProductSpace.volume_ball_of_dim_odd (E := ThreeSpace) (k := 1)
    (by simp) (0 : ThreeSpace) 1
  rw [h]
  norm_num [Nat.doubleFactorial]
  ring_nf

theorem euclideanMetric_ball_volume (c : ThreeSpace) {r : ℝ} (hr : 0 < r) :
    riemannianVolumeMeasure (I := I3) (M := ThreeSpace) (euclideanMetric (E := ThreeSpace))
        (riemannianBallOf (I := I3) (euclideanMetric (E := ThreeSpace)) c r)
      = euclideanUnitBallVolume 3 * ENNReal.ofReal (r ^ 3) := by
  rw [riemannianBallOf_euclideanMetric c hr, riemannianVolumeMeasure_euclideanMetric]
  have hball := MeasureTheory.Measure.addHaar_ball_of_pos (E := ThreeSpace)
    (μ := MeasureTheory.volume) c hr
  rw [hball]
  rw [flatUnitBallVolume_three, finrank_euclideanSpace, Fintype.card_fin]
  rw [mul_comm]

theorem euclideanFlatFlow_noncollapsed {kappa : ℝ} (hkappa : 0 < kappa)
    (hvol : ENNReal.ofReal kappa ≤ euclideanUnitBallVolume 3) :
    PointedFlowNoncollapsedAllScales (I := I3) euclideanFlatFlow kappa := by
  intro time B _hcontrolled
  refine ⟨hkappa, ?_⟩
  have hvolume : B.volume = euclideanUnitBallVolume 3 *
      ENNReal.ofReal (B.radius ^ 3) := by
    simp only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
      volumeMeasureOn_eq_metric, SolutionOn.family_metric, SolutionOn.const_metric]
    exact euclideanMetric_ball_volume B.center B.radius_pos
  rw [hvolume]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow B.radius_pos.le]
  exact mul_le_mul' hvol le_rfl

theorem euclideanFlatFlow_traceHarnack (t : ℝ) (ht : t ∈ ancientTimeInterval.carrier)
    (x : ThreeSpace) (V : TangentSpace I3 x) :
    0 ≤ derivWithin (fun s : ℝ => euclideanFlatFlow.S.scalar s x)
          ancientTimeInterval.carrier t +
      2 * (euclideanFlatFlow.S.base.metric t).inner x
        (gradientAt (I := I3) (flowG (I := I3) euclideanFlatFlow.S) t
          (euclideanFlatFlow.S.scalar t) x) V +
      2 * metricRicci (I := I3) (M := ThreeSpace)
        (euclideanFlatFlow.S.base.metric t) x (vec2 V V) := by
  have hcomplete : ∀ s ∈ ancientTimeInterval.carrier,
      RiemannianMetricComplete (I := I3) (euclideanFlatFlow.S.base.metric s) :=
    fun _ _ => euclideanMetric_complete (E := ThreeSpace)
  have hcurv : ∀ a b : ℝ, Set.Icc a b ⊆ ancientTimeInterval.carrier →
      ∃ C : ℝ, ∀ s ∈ Set.Icc a b, ∀ y : ThreeSpace,
        Tensor0SBundle.normSq0S (I := I3) (euclideanFlatFlow.S.base.metric s) y 4
          (euclideanFlatFlow.S.base.rm04 s y) ≤ C :=
    fun _ _ _ => ⟨0, fun s _ y => by
      rw [euclideanFlatFlow_rm04,
        DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero]
      simp only [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S]
      exact le_of_eq ((MetricFiberData.inner_self_eq_zero_iff _
        (0 : Tensor0SSpace 4 I3 y)).2 rfl)⟩
  have hR : ∀ s ∈ ancientTimeInterval.carrier, ∀ y : ThreeSpace,
      metricAlgebraicCurvatureTensorAt (I := I3) (M := ThreeSpace)
        (euclideanFlatFlow.S.base.metric s) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I3) (M := ThreeSpace) := by
    intro s _ y
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, SolutionOn.const_metric, metricRm04_apply] using
      euclideanFlatFlow_nonnegativeCurvatureOperator s y n c v w
  by_cases ht0 : t = 0
  · subst t
    exact hamilton_ancient_trace_harnack_at_terminal euclideanFlatFlow.S
      euclideanFlatFlow.isSolution ancientTimeInterval_carrier ancientTimeInterval_regular
      hcomplete hcurv hR x V
  · have htneg : t < 0 := lt_of_le_of_ne
      (by simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using ht) ht0
    have htreg : t ∈ ancientTimeInterval.regular := by
      simpa only [ancientTimeInterval_regular, Set.mem_Iio] using htneg
    rw [derivWithin_of_mem_nhds (ancientTimeInterval.regular_mem_nhds htreg)]
    apply hamilton_ancient_trace_harnack euclideanFlatFlow.S euclideanFlatFlow.isSolution
      (fun s hs => hcomplete s (ancientTimeInterval.regular_subset hs))
      (fun a b hab => hcurv a b (hab.trans ancientTimeInterval.regular_subset))
      (fun s hs y => hR s (ancientTimeInterval.regular_subset hs) y) _ x V
    intro s hs
    simpa only [ancientTimeInterval_regular, Set.mem_Iio] using hs.trans_lt htneg

theorem not_kLim_euclideanFlatFlow (kappa : ℝ) :
    ¬ KLim (I := I3) kappa euclideanFlatFlow :=
  fun hK => euclideanFlatFlow_not_notFlat hK.notFlat

theorem euclideanFlatFlow_kLim_iff_notFlat {kappa : ℝ} (hkappa : 0 < kappa)
    (hvol : ENNReal.ofReal kappa ≤ euclideanUnitBallVolume 3) :
    KLim (I := I3) kappa euclideanFlatFlow ↔
      PointedFlowNotFlat (I := I3) euclideanFlatFlow := by
  refine ⟨fun hK => hK.notFlat, fun hflat => ?_⟩
  exact
    { dimension_ge_two := by norm_num [finrank_euclideanSpace, Fintype.card_fin]
      kappa_pos := hkappa
      carrier_eq := rfl
      regular_eq := rfl
      connected := inferInstance
      complete := fun _ _ => (euclideanMetric_complete (E := ThreeSpace)).complete
      nonnegativeCurvatureOperator := fun t _ =>
        euclideanFlatFlow_nonnegativeCurvatureOperator t
      noncollapsed := euclideanFlatFlow_noncollapsed hkappa hvol
      notFlat := hflat
      traceHarnack := fun t ht x V => euclideanFlatFlow_traceHarnack t ht x V }

section KappaMonotone

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance kappaMonotoneMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance kappaMonotoneBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩

omit [CompleteSpace E] in
theorem flowMetricBall_isKappaNoncollapsed_of_kappa_le
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {t : RealTimeInterval.FlowTime D} {B : FlowMetricBall (I := I) S t}
    {kappa kappa' : ℝ} (hkappa : 0 < kappa) (hle : kappa ≤ kappa')
    (hB : B.IsKappaNoncollapsed kappa') : B.IsKappaNoncollapsed kappa := by
  obtain ⟨_, hvol⟩ := hB
  exact ⟨hkappa, (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl).trans hvol⟩

theorem pointedFlowNoncollapsedAllScales_of_kappa_le {D : RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa kappa' : ℝ} (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') (h : PointedFlowNoncollapsedAllScales (I := I) F kappa') :
    PointedFlowNoncollapsedAllScales (I := I) F kappa :=
  fun time B hcontrolled =>
    flowMetricBall_isKappaNoncollapsed_of_kappa_le hkappa hle (h time B hcontrolled)

theorem kLim_of_kappa_le {D : RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa kappa' : ℝ}
    (hK : KLim (I := I) kappa' F) (hkappa : 0 < kappa) (hle : kappa ≤ kappa') :
    KLim (I := I) kappa F :=
  { dimension_ge_two := hK.dimension_ge_two
    kappa_pos := hkappa
    carrier_eq := hK.carrier_eq
    regular_eq := hK.regular_eq
    connected := hK.connected
    complete := hK.complete
    nonnegativeCurvatureOperator := hK.nonnegativeCurvatureOperator
    noncollapsed := pointedFlowNoncollapsedAllScales_of_kappa_le hkappa hle hK.noncollapsed
    notFlat := hK.notFlat
    traceHarnack := hK.traceHarnack }

theorem kLimSeedVolumeBound_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimSeedVolumeBound.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimSeedVolumeBound.{u, uE, uH} (I := I) kappa' := by
  obtain ⟨v, hv, hbound⟩ := h
  exact ⟨v, hv, fun D F hK x hx => hbound D F (kLim_of_kappa_le hK hkappa hle) x hx⟩

theorem kLimNormalizedSeedVolumeBound_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimNormalizedSeedVolumeBound.{u, uE, uH} (I := I) kappa' := by
  obtain ⟨v, hv, hbound⟩ := h
  exact ⟨v, hv, fun F hK hbase =>
    hbound F (kLim_of_kappa_le hK hkappa hle) hbase⟩

theorem kLimAnchoredScalarBound_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimAnchoredScalarBound.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimAnchoredScalarBound.{u, uE, uH} (I := I) kappa' := by
  intro v D hv hD
  obtain ⟨C, hC, hbound⟩ := h v D hv hD
  exact ⟨C, hC, fun T F hK p hp q hq =>
    hbound T F (kLim_of_kappa_le hK hkappa hle) p hp q hq⟩

theorem kLimThreeCollapseRadius_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimThreeCollapseRadius.{u, uE, uH} (I := I) kappa' := by
  intro epsilon hepsilon
  obtain ⟨A, hA, hbound⟩ := h epsilon hepsilon
  exact ⟨A, hA, fun F hK hbase hscalar =>
    hbound F (kLim_of_kappa_le hK hkappa hle) hbase hscalar⟩

theorem kLimAlmostAncientCollapse_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa' := by
  intro epsilon hepsilon
  obtain ⟨A, L, hA, hAL, hbound⟩ := h epsilon hepsilon
  exact ⟨A, L, hA, hAL, fun D F hK x Q r hQ hx hr hlocal hscale =>
    hbound D F (kLim_of_kappa_le hK hkappa hle) x Q r hQ hx hr hlocal hscale⟩

theorem kLimSeedAncientLimit_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa' := by
  intro X hD hK hdim hvolume
  exact h X hD (fun i => kLim_of_kappa_le (hK i) hkappa hle) hdim hvolume

theorem kLimHarnackCollapseBound_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa' :=
  ⟨kLimSeedVolumeBound_of_kappa_le h.1 hkappa hle,
    kLimAnchoredScalarBound_of_kappa_le h.2 hkappa hle⟩

theorem kLimLocalCurvatureBound_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa' := by
  obtain ⟨C, hC, hbound⟩ := h
  exact ⟨C, hC, fun D F hK hbase A y hy t ht =>
    hbound D F (kLim_of_kappa_le hK hkappa hle) hbase A y hy t ht⟩

theorem kLimTerminalDerivativeBound_of_kappa_le {kappa kappa' : ℝ}
    (h : KLimTerminalDerivativeBound.{u, uE, uH} (I := I) kappa) (hkappa : 0 < kappa)
    (hle : kappa ≤ kappa') :
    KLimTerminalDerivativeBound.{u, uE, uH} (I := I) kappa' := by
  obtain ⟨K, hKpos, hbound⟩ := h
  exact ⟨K, hKpos, fun D F hK hbase A hA m y hy =>
    hbound D F (kLim_of_kappa_le hK hkappa hle) hbase A hA m y hy⟩

end KappaMonotone

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
