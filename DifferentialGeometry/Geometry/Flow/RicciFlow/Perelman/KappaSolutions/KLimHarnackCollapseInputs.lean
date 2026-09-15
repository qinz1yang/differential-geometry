import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimSeedCollapseInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimInstance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AnchoredSpatialPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Sphere
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance harnackInputTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance harnackInputCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance harnackInputSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance harnackInputC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance harnackInputT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance harnackInputSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance harnackInputTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance harnackInputMeasurable {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : MeasurableSpace F.M := borel F.M
private local instance harnackInputBorel {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : BorelSpace F.M := ⟨rfl⟩

namespace KLim

omit [I.Boundaryless] in
theorem exists_pos_scalar_three {D : RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    ∃ x : F.M, 0 < F.S.scalar 0 x := by
  obtain ⟨t, ht, x, hx⟩ := hK.notFlat
  have ht' : t ≤ 0 := by simpa only [hK.carrier_eq, Set.mem_Iic] using ht
  have hle := KLim.rmNormSq_le_of_terminal_scalar_le F hK hdim ht' x le_rfl
  have hpos : 0 < 3 * F.S.scalar 0 x ^ 2 :=
    lt_of_lt_of_le (lt_of_le_of_ne
      (normSq0S_nonneg (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)) (Ne.symm hx)) hle
  have hs2 : 0 < F.S.scalar 0 x ^ 2 :=
    (mul_pos_iff.mp hpos).elim (fun h => h.2) (fun h => absurd h.1 (by norm_num))
  exact ⟨x, lt_of_le_of_ne (hK.scalar_nonneg le_rfl x) (Ne.symm (sq_pos_iff.mp hs2))⟩

end KLim

theorem le_euclideanUnitBallVolume_three_of_kLim (hdim : Module.finrank ℝ E = 3)
    {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ}
    (hK : KLim (I := I) kappa F) :
    ENNReal.ofReal kappa ≤ euclideanUnitBallVolume 3 := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  let _ : ConnectedSpace F.M := hK.connected
  have hzero : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hK.complete 0 hzero⟩
  have hRic : RicciBoundedBelow (I := I) (F.S.base.metric 0) 0 := by
    intro z v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric 0) z).mpr
    intro n c u w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hK.nonnegativeCurvatureOperator 0 hzero z n c u w
  obtain ⟨x, hxpos⟩ := KLim.exists_pos_scalar_three (I := I) hK hdim
  have hxdist : (riemannianEDistOf (I := I) (F.S.base.metric 0) x x).toReal < (1 : ℝ) := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero]
    norm_num
  obtain ⟨w, _hw, _hsigma, hs, hQw, _hweight, hlocal⟩ :=
    exists_anchoredScalarSpatialPointSelection (I := I) (F.S.base.metric 0) hcomplete x
      (D := 1) (by norm_num) x hxdist hxpos
  let sigma : ℝ := 1 + 1 - (riemannianEDistOf (I := I) (F.S.base.metric 0) x w).toReal
  let s : ℝ := (1 - 1 / Real.sqrt 2) * sigma
  let Q : ℝ := F.S.scalar 0 w
  change 0 < s at hs
  change 0 < Q at hQw
  change ∀ z : F.M, riemannianEDistOf (I := I) (F.S.base.metric 0) w z <
    ENNReal.ofReal s → F.S.scalar 0 z ≤ 2 * Q at hlocal
  let r : ℝ := min s (1 / Real.sqrt (Real.sqrt (12 * Q ^ 2 + 1)))
  have hroot : 0 < Real.sqrt (Real.sqrt (12 * Q ^ 2 + 1)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith [sq_nonneg Q]))
  have hr : 0 < r := lt_min hs (one_div_pos.mpr hroot)
  have hden : (0 : ℝ) < 12 * Q ^ 2 + 1 := by linarith [sq_nonneg Q]
  have ha4 : (Real.sqrt (Real.sqrt (12 * Q ^ 2 + 1))) ^ 4 = 12 * Q ^ 2 + 1 := by
    rw [show (Real.sqrt (Real.sqrt (12 * Q ^ 2 + 1))) ^ 4 =
      ((Real.sqrt (Real.sqrt (12 * Q ^ 2 + 1))) ^ 2) ^ 2 by ring]
    rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hden.le]
  have hr4 : r ^ 4 ≤ 1 / (12 * Q ^ 2 + 1) := by
    calc r ^ 4 ≤ (1 / Real.sqrt (Real.sqrt (12 * Q ^ 2 + 1))) ^ 4 :=
          pow_le_pow_left₀ hr.le (min_le_right _ _) 4
      _ = 1 / (12 * Q ^ 2 + 1) := by rw [div_pow, one_pow, ha4]
  let B : FlowMetricBall F.S ⟨0, hzero⟩ := FlowMetricBall.mk w r hr
  have hcontrol : B.IsSpatiallyRmControlled := by
    intro z hz
    have hzs : riemannianEDistOf (I := I) (F.S.base.metric 0) w z < ENNReal.ofReal s :=
      lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    have hz2 : F.S.scalar 0 z ≤ 2 * Q := hlocal z hzs
    have hrm : F.rmNormSq (I := I) 0 z ≤ 12 * Q ^ 2 := by
      have h := KLim.rmNormSq_le_of_terminal_scalar_le F hK hdim (le_rfl : (0 : ℝ) ≤ 0) z hz2
      nlinarith [h]
    have hrmnn : 0 ≤ F.rmNormSq (I := I) 0 z :=
      normSq0S_nonneg (I := I) (F.S.base.metric 0) z 4 (F.S.base.rm04 0 z)
    have hprod := mul_le_mul hr4 hrm hrmnn (le_of_lt (div_pos one_pos hden))
    have hfinal : (1 / (12 * Q ^ 2 + 1)) * (12 * Q ^ 2) ≤ 1 := by
      rw [div_mul_eq_mul_div]
      rw [div_le_one hden]
      linarith
    change r ^ 4 * F.rmNormSq (I := I) 0 z ≤ 1
    linarith [hprod, hfinal]
  have hnc := (hK.noncollapsed ⟨0, hzero⟩ B hcontrol).2
  have hbishop := (riemannianBallOf_volume_bishop_nonnegative (I := I)
    (g := F.S.base.metric 0) hcomplete hRic w).2 r hr
  have hBvol : B.volume = riemannianVolumeMeasure (I := I) (M := F.M)
      (F.S.base.metric 0) (riemannianBallOf (I := I) (F.S.base.metric 0) w r) := by
    dsimp only [B]
    simp only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
      volumeMeasureOn_eq_metric, SolutionOn.family_metric, riemannianBallOf]
  rw [hdim, hBvol] at hnc
  rw [hdim] at hbishop
  have hcn : ENNReal.ofReal r ^ 3 * ENNReal.ofReal kappa ≤
      ENNReal.ofReal r ^ 3 * euclideanUnitBallVolume 3 := by
    have h1 : ENNReal.ofReal (r ^ 3) = ENNReal.ofReal r ^ 3 := ENNReal.ofReal_pow hr.le 3
    calc ENNReal.ofReal r ^ 3 * ENNReal.ofReal kappa
        = ENNReal.ofReal kappa * ENNReal.ofReal r ^ 3 := mul_comm _ _
      _ ≤ riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) w r) := hnc
      _ ≤ euclideanUnitBallVolume 3 * ENNReal.ofReal (r ^ 3) := hbishop
      _ = ENNReal.ofReal r ^ 3 * euclideanUnitBallVolume 3 := by rw [h1, mul_comm]
  have hr3 : ENNReal.ofReal r ^ 3 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne'
  have hr3top : ENNReal.ofReal r ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hr3 hr3top).1 hcn

theorem not_kLim_of_euclideanUnitBallVolume_three_lt (hdim : Module.finrank ℝ E = 3)
    {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ}
    (hvol : euclideanUnitBallVolume 3 < ENNReal.ofReal kappa) :
    ¬ KLim (I := I) kappa F :=
  fun hK => not_le.mpr hvol (le_euclideanUnitBallVolume_three_of_kLim (I := I) hdim hK)

theorem kLimSeedVolumeBound_of_euclideanUnitBallVolume_three_lt (hdim : Module.finrank ℝ E = 3)
    {kappa : ℝ} (hvol : euclideanUnitBallVolume 3 < ENNReal.ofReal kappa) :
    KLimSeedVolumeBound.{u, uE, uH} (I := I) kappa :=
  ⟨1, one_pos, fun _D _F hK _ _ =>
    absurd hK (not_kLim_of_euclideanUnitBallVolume_three_lt (I := I) hdim hvol)⟩

theorem kLimAnchoredScalarBound_of_euclideanUnitBallVolume_three_lt
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hvol : euclideanUnitBallVolume 3 < ENNReal.ofReal kappa) :
    KLimAnchoredScalarBound.{u, uE, uH} (I := I) kappa :=
  fun _ _ _ _ =>
    ⟨1, one_pos, fun _T _F hK _ _ _ _ =>
      absurd hK (not_kLim_of_euclideanUnitBallVolume_three_lt (I := I) hdim hvol)⟩

theorem kLimHarnackCollapseBound_of_euclideanUnitBallVolume_three_lt
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hvol : euclideanUnitBallVolume 3 < ENNReal.ofReal kappa) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa :=
  ⟨kLimSeedVolumeBound_of_euclideanUnitBallVolume_three_lt (I := I) hdim hvol,
    kLimAnchoredScalarBound_of_euclideanUnitBallVolume_three_lt (I := I) hdim hvol⟩

def KLimHarnackCollapseInput (kappa : ℝ) : Prop :=
  (0 < kappa ∧ ENNReal.ofReal kappa ≤ euclideanUnitBallVolume (Module.finrank ℝ E)) →
    KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa ∧
      KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa

theorem kLimHarnackCollapseBound_of_input (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (h : KLimHarnackCollapseInput.{u, uE, uH} (I := I) kappa) :
    KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa := by
  by_cases hpos : 0 < kappa
  · by_cases hle : ENNReal.ofReal kappa ≤ euclideanUnitBallVolume (Module.finrank ℝ E)
    · obtain ⟨hseed, hcollapse⟩ := h ⟨hpos, hle⟩
      exact kLimHarnackCollapseBound_of_seedAncientLimit_and_almostAncientCollapse
        (I := I) hdim hseed hcollapse
    · have hvol : euclideanUnitBallVolume 3 < ENNReal.ofReal kappa := by
        rw [hdim] at hle
        exact lt_of_not_ge hle
      exact kLimHarnackCollapseBound_of_euclideanUnitBallVolume_three_lt (I := I) hdim hvol
  · exact kLimHarnackCollapseBound_of_nonpos (I := I) hdim (not_lt.mp hpos)

omit [I.Boundaryless] in
theorem kLimHarnackCollapseInput_of_seedAncientLimit_and_almostAncientCollapse
    {kappa : ℝ}
    (hseed : KLimSeedAncientLimit.{u, uE, uH} (I := I) kappa)
    (hcollapse : KLimAlmostAncientCollapse.{u, uE, uH} (I := I) kappa) :
    KLimHarnackCollapseInput.{u, uE, uH} (I := I) kappa :=
  fun _ => ⟨hseed, hcollapse⟩

omit [I.Boundaryless] in
theorem kLimHarnackCollapseInput_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    KLimHarnackCollapseInput.{u, uE, uH} (I := I) kappa :=
  fun hrange => absurd hrange.1 (not_lt.mpr h)

omit [I.Boundaryless] in
theorem kLimHarnackCollapseInput_of_euclideanUnitBallVolume_lt {kappa : ℝ}
    (hvol : euclideanUnitBallVolume (Module.finrank ℝ E) < ENNReal.ofReal kappa) :
    KLimHarnackCollapseInput.{u, uE, uH} (I := I) kappa :=
  fun hrange => absurd hrange.2 (not_le.mpr hvol)

private instance roundSphereFourFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

private instance roundSphereThreeConnected :
    ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  refine Subtype.connectedSpace
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 zero_le_one)
  rw [← Module.finrank_eq_rank]
  simp

private theorem roundShrinkingSphereFlow_domain :
    ancientTimeInterval.carrier ⊆ Soliton.canonicalTimeDomain 1 := by
  intro t ht
  rw [Soliton.mem_canonicalTimeDomain_iff]
  simp only [one_mul]
  simp only [ancientTimeInterval_carrier, Set.mem_Iic] at ht
  linarith

abbrev roundShrinkingSphereFlow :
    PointedFlowData.{0, 0, 0} (I := 𝓡 3) ancientTimeInterval where
  M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  basepoint := ⟨EuclideanSpace.single 0 1, by simp⟩
  S := Soliton.canonicalSolutionOn
    (Geometry.roundSphereShrinkerMetric (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide))
    (Geometry.roundSphereShrinkerPotential (A := EuclideanSpace ℝ (Fin 4)) (n := 3)) 1
    (Geometry.roundSphereShrinkerMetric_complete (A := EuclideanSpace ℝ (Fin 4)) (n := 3)
      (by decide))
    (Geometry.gradientRicciSoliton_roundSphere (A := EuclideanSpace ℝ (Fin 4)) (n := 3)
      (by decide))
    ancientTimeInterval
  isSolution := Soliton.canonicalSolutionOn_isSolutionOn
    (Geometry.roundSphereShrinkerMetric (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide))
    (Geometry.roundSphereShrinkerPotential (A := EuclideanSpace ℝ (Fin 4)) (n := 3)) 1
    (Geometry.roundSphereShrinkerMetric_complete (A := EuclideanSpace ℝ (Fin 4)) (n := 3)
      (by decide))
    (Geometry.gradientRicciSoliton_roundSphere (A := EuclideanSpace ℝ (Fin 4)) (n := 3)
      (by decide))
    ancientTimeInterval roundShrinkingSphereFlow_domain

theorem roundShrinkingSphereFlow_metric_zero :
    roundShrinkingSphereFlow.S.base.metric 0 =
      Geometry.roundSphereShrinkerMetric (A := EuclideanSpace ℝ (Fin 4)) (n := 3)
        (by decide) :=
  Soliton.canonicalSolutionOn_metric_zero _ _ _ _ _ _

theorem roundShrinkingSphereFlow_scalar_zero (x : roundShrinkingSphereFlow.M) :
    roundShrinkingSphereFlow.S.scalar 0 x = (3 / 2 : ℝ) := by
  have h1 : roundShrinkingSphereFlow.S.scalar 0 x =
      metricScalarAt (I := 𝓡 3) (roundShrinkingSphereFlow.S.base.metric 0) x := rfl
  rw [h1, roundShrinkingSphereFlow_metric_zero]
  exact Geometry.roundSphereShrinkerMetric_scalarCurvature
    (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide) x

theorem roundShrinkingSphereFlow_notFlat :
    PointedFlowNotFlat (I := 𝓡 3) roundShrinkingSphereFlow := by
  refine pointedFlowNotFlat_of_scalar_ne_zero (F := roundShrinkingSphereFlow)
    (t := 0) ?_ roundShrinkingSphereFlow.basepoint ?_
  · simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  · rw [roundShrinkingSphereFlow_scalar_zero]
    norm_num

theorem not_kLim_roundShrinkingSphereFlow_of_euclideanUnitBallVolume_three_lt {kappa : ℝ}
    (hvol : euclideanUnitBallVolume 3 < ENNReal.ofReal kappa) :
    ¬ KLim (I := 𝓡 3) kappa roundShrinkingSphereFlow :=
  not_kLim_of_euclideanUnitBallVolume_three_lt (I := 𝓡 3) (by simp) hvol

theorem not_pointedFlowNoncollapsedAllScales_euclideanFlatFlow_of_lt {kappa : ℝ}
    (hvol : euclideanUnitBallVolume 3 < ENNReal.ofReal kappa) :
    ¬ PointedFlowNoncollapsedAllScales (I := I3) euclideanFlatFlow kappa := by
  intro hnc
  have hzero : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  let B : FlowMetricBall (I := I3) (M := ThreeSpace) euclideanFlatFlow.S
      ⟨0, hzero⟩ := ⟨0, 1, zero_lt_one⟩
  have hctrl : B.IsSpatiallyRmControlled := by
    intro x _hx
    have hrm : FlowMetricBall.rmNormSq (I := I3) euclideanFlatFlow.S (0 : ℝ) x = 0 := by
      have hflat : euclideanFlatFlow.rmNormSq (I := I3) (0 : ℝ) x = 0 :=
        euclideanFlatFlow_rmNormSq (0 : ℝ) x
      simpa only [PointedFlowData.rmNormSq, FlowMetricBall.rmNormSq, SolutionOn.family_metric]
        using hflat
    change (1 : ℝ) ^ 4 * FlowMetricBall.rmNormSq (I := I3) euclideanFlatFlow.S (0 : ℝ) x ≤ 1
    rw [hrm]
    norm_num
  have hle := (hnc ⟨0, hzero⟩ B hctrl).2
  have hvolB : B.volume = euclideanUnitBallVolume 3 * ENNReal.ofReal (B.radius ^ 3) := by
    simp only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
      volumeMeasureOn_eq_metric, SolutionOn.family_metric, SolutionOn.const_metric]
    exact euclideanMetric_ball_volume B.center B.radius_pos
  have hrad : B.radius = 1 := rfl
  rw [hvolB, hrad] at hle
  simp only [one_pow, ENNReal.ofReal_one, mul_one] at hle
  exact not_le.mpr hvol hle

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
