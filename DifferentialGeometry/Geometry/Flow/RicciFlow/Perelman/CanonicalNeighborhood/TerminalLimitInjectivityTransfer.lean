import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitFrontierInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalInjectivityRadiusDecay
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open Bundle Filter Set
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem hasInjRadiusAt_of_injOn_expMap
    (X : PointedRiemannianManifold.{u, 0, 0} (I := I3)) (p : X.M)
    {rho : ℝ} (hpos : 0 < rho)
    (hinj : Set.InjOn (fun v : TangentSpace I3 p =>
      DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I3) X.metric p v)
      {v | Real.sqrt (X.metric.inner p v v) < rho}) :
    HasInjRadiusAt X p rho := by
  refine ⟨hpos, fun hcomplete => ?_⟩
  let _ : IsManifold I3 1 X.M :=
    IsManifold.of_le (I := I3) (M := X.M) (n := ∞) (by decide)
  let _ : Bundle.RiemannianBundle (fun y : X.M => TangentSpace I3 y) := X.riemBundle
  let _ : (y : X.M) → InnerProductSpace ℝ (TangentSpace I3 y) := X.riemInner
  let _ : IsContinuousRiemannianBundle ThreeSpace
      (fun y : X.M => TangentSpace I3 y) := X.riemBundle_cont
  let _ : EMetricSpace X.M := X.emetricSpace
  let _ : CompleteSpace X.M := MetricComplete.complete X hcomplete
  let hEnorm : ∀ (y : X.M) (w : TangentSpace I3 y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I3) X.metric y w
  change ENNReal.ofReal rho ≤ intrinsicInjRadius X.metric hEnorm p
  apply le_intrInjRadius
  change Set.InjOn (intrinsicFramedExp X.metric hEnorm p) (Metric.eball 0 (ENNReal.ofReal rho))
  rw [Metric.eball_ofReal]
  intro v hv w hw heq
  apply (normalFrame X.metric p).injective
  apply hinj
  · simp only [Set.mem_ofPred_eq, normalFrame_sqrt]
    simpa only [Metric.mem_ball, dist_zero_right] using hv
  · simp only [Set.mem_ofPred_eq, normalFrame_sqrt]
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  · simpa only [intrinsicFrame_apply,
      ← Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic (I := I3) X.metric hEnorm p]
      using heq

private theorem riemannianMetricComplete_of_metricComplete
    (X : PointedRiemannianManifold.{u, 0, 0} (I := I3))
    (h : MetricComplete (I := I3) X) :
    DifferentialGeometry.RiemannianMetricComplete (I := I3) X.metric := by
  refine ⟨?_⟩
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace ThreeSpace X.M := X.charted
  let : IsManifold I3 ∞ X.M := X.smooth
  let : IsManifold I3 1 X.M :=
    IsManifold.of_le (I := I3) (M := X.M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace X.M := Manifold.metrizableSpace I3 X.M
  let : T3Space X.M := inferInstance
  let : RiemannianBundle (fun x : X.M => TangentSpace I3 x) :=
    ⟨X.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : X.M => TangentSpace I3 x) :=
    ⟨⟨X.metric.inner, X.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I3 X.M
  exact MetricComplete.complete (I := I3) X h

theorem terminalLimitBallInjectivity_of_curvatureAndNoncollapse
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {kappa' : ℝ} (hnc : X.TerminalSliceNoncollapsed kappa')
    (hcurv : TerminalDerivativeBounds X) :
    ∀ r : ℝ, 0 < r → ∃ η : ℝ, 0 < η ∧ ∀ᶠ i in Filter.atTop,
      ∀ x : ((X.toFlowSequence.atTime 0).obj i).M,
        riemannianEDistOf (I := I3) ((X.toFlowSequence.atTime 0).obj i).metric
          ((X.toFlowSequence.atTime 0).obj i).basepoint x ≤ ENNReal.ofReal r →
        HasInjRadiusAt (I := I3) ((X.toFlowSequence.atTime 0).obj i) x η := by
  classical
  intro r hr
  obtain ⟨C₀, hC₀⟩ := hcurv (r + 1) (by linarith) 0
  let C : ℝ := max C₀ 1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
  have hC₀le : C₀ ≤ C := le_max_left C₀ 1
  let rho : ℝ := min 1 (1 / C)
  have hrho_pos : 0 < rho := lt_min zero_lt_one (one_div_pos.mpr hCpos)
  have hrho_one : rho ≤ 1 := min_le_left 1 (1 / C)
  have hrho_inv : rho ≤ 1 / C := min_le_right 1 (1 / C)
  have hrhoC : rho * C ≤ 1 := (le_div_iff₀ hCpos).mp hrho_inv
  have hrho_sq : rho ^ 2 * C ≤ 1 := by
    calc rho ^ 2 * C = rho * (rho * C) := by ring
      _ ≤ rho * 1 := mul_le_mul_of_nonneg_left hrhoC hrho_pos.le
      _ = rho := mul_one rho
      _ ≤ 1 := hrho_one
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hnc.1
  refine ⟨iota * rho, mul_pos hiota hrho_pos, ?_⟩
  filter_upwards [hnc.2] with i hnc_i
  intro x hx
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  let F : PointedRiemannianManifold.{u, 0, 0} (I := I3) := (X.toFlowSequence.atTime 0).obj i
  let x₀ : (X.term i).M := x
  let B : FlowMetricBall (X.term i).S ⟨0, hzero⟩ := ⟨x₀, rho, hrho_pos⟩
  have hcomp : MetricComplete (I := I3) F := X.complete i 0 hzero
  let _ : TopologicalSpace (X.term i).M := (X.term i).topology
  let _ : ChartedSpace ThreeSpace (X.term i).M := (X.term i).charted
  let _ : IsManifold I3 ∞ (X.term i).M := (X.term i).smooth
  let _ : IsManifold I3 1 (X.term i).M :=
    IsManifold.of_le (I := I3) (M := (X.term i).M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
  let _ : T2Space (X.term i).M := (X.term i).t2
  let _ : RiemannianBundle (fun y : (X.term i).M => TangentSpace I3 y) := F.riemBundle (I := I3)
  let _ : IsContinuousRiemannianBundle ThreeSpace
      (fun y : (X.term i).M => TangentSpace I3 y) := F.riemBundle_cont (I := I3)
  let _ : EMetricSpace (X.term i).M := F.emetricSpace (I := I3)
  let _ : IsRiemannianManifold I3 (X.term i).M := ⟨fun _ _ => rfl⟩
  have hed : ∀ a b : (X.term i).M,
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0) a b = edist a b := by
    intro a b
    rw [riemannianEDistOf_eq_riemannianEDist (I := I3) ((X.term i).S.base.metric 0)
      (DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle (I := I3)
        ((X.term i).S.base.metric 0)) a b]
    exact (IsRiemannianManifold.out (I := I3) a b).symm
  have hx₀ : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
      (X.term i).basepoint x₀ ≤ ENNReal.ofReal r := hx
  have hx₀e : edist (X.term i).basepoint x₀ ≤ ENNReal.ofReal r := by
    have h := hx₀
    rwa [hed (X.term i).basepoint x₀] at h
  have hBctrl : B.IsSpatiallyRmControlled := by
    intro y hy
    have hy' : edist x₀ y < ENNReal.ofReal rho := by
      have h := hy
      change riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0) x₀ y <
        ENNReal.ofReal rho at h
      rwa [hed x₀ y] at h
    have hdist : metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ r + 1 := by
      have hbase : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
          (X.term i).basepoint y ≤ ENNReal.ofReal (r + 1) := by
        rw [hed (X.term i).basepoint y]
        calc edist (X.term i).basepoint y
            ≤ edist (X.term i).basepoint x₀ + edist x₀ y := edist_triangle _ _ _
          _ ≤ ENNReal.ofReal r + ENNReal.ofReal rho := add_le_add hx₀e hy'.le
          _ = ENNReal.ofReal (r + rho) := by
              rw [ENNReal.ofReal_add hr.le hrho_pos.le]
          _ ≤ ENNReal.ofReal (r + 1) := ENNReal.ofReal_le_ofReal (by linarith)
      simpa only [metricDistance] using
        ENNReal.toReal_le_of_le_ofReal (by linarith : (0 : ℝ) ≤ r + 1) hbase
    have hCb : curvDerivNorm (I := I3) 0 ((X.term i).S.base.metric 0) y ≤ C :=
      (hC₀ i y hdist).trans hC₀le
    have hnn : 0 ≤ Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
        (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) :=
      DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg (I := I3)
        ((X.term i).S.base.metric 0) y 4 _
    have hsqrt : Real.sqrt (Tensor0SBundle.normSq0S (I := I3)
        ((X.term i).S.base.metric 0) y 4
        (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y)) ≤ C :=
      (normSq0S_metricRm04At_le_curvDerivNorm (I := I3) ((X.term i).S.base.metric 0) y).trans
        hCb
    have hnorm : Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
        (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ C ^ 2 := by
      calc Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
            (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y)
          = (Real.sqrt (Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
              (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y))) ^ 2 :=
            (Real.sq_sqrt hnn).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    have hmain : rho ^ 4 * Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
        (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ 1 := by
      have h1 : rho ^ 4 * Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
          (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ rho ^ 4 * C ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      have h2 : rho ^ 4 * C ^ 2 = (rho ^ 2 * C) ^ 2 := by ring
      have h3 : (rho ^ 2 * C) ^ 2 ≤ 1 := by
        calc (rho ^ 2 * C) ^ 2 = (rho ^ 2 * C) * (rho ^ 2 * C) := by ring
          _ ≤ 1 * 1 := mul_le_mul hrho_sq hrho_sq (by positivity) zero_le_one
          _ = 1 := one_mul 1
      calc rho ^ 4 * Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
            (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y)
          ≤ rho ^ 4 * C ^ 2 := h1
        _ = (rho ^ 2 * C) ^ 2 := h2
        _ ≤ 1 := h3
    exact hmain
  have hvol : ENNReal.ofReal (kappa' * rho ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric 0)
        (riemannianBallOf (I := I3) ((X.term i).S.base.metric 0) x₀ rho) := by
    have hB := hnc_i ⟨0, hzero⟩ rfl B hrho_one hBctrl
    rw [ENNReal.ofReal_mul hnc.1.le, ENNReal.ofReal_pow hrho_pos.le]
    convert hB.2 using 1
    rfl
  have hrmc : DifferentialGeometry.RiemannianMetricComplete (I := I3)
      ((X.term i).S.base.metric 0) :=
    riemannianMetricComplete_of_metricComplete F hcomp
  exact hasInjRadiusAt_of_injOn_expMap F x₀ (mul_pos hiota hrho_pos)
    (hinj F.M F.metric hrmc x₀ rho hrho_pos (fun y hy => hBctrl y hy) hvol)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
