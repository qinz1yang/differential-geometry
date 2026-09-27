import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CGTInjectivityRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.NoncollapseInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle _root_.Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance localInjectivityMeasurableE : MeasurableSpace E := borel E
private local instance localInjectivityBorelE : BorelSpace E := ⟨rfl⟩

private theorem curvature_control_radius {C : ℝ} (hC : 0 ≤ C) :
    0 < 1 / (C + 1) ∧ 1 / (C + 1) ≤ 1 ∧ (1 / (C + 1)) ^ 4 * C ≤ 1 := by
  let r : ℝ := 1 / (C + 1)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hproduct : r * (C + 1) = 1 := by
    dsimp only [r]
    exact one_div_mul_cancel (by positivity)
  have hrone : r ≤ 1 := by nlinarith [mul_nonneg hr.le hC]
  have hrC : r * C ≤ 1 := by nlinarith
  have hpower : r ^ 3 ≤ 1 := pow_le_one₀ hr.le hrone
  have hmul := mul_le_mul hpower hrC (mul_nonneg hr.le hC) zero_le_one
  refine ⟨hr, hrone, ?_⟩
  change r ^ 4 * C ≤ 1
  nlinarith only [hmul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem smallBall_volume_of_unit_curvature
    {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (hzero : 0 ∈ D.carrier) {kappa C rho s : ℝ}
    (hnc : PointedFlowNoncollapsedAllScales F kappa)
    (hC : 0 ≤ C) (hrhoOne : rho ≤ 1) (hcontrol : rho ^ 4 * C ≤ 1)
    (hunit : ∀ z : F.M, riemannianEDistOf (F.S.base.metric 0) F.basepoint z <
      ENNReal.ofReal 1 → F.rmNormSq (I := I) 0 z ≤ C)
    (hs : 0 < s) (hsrho : s ≤ rho) :
    ENNReal.ofReal kappa * ENNReal.ofReal s ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
        {z : F.M | riemannianEDistOf (F.S.base.metric 0) F.basepoint z <
          ENNReal.ofReal s} := by
  let B := PointedFlowData.baseFlowBall (I := I) F hzero s hs
  have hcurvature : B.IsSpatiallyRmControlled := by
    intro z hz
    change riemannianEDistOf (F.S.base.metric 0) F.basepoint z < ENNReal.ofReal s at hz
    have hzunit := hz.trans_le (ENNReal.ofReal_le_ofReal (hsrho.trans hrhoOne))
    change s ^ 4 * F.rmNormSq (I := I) 0 z ≤ 1
    calc
      _ ≤ s ^ 4 * C := mul_le_mul_of_nonneg_left (hunit z hzunit) (pow_nonneg hs.le 4)
      _ ≤ rho ^ 4 * C :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hsrho 4) hC
      _ ≤ 1 := hcontrol
  exact (hnc ⟨0, hzero⟩ B hcurvature).2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem nonempty_flowScaleInjectivityBound_of_noncollapsed_unit_curvature
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hzero : 0 ∈ X.D.carrier) {kappa C : ℝ} (hkappa : 0 < kappa) (hC : 0 ≤ C)
    (hconn : ∀ i, ConnectedSpace (X.term i).M)
    (hnc : ∀ i, PointedFlowNoncollapsedAllScales (X.term i) kappa)
    (hnonneg : ∀ i, PointedFlowNonnegativeCurvatureOperator (X.term i) 0)
    (hunit : ∀ i, ∀ z : (X.term i).M,
      riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint z <
        ENNReal.ofReal 1 → (X.term i).rmNormSq (I := I) 0 z ≤ C) :
    Nonempty (FlowScaleInjectivityBound (I := I) X) := by
  classical
  let rho : ℝ := 1 / (C + 1)
  obtain ⟨hrho, hrhoOne, hcontrol⟩ := curvature_control_radius hC
  change 0 < rho at hrho
  change rho ≤ 1 at hrhoOne
  change rho ^ 4 * C ≤ 1 at hcontrol
  let K : ℝ := C + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨rJ, hrJ, hrJrho, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) hrho hK.le
  let R : ℝ := min rJ (Real.pi / Real.sqrt K)
  have hR : 0 < R := lt_min hrJ (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK))
  have hRj : R ≤ rJ := min_le_left _ _
  have hRrho : R ≤ rho := hRj.trans hrJrho
  have hRpi : R ≤ Real.pi / Real.sqrt K := min_le_right _ _
  have hs : 0 < R / 8 := by positivity
  have hsrho : R / 8 ≤ rho := by linarith
  have hη : 0 < selectedCGTInjRadius E kappa R := selectedCGTInjRadius_pos hkappa hR
  let Y := X.atZero (I := I)
  refine ⟨{ ρ := selectedCGTInjRadius E kappa R, pos := hη, bound := ?_ }⟩
  intro i
  refine ⟨hη, ?_⟩
  intro hcomplete
  let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
  let _ : ChartedSpace H (Y.obj i).M := (Y.obj i).charted
  let _ : IsManifold I ∞ (Y.obj i).M := (Y.obj i).smooth
  let _ : IsManifold I 1 (Y.obj i).M := IsManifold.of_le (n := ∞) (by decide)
  let _ : T2Space (Y.obj i).M := (Y.obj i).t2
  let _ : SigmaCompactSpace (Y.obj i).M := (Y.obj i).sigmaCompact
  let _ : T2Space (TangentBundle I (Y.obj i).M) := (Y.obj i).t2TangentBundle
  let _ : RiemannianBundle (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle (I := I)
  let _ : (y : (Y.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (Y.obj i).riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle_cont (I := I)
  let _ : EMetricSpace (Y.obj i).M := (Y.obj i).emetricSpace (I := I)
  have : IsRiemannianManifold I (Y.obj i).M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace (Y.obj i).M := MetricComplete.complete (I := I) (Y.obj i) hcomplete
  let _ : ConnectedSpace (Y.obj i).M := hconn i
  let hEnorm : IsMetricNorm (I := I) (Y.obj i).metric := by
    intro y v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (Y.obj i).metric y v
  have hRm : ∀ y : (Y.obj i).M,
      riemannianEDist I (Y.obj i).basepoint y < ENNReal.ofReal rho →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (Y.obj i).metric y 4
        (metricRm04At (I := I) (Y.obj i).metric y)) ≤ K := by
    intro y hy
    have hyOf : riemannianEDistOf (I := I) (Y.obj i).metric
        (Y.obj i).basepoint y < ENNReal.ofReal rho := by
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm]
      exact hy
    have hsq := hunit i y (hyOf.trans_le (ENNReal.ofReal_le_ofReal hrhoOne))
    apply Real.sqrt_le_iff.mpr
    refine ⟨hK.le, ?_⟩
    change (X.term i).rmNormSq (I := I) 0 y ≤ K ^ 2
    exact hsq.trans (by dsimp only [K]; nlinarith)
  have hRic : RicciBoundedBelow (I := I) (Y.obj i).metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) := by
    intro y v
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) (Y.obj i).metric y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (Y.obj i).metric y).mpr
      intro m c a b
      have hraw := hnonneg i y m c a b
      change 0 ≤ ∑ j, ∑ k, c j * c k *
        (metricRm04 (I := I) (Y.obj i).metric y) (vec4 (a j) (b j) (b k) (a k)) at hraw
      simpa only [metricRm04StandardAt_apply, metricRm04_apply] using hraw
    have h := metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) (Y.obj i).metric y hcone v
    change (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) *
      (Y.obj i).metric.inner y v v ≤ ricciTensor (I := I) (Y.obj i).metric y v v
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, neg_zero, zero_mul,
      metricRicciAt_apply_eq_ricciTensor] using h
  have hvolOf := smallBall_volume_of_unit_curvature (X.term i) hzero (hnc i)
    hC hrhoOne hcontrol (hunit i) hs hsrho
  have hvol : ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDist I (Y.obj i).basepoint y < ENNReal.ofReal (R / 8)} := by
    change ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDistOf (I := I) (Y.obj i).metric
          (Y.obj i).basepoint y < ENNReal.ofReal (R / 8)} at hvolOf
    simpa only [riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm]
      using hvolOf
  have hcgt := intrInj_ge_vol_of_ball (I := I) (Y.obj i).metric hEnorm
    (Y.obj i).basepoint hK hR hRrho hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRj))
    (r₀ := R / 8) (s := R / 8) hs hs (by linarith) (by linarith)
    (q := 0) (by norm_num) hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  rw [hhalf, hadd] at hcgt
  have hinj := (selectedCGTInjRadius_le_quotient (E := E) hkappa.le hR).trans hcgt
  simpa only [Y, PointedRiemannianManifold.intrinsicInjRadius] using hinj

end DifferentialGeometry.CheegerGromovCompactness
