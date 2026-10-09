import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Basic
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.FrameBound
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.Measure
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.NoConjugatePoints
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Basic

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem gBall_model_eucl
    (g : SmoothRiemannianMetric I M) (x : M) {R : ℝ} (hR : 0 < R) :
    (∫⁻ θ : Metric.sphere (0 : E) 1,
        ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
          (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
        ∂(modelHaar (E := E)).toSphere) *
      ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) R) =
        (volume : Measure E) (Metric.ball (0 : E) R) := by
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g x
  have hpreclosed :
      L ⁻¹' closedGBall (I := I) g x R =
        Metric.closedBall (0 : E) R := by
    ext w
    simp only [Set.mem_preimage, closedGBall, Set.mem_ofPred_eq,
      Metric.mem_closedBall, dist_zero_right]
    have hsqrt : Real.sqrt (g.inner x (L w) (L w)) = ‖w‖ := by
      with_unfolding_all exact normalFrame_sqrt (I := I) g x w
    rw [hsqrt]
  have hclosed : MeasurableSet (closedGBall (I := I) g x R) :=
    (isClosed_closedGBall (I := I) g x R).measurableSet
  have hmodel := gBall_model_int (I := I) g x 0 R (by positivity) hR
  calc
    (∫⁻ θ : Metric.sphere (0 : E) 1,
        ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
          (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
        ∂(modelHaar (E := E)).toSphere) *
        ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) R) =
      ∫⁻ v in closedGBall (I := I) g x R,
        ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
          hyperbolicDensity (0 * Real.sqrt (g.inner x
            (show TangentSpace I x from v)
            (show TangentSpace I x from v)))
            (Module.finrank ℝ E - 1) 1) ∂(modelHaar (E := E)) :=
      hmodel.symm
    _ = ENNReal.ofReal (normalChartDensity (I := I) g x 0) *
        (modelHaar (E := E)) (closedGBall (I := I) g x R) := by
      have hfun : (fun v : E =>
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            hyperbolicDensity (0 * Real.sqrt (g.inner x
              (show TangentSpace I x from v)
              (show TangentSpace I x from v)))
              (Module.finrank ℝ E - 1) 1)) =
          fun _ : E =>
            ENNReal.ofReal (normalChartDensity (I := I) g x 0) := by
        funext v
        simp [hyperbolicDensity, hyperbolicSn]
      rw [hfun, setLIntegral_const]
    _ = (ENNReal.ofReal (normalChartDensity (I := I) g x 0) •
          modelHaar (E := E)) (closedGBall (I := I) g x R) := by
      simp only [Measure.smul_apply, smul_eq_mul]
    _ = (Measure.map L (volume : Measure E))
        (closedGBall (I := I) g x R) := by
      with_unfolding_all exact
        (congrArg
          (fun μ : Measure E => μ (closedGBall (I := I) g x R))
          (normalHaar_eq (E := E) (M := M) (I := I) g x))
    _ = (volume : Measure E)
        (L ⁻¹' closedGBall (I := I) g x R) := by
      rw [Measure.map_apply L.continuous.measurable hclosed]
    _ = (volume : Measure E) (Metric.closedBall (0 : E) R) := by
      rw [hpreclosed]
    _ = (volume : Measure E) (Metric.ball (0 : E) R) :=
      Measure.addHaar_closedBall_eq_addHaar_ball
        (volume : Measure E) (0 : E) R

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_vol_le_euclidean [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
        * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  have heq : (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace =
      ‹PseudoEMetricSpace M› := by
    apply PseudoEMetricSpace.ext
    ext y z
    change riemannianEDist I y z = edist y z
    exact (IsRiemannianManifold.out (I := I) y z).symm
  have hc : @CompleteSpace M (EMetricSpace.ofRiemannianMetric I M).toUniformSpace := by
    rw [heq]
    infer_instance
  have hproper := HopfRinow.properSpace_riemMetric (I := I) hc g hEnorm
  have hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall x (ENNReal.ofReal R)) := by
    let m : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    have hm : m.toPseudoEMetricSpace = ‹PseudoEMetricSpace M› := by
      exact heq
    rw [← hm]
    let : MetricSpace M := m
    let : PseudoEMetricSpace M := m.toPseudoEMetricSpace
    let : ProperSpace M := hproper
    have hset : Metric.closedEBall x (ENNReal.ofReal R) = Metric.closedBall x R := by
      ext y
      simp only [Metric.mem_closedEBall, Metric.mem_closedBall, edist_dist,
        ENNReal.ofReal_le_ofReal_iff hR.le]
    rw [hset]
    exact isCompact_closedBall x R
  exact riemannianVolumeMeasure_ball_le_hyperbolic_of_isCompact_closedEBall g hEnorm x hq hR hcpt
    (fun y v _ => hRic y v)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_vol_pow [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (R ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hR : 0 < R := hs.trans_le hsR
  have hrel := segmentBall_vol_rel (I := I) g hEnorm x
    (q := 0) (s := s) (R := R) (by positivity) hs hsR (by simpa using hRic)
  have hmodel (t : ℝ) (ht : 0 ≤ t) :
      ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) t) =
        ENNReal.ofReal (t ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹) := by
    have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hyperbolicRadialVolume_zero, Nat.sub_add_cancel hn, hnR, div_eq_mul_inv,
      ENNReal.ofReal_mul (pow_nonneg ht n)]
  rw [show Module.finrank ℝ E - 1 = n - 1 by rfl,
    hmodel s hs.le, hmodel R hR.le] at hrel
  have hfactor_pos : 0 < ENNReal.ofReal ((n : ℝ)⁻¹) :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr (Nat.cast_pos.mpr hn))
  have hscaled :
      ENNReal.ofReal ((n : ℝ)⁻¹) *
          (riemannianVolumeMeasure (I := I) (M := M) g
              {y : M | riemannianEDist I x y < ENNReal.ofReal R} *
            ENNReal.ofReal (s ^ n)) ≤
        ENNReal.ofReal ((n : ℝ)⁻¹) *
          (ENNReal.ofReal (R ^ n) *
            riemannianVolumeMeasure (I := I) (M := M) g
              {y : M | riemannianEDist I x y < ENNReal.ofReal s}) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hrel
  exact (ENNReal.mul_le_mul_iff_right hfactor_pos.ne' ENNReal.ofReal_ne_top).mp hscaled

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
