import DifferentialGeometry.Geometry.Comparison.Volume.SegmentPolarRigidity
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentBallEuclideanUpper
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem segBall_vol_lt_eucl
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (y : M) ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRicPos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 →
      0 < ricciTensor (I := I) g y u u) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      < (volume : Measure E) (Metric.ball (0 : E) R) := by
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      < (∫⁻ θ : Metric.sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere) *
        ENNReal.ofReal (hypRadVol 0 (Module.finrank ℝ E - 1) R) :=
      segBall_vol_lt (I := I) g hEnorm x hR hd hRicPos
    _ = (volume : Measure E) (Metric.ball (0 : E) R) :=
      gBall_model_eucl (I := I) g x hR

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem segBall_lt_of_sec
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (y : M) ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hsec : ∀ (y : M) (a b : TangentSpace I y),
      a ≠ 0 → b ≠ 0 → g.inner y a b = 0 →
        0 < metricRm04StdAt (I := I) (M := M) g y a b b a) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      < (volume : Measure E) (Metric.ball (0 : E) R) :=
  segBall_vol_lt_eucl (I := I) g hEnorm x hR hd fun y _ hu ↦
    ricci_pos_of_sec (I := I) g y hd (hsec y) hu

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
