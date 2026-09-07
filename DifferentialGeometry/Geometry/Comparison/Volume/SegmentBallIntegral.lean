import DifferentialGeometry.Geometry.Comparison.Volume.SegmentIntegral
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Basic

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold MeasureTheory
open scoped Topology Manifold ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space (TangentBundle I M)] in
private theorem segBall_image_sub
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R) :
    (fun v : E => expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)) ''
        (SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R) ⊆
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} := by
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  have hvD : v ∈ SegmentDom (I := I) g hEnorm x :=
    segmentInt_subset (I := I) g hEnorm x hv.1
  have hfin : riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x _
  change riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) < ENNReal.ofReal R
  rw [← ENNReal.ofReal_toReal hfin, ← (mem_segmentDom (I := I)).mp hvD]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).2 hv.2

private theorem segBall_int_eq
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R) (f : M → ℝ) :
    (∫ y in {z : M | riemannianEDist I x z < ENNReal.ofReal R},
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  apply setIntegral_congr_set
  refine ae_eq_set.2 ⟨segmentBall_complement_volume_zero (I := I) g hEnorm x hR, ?_⟩
  rw [sdiff_eq_empty.mpr (segBall_image_sub (I := I) g hEnorm x hR),
    measure_empty]

theorem integral_eq_segmentBall_image
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R) (f : M → ℝ)
    (hf : Function.support f ⊆
      {y : M | riemannianEDist I x y < ENNReal.ofReal R}) :
    (∫ y, f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← setIntegral_univ]
  calc
    _ = ∫ y in {z : M | riemannianEDist I x z < ENNReal.ofReal R},
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
        (subset_univ _) fun y hy => by
          by_contra hfy
          exact hy.2 (hf (Function.mem_support.mpr hfy))
    _ = _ := segBall_int_eq (I := I) g hEnorm x hR f

theorem ball_integral_eq_segment_polar
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R) (f : M → ℝ)
    (hf : IntegrableOn f
      {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∫ y in {z : M | riemannianEDist I x z < ENNReal.ofReal R},
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ u : Metric.sphere (0 : E) 1,
        ∫ r : Ioi (0 : ℝ),
          (SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R).indicator
            (fun v : E => expJacobianDensity (I := I) g hEnorm x v *
              f (expMapIntrinsic (I := I) g hEnorm x
                (show TangentSpace I x from v)))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  rw [segBall_int_eq (I := I) g hEnorm x hR f]
  exact segBall_int_polar (I := I) g hEnorm x R f
    (hf.mono_set (segBall_image_sub (I := I) g hEnorm x hR))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
