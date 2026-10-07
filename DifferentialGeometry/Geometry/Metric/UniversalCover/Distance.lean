import DifferentialGeometry.Geometry.Metric.Covering.BallImage
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph

open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem localPullMetric_proj (g : SmoothRiemannianMetric I M) :
    localPullMetric g (proj : UniversalCover M → M) proj_localDiffeo = liftedMetric g := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  rw [localPullMetric_inner, (hasMFDerivAt_proj (I := I) y).mfderiv]
  rfl

theorem image_riemannianBallOf_proj (g : SmoothRiemannianMetric I M)
    (x : UniversalCover M) (r : ℝ) :
    proj '' riemannianBallOf (liftedMetric g) x r = riemannianBallOf g (proj x) r :=
  DifferentialGeometry.Geometry.Metric.image_riemannianBallOf_of_coveringMap_localPullMetric
    (liftedMetric g) g proj_localDiffeo proj_isCoveringMap (localPullMetric_proj g) x r

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem image_ball_proj_of_isometryEquiv {X : Type*} [PseudoMetricSpace X]
    (g : SmoothRiemannianMetric I M) :
    letI : RegularSpace (UniversalCover M) := uc_regularSpace I
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
      ⟨(liftedMetric g).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨(liftedMetric g).inner, (liftedMetric g).contMDiff.continuous,
        by intro x v w; rfl⟩⟩
    letI : PseudoEMetricSpace (UniversalCover M) :=
      PseudoEMetricSpace.ofRiemannianMetric I (UniversalCover M)
    ∀ (e : X ≃ᵢ UniversalCover M) (x : X) (r : ℝ),
      (proj ∘ e) '' Metric.ball x r = riemannianBallOf g (proj (e x)) r := by
  let _ : RegularSpace (UniversalCover M) := uc_regularSpace I
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
    ⟨(liftedMetric g).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨(liftedMetric g).inner, (liftedMetric g).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    PseudoEMetricSpace.ofRiemannianMetric I (UniversalCover M)
  intro e x r
  have hball : Metric.eball (e x) (ENNReal.ofReal r) =
      riemannianBallOf (liftedMetric g) (e x) r :=
    Set.ext fun y => Metric.mem_eball'
  have himage : e '' Metric.ball x r = riemannianBallOf (liftedMetric g) (e x) r :=
    (congrArg (Set.image e) Metric.eball_ofReal.symm).trans
      ((e.image_eball x (ENNReal.ofReal r)).trans hball)
  calc
    (proj ∘ e) '' Metric.ball x r = proj '' (e '' Metric.ball x r) :=
      (Set.image_image proj e (Metric.ball x r)).symm
    _ = proj '' riemannianBallOf (liftedMetric g) (e x) r :=
      congrArg (Set.image proj) himage
    _ = riemannianBallOf g (proj (e x)) r := image_riemannianBallOf_proj g (e x) r

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
