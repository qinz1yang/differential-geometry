import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Basic
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Interior
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Area
import DifferentialGeometry.Tensor.Coordinates.ModelBasis

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def segmentEndpointVectors [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    Set (TangentSpace I x) :=
  SegmentDom (I := I) g hEnorm x \ SegmentInt (I := I) g hEnorm x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def segmentEndpointImage [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) : Set M :=
  expMapIntrinsic (I := I) g hEnorm x '' segmentEndpointVectors (I := I) g hEnorm x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def segmentCutLocusCandidate [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) : Set M :=
  (expMapIntrinsic (I := I) g hEnorm x '' SegmentInt (I := I) g hEnorm x)ᶜ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem measurableSet_minimizingInterior [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    MeasurableSet (SegmentInt (I := I) g hEnorm x) :=
  measurableSet_segmentInt (I := I) g hEnorm x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem expMapIntrinsic_injOn_minimizingInterior [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    Set.InjOn (expMapIntrinsic (I := I) g hEnorm x)
      (SegmentInt (I := I) g hEnorm x) :=
  exp_inj_segmentInt (I := I) g hEnorm x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem minimizingInterior_no_conj [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {x : M} {v : TangentSpace I x}
    (hv : v ∈ SegmentInt (I := I) g hEnorm x) :
    ¬ IsConjVec (I := I) g hEnorm x (v : E) :=
  segmentInt_no_conj (I := I) g hEnorm hv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem minimizingSegment_no_conj [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {x : M} {v : TangentSpace I x}
    (hv : v ∈ SegmentDom (I := I) g hEnorm x) (hv0 : v ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ¬ IsConjVec (I := I) g hEnorm x
      ((t • v : TangentSpace I x) : E) :=
  segmentDom_no_conj (I := I) g hEnorm hv hv0 t ht

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segmentEndpointVectors_ray_subsingleton [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) :
    ({r : Ioi (0 : ℝ) |
      r.1 • u ∈ segmentEndpointVectors (I := I) g hEnorm x} :
      Set (Ioi (0 : ℝ))).Subsingleton :=
  segmentEnd_ray_sub (I := I) g hEnorm x u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem measurableSet_segmentEndpointVectors [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    MeasurableSet (segmentEndpointVectors (I := I) g hEnorm x) := by
  exact (measurableSet_segmentDom (I := I) g hEnorm x).diff
    (measurableSet_segmentInt (I := I) g hEnorm x)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segmentEndpointVectors_volume_zero [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    (volume : Measure E)
        ((normalFrame (I := I) (E := E) g x) ⁻¹'
          segmentEndpointVectors (I := I) g hEnorm x) = 0 := by
  exact segmentEnd_zero (I := I) (E := E) g hEnorm x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentCutLocusCandidate_inter_ball_volume_zero [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (segmentCutLocusCandidate (I := I) g hEnorm x ∩
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}) = 0 := by
  classical
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)
  let K : Set E :=
    (SegmentInt (I := I) g hEnorm x : Set E) ∩ gBall (I := I) g x R
  let B : Set M := {y : M | riemannianEDist I x y < ENNReal.ofReal R}
  have hKmeas : MeasurableSet K :=
    (measurableSet_segmentInt (I := I) g hEnorm x).inter
      (measurableSet_gBall (I := I) g x R)
  have hKinj : Set.InjOn F K := by
    exact (exp_inj_segmentInt (I := I) g hEnorm x).mono inter_subset_left
  have hFcont : Continuous F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hImageMeas : MeasurableSet (F '' K) :=
    hKmeas.image_of_continuousOn_injOn hFcont.continuousOn hKinj
  have hImageSub : F '' K ⊆ B := by
    rintro y ⟨v, hv, rfl⟩
    have hvD : (show TangentSpace I x from v) ∈
        SegmentDom (I := I) g hEnorm x :=
      segmentInt_subset (I := I) g hEnorm x hv.1
    have hfin : riemannianEDist I x (F v) ≠ ⊤ :=
      riemannianEDist_ne_top (I := I) x _
    change riemannianEDist I x (F v) < ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal hfin, ← (mem_segmentDom (I := I)).mp hvD]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 hv.2
  have hImageMeasure :
      riemannianVolumeMeasure (I := I) (M := M) g (F '' K) =
        ∫⁻ v in K, ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
    exact riemVol_exp_image_eq (I := I) g hEnorm x hKmeas hKinj
  have hBallMeasure :
      riemannianVolumeMeasure (I := I) (M := M) g B =
        ∫⁻ v in K, ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
    exact segmentBall_area_eq (I := I) g hEnorm x hR
  have hClosedFinite :
      ∫⁻ v in closedGBall (I := I) g x R,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) < ⊤ := by
    have hcompact : IsCompact (closedGBall (I := I) g x R) :=
      isCompact_closedGBall (I := I) g x R
    have hfiniteMeasure :
        modelHaar (E := E) (closedGBall (I := I) g x R) ≠ ⊤ :=
      hcompact.measure_ne_top
    have hcont : Continuous (fun v : E =>
        Real.toNNReal (expJacobianDensity (I := I) g hEnorm x v)) :=
      continuous_real_toNNReal.comp
        (expJacobian_continuous (I := I) g hEnorm x)
    simpa only [ENNReal.ofReal] using
      (setLIntegral_lt_top_of_isCompact hfiniteMeasure hcompact
        hcont)
  have hKSubClosed : K ⊆ closedGBall (I := I) g x R := by
    intro v hv
    change Real.sqrt (g.inner x (show TangentSpace I x from v)
      (show TangentSpace I x from v)) ≤ R
    exact le_of_lt hv.2
  have hKFinite :
      ∫⁻ v in K, ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hKSubClosed) hClosedFinite
  have hImageFinite :
      riemannianVolumeMeasure (I := I) (M := M) g (F '' K) ≠ ⊤ := by
    rw [hImageMeasure]
    exact hKFinite.ne
  have hDifferenceZero :
      riemannianVolumeMeasure (I := I) (M := M) g (B \ F '' K) = 0 := by
    rw [measure_sdiff hImageSub hImageMeas.nullMeasurableSet hImageFinite,
      hBallMeasure, hImageMeasure, tsub_self]
  apply measure_mono_null _ hDifferenceZero
  rintro y ⟨hyCut, hyB⟩
  refine ⟨hyB, ?_⟩
  intro hyImage
  apply hyCut
  rcases hyImage with ⟨v, hv, rfl⟩
  exact ⟨v, hv.1, rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentCutLocusCandidate_volume_zero [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (segmentCutLocusCandidate (I := I) g hEnorm x) = 0 := by
  apply measure_mono_null
    (show segmentCutLocusCandidate (I := I) g hEnorm x ⊆
      ⋃ n : ℕ, segmentCutLocusCandidate (I := I) g hEnorm x ∩
        {y : M | riemannianEDist I x y < ENNReal.ofReal ((n : ℝ) + 1)} by
      intro y hy
      obtain ⟨n, hn⟩ := exists_nat_gt (riemannianEDist I x y).toReal
      refine mem_iUnion.2 ⟨n, hy, ?_⟩
      have hfin : riemannianEDist I x y ≠ ⊤ :=
        riemannianEDist_ne_top (I := I) x y
      change riemannianEDist I x y < ENNReal.ofReal ((n : ℝ) + 1)
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (n : ℝ) + 1)).2
        (by linarith))
  apply measure_iUnion_null
  intro n
  exact segmentCutLocusCandidate_inter_ball_volume_zero
    (I := I) g hEnorm x (by positivity : 0 < (n : ℝ) + 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricBall_volume_eq_lintegral_minimizingInterior [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} =
      ∫⁻ v in SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R,
        ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
  segmentBall_area_eq (I := I) g hEnorm x hR

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
