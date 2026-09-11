import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Area
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Interior
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Integration

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Topology Manifold ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem map_expMapIntrinsic_withDensity_expJacobianDensity
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K) :
    Measure.map
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v))
        ((modelHaar (E := E)).restrict K |>.withDensity
          (fun v => ENNReal.ofReal
            (expJacobianDensity (I := I) g hEnorm x v))) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K) := by
  simpa only [← expJacobianDensity_eq_paramDensity g hEnorm x] using
    map_withDensity_paramDensity (I := I) g isOpen_univ hK (subset_univ _)
      ((intrinsicFiber_smooth (I := I) g hEnorm x).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffOn hinj

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_image_expMapIntrinsic
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K)
    (f : M → ℝ≥0∞) (hf : AEMeasurable f
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K))) :
    (∫⁻ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K,
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫⁻ v in K,
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  simpa only [← expJacobianDensity_eq_paramDensity g hEnorm x, mul_comm] using
    lintegral_image_eq_lintegral_paramDensity_mul (I := I) g isOpen_univ hK (subset_univ _)
      ((intrinsicFiber_smooth (I := I) g hEnorm x).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffOn hinj f hf

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrableOn_image_expMapIntrinsic_iff
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K)
    (f : M → F)
    (hf : AEStronglyMeasurable f
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K))) :
    IntegrableOn f
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) '' K)
      (riemannianVolumeMeasure (I := I) (M := M) g) ↔
    IntegrableOn
      (fun v : E => expJacobianDensity (I := I) g hEnorm x v •
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)))
      K (modelHaar (E := E)) := by
  simpa only [← expJacobianDensity_eq_paramDensity g hEnorm x] using
    integrableOn_image_iff_paramDensity_smul (I := I) g isOpen_univ hK (subset_univ _)
      ((intrinsicFiber_smooth (I := I) g hEnorm x).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffOn hinj f hf

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_image_expMapIntrinsic
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K)
    (f : M → F)
    (hf : AEStronglyMeasurable f
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K))) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K,
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ v in K,
        expJacobianDensity (I := I) g hEnorm x v •
          f (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v))
        ∂(modelHaar (E := E)) := by
  simpa only [← expJacobianDensity_eq_paramDensity g hEnorm x] using
    integral_image_eq_integral_paramDensity_smul (I := I) g isOpen_univ hK (subset_univ _)
      ((intrinsicFiber_smooth (I := I) g hEnorm x).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffOn hinj f hf

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem integrableOn_expJacobianDensity_smul
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K)
    (f : M → F)
    (hf : IntegrableOn f
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) '' K)
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IntegrableOn
      (fun v : E => expJacobianDensity (I := I) g hEnorm x v •
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)))
      K (modelHaar (E := E)) :=
  (integrableOn_image_expMapIntrinsic_iff g hEnorm x hK hinj f hf.aestronglyMeasurable).mp hf

end General

section Interior

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem lintegral_image_segmentInt
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫⁻ v in (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x),
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  exact lintegral_image_expMapIntrinsic (I := I) g hEnorm x
    (measurableSet_segmentInt (I := I) g (show _ from hEnorm) x)
    (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x) f hf.aemeasurable

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem integral_image_segmentInt
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → F)
    (hf : AEStronglyMeasurable f
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x)))) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ v in (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x),
        expJacobianDensity (I := I) g hEnorm x v •
          f (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v))
        ∂(modelHaar (E := E)) := by
  exact integral_image_expMapIntrinsic (I := I) g hEnorm x
    (measurableSet_segmentInt (I := I) g (show _ from hEnorm) x)
    (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x) f hf

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem integral_image_segmentInt_eq_polar
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → F)
    (hf : IntegrableOn f
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) ''
          (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ u : Metric.sphere (0 : E) 1,
        ∫ r : Ioi (0 : ℝ),
          (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x).indicator
            (fun v : E => expJacobianDensity (I := I) g hEnorm x v •
              f (expMapIntrinsic (I := I) g hEnorm x
                (show TangentSpace I x from v)))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)
  let D : E → ℝ := fun v => expJacobianDensity (I := I) g hEnorm x v
  let K : Set E := show Set E from SegmentInt (I := I) g (show _ from hEnorm) x
  have hK : MeasurableSet K :=
    measurableSet_segmentInt (I := I) g (show _ from hEnorm) x
  have hsource : IntegrableOn (fun v => D v • f (F v)) K
      (modelHaar (E := E)) := by
    simpa only [D, F, K] using
      integrableOn_expJacobianDensity_smul (I := I) g hEnorm x hK
        (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x) f hf
  rw [integral_image_segmentInt (I := I) g hEnorm x f hf.aestronglyMeasurable]
  change (∫ v in K, D v • f (F v) ∂(modelHaar (E := E))) = _
  exact MeasureTheory.setIntegral_polar (modelHaar (E := E)) K hK
    (fun v => D v • f (F v)) hsource

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem integral_image_segmentInt_inter_gBall_eq_polar
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (R : ℝ) (f : M → F)
    (hf : IntegrableOn f
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) ''
          (SegmentInt (I := I) g (show _ from hEnorm) x ∩ gBall (I := I) g x R))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (SegmentInt (I := I) g (show _ from hEnorm) x ∩ gBall (I := I) g x R),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ u : Metric.sphere (0 : E) 1,
        ∫ r : Ioi (0 : ℝ),
          (SegmentInt (I := I) g (show _ from hEnorm) x ∩ gBall (I := I) g x R).indicator
            (fun v : E => expJacobianDensity (I := I) g hEnorm x v •
              f (expMapIntrinsic (I := I) g hEnorm x
                (show TangentSpace I x from v)))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)
  let D : E → ℝ := fun v => expJacobianDensity (I := I) g hEnorm x v
  let K : Set E :=
    SegmentInt (I := I) g (show _ from hEnorm) x ∩ gBall (I := I) g x R
  have hK : MeasurableSet K :=
    (measurableSet_segmentInt (I := I) g (show _ from hEnorm) x).inter
      (measurableSet_gBall (I := I) g x R)
  have hinj : Set.InjOn F K :=
    (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x).mono inter_subset_left
  have hsource : IntegrableOn (fun v => D v • f (F v)) K
      (modelHaar (E := E)) := by
    simpa only [D, F, K] using
      integrableOn_expJacobianDensity_smul (I := I) g hEnorm x hK hinj f hf
  rw [integral_image_expMapIntrinsic (I := I) g hEnorm x hK hinj f
    hf.aestronglyMeasurable]
  change (∫ v in K, D v • f (F v) ∂(modelHaar (E := E))) = _
  exact MeasureTheory.setIntegral_polar (modelHaar (E := E)) K hK
    (fun v => D v • f (F v)) hsource

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem lintegral_image_segmentInt_eq_polar
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ),
          (show Set E from SegmentInt (I := I) g (show _ from hEnorm) x).indicator
            (fun v : E =>
              f (expMapIntrinsic (I := I) g hEnorm x
                (show TangentSpace I x from v)) *
                ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)
  let J : E → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
  let K : Set E := show Set E from SegmentInt (I := I) g (show _ from hEnorm) x
  have hF : Measurable F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable
  have hJ : Measurable J :=
    ENNReal.measurable_ofReal.comp
      (expJacobianDensity_continuous (I := I) g hEnorm x).measurable
  have hK : MeasurableSet K :=
    measurableSet_segmentInt (I := I) g (show _ from hEnorm) x
  rw [lintegral_image_segmentInt (I := I) g hEnorm x f hf]
  change (∫⁻ v in K, f (F v) * J v ∂(modelHaar (E := E))) = _
  exact MeasureTheory.setLIntegral_polar (modelHaar (E := E)) K hK
    (fun v => f (F v) * J v) ((hf.comp hF).mul hJ).aemeasurable.restrict

end Interior

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
