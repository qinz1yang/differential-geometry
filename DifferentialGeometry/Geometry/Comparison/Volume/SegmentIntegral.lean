import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Area
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Interior
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold MeasureTheory
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
/-- On a measurable set where the exponential map is injective, its Jacobian-
weighted source measure pushes forward to Riemannian volume on the image. -/
theorem expJac_map_eq
    [ConnectedSpace M] [PseudoEMetricSpace M]
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
  classical
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)
  let J : E → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
  have hF_cont : Continuous F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hF_meas : Measurable F := hF_cont.measurable
  have hJ_meas : Measurable J :=
    ENNReal.measurable_ofReal.comp
      (expJacobianDensity_continuous (I := I) g hEnorm x).measurable
  change Measure.map F ((modelHaar (E := E)).restrict K |>.withDensity J) =
    (riemannianVolumeMeasure (I := I) (M := M) g).restrict (F '' K)
  refine Measure.ext fun A hA => ?_
  have hpre : MeasurableSet (F ⁻¹' A ∩ K) :=
    (hA.preimage hF_meas).inter hK
  have hinj' : Set.InjOn F (F ⁻¹' A ∩ K) :=
    hinj.mono inter_subset_right
  rw [Measure.map_apply hF_meas hA, Measure.restrict_apply hA,
    withDensity_apply J (hA.preimage hF_meas),
    Measure.restrict_restrict (hA.preimage hF_meas)]
  rw [show A ∩ F '' K = F '' (F ⁻¹' A ∩ K) from
    (Set.image_preimage_inter F K A).symm]
  simpa only [F, J] using
    (riemVol_exp_image_eq (I := I) g hEnorm x hpre hinj').symm

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Weighted change of variables for the exponential map on an injective
measurable set. -/
theorem expJac_lintegral
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K)
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K,
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫⁻ v in K,
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  classical
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)
  let J : E → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
  have hF_meas : Measurable F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable
  have hJ_meas : Measurable J :=
    ENNReal.measurable_ofReal.comp
      (expJacobianDensity_continuous (I := I) g hEnorm x).measurable
  have hmap := expJac_map_eq (I := I) g hEnorm x hK hinj
  change (∫⁻ y, f y ∂
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict (F '' K)) = _
  rw [← hmap]
  rw [MeasureTheory.lintegral_map hf hF_meas]
  change (∫⁻ a, f (F a) ∂
      ((modelHaar (E := E)).restrict K).withDensity J) = _
  have hwd :
      (∫⁻ a, f (F a) ∂
          ((modelHaar (E := E)).restrict K).withDensity J) =
        ∫⁻ a, J a * f (F a) ∂(modelHaar (E := E)).restrict K := by
    simpa only [Pi.mul_apply, Function.comp_apply] using
      (MeasureTheory.lintegral_withDensity_eq_lintegral_mul
        ((modelHaar (E := E)).restrict K) hJ_meas
        (hf.comp hF_meas))
  rw [hwd]
  change (∫⁻ v in K, J v * f (F v) ∂(modelHaar (E := E))) = _
  refine setLIntegral_congr_fun hK fun v _ => ?_
  simp only [F, J, mul_comm]

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Integrability transported through exponential change of variables on an
injective measurable set. -/
theorem expJac_integrable
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K)
    (f : M → ℝ)
    (hf : IntegrableOn f
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) '' K)
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IntegrableOn
      (fun v : E => expJacobianDensity (I := I) g hEnorm x v *
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)))
      K (modelHaar (E := E)) := by
  classical
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)
  let J : E → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
  let μK : Measure E := (modelHaar (E := E)).restrict K
  have hF_meas : Measurable F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable
  have hJ_meas : Measurable J :=
    ENNReal.measurable_ofReal.comp
      (expJacobianDensity_continuous (I := I) g hEnorm x).measurable
  have hmap := expJac_map_eq (I := I) g hEnorm x hK hinj
  have hfmap : Integrable f (Measure.map F (μK.withDensity J)) := by
    rw [hmap]
    exact hf
  have hcomp : Integrable (f ∘ F) (μK.withDensity J) :=
    (integrable_map_measure hfmap.aestronglyMeasurable
      hF_meas.aemeasurable).mp hfmap
  have hweighted : Integrable (fun v => f (F v) * (J v).toReal) μK :=
    (integrable_withDensity_iff hJ_meas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hcomp
  change Integrable
    (fun v : E => expJacobianDensity (I := I) g hEnorm x v * f (F v)) μK
  apply hweighted.congr
  filter_upwards with v
  simp only [J, ENNReal.toReal_ofReal
    (show 0 ≤ expJacobianDensity (I := I) g hEnorm x v by
      exact Real.sqrt_nonneg _), mul_comm]

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Signed change of variables for the exponential map on an injective
measurable set. -/
theorem expJac_integral
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) K)
    (f : M → ℝ)
    (hf : AEStronglyMeasurable f
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K))) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) '' K,
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ v in K,
        expJacobianDensity (I := I) g hEnorm x v *
          f (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v))
        ∂(modelHaar (E := E)) := by
  classical
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)
  let J : E → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
  have hF_meas : Measurable F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable
  have hJ_meas : Measurable J :=
    ENNReal.measurable_ofReal.comp
      (expJacobianDensity_continuous (I := I) g hEnorm x).measurable
  have hmap := expJac_map_eq (I := I) g hEnorm x hK hinj
  have hfmap : AEStronglyMeasurable f
      (Measure.map F
        ((modelHaar (E := E)).restrict K |>.withDensity J)) := by
    rw [hmap]
    exact hf
  change (∫ y, f y ∂
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict (F '' K)) = _
  rw [← hmap]
  rw [MeasureTheory.integral_map hF_meas.aemeasurable hfmap]
  change (∫ v, f (F v) ∂
      ((modelHaar (E := E)).restrict K).withDensity J) = _
  rw [integral_withDensity_eq_integral_toReal_smul hJ_meas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [J, F, ENNReal.toReal_ofReal
    (show 0 ≤ expJacobianDensity (I := I) g hEnorm x v by
      exact Real.sqrt_nonneg _), smul_eq_mul]

end General

section Interior

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
/-- Weighted polar integration on the interior minimizing-segment domain. -/
theorem segInt_lintegral
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫⁻ v in (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x),
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  exact expJac_lintegral (I := I) g hEnorm x
    (measurableSet_segmentInt (I := I) g (show _ from hEnorm) x)
    (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x) f hf

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Signed exponential change of variables on the interior minimizing-segment
domain. -/
theorem segInt_integral
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → ℝ)
    (hf : AEStronglyMeasurable f
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x)))) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ v in (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x),
        expJacobianDensity (I := I) g hEnorm x v *
          f (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v))
        ∂(modelHaar (E := E)) := by
  exact expJac_integral (I := I) g hEnorm x
    (measurableSet_segmentInt (I := I) g (show _ from hEnorm) x)
    (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x) f hf

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Signed polar-coordinate change of variables on the interior
minimizing-segment domain. -/
theorem segInt_int_polar
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → ℝ)
    (hf : IntegrableOn f
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) ''
          (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ u : Metric.sphere (0 : E) 1,
        ∫ r : Ioi (0 : ℝ),
          (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x).indicator
            (fun v : E => expJacobianDensity (I := I) g hEnorm x v *
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
  let K : Set E := show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x
  have hK : MeasurableSet K :=
    measurableSet_segmentInt (I := I) g (show _ from hEnorm) x
  have hsource : IntegrableOn (fun v => D v * f (F v)) K
      (modelHaar (E := E)) := by
    simpa only [D, F, K] using
      expJac_integrable (I := I) g hEnorm x hK
        (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x) f hf
  rw [segInt_integral (I := I) g hEnorm x f hf.aestronglyMeasurable]
  change (∫ v in K, D v * f (F v) ∂(modelHaar (E := E))) = _
  exact MeasureTheory.setIntegral_polar (modelHaar (E := E)) K hK
    (fun v => D v * f (F v)) hsource

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Signed polar-coordinate change of variables on the part of the interior
minimizing-segment domain lying in a metric tangent ball. -/
theorem segBall_int_polar
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (R : ℝ) (f : M → ℝ)
    (hf : IntegrableOn f
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) ''
          (SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x ∩ gBall (I := I) g x R))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∫ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x ∩ gBall (I := I) g x R),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ u : Metric.sphere (0 : E) 1,
        ∫ r : Ioi (0 : ℝ),
          (SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x ∩ gBall (I := I) g x R).indicator
            (fun v : E => expJacobianDensity (I := I) g hEnorm x v *
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
    SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x ∩ gBall (I := I) g x R
  have hK : MeasurableSet K :=
    (measurableSet_segmentInt (I := I) g (show _ from hEnorm) x).inter
      (measurableSet_gBall (I := I) g x R)
  have hinj : Set.InjOn F K :=
    (exp_inj_segmentInt (I := I) g (show _ from hEnorm) x).mono inter_subset_left
  have hsource : IntegrableOn (fun v => D v * f (F v)) K
      (modelHaar (E := E)) := by
    simpa only [D, F, K] using
      expJac_integrable (I := I) g hEnorm x hK hinj f hf
  rw [expJac_integral (I := I) g hEnorm x hK hinj f
    hf.aestronglyMeasurable]
  change (∫ v in K, D v * f (F v) ∂(modelHaar (E := E))) = _
  exact MeasureTheory.setIntegral_polar (modelHaar (E := E)) K hK
    (fun v => D v * f (F v)) hsource

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Polar-coordinate form of exponential change of variables on the interior
minimizing-segment domain. -/
theorem segInt_polar
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x),
        f y ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ),
          (show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x).indicator
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
  let K : Set E := show Set E from SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) x
  have hF : Measurable F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable
  have hJ : Measurable J :=
    ENNReal.measurable_ofReal.comp
      (expJacobianDensity_continuous (I := I) g hEnorm x).measurable
  have hK : MeasurableSet K :=
    measurableSet_segmentInt (I := I) g (show _ from hEnorm) x
  rw [segInt_lintegral (I := I) g hEnorm x f hf]
  change (∫⁻ v in K, f (F v) * J v ∂(modelHaar (E := E))) = _
  exact MeasureTheory.setLIntegral_polar (modelHaar (E := E)) K hK
    (fun v => f (F v) * J v) ((hf.comp hF).mul hJ).aemeasurable

end Interior

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
