import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Basic
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball
import DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Area
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Pole
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Gauss
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Interior
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.Measure
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.FrameBound
import DifferentialGeometry.Geometry.Comparison.Volume.RatioIntegral
import DifferentialGeometry.Geometry.Comparison.Variation.NoConjugatePoints.MinimalGeodesic
import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Geometry.Comparison.HalfSquaredDistance.Basic
import DifferentialGeometry.Geometry.Comparison.HalfSquaredDistance.Gradient
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.IntrinsicDerivative
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def closedGBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) : Set E :=
  {v : E | Real.sqrt (g.inner x (show TangentSpace I x from v)
    (show TangentSpace I x from v)) ≤ R}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem isClosed_closedGBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    IsClosed (closedGBall (I := I) g x R) :=
  by
    have hcont : Continuous (fun v : E => g.inner x (show TangentSpace I x from v)
        (show TangentSpace I x from v)) := by
      with_unfolding_all exact continuous_gInner_self (I := I) g x
    exact isClosed_le (Real.continuous_sqrt.comp hcont) continuous_const

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem isCompact_closedGBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    IsCompact (closedGBall (I := I) g x R) := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closedGBall (I := I) g x R, ?_⟩
  rw [Metric.isBounded_iff_subset_ball (0 : E)]
  refine ⟨R / Real.sqrt (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst
    (I := I) g x) + 1, ?_⟩
  intro v hv
  have hc_pos : 0 < DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst
      (I := I) g x :=
    DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst_pos (I := I) g x
  have hsc_pos : 0 < Real.sqrt
      (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst (I := I) g x) :=
    Real.sqrt_pos.mpr hc_pos
  have hcoerc : DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst
      (I := I) g x * ‖v‖ ^ 2 ≤ g.inner x (show TangentSpace I x from v)
        (show TangentSpace I x from v) :=
    DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst_le (I := I) g x v
  have hgnn : 0 ≤ g.inner x v v := le_trans (by positivity) hcoerc
  have hkey : Real.sqrt (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst
      (I := I) g x) * ‖v‖ ≤ Real.sqrt (g.inner x v v) := by
    have hlhs_eq : Real.sqrt (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst
          (I := I) g x) * ‖v‖
        = Real.sqrt (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst
            (I := I) g x * ‖v‖ ^ 2) := by
      rw [Real.sqrt_mul hc_pos.le, Real.sqrt_sq (norm_nonneg v)]
    rw [hlhs_eq]
    exact Real.sqrt_le_sqrt hcoerc
  have hnorm : ‖v‖ ≤ Real.sqrt (g.inner x v v) / Real.sqrt
      (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst (I := I) g x) := by
    rw [le_div_iff₀ hsc_pos, mul_comm]
    exact hkey
  have hle : Real.sqrt (g.inner x v v) / Real.sqrt
        (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst (I := I) g x) ≤
      R / Real.sqrt (DifferentialGeometry.Geometry.Riemannian.metricCoerciveConst
        (I := I) g x) :=
    div_le_div_of_nonneg_right hv (Real.sqrt_nonneg _)
  simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using
    lt_of_le_of_lt (hnorm.trans hle) (lt_add_one _)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem ball_sub_image_segmentDom_closed [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (R : ℝ) :
    {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) ''
        ({v : E | (show TangentSpace I x from v) ∈ SegmentDom (I := I) g hEnorm x}
          ∩ closedGBall (I := I) g x R) := by
  have hcov := ball_sub_image_segmentDom (I := I) g hEnorm x R
  have hcovE : {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) ''
        {v : E | (show TangentSpace I x from v) ∈
          SegmentDom (I := I) g hEnorm x ∩ gBall (I := I) g x R} := by
    with_unfolding_all exact hcov
  have hgBallE : {v : E | (show TangentSpace I x from v) ∈
        gBall (I := I) g x R} ⊆ closedGBall (I := I) g x R := by
    intro v hv
    change Real.sqrt (g.inner x (show TangentSpace I x from v)
      (show TangentSpace I x from v)) ≤ R
    exact le_of_lt hv
  have hsub : {v : E | (show TangentSpace I x from v) ∈
        SegmentDom (I := I) g hEnorm x ∩ gBall (I := I) g x R} ⊆
      {v : E | (show TangentSpace I x from v) ∈ SegmentDom (I := I) g hEnorm x}
        ∩ closedGBall (I := I) g x R := by
    intro v hv
    exact ⟨hv.1, hgBallE hv.2⟩
  exact hcovE.trans (Set.image_mono hsub)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_vol_le_int
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (R : ℝ) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ ∫⁻ v in {v : E | (show TangentSpace I x from v) ∈
            SegmentDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcov := ball_sub_image_segmentDom_closed (I := I) g hEnorm x R
  have hK : IsCompact
      ({v : E | (show TangentSpace I x from v) ∈
          SegmentDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R) := by
    have hclosed : IsClosed {v : E | (show TangentSpace I x from v) ∈
        SegmentDom (I := I) g hEnorm x} := by
      with_unfolding_all exact
        ((isClosed_segmentDom (I := I) g hEnorm x).preimage
          (continuous_id : Continuous (fun v : E => v)))
    exact (isCompact_closedGBall (I := I) g x R).of_isClosed_subset
      (hclosed.inter (isClosed_closedGBall (I := I) g x R))
      (Set.inter_subset_right : {v : E | (show TangentSpace I x from v) ∈
          SegmentDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R ⊆
          closedGBall (I := I) g x R)
  have himg := riemVol_exp_image_le (I := I) g hEnorm x hK
  have hFcont : Continuous
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hball : MeasurableSet
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} := by
    have hcont : Continuous (fun y : M => riemannianEDist I x y) := by
      simpa [Manifold.riemannianEDist_comm] using
        (continuous_riemannianEDist_to (I := I) x)
    exact (isOpen_lt hcont continuous_const).measurableSet
  have himg_meas : MeasurableSet
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) ''
        ({v : E | (show TangentSpace I x from v) ∈
          SegmentDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R)) :=
    (hK.image hFcont).measurableSet
  exact (measure_mono hcov).trans himg

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentDom_not_conj
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegmentDom (I := I) g hEnorm x) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ IsConjVec (I := I) g hEnorm x ((t • v : TangentSpace I x) : E) := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  set ℓ : ℝ := Real.sqrt (g.inner x v v) with hℓ_def
  by_cases hv0 : v = 0
  · have htz : ((t • v : TangentSpace I x) : E) = 0 := by simp [hv0]
    rw [htz]
    unfold IsConjVec
    simp only [not_not]
    have hz := mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm x
    change Function.Injective (fun w : E =>
      mfderiv 𝓘(ℝ, E) I (fun b : E =>
        (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b) : M))
        (0 : E) w)
    rw [hz]
    with_unfolding_all exact (Function.injective_id : Function.Injective (id : E → E))
  · have hℓ_pos : 0 < ℓ := by
      rw [hℓ_def]
      exact Real.sqrt_pos.mpr (g.pos x v hv0)
    have hinner : g.inner x v v = ℓ ^ 2 := by
      rw [hℓ_def]
      exact (Real.sq_sqrt (gInner_self_nonneg (I := I) g x v)).symm
    let u : E := (ℓ⁻¹ • v : E)
    have hunit : g.inner x u u = 1 := by
      dsimp [u]
      rw [gInner_smul_self (I := I) g x ℓ⁻¹ v, hinner]
      have hpow : (ℓ⁻¹) ^ 2 * ℓ ^ 2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hℓ_pos), one_pow]
      exact hpow
    have hsmul : (ℓ : ℝ) • u = (v : E) := by
      change (ℓ : ℝ) • ((ℓ⁻¹ : ℝ) • (v : E)) = (v : E)
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ_pos), one_smul]
    have hlu : (ℓ • (show TangentSpace I x from u) : TangentSpace I x) = v := by
      with_unfolding_all exact hsmul
    have hmin : ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 ℓ) →
        η 0 = x →
        η ℓ = intrinsicGeodesic (I := I) g hEnorm x
            (show TangentSpace I x from u) ℓ →
        arcLength (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x
              (show TangentSpace I x from u)) 0 ℓ ≤
          arcLength (I := I) g η 0 ℓ := by
      intro η hη hη0 hηL
      have hγ_len : arcLength (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x
              (show TangentSpace I x from u)) 0 ℓ = ℓ := by
        rw [arcLength_radial (I := I) g hEnorm x
          (show TangentSpace I x from u) 0 ℓ, hunit]
        simp
      have hηL' : η ℓ = expMapIntrinsic (I := I) g hEnorm x v := by
        rw [hηL]
        rw [expMapIntrinsic_def]
        rw [← hlu]
        exact (intrinsicGeodesic_smul (I := I) g hEnorm x
          (show TangentSpace I x from u) ℓ).symm
      have hseg : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) =
          ENNReal.ofReal ℓ := by
        have hfin : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) ≠ ⊤ :=
          riemannianEDist_ne_top (I := I) x _
        rw [← (ENNReal.ofReal_toReal hfin)]
        congr 1
        exact hv.symm.trans hℓ_def.symm
      have hd := DifferentialGeometry.edistOf_le_arcLength (I := I) g
        (a := 0) (b := ℓ) hℓ_pos.le hη
      have hdist_le' : riemannianEDist I x (η ℓ) ≤
          ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
        have hbridge := DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist
          (I := I) g hEnorm x (η ℓ)
        rw [hη0] at hd
        rwa [hbridge] at hd
      have hof : ENNReal.ofReal ℓ ≤ ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
        have hd1 : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) ≤
            ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
          simpa [hηL'] using hdist_le'
        have hd2 : riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x v 1) ≤
            ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
          simpa [expMapIntrinsic_def] using hd1
        have hseg' : riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x v 1) =
            ENNReal.ofReal ℓ := by
          simpa [expMapIntrinsic_def] using hseg
        rwa [hseg'] at hd2
      have hle : ℓ ≤ arcLength (I := I) g η 0 ℓ := by
        exact (ENNReal.ofReal_le_ofReal_iff
          (arcLength_nonneg (I := I) g hℓ_pos.le)).mp hof
      rw [hγ_len]
      exact hle
    have hc : t * ℓ ∈ Set.Ioo (0 : ℝ) ℓ := by
      constructor
      · exact mul_pos ht.1 hℓ_pos
      · simpa using (mul_lt_mul_of_pos_right ht.2 hℓ_pos)
    have hn := not_conj_of_min_len (I := I) g hEnorm x u hunit ℓ hmin hc
    have htv : ((t • v : TangentSpace I x) : E) = (t * ℓ) • u := by
      rw [← hlu, smul_smul]
      rfl
    rwa [← htv] at hn

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expJacobianDensity_eq_ncd0_mul_transverse
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x} (hvne : v ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x v (w i) = 0) :
    expJacobianDensity (I := I) g hEnorm x (v : E) =
      normalChartDensity (I := I) g x 0 *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  have hv_li : LinearIndependent ℝ w := by
    exact linIndep_of_ortho (E := E) (I := I) (M := M) g x w hON
  obtain ⟨B, hBnone, hBsome⟩ :=
    exists_perp_basis (I := I) g x v w hv_li hperp (g.pos x v hvne)
  let a : Option (Fin d) → E := fun o => (B o : E)
  let e : Option (Fin d) ≃ Fin (Module.finrank ℝ E) := basisIndexEquiv B
  let V : Option (Fin d) → ∀ t : ℝ, TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm x v t) :=
    fun o t => intrinsicJacobi (I := I) g hEnorm x v (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (e o)) t
  let C : Matrix (Option (Fin d)) (Option (Fin d)) ℝ := (modelBasisFor B).toMatrix a
  have hC : ∀ o o', C o o' = (modelBasisFor B).repr (a o') o := by
    intro o o'
    rfl
  have hb : ∀ o, (modelBasisFor B) o = DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (e o) := by
    intro o
    simp [modelBasisFor, e, Module.Basis.reindex_apply]
  let vE : E := (tangentSpaceModelContinuousLinearEquiv (I := I) x) v
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) vE) :=
    Tensor0SBundle.tangentSpaceNormedAddCommGroup
      (I := 𝓘(ℝ, E)) (M := E) vE
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) vE) :=
    Tensor0SBundle.tangentSpaceNormedSpace
      (I := 𝓘(ℝ, E)) (M := E) vE
  have hjac : ∀ (u : E),
      intrinsicJacobi (I := I) g hEnorm x v (show TangentSpace I x from u) 1 =
        (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from z)) vE) u := by
    intro u
    with_unfolding_all exact
      (intrinsic_jacobi_one (I := I) g hEnorm x vE u)
  have hlin : ∀ o : Option (Fin d),
      (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from z)) vE) (a o)
        = ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) vE) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (e o')) := by
    intro o
    have hsum := (modelBasisFor B).sum_repr (a o)
    calc
      (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from z)) vE) (a o)
          = (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) vE)
              (∑ o', (modelBasisFor B).repr (a o) o' • (modelBasisFor B) o') := by
            exact congrArg (fun z : E =>
              (mfderiv 𝓘(ℝ, E) I (fun u : E =>
                (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from u) : M))
                vE) z) hsum.symm
      _ = ∑ o', (modelBasisFor B).repr (a o) o' •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) vE) ((modelBasisFor B) o') := by
          with_unfolding_all
            have hsumMap := map_sum
              (mfderiv 𝓘(ℝ, E) I (fun z : E =>
                (expMapIntrinsic (I := I) g hEnorm x
                  (show TangentSpace I x from z) : M)) vE)
              (fun o' : Option (Fin d) =>
                (modelBasisFor B).repr (a o) o' •
                  (show TangentSpace 𝓘(ℝ, E) vE from (modelBasisFor B) o'))
              Finset.univ
            refine hsumMap.trans ?_
            refine Finset.sum_congr rfl (fun o' _ => ?_)
            exact ContinuousLinearMap.map_smul
              (mfderiv 𝓘(ℝ, E) I (fun z : E =>
                (expMapIntrinsic (I := I) g hEnorm x
                  (show TangentSpace I x from z) : M)) vE)
              ((modelBasisFor B).repr (a o) o')
              (show TangentSpace 𝓘(ℝ, E) vE from (modelBasisFor B) o')
      _ = ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) vE) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (e o')) := by
          refine Finset.sum_congr rfl (fun o' _ => ?_)
          rw [hC o' o, hb o']
  have hrecomb : ∀ o : Option (Fin d),
      velocityJacobianFrame (I := I) g hEnorm x v w o 1 = ∑ o', C o' o • V o' 1 := by
    intro o
    have hV' : velocityJacobianFrame (I := I) g hEnorm x v w o 1 =
        intrinsicJacobi (I := I) g hEnorm x v (show TangentSpace I x from a o) 1 := by
      rcases o with - | i
      · simpa [velocityJacobianFrame, a, hBnone] using
          (radialJacobian_eq_velocity (I := I) g hEnorm x v).symm
      · simp [velocityJacobianFrame, a, hBsome]
    have h1' : velocityJacobianFrame (I := I) g hEnorm x v w o 1 =
        (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from z)) vE) (a o) :=
      hV'.trans (hjac (a o))
    have h2' : (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from z)) vE) (a o)
        = ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) vE) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (e o')) :=
      hlin o
    have h3' : ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) vE) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (e o'))
        = ∑ o', C o' o • V o' 1 := by
      refine Finset.sum_congr rfl (fun o' _ => ?_)
      rw [← hjac (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (e o'))]
      simp only [V]
      rfl
    exact h1'.trans (h2'.trans h3')
  have hrecomb' := curveDensity_recomb (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm x v) V
    (velocityJacobianFrame (I := I) g hEnorm x v w) 1 C hrecomb
  have hsplit := velocityJacobian_density_split (I := I) g hEnorm x v w hperp
  have hExp : expJacobianDensity (I := I) g hEnorm x (v : E) =
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 := by
    unfold expJacobianDensity
    exact (curveDensity_reindex (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
      (fun i : Fin (Module.finrank ℝ E) =>
        intrinsicJacobi (I := I) g hEnorm x v (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) 1 e).symm
  have hBperp : ∀ i, g.inner x (v : E) (B (some i)) = 0 := by
    intro i
    rw [hBsome i]
    exact hperp i
  have hONB : ∀ i j, g.inner x (B (some i)) (B (some j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hBsome i, hBsome j]
    exact hON i j
  have hncd := normalChartDensity_zero_of_perpOrthonormal (I := I) g x (v : E) B
    hBnone hBperp hONB
  have hdetC : |C.det| = |(modelBasisFor B).det B| := by
    change |((modelBasisFor B).toMatrix a).det| = |(modelBasisFor B).det B|
    rw [Module.Basis.det_apply]
  have hV1 : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 =
      (Real.sqrt (g.inner x v v) / |C.det|) *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 := by
    have hdet_ne : |C.det| ≠ 0 := by
      rw [hdetC]
      exact abs_ne_zero.mpr ((modelBasisFor B).isUnit_det B).ne_zero
    have hV : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 =
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
            (velocityJacobianFrame (I := I) g hEnorm x v w) 1 / |C.det| := by
      have hA : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
            (velocityJacobianFrame (I := I) g hEnorm x v w) 1 =
          |C.det| * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 := by
        simpa [mul_comm] using hrecomb'
      exact (eq_div_iff hdet_ne).mpr (by rw [mul_comm]; exact hA.symm)
    rw [hV, hsplit]
    field_simp [hdet_ne]
  rw [hExp, hV1]
  rw [hncd]
  rw [← hdetC]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem transverseDensity_le_hyperbolic
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegmentDom (I := I) g hEnorm x) (hvne : v ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x v (w i) = 0)
    (q : ℝ) (hq : 0 ≤ q) (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t ≤
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) t := by
  have hno : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ¬ IsConjVec (I := I) g hEnorm x ((t • v : TangentSpace I x) : E) :=
    fun t ht => segmentDom_not_conj (I := I) g hEnorm x hv ht
  have hanti := intrinsicRatioOfFrame (I := I) g hEnorm x v q 1 hq hd (g.pos x v hvne)
    w hON hperp hno hRic
  have hlim := poleLimit (I := I) g hEnorm x v q hq w hON
  intro t ht
  have hpos : 0 < hyperbolicDensity (q * Real.sqrt (g.inner x v v))
      (Module.finrank ℝ E - 1) t :=
    hyperbolicDensity_pos (mul_nonneg hq (Real.sqrt_nonneg _)) ht.1
  have hRatioLE :
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t /
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) t ≤ 1 := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
            (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t /
          hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) t ≤
          curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
              (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) s /
            hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) s := by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      have hsb : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
      exact hanti hsb ht hs.2.le
    exact ge_of_tendsto hlim hev
  rwa [div_le_one hpos] at hRatioLE

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private lemma symmL_eq_sum_chartBasis (α : M) (y : M) (c : E) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ y c =
      ∑ k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr c k • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y := by
  calc
    (trivializationAt E (TangentSpace I) α).symmL ℝ y c
        = (trivializationAt E (TangentSpace I) α).symmL ℝ y
            (∑ k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr c k • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) := by
            congr 1
            exact ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr c).symm
    _ = ∑ k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr c k •
          (trivializationAt E (TangentSpace I) α).symmL ℝ y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [ContinuousLinearMap.map_smul]
    _ = ∑ k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr c k • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k y := by
          rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private lemma chartRep_inner_eq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t₀ t : ℝ)
    (ht : γ t ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet) :
    g.inner (γ t) (V t) (W t) =
      ∑ k, ∑ l,
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ V t₀ t) k *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ W t₀ t) l *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g (γ t₀) (γ t) k l := by
  set T := trivializationAt E (TangentSpace I) (γ t₀) with hT
  have hV : V t = T.symmL ℝ (γ t) (chartRepAt (I := I) γ V t₀ t) := by
    simpa [hT, chartRepAt] using
      (T.symmL_continuousLinearMapAt (R := ℝ) ht (V t)).symm
  have hW : W t = T.symmL ℝ (γ t) (chartRepAt (I := I) γ W t₀ t) := by
    simpa [hT, chartRepAt] using
      (T.symmL_continuousLinearMapAt (R := ℝ) ht (W t)).symm
  rw [hV, hW]
  rw [symmL_eq_sum_chartBasis (γ t₀) (γ t) (chartRepAt (I := I) γ V t₀ t)]
  rw [symmL_eq_sum_chartBasis (γ t₀) (γ t) (chartRepAt (I := I) γ W t₀ t)]
  have hL : g.inner (γ t)
        (∑ k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ V t₀ t) k •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (γ t₀) k (γ t))
      = ∑ k, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ V t₀ t) k •
          g.inner (γ t) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (γ t₀) k (γ t)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  rw [hL, sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_apply]
  have hR : g.inner (γ t) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (γ t₀) k (γ t))
        (∑ l, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ W t₀ t) l •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (γ t₀) l (γ t))
      = ∑ l, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ W t₀ t) l *
          g.inner (γ t) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (γ t₀) k (γ t))
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) (γ t₀) l (γ t)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hR, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicJacobi_chartRep_differentiableAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v w : TangentSpace I x) (t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (intrinsicGeodesic (I := I) g hEnorm x v)
        (fun t => intrinsicJacobi (I := I) g hEnorm x v w t) t₀) t₀ := by
  have hf : IsSmoothVariation (I := I)
      (fun s t : ℝ => intrinsicGeodesic (I := I) g hEnorm x (v + s • w) t) := by
    with_unfolding_all exact
      ((intrinsicVar_smooth (I := I) g hEnorm x (v : E) (w : E)).of_le
        ENat.LEInfty.out)
  have hγ : (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm x (v + (0 : ℝ) • w) s) =
      intrinsicGeodesic (I := I) g hEnorm x v := by
    funext s
    congr 1
    simp
  have h := variationField_chartRep_differentiableAt (I := I)
    (fun s t : ℝ => intrinsicGeodesic (I := I) g hEnorm x (v + s • w) t) hf t₀
  have h' : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm x (v + (0 : ℝ) • w) s)
        (fun t => intrinsicJacobi (I := I) g hEnorm x v w t) t₀) t₀ := by
    with_unfolding_all exact h
  rw [hγ] at h'
  exact h'

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma continuousAt_sum {ι : Type*} [Fintype ι]
    (F : ℝ → ι → ℝ) (t₀ : ℝ)
    (hF : ∀ i, ContinuousAt (fun t => F t i) t₀) :
    ContinuousAt (fun t => ∑ i, F t i) t₀ := by
  classical
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using continuousAt_const
  · intro a s has ih
    have heq : (fun t => ∑ i ∈ insert a s, F t i) =
        (fun t => F t a + ∑ i ∈ s, F t i) := by
      funext t
      rw [Finset.sum_insert has]
    rw [heq]
    change ContinuousAt ((fun t => F t a) + (fun t => ∑ i ∈ s, F t i)) t₀
    exact (hF a).add ih

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma continuousAt_prod {ι : Type*} [Fintype ι]
    (F : ℝ → ι → ℝ) (t₀ : ℝ)
    (hF : ∀ i, ContinuousAt (fun t => F t i) t₀) :
    ContinuousAt (fun t => ∏ i, F t i) t₀ := by
  classical
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using continuousAt_const
  · intro a s has ih
    have heq : (fun t => ∏ i ∈ insert a s, F t i) =
        (fun t => F t a * ∏ i ∈ s, F t i) := by
      funext t
      rw [Finset.prod_insert has]
    rw [heq]
    change ContinuousAt ((fun t => F t a) * (fun t => ∏ i ∈ s, F t i)) t₀
    exact (hF a).mul ih

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma continuousAt_double_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ℝ → ι → κ → ℝ) (t₀ : ℝ)
    (hF : ∀ i j, ContinuousAt (fun t => F t i j) t₀) :
    ContinuousAt (fun t => ∑ i, ∑ j, F t i j) t₀ := by
  refine continuousAt_sum (fun t i => ∑ j, F t i j) t₀ ?_
  intro i
  refine continuousAt_sum (fun t j => F t i j) t₀ ?_
  intro j
  exact hF i j

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem curveDensity_jacobiFrame_continuousAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : TangentSpace I x)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (t₀ : ℝ) :
    ContinuousAt (fun t : ℝ =>
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
        (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t) t₀ := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x v
  set V : Fin (Module.finrank ℝ E - 1) → ∀ t, TangentSpace I (γ t) :=
    fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)
  have hγc : ContinuousAt γ t₀ :=
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm x v).continuous.continuousAt
  have hb₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀)
  have hpre : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t₀)).baseSet ∈ 𝓝 t₀ :=
    hγc.preimage_mem_nhds ((trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet.mem_nhds hb₀)
  have hcoord_cont : ∀ k, Continuous (fun c : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr c k) := by
    intro k
    refine LinearMap.continuous_of_finiteDimensional
      { toFun := fun c : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr c k,
        map_add' := fun x y => by simp [Finsupp.add_apply],
        map_smul' := fun a x => by
          calc
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (a • x)) k = (a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr x) k := by
              rw [map_smul]
            _ = a • ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr x) k := by rw [Finsupp.smul_apply] }
  have hjac_diff : ∀ i, DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t₀) t₀ := by
    intro i
    simpa [γ, V] using intrinsicJacobi_chartRep_differentiableAt (I := I) g hEnorm x v (w i) t₀
  have hEntry : ∀ i j, ContinuousAt
      (fun t : ℝ => g.inner (γ t) (V i t) (V j t)) t₀ := by
    intro i j
    have hcontA : ContinuousAt (fun t : ℝ => chartRepAt (I := I) γ (V i) t₀ t) t₀ :=
      (hjac_diff i).continuousAt
    have hcontB : ContinuousAt (fun t : ℝ => chartRepAt (I := I) γ (V j) t₀ t) t₀ :=
      (hjac_diff j).continuousAt
    have hcoordA : ∀ k, ContinuousAt
        (fun t : ℝ => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V i) t₀ t) k) t₀ := by
      intro k
      exact (hcoord_cont k).continuousAt.comp hcontA
    have hcoordB : ∀ l, ContinuousAt
        (fun t : ℝ => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V j) t₀ t) l) t₀ := by
      intro l
      exact (hcoord_cont l).continuousAt.comp hcontB
    have hgram : ∀ k l, ContinuousAt
        (fun t : ℝ => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g (γ t₀) (γ t) k l) t₀ := by
      intro k l
      have hc := (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g (γ t₀) k l).continuousOn
      have hcat : ContinuousAt (fun x : M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g (γ t₀) x k l) (γ t₀) :=
        hc.continuousAt ((trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet.mem_nhds hb₀)
      exact hcat.comp hγc
    have hR : ContinuousAt (fun t : ℝ =>
        ∑ k, ∑ l,
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V i) t₀ t) k *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V j) t₀ t) l *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g (γ t₀) (γ t) k l) t₀ := by
      refine continuousAt_double_sum
        (fun t (k : Fin (Module.finrank ℝ E)) (l : Fin (Module.finrank ℝ E)) =>
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V i) t₀ t) k *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V j) t₀ t) l *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g (γ t₀) (γ t) k l) t₀ ?_
      intro k l
      exact ((hcoordA k).mul (hcoordB l)).mul (hgram k l)
    have heq : (fun t : ℝ => g.inner (γ t) (V i t) (V j t)) =ᶠ[𝓝 t₀]
        (fun t : ℝ => ∑ k, ∑ l,
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V i) t₀ t) k *
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (chartRepAt (I := I) γ (V j) t₀ t) l *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g (γ t₀) (γ t) k l) := by
      filter_upwards [hpre] with t ht
      exact chartRep_inner_eq (I := I) g γ (V i) (V j) t₀ t ht
    exact hR.congr heq.symm
  have hdet : ContinuousAt (fun t : ℝ => (curveGram (I := I) g γ V t).det) t₀ := by
    simp only [Matrix.det_apply]
    refine Finset.induction_on Finset.univ ?_ ?_
    · simpa using continuousAt_const
    · intro σ s hσs ih
      have hprod : ContinuousAt (fun t : ℝ =>
          ∏ i : Fin (Module.finrank ℝ E - 1), (curveGram (I := I) g γ V t) (σ i) i) t₀ := by
        refine continuousAt_prod
          (fun t (i : Fin (Module.finrank ℝ E - 1)) => (curveGram (I := I) g γ V t) (σ i) i) t₀ ?_
        intro i
        simpa [curveGram] using hEntry (σ i) i
      have hterm : ContinuousAt (fun t : ℝ =>
          Equiv.Perm.sign σ • ∏ i : Fin (Module.finrank ℝ E - 1),
            (curveGram (I := I) g γ V t) (σ i) i) t₀ := by
        with_unfolding_all exact hprod.const_smul (Equiv.Perm.sign σ)
      have heq : (fun t => ∑ τ ∈ insert σ s,
          Equiv.Perm.sign τ • ∏ i, (curveGram (I := I) g γ V t) (τ i) i) =
          (fun t => Equiv.Perm.sign σ •
              ∏ i, (curveGram (I := I) g γ V t) (σ i) i +
            ∑ τ ∈ s, Equiv.Perm.sign τ •
              ∏ i, (curveGram (I := I) g γ V t) (τ i) i) := by
        funext t
        rw [Finset.sum_insert hσs]
      rw [heq]
      change ContinuousAt
        ((fun t => Equiv.Perm.sign σ •
            ∏ i, (curveGram (I := I) g γ V t) (σ i) i) +
          (fun t => ∑ τ ∈ s, Equiv.Perm.sign τ •
            ∏ i, (curveGram (I := I) g γ V t) (τ i) i)) t₀
      exact hterm.add ih
  have hsqrt : ContinuousAt (fun t : ℝ =>
      Real.sqrt ((curveGram (I := I) g γ V t).det)) t₀ :=
    Real.continuous_sqrt.continuousAt.comp hdet
  with_unfolding_all exact hsqrt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma transverseDensity_le_hyperbolic_at_one
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegmentDom (I := I) g hEnorm x) (hvne : v ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x v (w i) = 0)
    (q : ℝ) (hq : 0 ≤ q) (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 ≤
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) 1 := by
  have hwin : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t ≤
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) t :=
    transverseDensity_le_hyperbolic (I := I) g hEnorm x hv hvne w hON hperp q hq hd hRic
  set ℓ : ℝ := Real.sqrt (g.inner x v v) with hℓ
  have hqℓ : 0 ≤ q * ℓ := mul_nonneg hq (Real.sqrt_nonneg _)
  have hpos : 0 < hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) 1 :=
    hyperbolicDensity_pos hqℓ (by norm_num)
  have hcontNum : ContinuousAt (fun t : ℝ =>
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t) 1 :=
    curveDensity_jacobiFrame_continuousAt (I := I) g hEnorm x v w 1
  have hcontDen : ContinuousAt (fun t : ℝ =>
      hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) t) 1 :=
    (hyperbolicDen_continuous (q * ℓ) (Module.finrank ℝ E - 1)).continuousAt
  have hratio_cont : ContinuousAt (fun t : ℝ =>
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t /
        hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) t) 1 := by
    exact hcontNum.div hcontDen hpos.ne'
  have hlim : Tendsto
      (fun t : ℝ => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t /
        hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) t)
      (𝓝[<] (1 : ℝ))
      (𝓝 (curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 /
        hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) 1)) := by
    simpa [hℓ] using hratio_cont.continuousWithinAt.tendsto
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t /
        hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) t ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    have htwin : t ∈ Set.Ioo (0 : ℝ) 1 := ht
    have h1 : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t ≤
        hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) t := by
      simpa [hℓ] using hwin t htwin
    have hpt : 0 < hyperbolicDensity (q * ℓ) (Module.finrank ℝ E - 1) t :=
      hyperbolicDensity_pos hqℓ ht.1
    exact (div_le_one hpt).mpr h1
  have hc := le_of_tendsto hlim hev
  rwa [div_le_one hpos] at hc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expJacobianDensity_le_of_perpOrthonormalFrame
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegmentDom (I := I) g hEnorm x) (hvne : v ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x v (w i) = 0)
    (q : ℝ) (hq : 0 ≤ q) (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    expJacobianDensity (I := I) g hEnorm x (v : E) ≤
      normalChartDensity (I := I) g x 0 *
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) 1 := by
  have hfac := expJacobianDensity_eq_ncd0_mul_transverse (I := I) g hEnorm x hvne w hON hperp
  have hT := transverseDensity_le_hyperbolic_at_one (I := I) g hEnorm x hv hvne w hON hperp q hq hd hRic
  have hncd : 0 ≤ normalChartDensity (I := I) g x 0 := by
    rw [normalChartDensity, paramDensity_apply]
    exact Real.sqrt_nonneg _
  rw [hfac]
  exact mul_le_mul_of_nonneg_left hT hncd

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expJacobianDensity_le
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegmentDom (I := I) g hEnorm x) (hvne : v ≠ 0)
    (q : ℝ) (hq : 0 ≤ q) (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    expJacobianDensity (I := I) g hEnorm x (v : E) ≤
      normalChartDensity (I := I) g x 0 *
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) 1 := by
  obtain ⟨w, hON, hperp'⟩ :=
    exists_perp_pos (I := I) g x v (g.pos x v hvne)
  have hperp : ∀ i, g.inner x v (w i) = 0 := by
    intro i
    rw [← g.symm x (w i) v]
    exact hperp' i
  exact expJacobianDensity_le_of_perpOrthonormalFrame (I := I) g hEnorm x hv hvne w hON hperp
    q hq hd hRic

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma hyperbolicSn_scale_one (q r : ℝ) : r * hyperbolicSn (q * r) 1 = hyperbolicSn q r := by
  by_cases hq : q = 0
  · subst q
    simp [hyperbolicSn]
  · by_cases hr : r = 0
    · subst r
      simp [hyperbolicSn]
    · rw [hyperbolicSn, hyperbolicSn]
      have hqr : q * r ≠ 0 := mul_ne_zero hq hr
      rw [if_neg hq, if_neg hqr]
      field_simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma hyperbolicDensity_scale_one (q r : ℝ) (d : ℕ) :
    r ^ d * hyperbolicDensity (q * r) d 1 = hyperbolicDensity q d r := by
  simp only [hyperbolicDensity]
  rw [← mul_pow, hyperbolicSn_scale_one]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma hyperbolicDensity_scaled_nonneg {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) (d : ℕ) :
    0 ≤ hyperbolicDensity (q * r) d 1 := by
  have hqr : 0 ≤ q * r := mul_nonneg hq hr.le
  have hsn : 0 ≤ hyperbolicSn (q * r) 1 := by
    by_cases h0 : q * r = 0
    · simp [hyperbolicSn, h0]
    · exact (hyperbolicSn_pos hqr (by norm_num : (0 : ℝ) < 1)).le
  exact pow_nonneg hsn d

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma radial_model_lintegral
    (q : ℝ) {d : ℕ} (hq : 0 ≤ q) {R : ℝ} (hR : 0 < R) :
    (∫⁻ r : Ioi (0 : ℝ) in Iic (⟨R, hR⟩ : Ioi (0 : ℝ)),
        ENNReal.ofReal (hyperbolicDensity (q * r.1) d 1) ∂Measure.volumeIoiPow d)
      = ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
  have hpowMeas : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ d)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const d)
  rw [Measure.volumeIoiPow]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    _ hpowMeas _ measurableSet_Iic]
  · have hmul :
        (∫⁻ r : Ioi (0 : ℝ) in Iic (⟨R, hR⟩ : Ioi (0 : ℝ)),
            ((fun s : Ioi (0 : ℝ) => ENNReal.ofReal (s.1 ^ d)) *
              (fun s : Ioi (0 : ℝ) => ENNReal.ofReal (hyperbolicDensity (q * s.1) d 1))) r
            ∂Measure.comap Subtype.val volume)
      = ∫⁻ r : Ioi (0 : ℝ) in Iic (⟨R, hR⟩ : Ioi (0 : ℝ)),
          ENNReal.ofReal (hyperbolicDensity q d r.1) ∂Measure.comap Subtype.val volume := by
      apply setLIntegral_congr_fun measurableSet_Iic
      intro r _hr
      rw [Pi.mul_apply,
        ← ENNReal.ofReal_mul (pow_nonneg r.2.le d)]
      congr 1
      exact hyperbolicDensity_scale_one q r.1 d
    rw [hmul]
    rw [setLIntegral_subtype measurableSet_Ioi (Iic (⟨R, hR⟩ : Ioi (0 : ℝ)))
      (fun t : Real => ENNReal.ofReal (hyperbolicDensity q d t))]
    rw [image_subtype_val_Ioi_Iic]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← intervalIntegral.integral_of_le hR.le]
      rfl
    · exact (hyperbolicDen_continuous q d).continuousOn.intervalIntegrable_of_Icc hR.le |>.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (hyperbolicDensity_pos hq ht.1).le
  · filter_upwards [] with r
    exact ENNReal.ofReal_lt_top

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma hyperbolicSn_one_continuous : Continuous (fun q' : ℝ => hyperbolicSn q' 1) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  by_cases hq₀ : q₀ = 0
  · subst q₀
    have hsinc : Tendsto (fun x : ℝ => Real.sinh x / x) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      have hsinh' : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ)) Real.sinh id :=
        (Real.isEquivalent_sinh).mono
          (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) ≤ nhds (0 : ℝ))
      have hz : ∀ᶠ x in 𝓝[≠] (0 : ℝ), id x ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact hx
      have ht := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hsinh'
      with_unfolding_all exact ht
    have hg : ContinuousAt (fun x : ℝ => if x = 0 then 1 else Real.sinh x / x) 0 := by
      have hg0 : ContinuousAt (Function.update (fun x : ℝ => Real.sinh x / x) 0 1) 0 :=
        (continuousAt_update_same (f := fun x : ℝ => Real.sinh x / x)
          (x := (0 : ℝ)) (y := (1 : ℝ))).mpr hsinc
      have hfeq : (fun x : ℝ => if x = 0 then 1 else Real.sinh x / x) =
          Function.update (fun x : ℝ => Real.sinh x / x) 0 1 := by
        funext x
        by_cases hx : x = 0 <;> simp [Function.update, hx]
      rw [hfeq]
      exact hg0
    have hfun : (fun x : ℝ => if x = 0 then 1 else Real.sinh x / x) =ᶠ[𝓝 (0 : ℝ)]
        (fun x : ℝ => hyperbolicSn x 1) := by
      filter_upwards with x
      by_cases hx : x = 0
      · simp [hyperbolicSn, hx]
      · simp [hyperbolicSn, hx]
    exact ContinuousAt.congr hg hfun
  · have hc_quot : ContinuousAt (fun q' : ℝ => Real.sinh q' / q') q₀ := by
      exact (Real.continuous_sinh.continuousAt.div continuousAt_id hq₀)
    have hfun : (fun q' : ℝ => hyperbolicSn q' 1) =ᶠ[𝓝 q₀] (fun q' : ℝ => Real.sinh q' / q') := by
      filter_upwards [isOpen_ne.mem_nhds hq₀] with q' hq'ne
      simp [hyperbolicSn, hq'ne]
    exact ContinuousAt.congr hc_quot hfun.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma hyperbolicDensity_scale_continuous (q : ℝ) (d : ℕ) :
    Continuous (fun r : ℝ => hyperbolicDensity (q * r) d 1) := by
  have h1 : Continuous (fun q' : ℝ => hyperbolicDensity q' d 1) := by
    with_unfolding_all exact hyperbolicSn_one_continuous.pow d
  exact h1.comp (continuous_const.mul continuous_id)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma ball_model_lintegral
    (q R : ℝ) (hq : 0 ≤ q) (hR : 0 < R) :
    ∫⁻ w in Metric.closedBall (0 : E) R,
        ENNReal.ofReal (hyperbolicDensity (q * ‖w‖) (Module.finrank ℝ E - 1) 1) ∂(modelHaar (E := E))
      = ((modelHaar (E := E)).toSphere Set.univ) *
          ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
  classical
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let d : ℕ := Module.finrank ℝ E - 1
  let F : E → ℝ≥0∞ := fun w => ENNReal.ofReal (hyperbolicDensity (q * ‖w‖) d 1)
  have hFmeas : AEMeasurable F (modelHaar (E := E)) := by
    have hcont : Continuous (fun w : E => hyperbolicDensity (q * ‖w‖) d 1) :=
      (hyperbolicDensity_scale_continuous q d).comp continuous_norm
    exact ENNReal.continuous_ofReal.comp hcont |>.aemeasurable
  have hball_meas : MeasurableSet (Metric.closedBall (0 : E) R) :=
    (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : E) R)).measurableSet
  calc
    ∫⁻ w in Metric.closedBall (0 : E) R, F w ∂(modelHaar (E := E))
        = ∫⁻ w, (Metric.closedBall (0 : E) R).indicator F w ∂(modelHaar (E := E)) := by
          rw [lintegral_indicator hball_meas]
    _ = ∫⁻ u : sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : ℝ), (Metric.closedBall (0 : E) R).indicator F (r.1 • u.1)
            ∂(Measure.volumeIoiPow d) ∂(modelHaar (E := E)).toSphere := by
          simpa [d] using
            (lintegral_polar (modelHaar (E := E)) ((Metric.closedBall (0 : E) R).indicator F)
              (hFmeas.indicator hball_meas))
    _ = ∫⁻ u : sphere (0 : E) 1, ENNReal.ofReal (hyperbolicRadialVolume q d R)
          ∂(modelHaar (E := E)).toSphere := by
          apply lintegral_congr
          intro u
          have hu : ‖u.1‖ = 1 := by
            simpa only [mem_sphere_zero_iff_norm] using u.2
          have hinner : (∫⁻ r : Ioi (0 : ℝ),
              (Metric.closedBall (0 : E) R).indicator F (r.1 • u.1)
                ∂(Measure.volumeIoiPow d))
              = ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
            have hEq : (fun r : Ioi (0 : ℝ) =>
                  (Metric.closedBall (0 : E) R).indicator F (r.1 • u.1))
                = fun r : Ioi (0 : ℝ) => (Iic (⟨R, hR⟩ : Ioi (0 : ℝ))).indicator
                    (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (hyperbolicDensity (q * r.1) d 1)) r := by
              funext r
              by_cases hr : r.1 ≤ R
              · have hmem : r ∈ Iic (⟨R, hR⟩ : Ioi (0 : ℝ)) := hr
                have hb : r.1 • u.1 ∈ Metric.closedBall (0 : E) R := by
                  rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
                    Real.norm_of_nonneg r.2.le, hu, mul_one]
                  exact hr
                simp only [F, Set.indicator_of_mem hmem, Set.indicator_of_mem hb]
                congr 2
                rw [norm_smul, Real.norm_of_nonneg r.2.le, hu, mul_one]
              · have hmem : r ∉ Iic (⟨R, hR⟩ : Ioi (0 : ℝ)) := fun h => hr h
                have hb : r.1 • u.1 ∉ Metric.closedBall (0 : E) R := by
                  intro hmem_ball
                  have hrle : r.1 ≤ R := by
                    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
                      Real.norm_of_nonneg r.2.le, hu, mul_one] at hmem_ball
                    exact hmem_ball
                  exact hr hrle
                simp only [F, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hb]
            rw [hEq]
            rw [lintegral_indicator measurableSet_Iic]
            exact radial_model_lintegral q hq hR
          exact hinner
    _ = ((modelHaar (E := E)).toSphere Set.univ) * ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
          rw [lintegral_const, mul_comm]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma radial_model_lintegral_scaled
    (q : ℝ) {d : ℕ} (hq : 0 ≤ q) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    (∫⁻ r : Ioi (0 : ℝ) in Iic (⟨R / c, div_pos hR hc⟩ : Ioi (0 : ℝ)),
        ENNReal.ofReal (hyperbolicDensity (q * (r.1 * c)) d 1) ∂Measure.volumeIoiPow d)
      = ENNReal.ofReal ((c ^ (d + 1))⁻¹ * hyperbolicRadialVolume q d R) := by
  have hpowMeas : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ d)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const d)
  rw [Measure.volumeIoiPow]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hpowMeas _
    measurableSet_Iic (by filter_upwards [] with r; exact ENNReal.ofReal_lt_top)]
  · have hmul :
        (∫⁻ r : Ioi (0 : ℝ) in Iic (⟨R / c, div_pos hR hc⟩ : Ioi (0 : ℝ)),
            ((fun s : Ioi (0 : ℝ) => ENNReal.ofReal (s.1 ^ d)) *
              (fun s : Ioi (0 : ℝ) => ENNReal.ofReal (hyperbolicDensity (q * (s.1 * c)) d 1))) r
            ∂Measure.comap Subtype.val volume)
      = ∫⁻ r : Ioi (0 : ℝ) in Iic (⟨R / c, div_pos hR hc⟩ : Ioi (0 : ℝ)),
          ENNReal.ofReal (r.1 ^ d * hyperbolicDensity (q * (r.1 * c)) d 1)
            ∂Measure.comap Subtype.val volume := by
      apply setLIntegral_congr_fun measurableSet_Iic
      intro r _hr
      rw [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (pow_nonneg r.2.le d)]
    rw [hmul]
    rw [setLIntegral_subtype measurableSet_Ioi (Iic (⟨R / c, div_pos hR hc⟩ : Ioi (0 : ℝ)))
      (fun t : Real => ENNReal.ofReal (t ^ d * hyperbolicDensity (q * (t * c)) d 1))]
    rw [image_subtype_val_Ioi_Iic]
    have hfi : Integrable (fun x : ℝ => x ^ d * hyperbolicDensity (q * (x * c)) d 1)
        (volume.restrict (Ioc (0 : ℝ) (R / c))) := by
      have hcont : Continuous
          (fun x : ℝ => x ^ d * hyperbolicDensity (q * (x * c)) d 1) := by
        have heq : (fun x : ℝ => x ^ d * hyperbolicDensity (q * (x * c)) d 1) =
            (fun x : ℝ => x ^ d * hyperbolicDensity ((q * c) * x) d 1) := by
          funext z
          rw [show q * (z * c) = (q * c) * z by ring]
        rw [heq]
        exact (continuous_pow d).mul (hyperbolicDensity_scale_continuous (q * c) d)
      exact (hcont.continuousOn.intervalIntegrable_of_Icc (div_pos hR hc).le).1
    have hnn : 0 ≤ᶠ[ae (volume.restrict (Ioc (0 : ℝ) (R / c)))]
        (fun x : ℝ => x ^ d * hyperbolicDensity (q * (x * c)) d 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (pow_nonneg ht.1.le d)
        (hyperbolicDensity_scaled_nonneg hq (mul_pos ht.1 hc) d)
    have hbridge :
        ENNReal.ofReal (∫ x in Ioc (0 : ℝ) (R / c), x ^ d * hyperbolicDensity (q * (x * c)) d 1 ∂volume)
          = ∫⁻ x in Ioc (0 : ℝ) (R / c),
            ENNReal.ofReal (x ^ d * hyperbolicDensity (q * (x * c)) d 1) ∂volume := by
      exact (ofReal_integral_eq_lintegral_ofReal hfi hnn)
    rw [← hbridge]
    · have hsub : ∫ t in (0 : ℝ)..(R / c), t ^ d * hyperbolicDensity (q * (t * c)) d 1
          = (c ^ (d + 1))⁻¹ * ∫ s in (0 : ℝ)..R, s ^ d * hyperbolicDensity (q * s) d 1 := by
        let g : ℝ → ℝ := fun s => s ^ d * hyperbolicDensity (q * s) d 1 * (c ^ (d + 1))⁻¹
        have hcomp : ∀ t ∈ Set.uIcc (0 : ℝ) (R / c),
            (g ∘ fun x : ℝ => c * x) t * c = t ^ d * hyperbolicDensity (q * (t * c)) d 1 := by
          intro t ht
          dsimp [g]
          have hpow : (c * t) ^ d * (c ^ (d + 1))⁻¹ * c = t ^ d := by
            rw [mul_pow]
            field_simp [hc.ne']
            ring
          calc
            (c * t) ^ d * hyperbolicDensity (q * (c * t)) d 1 * (c ^ (d + 1))⁻¹ * c
                = ((c * t) ^ d * (c ^ (d + 1))⁻¹ * c) * hyperbolicDensity (q * (c * t)) d 1 := by ring
            _ = t ^ d * hyperbolicDensity (q * (t * c)) d 1 := by
                rw [hpow]
                congr 1
                congr 1
                ring
        have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (R / c),
            HasDerivAt (fun t : ℝ => c * t) c x := fun x hx => by
          have hd : HasDerivAt (fun y : ℝ => c * y) (c * 1) x := (hasDerivAt_id x).const_mul c
          convert hd using 1
          ring
        have hgcont : Continuous g := by
          dsimp [g]
          exact (((continuous_pow d).mul (hyperbolicDensity_scale_continuous q d)).mul
            continuous_const)
        have hsubst := intervalIntegral.integral_comp_mul_deriv hderiv
          (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => c)
            (Set.uIcc (0 : ℝ) (R / c))) hgcont
        calc
          ∫ t in (0 : ℝ)..(R / c), t ^ d * hyperbolicDensity (q * (t * c)) d 1
              = ∫ t in (0 : ℝ)..(R / c), (g ∘ fun x : ℝ => c * x) t * c := by
                refine intervalIntegral.integral_congr ?_
                intro t ht
                exact (hcomp t ht).symm
          _ = ∫ s in (0 : ℝ)..R, g s := by
                simpa [mul_div_cancel₀ R hc.ne'] using hsubst
          _ = (c ^ (d + 1))⁻¹ * ∫ s in (0 : ℝ)..R, s ^ d * hyperbolicDensity (q * s) d 1 := by
                dsimp [g]
                rw [← intervalIntegral.integral_const_mul (r := (c ^ (d + 1))⁻¹)
                  (f := fun s : ℝ => s ^ d * hyperbolicDensity (q * s) d 1)]
                refine intervalIntegral.integral_congr ?_
                intro s hs
                ring
      rw [← intervalIntegral.integral_of_le (div_pos hR hc).le]
      rw [hsub]
      congr 1
      have hrad : ∫ s in (0 : ℝ)..R, s ^ d * hyperbolicDensity (q * s) d 1 = hyperbolicRadialVolume q d R := by
        change ∫ s in (0 : ℝ)..R, s ^ d * hyperbolicDensity (q * s) d 1 =
          ∫ s in (0 : ℝ)..R, hyperbolicDensity q d s
        refine intervalIntegral.integral_congr ?_
        intro s hs
        exact hyperbolicDensity_scale_one q s d
      rw [hrad]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma radial_model_lintegral_scaled_mul
    (q : ℝ) {d : ℕ} (hq : 0 ≤ q) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ r : Ioi (0 : ℝ) in Iic (⟨R / c, div_pos hR hc⟩ : Ioi (0 : ℝ)),
        ENNReal.ofReal (A * hyperbolicDensity (q * (r.1 * c)) d 1) ∂Measure.volumeIoiPow d)
      = ENNReal.ofReal (A * (c ^ (d + 1))⁻¹ * hyperbolicRadialVolume q d R) := by
  have hmeas : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal
      (hyperbolicDensity (q * (r.1 * c)) d 1)) := by
    have hc0 : Continuous (fun t : ℝ => hyperbolicDensity (q * (t * c)) d 1) := by
      have hf : Continuous (fun t : ℝ => hyperbolicDensity ((q * c) * t) d 1) :=
        hyperbolicDensity_scale_continuous (q * c) d
      simpa [mul_assoc, mul_comm, mul_left_comm] using hf
    exact ENNReal.measurable_ofReal.comp ((hc0.measurable).comp measurable_subtype_coe)
  calc
    ∫⁻ r in Iic (⟨R / c, div_pos hR hc⟩ : Ioi (0 : ℝ)),
        ENNReal.ofReal (A * hyperbolicDensity (q * (r.1 * c)) d 1)
        ∂(Measure.volumeIoiPow d)
        = ENNReal.ofReal A *
          ∫⁻ r in Iic (⟨R / c, div_pos hR hc⟩ : Ioi (0 : ℝ)),
            ENNReal.ofReal (hyperbolicDensity (q * (r.1 * c)) d 1)
            ∂(Measure.volumeIoiPow d) := by
          rw [← lintegral_const_mul (ENNReal.ofReal A) hmeas]
          apply lintegral_congr
          intro r
          rw [← ENNReal.ofReal_mul hA]
    _ = ENNReal.ofReal A *
        ENNReal.ofReal ((c ^ (d + 1))⁻¹ * hyperbolicRadialVolume q d R) := by
          rw [radial_model_lintegral_scaled (d := d) q hq hR hc]
    _ = ENNReal.ofReal (A * (c ^ (d + 1))⁻¹ * hyperbolicRadialVolume q d R) := by
          rw [← ENNReal.ofReal_mul hA]
          rw [← mul_assoc]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
theorem gBall_model_int
    (g : SmoothRiemannianMetric I M)
    (x : M) (q R : ℝ) (hq : 0 ≤ q) (hR : 0 < R) :
    ∫⁻ v in closedGBall g x R,
        ENNReal.ofReal (normalChartDensity g x 0 *
          hyperbolicDensity (q * Real.sqrt (g.inner x (show TangentSpace I x from v)
            (show TangentSpace I x from v))) (Module.finrank ℝ E - 1) 1)
      ∂(modelHaar (E := E))
    = (∫⁻ θ : sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
      * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
  classical
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let d : ℕ := Module.finrank ℝ E - 1
  let F : E → ℝ≥0∞ := fun v => ENNReal.ofReal (normalChartDensity g x 0 *
    hyperbolicDensity (q * Real.sqrt (g.inner x (show TangentSpace I x from v)
      (show TangentSpace I x from v))) d 1)
  have hFmeas : AEMeasurable F (modelHaar (E := E)) := by
    have hcont1 : Continuous (fun v : E => Real.sqrt (g.inner x
        (show TangentSpace I x from v) (show TangentSpace I x from v))) := by
      exact (continuous_sqrt_gInner_self (I := I) g x).comp continuous_id
    have hcont : Continuous (fun v : E => hyperbolicDensity (q *
        Real.sqrt (g.inner x (show TangentSpace I x from v) (show TangentSpace I x from v))) d 1) :=
      (hyperbolicDensity_scale_continuous q d).comp hcont1
    have hcd : Continuous (fun v : E => normalChartDensity g x 0 *
        hyperbolicDensity (q * Real.sqrt (g.inner x (show TangentSpace I x from v)
          (show TangentSpace I x from v))) d 1) :=
      continuous_const.mul hcont
    exact ENNReal.continuous_ofReal.comp hcd |>.aemeasurable
  have hball_meas : MeasurableSet (closedGBall g x R) :=
    (isClosed_closedGBall (I := I) g x R).measurableSet
  calc
    ∫⁻ v in closedGBall g x R, F v ∂(modelHaar (E := E))
        = ∫⁻ v, (closedGBall g x R).indicator F v ∂(modelHaar (E := E)) := by
          rw [lintegral_indicator hball_meas]
    _ = ∫⁻ u : sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : ℝ), (closedGBall g x R).indicator F (r.1 • u.1)
            ∂(Measure.volumeIoiPow d) ∂(modelHaar (E := E)).toSphere := by
          simpa [d] using
            (lintegral_polar (modelHaar (E := E)) ((closedGBall g x R).indicator F)
              (hFmeas.indicator hball_meas))
    _ = (∫⁻ u : sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity g x 0 *
            (Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
      * ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
          have hd1 : d + 1 = Module.finrank ℝ E := by
            dsimp [d]
            exact Nat.sub_add_cancel (Nat.succ_le_of_lt
              (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))))
          have hcd0 : 0 ≤ normalChartDensity g x 0 := by
            rw [normalChartDensity, paramDensity_apply]
            exact Real.sqrt_nonneg _
          have hinner (u : sphere (0 : E) 1) :
              (∫⁻ r : Ioi (0 : ℝ), (closedGBall g x R).indicator F (r.1 • u.1)
                ∂(Measure.volumeIoiPow d))
              = ENNReal.ofReal (normalChartDensity g x 0 *
                  (Real.sqrt (g.inner x u.1 u.1) ^ (d + 1))⁻¹ * hyperbolicRadialVolume q d R) := by
            have hne : u.1 ≠ 0 := by
              intro h
              have hu := u.2
              rw [h] at hu
              simp at hu
            have hc : 0 < Real.sqrt (g.inner x u.1 u.1) :=
              Real.sqrt_pos.mpr (g.pos x u.1 hne)
            have hEq : (fun r : Ioi (0 : ℝ) => (closedGBall g x R).indicator F (r.1 • u.1))
                = fun r : Ioi (0 : ℝ) => (Iic (⟨R / Real.sqrt (g.inner x u.1 u.1),
                    div_pos hR hc⟩ : Ioi (0 : ℝ))).indicator
                      (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (normalChartDensity g x 0 *
                        hyperbolicDensity (q * (r.1 * Real.sqrt (g.inner x u.1 u.1))) d 1)) r := by
              funext r
              by_cases hr : r.1 * Real.sqrt (g.inner x u.1 u.1) ≤ R
              · have hmem : r ∈ Iic (⟨R / Real.sqrt (g.inner x u.1 u.1),
                div_pos hR hc⟩ : Ioi (0 : ℝ)) :=
                  (le_div_iff₀ hc).mpr hr
                have hb : r.1 • u.1 ∈ closedGBall g x R := by
                  change Real.sqrt (g.inner x (show TangentSpace I x from (r.1 • u.1))
                      (show TangentSpace I x from (r.1 • u.1))) ≤ R
                  have hbval : g.inner x u.1 u.1 =
                      (Real.sqrt (g.inner x u.1 u.1)) ^ 2 :=
                    (Real.sq_sqrt (gInner_self_nonneg (I := I) g x u.1)).symm
                  have hsq : g.inner x (show TangentSpace I x from (r.1 • u.1))
                        (show TangentSpace I x from (r.1 • u.1))
                      = (r.1 * Real.sqrt (g.inner x u.1 u.1)) ^ 2 := by
                    change g.inner x (r.1 • (u.1 : TangentSpace I x)) (r.1 •
                      (u.1 : TangentSpace I x))
                        = (r.1 * Real.sqrt (g.inner x u.1 u.1)) ^ 2
                    calc
                      g.inner x (r.1 • (u.1 : TangentSpace I x)) (r.1 • (u.1 : TangentSpace I x))
                          = r.1 ^ 2 * g.inner x u.1 u.1 := gInner_smul_self (I := I) g x r.1 u.1
                      _ = (r.1 * Real.sqrt (g.inner x u.1 u.1)) ^ 2 := by
                            rw [mul_pow]
                            conv_lhs => rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g x u.1)]
                  rw [hsq]
                  rw [Real.sqrt_sq_eq_abs]
                  rw [abs_of_nonneg (mul_nonneg r.2.le hc.le)]
                  exact hr
                simp only [F, Set.indicator_of_mem hmem, Set.indicator_of_mem hb]
                congr 5
                exact sqrt_gInner_smul_self (I := I) g x r.2.le u.1
              · have hmem : r ∉ Iic (⟨R / Real.sqrt (g.inner x u.1 u.1),
                div_pos hR hc⟩ : Ioi (0 : ℝ)) :=
                  fun h => hr ((le_div_iff₀ hc).mp h)
                have hb : r.1 • u.1 ∉ closedGBall g x R := by
                  intro hmem_ball
                  have hbval : g.inner x u.1 u.1 =
                      (Real.sqrt (g.inner x u.1 u.1)) ^ 2 :=
                    (Real.sq_sqrt (gInner_self_nonneg (I := I) g x u.1)).symm
                  have hsq : Real.sqrt (g.inner x (show TangentSpace I x from (r.1 • u.1))
                        (show TangentSpace I x from (r.1 • u.1)))
                      = r.1 * Real.sqrt (g.inner x u.1 u.1) := by
                    change Real.sqrt (g.inner x (r.1 • (u.1 : TangentSpace I x))
                        (r.1 • (u.1 : TangentSpace I x)))
                        = r.1 * Real.sqrt (g.inner x u.1 u.1)
                    exact sqrt_gInner_smul_self (I := I) g x r.2.le u.1
                  have hrle : r.1 * Real.sqrt (g.inner x u.1 u.1) ≤ R := by
                    rw [← hsq]
                    exact hmem_ball
                  exact hr hrle
                simp only [F, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hb]
            rw [hEq]
            rw [lintegral_indicator measurableSet_Iic]
            exact (radial_model_lintegral_scaled_mul (d := d)
              (A := normalChartDensity g x 0) q hq hR hc hcd0)
          have hfmeas : Measurable (fun u : sphere (0 : E) 1 => ENNReal.ofReal
                (normalChartDensity g x 0 *
                  (Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E))⁻¹)) := by
              have hc1 : Continuous (fun u : sphere (0 : E) 1 => Real.sqrt (g.inner x u.1 u.1)) :=
                (continuous_sqrt_gInner_self (I := I) g x).comp continuous_subtype_val
              have hc2 : Continuous (fun u : sphere (0 : E) 1 =>
                  (Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E))⁻¹) := by
                have hne : ∀ u : sphere (0 : E) 1,
                  Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E) ≠ 0 := by
                  intro u
                  have hu : u.1 ≠ 0 := by
                    intro h
                    have hu2 := u.2
                    rw [h] at hu2
                    simp at hu2
                  exact pow_ne_zero _ (Real.sqrt_pos.mpr (g.pos x u.1 hu)).ne'
                exact (hc1.pow (Module.finrank ℝ E)).inv₀ hne
              exact ENNReal.measurable_ofReal.comp
                (continuous_const.mul hc2 |>.measurable)
          calc
            ∫⁻ u : sphere (0 : E) 1,
                ∫⁻ r : Ioi (0 : ℝ), (closedGBall g x R).indicator F (r.1 • u.1)
                  ∂(Measure.volumeIoiPow d) ∂(modelHaar (E := E)).toSphere
                = ∫⁻ u : sphere (0 : E) 1,
                    ENNReal.ofReal (normalChartDensity g x 0 *
                      (Real.sqrt (g.inner x u.1 u.1) ^ (d + 1))⁻¹ * hyperbolicRadialVolume q d R)
                    ∂(modelHaar (E := E)).toSphere := by
                  apply lintegral_congr
                  intro u
                  exact hinner u
            _ = ∫⁻ u : sphere (0 : E) 1,
                  ENNReal.ofReal (normalChartDensity g x 0 *
                    (Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E))⁻¹ * hyperbolicRadialVolume q d R)
                  ∂(modelHaar (E := E)).toSphere := by
                  apply lintegral_congr
                  intro u
                  rw [hd1]
            _ = (∫⁻ u : sphere (0 : E) 1,
                    ENNReal.ofReal (normalChartDensity g x 0 *
                      (Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E))⁻¹)
                    ∂(modelHaar (E := E)).toSphere)
                  * ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
                  have hsplit : (fun u : sphere (0 : E) 1 => ENNReal.ofReal
                    (normalChartDensity g x 0 *
                        (Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E))⁻¹ * hyperbolicRadialVolume q d R))
                      = fun u => ENNReal.ofReal (normalChartDensity g x 0 *
                        (Real.sqrt (g.inner x u.1 u.1) ^ (Module.finrank ℝ E))⁻¹) *
                          ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
                    funext u
                    rw [← ENNReal.ofReal_mul (mul_nonneg hcd0
                      (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))) ]
                  rw [hsplit]
                  simpa using (lintegral_mul_const (r := ENNReal.ofReal (hyperbolicRadialVolume q d R)) hfmeas)
    _ = (∫⁻ θ : sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
      * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
          rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma segmentBall_vol_le_explicit
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ (∫⁻ θ : sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
        * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
  classical
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let K : Set E := {v : E | (show TangentSpace I x from v) ∈ SegmentDom (I := I) g hEnorm x} ∩
    closedGBall g x R
  let F : E → ℝ := fun v => normalChartDensity (I := I) g x 0 *
    hyperbolicDensity (q * Real.sqrt (g.inner x (show TangentSpace I x from v)
      (show TangentSpace I x from v))) (Module.finrank ℝ E - 1) 1
  have hV := segmentBall_vol_le_int (I := I) g hEnorm x R
  have hpoint : ∀ v : E, v ∈ K → v ≠ 0 →
      expJacobianDensity (I := I) g hEnorm x v ≤ F v := by
    intro v hv hvne
    exact expJacobianDensity_le (I := I) g hEnorm x hv.1 hvne q hq hd hRic
  have hcontG : Continuous (fun v : E => ENNReal.ofReal (F v)) := by
    have hcont1 : Continuous (fun v : E => Real.sqrt (g.inner x
        (show TangentSpace I x from v) (show TangentSpace I x from v))) := by
      exact (continuous_sqrt_gInner_self (I := I) g x).comp continuous_id
    have hcont : Continuous (fun v : E => hyperbolicDensity (q *
        Real.sqrt (g.inner x (show TangentSpace I x from v)
          (show TangentSpace I x from v))) (Module.finrank ℝ E - 1) 1) :=
      (hyperbolicDensity_scale_continuous q (Module.finrank ℝ E - 1)).comp hcont1
    exact ENNReal.continuous_ofReal.comp (continuous_const.mul hcont)
  have hcontF : Continuous (fun v : E => ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)) :=
    ENNReal.continuous_ofReal.comp (expJacobianDensity_continuous (I := I) g hEnorm x)
  have hKmeas : MeasurableSet K := by
    have h1 : MeasurableSet {v : E | (show TangentSpace I x from v) ∈ SegmentDom
      (I := I) g hEnorm x} := by
      exact (isClosed_segmentDom (I := I) g hEnorm x).measurableSet.preimage
        (by fun_prop : Measurable (fun v : E => (show TangentSpace I x from v)))
    exact h1.inter (isClosed_closedGBall (I := I) g x R).measurableSet
  have hle_meas : MeasurableSet {v : E | ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) ≤
        ENNReal.ofReal (F v)} :=
    (isClosed_le hcontF hcontG).measurableSet
  have hmono : (∫⁻ v in K,
    ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E)))
      ≤ ∫⁻ v in K, ENNReal.ofReal (F v) ∂(modelHaar (E := E)) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff hle_meas]
    rw [ae_iff]
    have hnull : {a : E | ¬ (a ∈ K → ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x a) ≤
          ENNReal.ofReal (F a))} ⊆ ({0} : Set E) := by
      intro v hv
      have hv' : v ∈ K ∧ ¬ (ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) ≤
          ENNReal.ofReal (F v)) := Classical.not_imp.mp hv
      by_contra hv0
      have hb : expJacobianDensity (I := I) g hEnorm x v ≤ F v := hpoint v hv'.1 hv0
      exact hv'.2 (ENNReal.ofReal_le_ofReal hb)
    exact measure_mono_null hnull (measure_singleton (μ := (modelHaar (E := E))) (0 : E))
  have hstep3 : (∫⁻ v in K, ENNReal.ofReal (F v) ∂(modelHaar (E := E)))
      ≤ ∫⁻ v in closedGBall g x R, ENNReal.ofReal (F v) ∂(modelHaar (E := E)) :=
    lintegral_mono_set (Set.inter_subset_right : K ⊆ closedGBall g x R)
  have hstep4 := gBall_model_int (I := I) g x q R hq hR
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        ≤ ∫⁻ v in K, ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
            ∂(modelHaar (E := E)) := by
          simpa [K] using hV
    _ ≤ ∫⁻ v in K, ENNReal.ofReal (F v) ∂(modelHaar (E := E)) := hmono
    _ ≤ ∫⁻ v in closedGBall g x R, ENNReal.ofReal (F v) ∂(modelHaar (E := E)) := hstep3
    _ = (∫⁻ θ : sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
        * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
          simpa [F] using hstep4

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_vol_le [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ (∫⁻ θ : sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
        * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
  exact segmentBall_vol_le_explicit (I := I) g hEnorm x hq hR hd hRic

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_vol_fin [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} < ⊤ := by
  classical
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let K : Set E := {v : E | (show TangentSpace I x from v) ∈ SegmentDom (I := I) g hEnorm x} ∩
    closedGBall g x R
  have hV := segmentBall_vol_le_int (I := I) g hEnorm x R
  have hKcomp : IsCompact K := by
    have hclosed : IsClosed {v : E | (show TangentSpace I x from v) ∈ SegmentDom
      (I := I) g hEnorm x} := by
      with_unfolding_all exact
        (isClosed_segmentDom (I := I) g hEnorm x).preimage continuous_id
    exact (isCompact_closedGBall (I := I) g x R).of_isClosed_subset
      (hclosed.inter (isClosed_closedGBall (I := I) g x R))
      (Set.inter_subset_right : K ⊆ closedGBall g x R)
  have hbdd : ∃ M : ℝ, ∀ v ∈ K, expJacobianDensity (I := I) g hEnorm x v ≤ M := by
    have hcont : ContinuousOn (fun v : E => expJacobianDensity (I := I) g hEnorm x v) K :=
      (expJacobianDensity_continuous (I := I) g hEnorm x).continuousOn
    have himg : IsCompact ((fun v : E => expJacobianDensity (I := I) g hEnorm x v) '' K) :=
      hKcomp.image_of_continuousOn hcont
    obtain ⟨M, hM⟩ := himg.isBounded.exists_norm_le
    refine ⟨M, fun v hv => ?_⟩
    have hx : expJacobianDensity (I := I) g hEnorm x v ∈
        (fun v : E => expJacobianDensity (I := I) g hEnorm x v) '' K := ⟨v, hv, rfl⟩
    exact le_trans (le_abs_self _) (hM (expJacobianDensity (I := I) g hEnorm x v) hx)
  obtain ⟨M, hM⟩ := hbdd
  have hKmeas : MeasurableSet K := hKcomp.measurableSet
  have hpoint : (fun v : E => (K.indicator (fun v : E =>
        ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v))) v)
      ≤ (fun v : E => K.indicator (fun _ : E => ENNReal.ofReal M) v) := by
    intro v
    by_cases hv : v ∈ K
    · simp [hv, ENNReal.ofReal_le_ofReal (hM v hv)]
    · simp [hv]
  have hmono' : (∫⁻ v in K, ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)))
      ≤ ∫⁻ v in K, ENNReal.ofReal M ∂(modelHaar (E := E)) := by
    rw [← lintegral_indicator hKmeas]
    rw [← lintegral_indicator hKmeas]
    exact lintegral_mono hpoint
  have hconst : (∫⁻ v in K, ENNReal.ofReal M ∂(modelHaar (E := E)))
      = ENNReal.ofReal M * (modelHaar (E := E)) K :=
    setLIntegral_const K (ENNReal.ofReal M)
  have hfin : ENNReal.ofReal M * (modelHaar (E := E)) K < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKcomp.measure_lt_top
  have hKfin : (∫⁻ v in K, ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
      ∂(modelHaar (E := E))) < ⊤ :=
    lt_of_le_of_lt hmono' (by rw [hconst]; exact hfin)
  exact lt_of_le_of_lt (by simpa [K] using hV) hKfin

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private lemma expMapIntrinsic_eq_scaled
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : TangentSpace I x) (hvne : v ≠ 0) :
    expMapIntrinsic (I := I) g hEnorm x v =
      intrinsicGeodesic (I := I) g hEnorm x
        ((Real.sqrt (g.inner x v v))⁻¹ • v) (Real.sqrt (g.inner x v v)) := by
  let ℓ : ℝ := Real.sqrt (g.inner x v v)
  have hℓ0 : ℓ ≠ 0 := by
    dsimp [ℓ]
    exact ne_of_gt (Real.sqrt_pos.2 (g.pos x v hvne))
  calc
    expMapIntrinsic (I := I) g hEnorm x v =
        intrinsicGeodesic (I := I) g hEnorm x v 1 := by
          rw [expMapIntrinsic_def]
    _ = intrinsicGeodesic (I := I) g hEnorm x (ℓ • (ℓ⁻¹ • v)) 1 := by
          rw [smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
    _ = intrinsicGeodesic (I := I) g hEnorm x (ℓ⁻¹ • v) ℓ := by
          rw [intrinsicGeodesic_smul (I := I) g hEnorm x (ℓ⁻¹ • v) ℓ]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private lemma gUnit_speedSq_one
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (hvne : v ≠ 0) :
    g.inner x (((Real.sqrt (g.inner x v v))⁻¹ • v) : TangentSpace I x)
      (((Real.sqrt (g.inner x v v))⁻¹ • v) : TangentSpace I x) = 1 := by
  have hpos : 0 < g.inner x v v := g.pos x v hvne
  have hℓ : Real.sqrt (g.inner x v v) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  rw [gInner_smul_self (I := I) g x (Real.sqrt (g.inner x v v))⁻¹ v]
  calc
    ((Real.sqrt (g.inner x v v))⁻¹) ^ 2 * g.inner x v v =
        ((Real.sqrt (g.inner x v v))⁻¹) ^ 2 * (Real.sqrt (g.inner x v v)) ^ 2 := by
          rw [Real.sq_sqrt (le_of_lt hpos)]
    _ = (((Real.sqrt (g.inner x v v))⁻¹) * Real.sqrt (g.inner x v v)) ^ 2 := by
          rw [← mul_pow]
    _ = 1 := by
          rw [inv_mul_cancel₀ hℓ, one_pow]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private lemma segmentDom_ext_dist
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : TangentSpace I x) (hvne : v ≠ 0) (ε : ℝ) (hε : 0 < ε)
    (hseg : (((Real.sqrt (g.inner x v v) + ε) •
        ((Real.sqrt (g.inner x v v))⁻¹ • v) : TangentSpace I x)) ∈
        SegmentDom (I := I) g hEnorm x) :
    riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x
        ((Real.sqrt (g.inner x v v))⁻¹ • v) (Real.sqrt (g.inner x v v) + ε))
      = ENNReal.ofReal (Real.sqrt (g.inner x v v) + ε) := by
  let ℓ : ℝ := Real.sqrt (g.inner x v v)
  let u : TangentSpace I x := ℓ⁻¹ • v
  have hℓ0 : 0 ≤ ℓ := by
    dsimp [ℓ]
    exact Real.sqrt_nonneg _
  have hseg' : ((ℓ + ε) • u : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x := by
    simpa [ℓ, u, smul_smul, mul_assoc] using hseg
  have hmem : (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x ((ℓ + ε) • u))).toReal
      = Real.sqrt (g.inner x ((ℓ + ε) • u) ((ℓ + ε) • u)) := by
    exact ((mem_segmentDom (I := I) (g := g) (hEnorm := hEnorm) (x := x)
      (v := ((ℓ + ε) • u : TangentSpace I x))).mp hseg').symm
  have hsqrt : Real.sqrt (g.inner x ((ℓ + ε) • u) ((ℓ + ε) • u)) = ℓ + ε := by
    rw [gInner_smul_self (I := I) g x (ℓ + ε) u]
    have hu : g.inner x u u = 1 := by
      simpa [u, ℓ] using gUnit_speedSq_one (I := I) g x v hvne
    rw [hu, mul_one]
    have hℓε : 0 ≤ ℓ + ε := le_trans hℓ0 (le_of_lt (lt_add_of_pos_right ℓ hε))
    exact Real.sqrt_sq hℓε
  have heq : expMapIntrinsic (I := I) g hEnorm x ((ℓ + ε) • u) =
      intrinsicGeodesic (I := I) g hEnorm x u (ℓ + ε) := by
    rw [expMapIntrinsic_def, intrinsicGeodesic_smul (I := I) g hEnorm x u (ℓ + ε)]
  rw [← heq]
  have hfin : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x ((ℓ + ε) • u)) ≠ ⊤ := by
    have hto : (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x ((ℓ + ε) • u))).toReal
        = ℓ + ε := by
      rw [hmem, hsqrt]
    by_contra htop
    rw [htop, ENNReal.toReal_top] at hto
    linarith [hε, hℓ0]
  rw [← ENNReal.ofReal_toReal hfin]
  rw [hmem, hsqrt]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private lemma segmentDom_same_length
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v w : TangentSpace I x}
    (hvseg : v ∈ SegmentDom (I := I) g hEnorm x)
    (hwseg : w ∈ SegmentDom (I := I) g hEnorm x)
    (hvw : expMapIntrinsic (I := I) g hEnorm x v = expMapIntrinsic (I := I) g hEnorm x w) :
    Real.sqrt (g.inner x v v) = Real.sqrt (g.inner x w w) := by
  have h1 : Real.sqrt (g.inner x v v)
      = (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal :=
    (mem_segmentDom (I := I) (g := g) (hEnorm := hEnorm) (x := x) (v := v)).mp hvseg
  have h2 : Real.sqrt (g.inner x w w)
      = (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x w)).toReal :=
    (mem_segmentDom (I := I) (g := g) (hEnorm := hEnorm) (x := x) (v := w)).mp hwseg
  rw [h1, h2]
  congr 1
  rw [hvw]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private lemma mfderiv_shift_apply
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I (∞ : WithTop ℕ∞) γ) (T a : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (s + T)) a (1 : ℝ) : E)
      = (mfderiv 𝓘(ℝ, ℝ) I γ (a + T) (1 : ℝ) : E) := by
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + T)
      a (ContinuousLinearMap.id ℝ ℝ) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    exact (hasFDerivAt_id a).add_const T
  have hγ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (a + T) (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) := by
    exact (hγ.contMDiffAt.mdifferentiableAt (by norm_num)).hasMFDerivAt
  have hη_mfderiv : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun s : ℝ => s + T)) a
      = (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)).comp (ContinuousLinearMap.id ℝ ℝ) :=
    (hγ_at.comp a hshift).mfderiv
  change (mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun s : ℝ => s + T)) a (1 : ℝ) : E)
      = (mfderiv 𝓘(ℝ, ℝ) I γ (a + T) (1 : ℝ) : E)
  rw [hη_mfderiv]
  change (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) ((ContinuousLinearMap.id ℝ ℝ) (1 : ℝ))
      = (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) (1 : ℝ)
  simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private lemma expMapIntrinsic_injective_early
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v w : TangentSpace I x}
    (hvseg : v ∈ SegmentDom (I := I) g hEnorm x)
    (hwseg : w ∈ SegmentDom (I := I) g hEnorm x)
    (hvne : v ≠ 0) (hwne : w ≠ 0)
    (hvw : expMapIntrinsic (I := I) g hEnorm x v = expMapIntrinsic (I := I) g hEnorm x w)
    {ε : ℝ} (hε : 0 < ε)
    (hext : (((Real.sqrt (g.inner x v v) + ε) •
        ((Real.sqrt (g.inner x v v))⁻¹ • v) : TangentSpace I x)) ∈
        SegmentDom (I := I) g hEnorm x) :
    v = w := by
  let ℓ : ℝ := Real.sqrt (g.inner x v v)
  have hℓpos : 0 < ℓ := by
    dsimp [ℓ]
    exact Real.sqrt_pos.2 (g.pos x v hvne)
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
  have hℓnonneg : 0 ≤ ℓ := le_of_lt hℓpos
  let u : TangentSpace I x := ℓ⁻¹ • v
  have hu : g.inner x u u = 1 := by
    simpa [u, ℓ] using gUnit_speedSq_one (I := I) g x v hvne
  have hℓw : Real.sqrt (g.inner x w w) = ℓ := by
    dsimp [ℓ]
    exact (segmentDom_same_length (I := I) g hEnorm x (v := v) (w := w) hvseg hwseg hvw).symm
  let uw : TangentSpace I x := ℓ⁻¹ • w
  have huw : g.inner x uw uw = 1 := by
    simpa [uw, ← hℓw] using gUnit_speedSq_one (I := I) g x w hwne
  let γv : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u
  let γw : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x uw
  have hγv_geo : IsGeodesic (I := I) g γv := by
    simpa [γv] using intrinsicGeodesic_isGeodesic (I := I) g hEnorm x u
  have hγw_geo : IsGeodesic (I := I) g γw := by
    simpa [γw] using intrinsicGeodesic_isGeodesic (I := I) g hEnorm x uw
  have hγv_cont : Continuous γv := by
    simpa [γv] using intrinsicGeodesic_continuous (I := I) g hEnorm x u
  have hγw_cont : Continuous γw := by
    simpa [γw] using intrinsicGeodesic_continuous (I := I) g hEnorm x uw
  have hγv_smooth : ContMDiff 𝓘(ℝ, ℝ) I (∞ : WithTop ℕ∞) γv := by
    simpa [γv] using intrinsicGeodesic_contMDiff (I := I) g hEnorm x u
  have hγw_smooth : ContMDiff 𝓘(ℝ, ℝ) I (∞ : WithTop ℕ∞) γw := by
    simpa [γw] using intrinsicGeodesic_contMDiff (I := I) g hEnorm x uw
  have hγv_unit : ∀ t ∈ Set.Icc 0 ℓ,
      g.inner (γv t) (mfderiv 𝓘(ℝ, ℝ) I γv t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γv t (1 : ℝ)) = 1 := by
    intro t ht
    dsimp only [γv]
    calc
      g.inner (intrinsicGeodesic (I := I) g hEnorm x u t)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x u) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x u) t (1 : ℝ)) =
        g.inner x u u := by
          with_unfolding_all exact
            intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x u t
      _ = 1 := hu
  have hγw_unit : ∀ t ∈ Set.Icc 0 ℓ,
      g.inner (γw t) (mfderiv 𝓘(ℝ, ℝ) I γw t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γw t (1 : ℝ)) = 1 := by
    intro t ht
    dsimp only [γw]
    calc
      g.inner (intrinsicGeodesic (I := I) g hEnorm x uw t)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x uw) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x uw) t (1 : ℝ)) =
        g.inner x uw uw := by
          with_unfolding_all exact
            intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x uw t
      _ = 1 := huw
  have hγvℓ : γv ℓ = expMapIntrinsic (I := I) g hEnorm x v := by
    symm
    simpa [γv, u, ℓ] using expMapIntrinsic_eq_scaled (I := I) g hEnorm x v hvne
  have hγwℓ : γw ℓ = expMapIntrinsic (I := I) g hEnorm x w := by
    symm
    simpa [γw, uw, hℓw, ℓ] using expMapIntrinsic_eq_scaled (I := I) g hEnorm x w hwne
  have hγvγw : γv ℓ = γw ℓ := by
    rw [hγvℓ, hγwℓ, hvw]
  have hγv0 : γv 0 = x := by simp [γv]
  have hγw0 : γw 0 = x := by simp [γw]
  let σ : ℝ → M := fun s => γv (s + ℓ)
  have hσgeo : IsGeodesicOn (I := I) g σ (Set.Icc 0 ε) := by
    have hfull : IsGeodesicOn (I := I) g σ Set.univ := by
      change IsGeodesicOn (I := I) g (fun s : ℝ => γv (s + ℓ)) Set.univ
      exact (isGeodesic_comp_add hγv_geo ℓ).isGeodesicOn Set.univ
    exact hfull.mono (Set.subset_univ _)
  have hσsmooth : ContMDiff 𝓘(ℝ, ℝ) I (∞ : WithTop ℕ∞) σ := by
    have hadd : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) (fun s : ℝ => s + ℓ) := by
      exact (contMDiff_id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        (fun s : ℝ => s)).add
        (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun _ : ℝ => ℓ))
    exact hγv_smooth.comp hadd
  have hσunit : ∀ t ∈ Set.Icc 0 ε,
      g.inner (σ t) (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ)) = 1 := by
    intro t ht
    have hspe := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x u (t + ℓ)
    have hσ' : σ t = γv (t + ℓ) := rfl
    have hmfd : (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ) : E) = (mfderiv 𝓘(ℝ,
      ℝ) I γv (t + ℓ) (1 : ℝ) : E) := by
      have h := mfderiv_shift_apply (I := I) (γ := γv) hγv_smooth ℓ t
      simpa [σ] using h
    rw [hσ', hmfd]
    dsimp only [γv]
    calc
      g.inner (intrinsicGeodesic (I := I) g hEnorm x u (t + ℓ))
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x u)
            (t + ℓ) (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x u)
            (t + ℓ) (1 : ℝ)) = g.inner x u u := by
          with_unfolding_all exact hspe
      _ = 1 := hu
  have hmin : riemannianEDist I (γw 0) (σ ε) = ENNReal.ofReal (ℓ + ε) := by
    have hd : riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x u (ε + ℓ))
        = ENNReal.ofReal (ℓ + ε) := by
      simpa [ℓ, u, add_comm] using segmentDom_ext_dist (I := I) g hEnorm x v hvne ε hε hext
    simpa [σ, hγw0, add_comm] using hd
  have hvel : mfderiv 𝓘(ℝ, ℝ) I γw ℓ (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) I γv ℓ (1 : ℝ) := by
    have hbm := broken_minimizer_velocity_match (I := I) g hEnorm
      (ℓ₁ := ℓ) (ℓ₂ := ε) (γ := γw) (σ := σ)
      hℓpos hε (hγw_geo.isGeodesicOn (Set.Icc 0 ℓ)) hσgeo hγw_smooth hσsmooth
      hγw_unit hσunit (hjunc := by simpa [σ] using hγvγw.symm) hmin
    have hσ0 : mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) I γv ℓ (1 : ℝ) := by
      have h := mfderiv_shift_apply (I := I) (γ := γv) hγv_smooth ℓ 0
      rw [zero_add] at h
      with_unfolding_all exact h
    rw [← hσ0]
    exact hbm
  let η₁ : ℝ → M := fun s => γw (s + ℓ)
  let η₂ : ℝ → M := fun s => γv (s + ℓ)
  have hη₁_geo : IsGeodesic (I := I) g η₁ := by
    simpa [η₁] using isGeodesic_comp_add hγw_geo ℓ
  have hη₂_geo : IsGeodesic (I := I) g η₂ := by
    simpa [η₂] using isGeodesic_comp_add hγv_geo ℓ
  have hη₁_cont : Continuous η₁ := hγw_cont.comp (by fun_prop)
  have hη₂_cont : Continuous η₂ := hγv_cont.comp (by fun_prop)
  have hη0 : η₁ 0 = η₂ 0 := by
    simpa [η₁, η₂] using hγvγw.symm
  have hηvelocity : (mfderiv 𝓘(ℝ, ℝ) I η₁ 0 (1 : ℝ) : E) = (mfderiv 𝓘(ℝ, ℝ) I η₂ 0 (1 : ℝ) : E) := by
    have h1 : (mfderiv 𝓘(ℝ, ℝ) I η₁ 0 (1 : ℝ) : E)
        = (mfderiv 𝓘(ℝ, ℝ) I γw ℓ (1 : ℝ) : E) := by
      have h := mfderiv_shift_apply (I := I) (γ := γw) hγw_smooth ℓ 0
      rw [zero_add] at h
      with_unfolding_all exact h
    have h2 : (mfderiv 𝓘(ℝ, ℝ) I η₂ 0 (1 : ℝ) : E)
        = (mfderiv 𝓘(ℝ, ℝ) I γv ℓ (1 : ℝ) : E) := by
      have h := mfderiv_shift_apply (I := I) (γ := γv) hγv_smooth ℓ 0
      rw [zero_add] at h
      with_unfolding_all exact h
    rw [h1, h2]
    exact hvel
  have hηeq : η₁ = η₂ :=
    isGeodesic_eq_of_initial (I := I) g hη₁_geo hη₂_geo hη₁_cont hη₂_cont hη0 hηvelocity
  have hu0 : (u : E) = (uw : E) := by
    have h1 : (mfderiv 𝓘(ℝ, ℝ) I η₁ (-ℓ) (1 : ℝ) : E)
        = (mfderiv 𝓘(ℝ, ℝ) I γw 0 (1 : ℝ) : E) := by
      have h := mfderiv_shift_apply (I := I) (γ := γw) hγw_smooth ℓ (-ℓ)
      have hneg : (-ℓ + ℓ : ℝ) = 0 := by ring
      rw [hneg] at h
      with_unfolding_all exact h
    have h2 : (mfderiv 𝓘(ℝ, ℝ) I η₂ (-ℓ) (1 : ℝ) : E)
        = (mfderiv 𝓘(ℝ, ℝ) I γv 0 (1 : ℝ) : E) := by
      have h := mfderiv_shift_apply (I := I) (γ := γv) hγv_smooth ℓ (-ℓ)
      have hneg : (-ℓ + ℓ : ℝ) = 0 := by ring
      rw [hneg] at h
      with_unfolding_all exact h
    have hmf : (mfderiv 𝓘(ℝ, ℝ) I η₁ (-ℓ) (1 : ℝ) : E)
        = (mfderiv 𝓘(ℝ, ℝ) I η₂ (-ℓ) (1 : ℝ) : E) := by
      rw [hηeq]
    rw [h1, h2] at hmf
    have hγw0v : (mfderiv 𝓘(ℝ, ℝ) I γw 0 (1 : ℝ) : E) = (uw : E) := by
      simpa [γw] using intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x uw
    have hγv0v : (mfderiv 𝓘(ℝ, ℝ) I γv 0 (1 : ℝ) : E) = (u : E) := by
      simpa [γv] using intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x u
    rw [hγw0v, hγv0v] at hmf
    exact hmf.symm
  have hv : (v : E) = (w : E) := by
    calc
      (v : E) = (ℓ • u : E) := by
        dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ hℓne, one_smul]
      _ = (ℓ • uw : E) := by rw [hu0]
      _ = (w : E) := by
        dsimp [uw]
        rw [smul_smul, mul_inv_cancel₀ hℓne, one_smul]
  exact hv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private lemma intrinsicGeodesic_smul_apply
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) (c t : ℝ) :
    intrinsicGeodesic (I := I) g hEnorm p (c • v) t
      = intrinsicGeodesic (I := I) g hEnorm p v (c * t) := by
  by_cases hc : c = 0
  · subst c
    have hgeo1 : IsGeodesic (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)) :=
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)
    have hgeo2 : IsGeodesic (I := I) g (fun _ : ℝ => p) := isGeodesic_const (I := I) g p
    have hcont1 : Continuous (intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)) :=
      intrinsicGeodesic_continuous (I := I) g hEnorm p (0 : TangentSpace I p)
    have hcont2 : Continuous (fun _ : ℝ => p) := continuous_const
    have h0 : intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p) 0 = p :=
      intrinsicGeodesic_zero (I := I) g hEnorm p (0 : TangentSpace I p)
    have hvel : (mfderiv 𝓘(ℝ, ℝ) I
        (intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)) 0 (1 : ℝ) : E)
        = (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => p) 0 (1 : ℝ) : E) := by
      have hv := intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p (0 : TangentSpace I p)
      rw [hv, mfderiv_const]
      rfl
    have heq := isGeodesic_eq_of_initial (I := I) g hgeo1 hgeo2 hcont1 hcont2 h0 hvel
    simpa using congrFun heq t
  · calc
      intrinsicGeodesic (I := I) g hEnorm p (c • v) t =
          intrinsicGeodesic (I := I) g hEnorm p (t • (c • v)) 1 := by
            rw [← intrinsicGeodesic_smul (I := I) g hEnorm p (c • v) t]
      _ = intrinsicGeodesic (I := I) g hEnorm p ((t * c) • v) 1 := by
            rw [smul_smul, mul_comm]
      _ = intrinsicGeodesic (I := I) g hEnorm p v (t * c) := by
            rw [intrinsicGeodesic_smul (I := I) g hEnorm p v (t * c)]
      _ = intrinsicGeodesic (I := I) g hEnorm p v (c * t) := by
            rw [mul_comm]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [TopologicalSpace M] in
private lemma mfderiv_div_const
    (c : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun ρ : ℝ => ρ / c) 0
      = (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) := by
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun ρ : ℝ => ρ / c)
      0 (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    have hf : HasFDerivAt (fun ρ : ℝ => ρ / c) (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) 0 := by
      have hf' : HasFDerivAt (fun ρ : ℝ => c⁻¹ * ρ)
          (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) 0 :=
        (hasFDerivAt_id (0 : ℝ)).const_mul c⁻¹
      convert hf' using 1
      funext ρ
      ring
    with_unfolding_all exact hf
  exact hlin.mfderiv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private lemma intrinsicJacobi_smul
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u w : TangentSpace I x) (c : ℝ) (hc : c ≠ 0) :
    (intrinsicJacobi (I := I) g hEnorm x (c • u) w 1 : E)
      = ((c⁻¹ : ℝ) • (intrinsicJacobi (I := I) g hEnorm x u w c : E)) := by
  unfold intrinsicJacobi
  have hfun : (fun ρ : ℝ => intrinsicGeodesic (I := I) g hEnorm x (c • u + ρ • w) 1)
      = fun ρ : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + (ρ / c) • w) c := by
    funext ρ
    have hscal := intrinsicGeodesic_smul_apply (I := I) g hEnorm x
      (u + (ρ / c) • w) c 1
    have hinner : c • (u + (ρ / c) • w) = c • u + ρ • w := by
      rw [smul_add, smul_smul, mul_div_cancel₀ ρ hc]
    rw [← hinner]
    rw [hscal]
    simp
  rw [hfun]
  let G : ℝ → M := fun σ : ℝ => intrinsicGeodesic (I := I) g hEnorm x (u + σ • w) c
  have hG_smooth : ContMDiff 𝓘(ℝ, ℝ) I (∞ : WithTop ℕ∞) G := by
    have hvar := intrinsicVar_smooth (I := I) g hEnorm x (u : E) (w : E)
    have hσ : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (∞ : WithTop ℕ∞)
        (fun σ : ℝ => (σ, c)) := by
      exact (contMDiff_id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        (fun σ : ℝ => σ)).prodMk
        (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun _ : ℝ => c))
    with_unfolding_all exact hvar.comp hσ
  have hγ0 : HasMFDerivAt 𝓘(ℝ, ℝ) I G (0 / c) (mfderiv 𝓘(ℝ, ℝ) I G (0 / c)) := by
    exact (hG_smooth.contMDiffAt.mdifferentiableAt (by norm_num)).hasMFDerivAt
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun ρ : ℝ => ρ / c)
      0 (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    have hf : HasFDerivAt (fun ρ : ℝ => ρ / c) (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) 0 := by
      have hf' : HasFDerivAt (fun ρ : ℝ => c⁻¹ * ρ)
          (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) 0 :=
        (hasFDerivAt_id (0 : ℝ)).const_mul c⁻¹
      convert hf' using 1
      funext ρ
      ring
    with_unfolding_all exact hf
  have hcomp := (hγ0.comp 0 hlin).mfderiv
  change (mfderiv 𝓘(ℝ, ℝ) I (G ∘ (fun ρ : ℝ => ρ / c)) 0 (1 : ℝ) : E)
      = ((c⁻¹ : ℝ) • (mfderiv 𝓘(ℝ, ℝ) I G 0 (1 : ℝ) : E))
  rw [hcomp]
  have hzero : (0 / c : ℝ) = 0 := zero_div c
  rw [hzero]
  change (mfderiv 𝓘(ℝ, ℝ) I G 0) ((c⁻¹ • ContinuousLinearMap.id ℝ ℝ) 1)
      = c⁻¹ • (mfderiv 𝓘(ℝ, ℝ) I G 0) 1
  rw [smul_apply, ContinuousLinearMap.id_apply]
  exact ContinuousLinearMap.map_smul (mfderiv 𝓘(ℝ, ℝ) I G 0) c⁻¹ (1 : ℝ)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private lemma curveDensity_smul
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → ∀ t, TangentSpace I (γ t)) (t c : ℝ) (hc : 0 ≤ c)
    (hLI : LinearIndependent ℝ fun i => V i t) :
    curveDensity (I := I) g γ (fun i => c • V i) t
      = c ^ (Fintype.card ι) * curveDensity (I := I) g γ V t := by
  classical
  unfold curveDensity curveGram
  have hmat : Matrix.of (fun i j => g.inner (γ t) (c • V i t) (c • V j t))
      = (c ^ 2 : ℝ) • Matrix.of (fun i j => g.inner (γ t) (V i t) (V j t)) := by
    ext i j
    have h1 := map_smul (g.inner (γ t)) c (V i t)
    have h2 := map_smul (g.inner (γ t) (c • V i t)) c (V j t)
    calc
      g.inner (γ t) (c • V i t) (c • V j t)
          = (g.inner (γ t) (c • V i t)) (c • V j t) := rfl
      _ = c • ((g.inner (γ t) (c • V i t)) (V j t)) := h2
      _ = c • (c • (g.inner (γ t) (V i t)) (V j t)) := by
            rw [h1]
            simp []
      _ = (c ^ 2 : ℝ) • g.inner (γ t) (V i t) (V j t) := by
            rw [smul_smul]
            ring_nf
  change Real.sqrt ((Matrix.of (fun i j => g.inner (γ t) (c • V i t) (c • V j t))).det)
      = c ^ Fintype.card ι * Real.sqrt ((Matrix.of (fun i j => g.inner (γ t) (V i t) (V j t))).det)
  rw [hmat]
  rw [Matrix.det_smul]
  have hdet : 0 ≤ (Matrix.of fun i j => g.inner (γ t) (V i t) (V j t)).det := by
    exact le_of_lt (curveGram_det_pos (I := I) g γ V t hLI)
  have hpow : 0 ≤ c ^ Fintype.card ι := pow_nonneg hc _
  calc
    Real.sqrt ((c ^ 2) ^ Fintype.card ι • (Matrix.of fun i j => g.inner (γ t) (V i t) (V j t)).det)
        = Real.sqrt ((c ^ Fintype.card ι) ^ 2 * (Matrix.of fun i j => g.inner (γ t) (V i t)
          (V j t)).det) := by
          rw [← pow_mul, mul_comm, pow_mul, smul_eq_mul]
    _ = c ^ Fintype.card ι * Real.sqrt (Matrix.of fun i j => g.inner (γ t) (V i t)
      (V j t)).det := by
          have hsq2 : (c ^ Fintype.card ι) ^ 2 * (Matrix.of fun i j => g.inner (γ t) (V i t)
            (V j t)).det
              = (c ^ Fintype.card ι * Real.sqrt (Matrix.of fun i j => g.inner (γ t) (V i t)
                (V j t)).det) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hdet]
          rw [hsq2]
          rw [Real.sqrt_sq (mul_nonneg hpow (Real.sqrt_nonneg _))]
    _ = c ^ Fintype.card ι * curveDensity (I := I) g γ V t := by
          simp [curveDensity, curveGram]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private lemma curveDensity_congr_eval
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V V' : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (h : ∀ i, (V i t : E) = (V' i t : E)) :
    curveDensity (I := I) g γ V t = curveDensity (I := I) g γ V' t := by
  unfold curveDensity curveGram
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  have hi : V i t = V' i t := by
    exact h i
  have hj : V j t = V' j t := by
    exact h j
  simp [hi, hj]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private lemma expJacobianDensity_radial_scaled
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {u : TangentSpace I x} (hu : u ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x u (w i) = 0)
    (r : ℝ) (hr : 0 < r)
    (hLI : LinearIndependent ℝ fun i =>
      intrinsicJacobi (I := I) g hEnorm x u (w i) r) :
    expJacobianDensity (I := I) g hEnorm x ((r • u) : E) * r ^ (Module.finrank ℝ E - 1) =
      normalChartDensity (I := I) g x 0 *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  have hperp' : ∀ i, g.inner x ((r • u) : TangentSpace I x) (w i) = 0 := by
    intro i
    calc
      g.inner x ((r • u) : TangentSpace I x) (w i)
          = (r • (g.inner x u)) (w i) := by
            rw [map_smul (g.inner x) r u]
      _ = r • (g.inner x u (w i)) := by
            simp [smul_apply]
      _ = 0 := by simp [hperp i]
  have hvne : (r • u : TangentSpace I x) ≠ 0 := by
    intro hz
    have : r • (u : E) = 0 := by simpa using congrArg (fun v : TangentSpace I x => (v : E)) hz
    exact hu (smul_eq_zero.mp this |>.resolve_left (ne_of_gt hr))
  have hfac := expJacobianDensity_eq_ncd0_mul_transverse (I := I) g hEnorm x
    (v := (r • u : TangentSpace I x)) hvne w hON hperp'
  have hsc : ∀ i,
      (intrinsicJacobi (I := I) g hEnorm x ((r • u : TangentSpace I x)) (w i) 1 : E)
        = (r⁻¹ : ℝ) • (intrinsicJacobi (I := I) g hEnorm x u (w i) r : E) := by
    intro i
    exact intrinsicJacobi_smul (I := I) g hEnorm x u (w i) r (ne_of_gt hr)
  let V : Fin d → ∀ t : ℝ, TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm x (r • u) t) :=
    fun i t => (intrinsicJacobi (I := I) g hEnorm x u (w i) r : E)
  have hV1 : ∀ i, (intrinsicJacobi (I := I) g hEnorm x (r • u) (w i) 1 : E)
      = ((r⁻¹ : ℝ) • (V i 1 : E) : E) := by
    intro i
    change (intrinsicJacobi (I := I) g hEnorm x (r • u) (w i) 1 : E)
        = (r⁻¹ : ℝ) • (intrinsicJacobi (I := I) g hEnorm x u (w i) r : E)
    exact hsc i
  have hcong : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x (r • u))
      (fun i => intrinsicJacobi (I := I) g hEnorm x (r • u) (w i)) 1
      = curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x (r • u))
          (fun i t => (r⁻¹ : ℝ) • (V i t : E)) 1 := by
    apply curveDensity_congr_eval
    intro i
    exact hV1 i
  have hsmul := curveDensity_smul (I := I) g
    (γ := intrinsicGeodesic (I := I) g hEnorm x (r • u)) (V := V)
    (t := 1) (c := r⁻¹) (inv_nonneg.mpr (le_of_lt hr)) hLI
  have hbridge : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x (r • u))
      V 1 = curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r := by
    unfold curveDensity curveGram
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    have hpt : intrinsicGeodesic (I := I) g hEnorm x (r • u) 1
        = intrinsicGeodesic (I := I) g hEnorm x u r :=
      by simpa using intrinsicGeodesic_smul_apply (I := I) g hEnorm x u r 1
    rw [hpt]
  have hC : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x (r • u))
      (fun i => intrinsicJacobi (I := I) g hEnorm x (r • u) (w i)) 1
      = (r⁻¹ ^ d) * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
          (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r := by
    calc
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x (r • u))
          (fun i => intrinsicJacobi (I := I) g hEnorm x (r • u) (w i)) 1
          = curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x (r • u))
              (fun i t => (r⁻¹ : ℝ) • (V i t : E)) 1 := hcong
      _ = (r⁻¹ ^ d) * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x (r • u))
              V 1 := by
            rw [Fintype.card_fin] at hsmul
            with_unfolding_all exact hsmul
      _ = (r⁻¹ ^ d) * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
              (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r := by
            rw [hbridge]
  have hmult : (r⁻¹ ^ d) * r ^ d = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hr), one_pow]
  have hmain : expJacobianDensity (I := I) g hEnorm x ((r • u) : E)
      = normalChartDensity (I := I) g x 0 *
          ((r⁻¹ ^ d) * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
            (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r) := by
    rw [hfac, hC]
  calc
    expJacobianDensity (I := I) g hEnorm x ((r • u) : E) * r ^ d
        = normalChartDensity (I := I) g x 0 *
            ((r⁻¹ ^ d) * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
              (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r) * r ^ d := by
          rw [hmain]
    _ = normalChartDensity (I := I) g x 0 *
          curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
            (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r := by
          rw [mul_assoc]
          congr 1
          calc
            (r⁻¹ ^ d * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
              (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r) * r ^ d
                = (r⁻¹ ^ d * r ^ d) * curveDensity (I := I) g (intrinsicGeodesic
                  (I := I) g hEnorm x u)
                  (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r := by
                  ring
            _ = curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x u)
                  (fun i => intrinsicJacobi (I := I) g hEnorm x u (w i)) r := by
                  rw [hmult, one_mul]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end

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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_area_eq [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (y : M) ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {R : ℝ} (hR : 0 < R) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      = ∫⁻ v in
          SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  classical
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let L : E ≃L[ℝ] E :=
    normalFrame (I := I) (E := E) g x
  let Kc : Set E :=
    (SegmentDom (I := I) g hEnorm x : Set E) ∩
      L '' Metric.closedBall (0 : E) R
  let Ki : Set E :=
    (SegmentInt (I := I) g hEnorm x : Set E) ∩
      gBall (I := I) g x R
  have hKc : IsCompact Kc := by
    dsimp only [Kc]
    exact
      ((isCompact_closedBall (0 : E) R).image L.continuous).inter_left
        (isClosed_segmentDom (I := I) g hEnorm x)
  have hKi : MeasurableSet Ki := by
    exact (measurableSet_segmentInt (I := I) g hEnorm x).inter
      (measurableSet_gBall (I := I) g x R)
  have hpre :
      L ⁻¹' gBall (I := I) g x R = Metric.ball (0 : E) R := by
    with_unfolding_all exact preimage_gBall (I := I) (E := E) g x R
  have hKiKc : Ki ⊆ Kc := by
    intro v hv
    have hwopen : L.symm v ∈ Metric.ball (0 : E) R := by
      rw [← hpre]
      change (show TangentSpace I x from
        L (L.symm (show E from v))) ∈ gBall (I := I) g x R
      have hL : L (L.symm (show E from v)) = (show E from v) :=
        L.apply_symm_apply (show E from v)
      rw [hL]
      exact hv.2
    exact ⟨segmentInt_subset (I := I) g hEnorm x hv.1,
      ⟨L.symm v, Metric.ball_subset_closedBall hwopen,
        L.apply_symm_apply v⟩⟩
  have hdiff_sub :
      L ⁻¹' Kc \ L ⁻¹' Ki ⊆
        L ⁻¹' (SegmentDom (I := I) g hEnorm x \
          SegmentInt (I := I) g hEnorm x) ∪
            Metric.sphere (0 : E) R := by
    intro w hw
    rcases hw with ⟨hwc, hwnKi⟩
    change L w ∈ Kc at hwc
    by_cases hwI : L w ∈ SegmentInt (I := I) g hEnorm x
    · right
      have hwclosed : w ∈ Metric.closedBall (0 : E) R := by
        rcases hwc.2 with ⟨z, hz, hzw⟩
        have hzw' : z = w := L.injective hzw
        simpa only [hzw'] using hz
      have hwnopen : w ∉ Metric.ball (0 : E) R := by
        intro hwopen
        apply hwnKi
        change L w ∈ Ki
        refine ⟨hwI, ?_⟩
        change w ∈ L ⁻¹' gBall (I := I) g x R
        rw [hpre]
        exact hwopen
      rw [← Metric.closedBall_sdiff_ball]
      exact ⟨hwclosed, hwnopen⟩
    · left
      exact ⟨hwc.1, hwI⟩
  have hdiff :
      (volume : Measure E) (L ⁻¹' Kc \ L ⁻¹' Ki) = 0 := by
    apply measure_mono_null hdiff_sub
    apply measure_union_null
    · with_unfolding_all exact segmentEnd_zero (I := I) (E := E) g hEnorm x
    · exact Measure.addHaar_sphere (volume : Measure E) (0 : E) R
  have hpre_ae :
      L ⁻¹' Kc =ᵐ[(volume : Measure E)] L ⁻¹' Ki := by
    rw [ae_eq_set]
    refine ⟨hdiff, ?_⟩
    rw [sdiff_eq_empty.mpr (preimage_mono hKiKc), measure_empty]
  have harea :
      (∫⁻ v in Kc,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in Ki,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
    calc
      _ = ∫⁻ w in L ⁻¹' Kc,
          ENNReal.ofReal
            (curveDensity (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm x (L w))
              (fun i t =>
                intrinsicJacobi (I := I) g hEnorm x (L w)
                  ((normalBasis (I := I) g x) i) t)
              1)
          ∂(volume : Measure E) := by
        with_unfolding_all exact
          expJacobian_normal_int (I := I) (E := E) g hEnorm x Kc
      _ = ∫⁻ w in L ⁻¹' Ki,
          ENNReal.ofReal
            (curveDensity (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm x (L w))
              (fun i t =>
                intrinsicJacobi (I := I) g hEnorm x (L w)
                  ((normalBasis (I := I) g x) i) t)
              1)
          ∂(volume : Measure E) :=
        setLIntegral_congr hpre_ae
      _ = ∫⁻ v in Ki,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
        with_unfolding_all exact
          (expJacobian_normal_int (I := I) (E := E) g hEnorm x Ki).symm
  have hcover :
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
        (fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' Kc := by
    intro y hy
    obtain ⟨v, hv, hexp⟩ :=
      ball_sub_image_segmentDom (I := I) g hEnorm x R hy
    have hwopen : L.symm v ∈ Metric.ball (0 : E) R := by
      rw [← hpre]
      change (show TangentSpace I x from
        L (L.symm (show E from v))) ∈ gBall (I := I) g x R
      have hL : L (L.symm (show E from v)) = (show E from v) :=
        L.apply_symm_apply (show E from v)
      rw [hL]
      exact hv.2
    exact ⟨v, ⟨hv.1, ⟨L.symm v,
      Metric.ball_subset_closedBall hwopen,
      L.apply_symm_apply v⟩⟩, hexp⟩
  have hKi_image :
      (fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' Ki ⊆
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} := by
    rintro y ⟨v, hv, rfl⟩
    have hvD :
        v ∈ SegmentDom (I := I) g hEnorm x :=
      segmentInt_subset (I := I) g hEnorm x hv.1
    have hfin :
        riemannianEDist I x
          (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) ≠ ⊤ :=
      riemannianEDist_ne_top (I := I) x _
    change riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) < ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal hfin,
      ← (mem_segmentDom (I := I)).mp hvD]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 hv.2
  have hKi_inj : Set.InjOn
      (fun b : E =>
        expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from b)) Ki :=
    (exp_inj_segmentInt (I := I) g hEnorm x).mono inter_subset_left
  apply le_antisymm
  · calc
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R} ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          ((fun b : E =>
            expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from b)) '' Kc) :=
        measure_mono hcover
      _ ≤ ∫⁻ v in Kc,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
        riemVol_exp_image_le (I := I) g hEnorm x hKc
      _ = ∫⁻ v in Ki,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
        harea
      _ = ∫⁻ v in
          SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := rfl
  · calc
      (∫⁻ v in
          SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x R,
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        riemannianVolumeMeasure (I := I) (M := M) g
          ((fun b : E =>
            expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from b)) '' Ki) := by
        simpa only [Ki] using
          (riemVol_exp_image_eq (I := I) g hEnorm x hKi hKi_inj).symm
      _ ≤ riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R} :=
        measure_mono hKi_image

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_vol_rel
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {q s R : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) s)
      ≤ ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R)
        * riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  classical
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let d : ℕ := Module.finrank ℝ E - 1
  let L : E ≃L[ℝ] TangentSpace I x :=
    normalFrame (I := I) (E := E) g x
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    normalBasis (I := I) g x
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x (L w))
      (fun i t =>
        intrinsicJacobi (I := I) g hEnorm x (L w) (B i) t)
      1
  let T : Set E :=
    L ⁻¹' SegmentInt (I := I) g hEnorm x
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | L (r.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  let G : Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (hyperbolicDensity (q * r.1) d 1)
  have hDn_eq (w : E) :
      Dn w =
        |(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).det B| *
          expJacobianDensity (I := I) g hEnorm x (L w) := by
    with_unfolding_all exact
      (jacobianDens_basis (I := I) g hEnorm x (L w) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) B)
  have hDn_cont : Continuous Dn := by
    rw [show Dn = fun w =>
        |(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).det B| *
          expJacobianDensity (I := I) g hEnorm x (L w) by
      funext w
      exact hDn_eq w]
    exact continuous_const.mul
      ((expJacobian_continuous (I := I) g hEnorm x).comp L.continuous)
  have hDn_nonneg (w : E) : 0 ≤ Dn w := by
    simp only [Dn, curveDensity]
    exact Real.sqrt_nonneg _
  have hT_meas : MeasurableSet T :=
    (measurableSet_segmentInt (I := I) g hEnorm x).preimage
      L.continuous.measurable
  have hS_meas (u : Metric.sphere (0 : E) 1) :
      MeasurableSet (S u) := by
    exact (measurableSet_segmentInt (I := I) g hEnorm x).preimage
      (L.continuous.comp
        (continuous_subtype_val.smul continuous_const)).measurable
  have hF_meas (u : Metric.sphere (0 : E) 1) :
      Measurable (F u) := by
    exact (ENNReal.measurable_ofReal.comp
      (hDn_cont.measurable.comp
        (continuous_subtype_val.smul continuous_const).measurable)).indicator
          (hS_meas u)
  have hG_meas : Measurable G := by
    have hscale (r : Set.Ioi (0 : ℝ)) :
        hyperbolicDensity (q * r.1) d 1 =
          hyperbolicDensity q d r.1 / r.1 ^ d := by
      apply (eq_div_iff (pow_ne_zero d r.2.ne')).2
      simpa only [mul_one, mul_comm] using
        hyperbolicDens_scale q r.1 d 1 r.2.ne'
    rw [show G = fun r : Set.Ioi (0 : ℝ) =>
        ENNReal.ofReal (hyperbolicDensity q d r.1 / r.1 ^ d) by
      funext r
      change ENNReal.ofReal (hyperbolicDensity (q * r.1) d 1) =
        ENNReal.ofReal (hyperbolicDensity q d r.1 / r.1 ^ d)
      rw [hscale r]]
    exact ENNReal.measurable_ofReal.comp
      (((hyperbolicDen_continuous q d).measurable.comp measurable_subtype_coe).div
        (measurable_subtype_coe.pow_const d))
  have hS_down (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b) (hb : b ∈ S u) :
      a ∈ S u := by
    change L (b.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x at hb
    change L (a.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x
    have hab' : a.1 ≤ b.1 := hab
    have hratio0 : 0 ≤ a.1 / b.1 :=
      div_nonneg a.2.le b.2.le
    have hratio1 : a.1 / b.1 ≤ 1 :=
      (div_le_one b.2).2 hab'
    have hscaled :=
      segmentInt_smul (I := I) g hEnorm hb hratio0 hratio1
    simpa only [map_smul, smul_smul,
      div_mul_cancel₀ a.1 b.2.ne'] using hscaled
  have hu_inner (u : Metric.sphere (0 : E) 1) :
      g.inner x (L u.1) (L u.1) = 1 := by
    have hunorm : ‖u.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using u.2
    simp only [L, normalFrame_inner, real_inner_self_eq_norm_sq,
      hunorm, one_pow]
  have hG_pos (r : Set.Ioi (0 : ℝ)) :
      0 < hyperbolicDensity (q * r.1) d 1 :=
    hyperbolicDensity_pos (mul_nonneg hq r.2.le) one_pos
  have hsingle (r : Set.Ioi (0 : ℝ)) :
      Measure.volumeIoiPow d ({r} : Set (Set.Ioi (0 : ℝ))) = 0 := by
    rw [Measure.volumeIoiPow]
    apply withDensity_absolutelyContinuous
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    exact ((show ({r} : Set (Set.Ioi (0 : ℝ))).Subsingleton from
      Set.subsingleton_singleton).image
        ((↑) : Set.Ioi (0 : ℝ) → ℝ)).measure_zero volume
  have hIio_Iic (r : Set.Ioi (0 : ℝ)) :
      Set.Iio r =ᵐ[Measure.volumeIoiPow d] Set.Iic r :=
    Iio_ae_eq_Iic' (hsingle r)
  have hR : 0 < R := hs.trans_le hsR
  have hmodel {t : ℝ} (ht : 0 < t) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d) =
        ENNReal.ofReal (hyperbolicRadialVolume q d t) := by
    calc
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d) =
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
            ∂Measure.volumeIoiPow d :=
        setLIntegral_congr (hIio_Iic ⟨t, ht⟩).symm
      _ = ∫⁻ r : Set.Ioi (0 : ℝ),
          (Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))).indicator G r
          ∂Measure.volumeIoiPow d :=
        (lintegral_indicator measurableSet_Iio G).symm
      _ = ENNReal.ofReal (hyperbolicRadialVolume q d t) := by
        simpa only [G] using lintegral_hyperbolicDensity_eq_hyperbolicRadialVolume q hq d ht
  have hpolar {t : ℝ} (ht : 0 < t) :
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal t} =
        ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
    let K : Set E :=
      SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x t
    have hpre :
        L ⁻¹' K = T ∩ Metric.ball (0 : E) t := by
      dsimp only [K]
      change
        (L ⁻¹' SegmentInt (I := I) g hEnorm x) ∩
            (L ⁻¹' gBall (I := I) g x t) =
          T ∩ Metric.ball (0 : E) t
      rw [preimage_gBall (I := I) (E := E) g x t]
    have hset : MeasurableSet (T ∩ Metric.ball (0 : E) t) :=
      hT_meas.inter measurableSet_ball
    have hfun : Measurable (fun w : E => ENNReal.ofReal (Dn w)) :=
      ENNReal.measurable_ofReal.comp hDn_cont.measurable
    have hind :
        Measurable ((T ∩ Metric.ball (0 : E) t).indicator
          (fun w : E => ENNReal.ofReal (Dn w))) :=
      hfun.indicator hset
    calc
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal t} =
          ∫⁻ v in K,
            ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
            ∂(modelHaar (E := E)) := by
        simpa only [K] using segmentBall_area_eq (I := I) g hEnorm x ht
      _ = ∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn w)
          ∂(volume : Measure E) := by
        simpa only [Dn, L, B] using
          expJacobian_normal_int (I := I) (E := E) g hEnorm x K
      _ = ∫⁻ w in T ∩ Metric.ball (0 : E) t,
          ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by
        rw [hpre]
      _ = ∫⁻ w : E,
          (T ∩ Metric.ball (0 : E) t).indicator
            (fun z => ENNReal.ofReal (Dn z)) w
          ∂(volume : Measure E) :=
        (lintegral_indicator hset _).symm
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ),
            (T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        simpa only [d] using
          lintegral_polar (volume : Measure E)
            ((T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z))) hind.aemeasurable
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        apply lintegral_congr
        intro u
        have hunorm : ‖u.1‖ = 1 := by
          simpa only [mem_sphere_zero_iff_norm] using u.2
        have hball (r : Set.Ioi (0 : ℝ)) :
            r.1 • u.1 ∈ Metric.ball (0 : E) t ↔
              r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)) := by
          rw [Metric.mem_ball, dist_zero_right, norm_smul,
            Real.norm_of_nonneg r.2.le, hunorm, mul_one]
          rfl
        calc
          (∫⁻ r : Set.Ioi (0 : ℝ),
              (T ∩ Metric.ball (0 : E) t).indicator
                (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
              ∂Measure.volumeIoiPow d) =
              ∫⁻ r : Set.Ioi (0 : ℝ) in
                Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
                ∂Measure.volumeIoiPow d := by
            rw [← lintegral_indicator measurableSet_Iio]
            apply lintegral_congr
            intro r
            have hseg : r ∈ S u ↔ r.1 • u.1 ∈ T := Iff.rfl
            dsimp only [F]
            by_cases hrS : r ∈ S u
            · by_cases hrt : r ∈
                  Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · have hmem :
                    r.1 • u.1 ∈ T ∩ Metric.ball (0 : E) t :=
                  ⟨hseg.mp hrS, (hball r).mpr hrt⟩
                rw [Set.indicator_of_mem hmem,
                  Set.indicator_of_mem hrt,
                  Set.indicator_of_mem hrS]
              · rw [Set.indicator_of_notMem
                    (fun h => hrt ((hball r).mp h.2)),
                  Set.indicator_of_notMem hrt]
            · rw [Set.indicator_of_notMem
                  (fun h => hrS (hseg.mpr h.1))]
              by_cases hrt : r ∈
                  Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · rw [Set.indicator_of_mem hrt,
                  Set.indicator_of_notMem hrS]
              · rw [Set.indicator_of_notMem hrt]
          _ = ∫⁻ r : Set.Ioi (0 : ℝ) in
              Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
              ∂Measure.volumeIoiPow d :=
            setLIntegral_congr (hIio_Iic ⟨t, ht⟩)
  have hcross (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b)
      (hbR : b ≤ (⟨R, hR⟩ : Set.Ioi (0 : ℝ))) :
      F u b * G a ≤ F u a * G b := by
    by_cases hbS : b ∈ S u
    · have haS : a ∈ S u := hS_down u hab hbS
      have hbS' := hbS
      change L (b.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x at hbS'
      obtain ⟨c, hc, hcb⟩ := hbS'
      let uT : TangentSpace I x := L u.1
      have huT_pos : 0 < g.inner x uT uT := by
        simpa only [uT, hu_inner u] using one_pos
      have huT0 : uT ≠ 0 := by
        intro hu0
        rw [hu0] at huT_pos
        simp only [map_zero, lt_self_iff_false] at huT_pos
      have hc0 : 0 < c := one_pos.trans hc
      have hcb_pos : 0 < c * b.1 := mul_pos hc0 b.2
      have hcbD :
          (c * b.1) • uT ∈ SegmentDom (I := I) g hEnorm x := by
        simpa only [uT, map_smul, smul_smul] using hcb
      have hcb0 : (c * b.1) • uT ≠ 0 :=
        smul_ne_zero hcb_pos.ne' huT0
      have hno :
          ∀ t ∈ Set.Ioo (0 : ℝ) (c * b.1),
            ¬ IsConjVec (I := I) g hEnorm x
              ((t • uT : TangentSpace I x) : E) := by
        intro t ht
        have hratio :
            t / (c * b.1) ∈ Set.Ioo (0 : ℝ) 1 := by
          exact ⟨div_pos ht.1 hcb_pos,
            (div_lt_one hcb_pos).2 ht.2⟩
        have hraw :=
          segmentDom_no_conj (I := I) g hEnorm hcbD hcb0
            (t / (c * b.1)) hratio
        simpa only [smul_smul,
          div_mul_cancel₀ t hcb_pos.ne'] using hraw
      have hb_lt : b.1 < c * b.1 :=
        lt_mul_of_one_lt_left b.2 hc
      have haWin : a.1 ∈ Set.Ioo (0 : ℝ) (c * b.1) :=
        ⟨a.2, (show a.1 ≤ b.1 from hab).trans_lt hb_lt⟩
      have hbWin : b.1 ∈ Set.Ioo (0 : ℝ) (c * b.1) :=
        ⟨b.2, hb_lt⟩
      by_cases hd : 0 < d
      · obtain ⟨v, hON, hperp'⟩ :=
          exists_perp_pos (I := I) g x uT huT_pos
        have hperp : ∀ i, g.inner x uT (v i) = 0 := by
          intro i
          rw [g.symm x uT (v i)]
          exact hperp' i
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x uT)
            (fun i => intrinsicJacobi (I := I) g hEnorm x uT (v i)) t
        have huT_one : g.inner x uT uT = 1 := by
          simpa only [uT] using hu_inner u
        have hanti :
            AntitoneOn
              (fun t => Dt t / hyperbolicDensity q d t)
              (Set.Ioo (0 : ℝ) (c * b.1)) := by
          simpa only [Dt, d, huT_one, Real.sqrt_one, mul_one] using
            intrinsicRatioOfFrame (I := I) g hEnorm x uT q
              (c * b.1) hq hd huT_pos v hON hperp hno hRic
        have hratio :=
          hanti haWin hbWin (show a.1 ≤ b.1 from hab)
        have hHa : 0 < hyperbolicDensity q d a.1 :=
          hyperbolicDensity_pos hq a.2
        have hHb : 0 < hyperbolicDensity q d b.1 :=
          hyperbolicDensity_pos hq b.2
        have htrans :
            Dt b.1 * hyperbolicDensity q d a.1 ≤
              Dt a.1 * hyperbolicDensity q d b.1 :=
          (div_le_div_iff₀ hHb hHa).1 hratio
        have hB :
            ∀ i j, g.inner x (B i) (B j) =
              if i = j then 1 else 0 := by
          simpa only [B] using normalBasis_inner (I := I) g x
        have hLa : L (a.1 • u.1) = a.1 • uT := by
          simpa only [uT] using L.map_smul a.1 u.1
        have hLb : L (b.1 • u.1) = b.1 • uT := by
          simpa only [uT] using L.map_smul b.1 u.1
        have hDnA :
            Dn (a.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (a.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (a.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLa]
        have hDnB :
            Dn (b.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (b.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (b.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLb]
        have hDa :
            a.1 ^ d * Dn (a.1 • u.1) = Dt a.1 := by
          rw [hDnA]
          simpa only [d, Dt] using
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp a.2
        have hDb :
            b.1 ^ d * Dn (b.1 • u.1) = Dt b.1 := by
          rw [hDnB]
          simpa only [d, Dt] using
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp b.2
        have hGa :
            a.1 ^ d * hyperbolicDensity (q * a.1) d 1 =
              hyperbolicDensity q d a.1 := by
          simpa only [mul_one] using
            hyperbolicDens_scale q a.1 d 1 a.2.ne'
        have hGb :
            b.1 ^ d * hyperbolicDensity (q * b.1) d 1 =
              hyperbolicDensity q d b.1 := by
          simpa only [mul_one] using
            hyperbolicDens_scale q b.1 d 1 b.2.ne'
        have hpowa : 0 < a.1 ^ d := pow_pos a.2 d
        have hpowb : 0 < b.1 ^ d := pow_pos b.2 d
        have hreal :
            Dn (b.1 • u.1) * hyperbolicDensity (q * a.1) d 1 ≤
              Dn (a.1 • u.1) * hyperbolicDensity (q * b.1) d 1 := by
          apply (mul_le_mul_iff_right₀ (mul_pos hpowa hpowb)).mp
          calc
            (a.1 ^ d * b.1 ^ d) *
                (Dn (b.1 • u.1) * hyperbolicDensity (q * a.1) d 1) =
                (b.1 ^ d * Dn (b.1 • u.1)) *
                  (a.1 ^ d * hyperbolicDensity (q * a.1) d 1) := by ring
            _ = Dt b.1 * hyperbolicDensity q d a.1 := by
              rw [hDb, hGa]
            _ ≤ Dt a.1 * hyperbolicDensity q d b.1 := htrans
            _ = (a.1 ^ d * Dn (a.1 • u.1)) *
                (b.1 ^ d * hyperbolicDensity (q * b.1) d 1) := by
              rw [hDa, hGb]
            _ = (a.1 ^ d * b.1 ^ d) *
                (Dn (a.1 • u.1) * hyperbolicDensity (q * b.1) d 1) := by ring
        simp only [F, G, Set.indicator_of_mem hbS,
          Set.indicator_of_mem haS]
        rw [← ENNReal.ofReal_mul (hDn_nonneg (b.1 • u.1)),
          ← ENNReal.ofReal_mul (hDn_nonneg (a.1 • u.1))]
        exact ENNReal.ofReal_le_ofReal hreal
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        let v : Fin d → TangentSpace I x := fun i =>
          isEmptyElim (hd0 ▸ i)
        have hON :
            ∀ i j, g.inner x (v i) (v j) =
              if i = j then 1 else 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hperp : ∀ i, g.inner x uT (v i) = 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hB :
            ∀ i j, g.inner x (B i) (B j) =
              if i = j then 1 else 0 := by
          simpa only [B] using normalBasis_inner (I := I) g x
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x uT)
            (fun i => intrinsicJacobi (I := I) g hEnorm x uT (v i)) t
        have hDt (t : ℝ) : Dt t = 1 := by
          have hgram :
              curveGram (I := I) g
                  (intrinsicGeodesic (I := I) g hEnorm x uT)
                  (fun i =>
                    intrinsicJacobi (I := I) g hEnorm x uT (v i)) t =
                1 := by
            ext i
            exact isEmptyElim (hd0 ▸ i)
          simp only [Dt, curveDensity, hgram, Matrix.det_one, Real.sqrt_one]
        have hLa : L (a.1 • u.1) = a.1 • uT := by
          simpa only [uT] using L.map_smul a.1 u.1
        have hLb : L (b.1 • u.1) = b.1 • uT := by
          simpa only [uT] using L.map_smul b.1 u.1
        have hDnA :
            Dn (a.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (a.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (a.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLa]
        have hDnB :
            Dn (b.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (b.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (b.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLb]
        have hDa : Dn (a.1 • u.1) = 1 := by
          rw [hDnA]
          have hscale :=
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp a.2
          simpa only [d, hd0, pow_zero, one_mul, Dt, hDt] using hscale
        have hDb : Dn (b.1 • u.1) = 1 := by
          rw [hDnB]
          have hscale :=
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp b.2
          simpa only [d, hd0, pow_zero, one_mul, Dt, hDt] using hscale
        have hGa : hyperbolicDensity (q * a.1) d 1 = 1 := by
          simp only [hd0, hyperbolicDensity, pow_zero]
        have hGb : hyperbolicDensity (q * b.1) d 1 = 1 := by
          simp only [hd0, hyperbolicDensity, pow_zero]
        simp only [F, G, Set.indicator_of_mem hbS,
          Set.indicator_of_mem haS, hDa, hDb, hGa, hGb,
          ENNReal.ofReal_one, mul_one, le_refl]
    · simp only [F, Set.indicator_of_notMem hbS, zero_mul, zero_le]
  have hdir (u : Metric.sphere (0 : E) 1) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) *
          ENNReal.ofReal (hyperbolicRadialVolume q d s) ≤
        (∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d) *
          ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
    have h :=
      lintegral_Iic_cross
        (μ := Measure.volumeIoiPow d) (f := F u) (g := G)
        (hF_meas u).aemeasurable.restrict
        hG_meas.aemeasurable.restrict
        (fun {_a _b} hab hbR => hcross u hab hbR)
        (show (⟨s, hs⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨R, hR⟩ from hsR)
    rw [hmodel hs, hmodel hR] at h
    exact h
  rw [show Module.finrank ℝ E - 1 = d by rfl]
  rw [hpolar hR, hpolar hs]
  rw [mul_comm
    (ENNReal.ofReal (hyperbolicRadialVolume q d R))
    (∫⁻ u : Metric.sphere (0 : E) 1,
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d
      ∂(volume : Measure E).toSphere)]
  rw [← lintegral_mul_const'
    (ENNReal.ofReal (hyperbolicRadialVolume q d s))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d)
    ENNReal.ofReal_ne_top]
  rw [← lintegral_mul_const'
    (ENNReal.ofReal (hyperbolicRadialVolume q d R))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d)
    ENNReal.ofReal_ne_top]
  exact lintegral_mono hdir

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
