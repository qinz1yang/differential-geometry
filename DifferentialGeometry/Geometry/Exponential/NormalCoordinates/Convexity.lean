import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.MetricExtension
import DifferentialGeometry.Geometry.Exponential.MinimizingVector
import DifferentialGeometry.Geometry.Exponential.Variation.EndpointShape
import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic
import DifferentialGeometry.Geometry.Exponential.Injectivity

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential Geodesic
open DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem extension_inner_zero
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E) {B : ℝ} (hB : 0 ≤ B)
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (v w : E) : gExt.inner (0 : E) v w = inner ℝ v w := by
  rw [hmetric 0 (by simpa only [norm_zero] using hB)]
  have h0 : normalFrame g p (0 : E) ∈ expDomain g p := by
    simpa only [map_zero] using zero_mem_expDomain g p
  have hF0 : framedExpMap g p (0 : E) = p := by
    rw [framedExpMap_apply, map_zero, expMap_zero]
  have hD0 : mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (0 : E) =
      (normalFrame g p).toContinuousLinearMap := by
    rw [mfderiv_framedExpMap g p h0, map_zero]
    have hraw := mfderiv_expMap_at_zero g p
    have hcomp := congrArg
      (fun D : E →L[ℝ] E => D.comp (normalFrame g p).toContinuousLinearMap) hraw
    simpa only [ContinuousLinearMap.id_comp] using! hcomp
  rw [hF0, hD0]
  exact normalFrame_inner g p v w

end Radial

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem hess_half_norm_sq_pos_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B K : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita gExt) z) v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w)
    {z : E} (hz : ‖z‖ < B) (hsmall : K * ‖z‖ ^ 2 < (Real.pi / 2) ^ 2)
    (v : E) (hv : v ≠ 0) :
    0 < hessFun gExt (fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2) z v v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let hom : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { toPartialEquiv := PartialEquiv.ofSet (Metric.ball (0 : E) B)
      open_source := Metric.isOpen_ball
      open_target := Metric.isOpen_ball
      contMDiffOn_toFun := contMDiff_id.contMDiffOn
      contMDiffOn_invFun := contMDiff_id.contMDiffOn }
  let β : ExponentialInverseBranch gExt hExt (0 : E) :=
    { hom := hom
      hom_eq := by
        intro y hy
        have hy' : ‖y‖ < B := by
          simpa only [hom, PartialEquiv.ofSet_source, Metric.mem_ball, dist_zero_right] using hy
        change intrinsicGeodesic gExt hExt (0 : E) y 1 = y
        simpa only [one_smul] using!
          intrinsicGeodesic_zero_eq_smul_of_pullback_extension g p gExt hcomplete hdom hmetric
            (z := y) (t := 1) (by simpa only [one_smul] using hy') }
  have henergy : branchEnergy gExt β = fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
    funext y
    change (1 / 2 : ℝ) * gExt.inner (0 : E) y y = (1 / 2 : ℝ) * ‖y‖ ^ 2
    rw [extension_inner_zero g p gExt ((norm_nonneg z).trans hz.le) hmetric,
      real_inner_self_eq_norm_sq]
  have hlaunch : expMapIntrinsic gExt hExt (0 : E) z = z := by
    change intrinsicGeodesic gExt hExt (0 : E) z 1 = z
    simpa only [one_smul] using!
      intrinsicGeodesic_zero_eq_smul_of_pullback_extension g p gExt hcomplete hdom hmetric
        (z := z) (t := 1) (by simpa only [one_smul] using hz)
  have hsrc : tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (0 : E) z ∈
      β.hom.source := by
    change z ∈ Metric.ball (0 : E) B
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hpos := branchEnergy_hess_pos β hsrc hsmall (fun t ht w => ?_) v hv
  · rw [henergy, hlaunch] at hpos
    exact hpos
  let γ := intrinsicGeodesic gExt hExt (0 : E) z
  have hγt : γ t = t • z :=
    intrinsicGeodesic_zero_eq_smul_of_pullback_extension g p gExt hcomplete hdom hmetric
      (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2.le).trans_lt hz)
  have hfence : ‖γ t‖ < B := by
    rw [hγt, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2.le).trans_lt hz
  have hspeed : gExt.inner (γ t)
      (Variation.curveVelocity γ t) (Variation.curveVelocity γ t) = ‖z‖ ^ 2 := by
    rw [show gExt.inner (γ t) (Variation.curveVelocity γ t)
        (Variation.curveVelocity γ t) = gExt.inner (0 : E) z z from by
      simpa only [γ, Variation.curveVelocity] using!
        intrinsicGeodesic_speedSq_eq gExt hExt (0 : E) z t]
    rw [extension_inner_zero g p gExt ((norm_nonneg z).trans hz.le) hmetric,
      real_inner_self_eq_norm_sq]
  calc
    _ ≤ K * gExt.inner (γ t) w w *
        gExt.inner (γ t) (Variation.curveVelocity γ t) (Variation.curveVelocity γ t) :=
      hcurv (γ t) hfence w (Variation.curveVelocity γ t)
    _ = (K * ‖z‖ ^ 2) * gExt.inner (γ t) w w := by rw [hspeed]; ring

theorem strictConvexOn_half_norm_sq_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B K : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita gExt) z) v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w)
    {γ : ℝ → E} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ) {D : Set ℝ}
    (hgeo : IsGeodesicOn gExt γ (interior D)) (hD : Convex ℝ D)
    (hfence : ∀ t ∈ interior D, ‖γ t‖ < B)
    (hsmall : ∀ t ∈ interior D, K * ‖γ t‖ ^ 2 < (Real.pi / 2) ^ 2)
    (hvel : ∀ t ∈ interior D, (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) : E) ≠ 0) :
    StrictConvexOn ℝ D ((fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2) ∘ γ) := by
  have hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).contMDiff
  exact strictConvex_geo_on gExt isOpen_univ hf.contMDiffOn hγ hgeo hD
    (hf.continuous.comp hγ.continuous).continuousOn (fun _ _ => mem_univ _)
    (fun t ht => hess_half_norm_sq_pos_of_pullback_extension
      g p gExt hcomplete hdom hmetric hcurv (hfence t ht) (hsmall t ht) _ (hvel t ht))

end Hessian

section Fence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem extension_norm_sub_le_of_speed
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E) {B : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    {γ : ℝ → E} {s t c : ℝ} (hst : s ≤ t) (hc : 0 ≤ c)
    (hγ : ContDiffOn ℝ 1 γ (Icc s t))
    (hfence : ∀ u ∈ Ioo s t, ‖γ u‖ < B)
    (hspeed : ∀ u ∈ Ioo s t,
      Real.sqrt (gExt.inner (γ u) (deriv γ u) (deriv γ u)) ≤ c) :
    ‖γ t‖ - ‖γ s‖ ≤ c * (t - s) := by
  have h := hγ.norm_sub_le_integral_of_inner_deriv_le hst
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume s t)
    (fun _ _ => hc) (fun u hu => ?_)
  · simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hrad : inner ℝ (γ u) (deriv γ u) ≤
      ‖γ u‖ * Real.sqrt (gExt.inner (γ u) (deriv γ u) (deriv γ u)) := by
    let w : E := deriv γ u
    change inner ℝ (γ u) w ≤ ‖γ u‖ * Real.sqrt (gExt.inner (γ u) w w)
    rw [hmetric (γ u) (hfence u hu).le w w]
    exact (le_abs_self _).trans (framedExpMap_radial_lower_bound g p w
      (hdom (by simpa only [Metric.mem_closedBall, dist_zero_right] using (hfence u hu).le)))
  exact hrad.trans (mul_le_mul_of_nonneg_left (hspeed u hu) (norm_nonneg _))

variable [NeZero (Module.finrank ℝ E)]

private theorem extension_launch_fenced
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (x : E) (v : TangentSpace 𝓘(ℝ, E) x)
    (hbudget : ‖x‖ + Real.sqrt (gExt.inner x v v) < B) :
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  MapsTo (intrinsicGeodesic gExt hExt x v) (Icc (0 : ℝ) 1) (Metric.ball (0 : E) B) := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let γ := intrinsicGeodesic gExt hExt x v
  have hγ : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1) :=
    ((contMDiff_iff_contDiff.mp
      (intrinsicGeodesic_contMDiff gExt hExt x v)).of_le (by decide)).contDiffOn
  apply mapsTo_ball_of_pathELength_lt_of_pullback_extension g p gExt hdom hmetric zero_le_one hγ
  have hlen : Manifold.pathELength 𝓘(ℝ, E) γ 0 1 ≤
      ENNReal.ofReal (Real.sqrt (gExt.inner x v v)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    calc
      _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (gExt.inner x v v)) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t _
        exact intrinsicGeodesic_velocity_enorm_le gExt hExt x v t
      _ = ENNReal.ofReal (Real.sqrt (gExt.inner x v v)) := by
        rw [setLIntegral_const, Real.volume_Icc]
        norm_num
  apply hlen.trans_lt
  rw [show γ 0 = x from intrinsicGeodesic_zero gExt hExt x v]
  apply (ENNReal.ofReal_lt_ofReal_iff (by linarith [Real.sqrt_nonneg (gExt.inner x v v)])).mpr
  linarith

private theorem extension_launch_norm_bound
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (x : E) (v : TangentSpace 𝓘(ℝ, E) x) :
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let γ := intrinsicGeodesic gExt hExt x v
  (∀ s ∈ Icc (0 : ℝ) 1, ‖γ s‖ < B) →
  ∀ t ∈ Icc (0 : ℝ) 1,
    ‖γ t‖ ≤ min (‖x‖ + Real.sqrt (gExt.inner x v v) * t)
      (‖γ 1‖ + Real.sqrt (gExt.inner x v v) * (1 - t)) := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let γ := intrinsicGeodesic gExt hExt x v
  intro hfence t ht
  have hγ : ContDiff ℝ 1 γ :=
    (contMDiff_iff_contDiff.mp (intrinsicGeodesic_contMDiff gExt hExt x v)).of_le (by decide)
  have hspeed (s : ℝ) : gExt.inner (γ s) (deriv γ s) (deriv γ s) = gExt.inner x v v := by
    simpa only [γ, mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      intrinsicGeodesic_speedSq_eq gExt hExt x v s
  have hpre := extension_norm_sub_le_of_speed g p gExt hdom hmetric ht.1
    (Real.sqrt_nonneg (gExt.inner x v v)) hγ.contDiffOn
    (fun s hs => hfence s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
    (fun s _ => by rw [hspeed])
  rw [show γ 0 = x from intrinsicGeodesic_zero gExt hExt x v, sub_zero] at hpre
  let η : ℝ → E := fun s => γ (1 - s)
  have hη : ContDiff ℝ 1 η := hγ.comp (contDiff_const.sub contDiff_id)
  have hηd (s : ℝ) : deriv η s = -(deriv γ (1 - s)) := by
    have hd := (hγ.differentiable one_ne_zero (1 - s)).hasDerivAt.scomp s
      ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))
    simpa only [η, Function.comp_def, zero_sub, one_smul, neg_smul] using! hd.deriv
  have hηspeed (s : ℝ) : gExt.inner (η s) (deriv η s) (deriv η s) = gExt.inner x v v := by
    let F : E →L[ℝ] E →L[ℝ] ℝ := gExt.inner (η s)
    have hneg (w : E) : F (-w) (-w) = F w w := by
      rw [map_neg F w]
      change -(F w (-w)) = F w w
      rw [map_neg (F w) w, neg_neg]
    change F (deriv η s) (deriv η s) = _
    rw [hηd]
    exact (hneg _).trans (hspeed (1 - s))
  have hsuf := extension_norm_sub_le_of_speed g p gExt hdom hmetric (sub_nonneg.mpr ht.2)
    (Real.sqrt_nonneg (gExt.inner x v v)) hη.contDiffOn
    (fun s hs => hfence (1 - s) ⟨by linarith [hs.2, ht.1], by linarith [hs.1]⟩)
    (fun s _ => by rw [hηspeed])
  have hη0 : η 0 = γ 1 := by simp only [η, sub_zero]
  have hηend : η (1 - t) = γ t := by simp only [η, sub_sub_cancel]
  rw [hη0, hηend, sub_zero] at hsuf
  exact le_min (by linarith) (by linarith)

end Fence

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem norm_intrinsicGeodesic_le_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B K a L : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita gExt) z) v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w)
    (hbudget : a + L < B)
    (hsmall : K * (a + L / 2) ^ 2 < (Real.pi / 2) ^ 2)
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (v : TangentSpace 𝓘(ℝ, E) x)
    (hv : Real.sqrt (gExt.inner x v v) ≤ L) :
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  intrinsicGeodesic gExt hExt x v 1 = y →
  ∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x v t‖ ≤ a := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let γ := intrinsicGeodesic gExt hExt x v
  intro hend t ht
  have hγ0 : γ 0 = x := intrinsicGeodesic_zero gExt hExt x v
  have hγ1 : γ 1 = y := hend
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hL : 0 ≤ L := (Real.sqrt_nonneg _).trans hv
  by_cases hv0 : v = 0
  · have hdist := intrinsicGeodesic_riemannianEDist_le gExt hExt x v (s := 0) (t := t) ht.1
    have hspeed0 : Real.sqrt (gExt.inner x v v) = 0 := by rw [hv0]; simp
    rw [hspeed0, zero_mul, ENNReal.ofReal_zero] at hdist
    have heq : γ 0 = γ t := riemannianEDist_eq_zero_imp_eq (γ 0) (γ t)
      (le_antisymm (by simpa only [γ, sub_zero] using hdist) bot_le)
    rw [hγ0] at heq
    simpa only [γ, ← heq] using hx
  have hfence : ∀ s ∈ Icc (0 : ℝ) 1, ‖γ s‖ < B := by
    have hf := extension_launch_fenced g p gExt hcomplete hdom hmetric x v
      (by linarith : ‖x‖ + Real.sqrt (gExt.inner x v v) < B)
    simpa only [MapsTo, Metric.mem_ball, dist_zero_right, γ] using! hf
  have hscale : ∀ s ∈ Icc (0 : ℝ) 1, ‖γ s‖ ≤ a + L / 2 := by
    intro s hs
    have hboth := extension_launch_norm_bound g p gExt hcomplete hdom hmetric x v hfence s hs
    change ‖γ s‖ ≤ min _ _ at hboth
    have hpre := hboth.trans (min_le_left _ _)
    have hsuf := hboth.trans (min_le_right _ _)
    change ‖γ s‖ ≤ ‖γ 1‖ + Real.sqrt (gExt.inner x v v) * (1 - s) at hsuf
    rw [hγ1] at hsuf
    nlinarith
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      ((fun z : E => (1 / 2 : ℝ) * ‖z‖ ^ 2) ∘ γ) :=
    strictConvexOn_half_norm_sq_of_pullback_extension g p gExt hcomplete hdom hmetric hcurv
      (intrinsicGeodesic_contMDiff gExt hExt x v)
      (by simpa only [interior_Icc] using
        (intrinsicGeodesic_isGeodesic gExt hExt x v).isGeodesicOn (Ioo (0 : ℝ) 1))
      (convex_Icc (0 : ℝ) 1)
      (fun s hs => hfence s (Ioo_subset_Icc_self (by simpa only [interior_Icc] using hs)))
      (fun s hs => by
        have hs' : s ∈ Icc (0 : ℝ) 1 :=
          Ioo_subset_Icc_self (by simpa only [interior_Icc] using hs)
        by_cases hK : 0 ≤ K
        · apply lt_of_le_of_lt ?_ hsmall
          exact mul_le_mul_of_nonneg_left
            ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hscale s hs')) hK
        · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK) (sq_nonneg _)).trans_lt
            (sq_pos_of_pos (div_pos Real.pi_pos (by norm_num))))
      (fun s _ => intrinsicGeo_velocity_ne gExt hExt x v hv0 s)
  have hjensen := hstrict.convexOn.2 (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) (sub_nonneg.mpr ht.2) ht.1
    (by ring : (1 - t) + t = 1)
  have henergy : (1 / 2 : ℝ) * ‖γ t‖ ^ 2 ≤
      (1 - t) * ((1 / 2 : ℝ) * ‖γ 0‖ ^ 2) + t * ((1 / 2 : ℝ) * ‖γ 1‖ ^ 2) := by
    simpa only [Function.comp_apply, smul_eq_mul, mul_zero, zero_add, mul_one] using hjensen
  rw [hγ0, hγ1] at henergy
  have hxSq := (sq_le_sq₀ (norm_nonneg x) ha).mpr hx
  have hySq := (sq_le_sq₀ (norm_nonneg y) ha).mpr hy
  have hxt := mul_le_mul_of_nonneg_left hxSq (sub_nonneg.mpr ht.2)
  have hyt := mul_le_mul_of_nonneg_left hySq ht.1
  exact (sq_le_sq₀ (norm_nonneg (γ t)) ha).mp (by nlinarith)

end Core

section Injectivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

private theorem extension_launch_derivative_injective
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B K : ℝ}
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita gExt) z) v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w)
    (x u : E) (hsmall : K * gExt.inner x u u < (Real.pi / 2) ^ 2) :
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  (∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x u t‖ < B) →
  Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
    (fun b : E => expMap gExt x (show TangentSpace 𝓘(ℝ, E) x from b)) u) := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  intro hfence
  let γ := intrinsicGeodesic gExt hExt x u
  have hradial : VolumeComparison.radialCurve gExt x u = γ :=
    radialCurve_eq_intrinsicGeodesic gExt hExt x u
  have hxdom : (show TangentSpace 𝓘(ℝ, E) x from u) ∈ expDomain gExt x := by
    rw [expDomain_eq_univ_of_completeSpace gExt hExt x]
    exact mem_univ _
  have hinj := injective_mfderiv_expMap_of_curvature_upper_bound gExt x u hxdom hsmall (by
    rw [hradial]
    intro t ht v
    have hspeed : gExt.inner (γ t) (Variation.curveVelocity γ t)
        (Variation.curveVelocity γ t) = gExt.inner x u u := by
      simpa only [γ, Variation.curveVelocity] using! intrinsicGeodesic_speedSq_eq gExt hExt x u t
    calc
      _ ≤ K * gExt.inner (γ t) v v *
          gExt.inner (γ t) (Variation.curveVelocity γ t) (Variation.curveVelocity γ t) :=
        hcurv (γ t) (hfence t (Ioo_subset_Icc_self ht)) v (Variation.curveVelocity γ t)
      _ = (K * gExt.inner x u u) * gExt.inner (γ t) v v := by rw [hspeed]; ring)
  exact hinj

private theorem extension_launch_not_conj
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B K : ℝ}
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita gExt) z) v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w)
    (x u : E) (hsmall : K * gExt.inner x u u < (Real.pi / 2) ^ 2) :
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  (∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x u t‖ < B) →
  ¬ IsConjVec gExt hExt x u := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  intro hfence
  have hinj := extension_launch_derivative_injective gExt hcomplete hcurv x u hsmall hfence
  have heq : (fun b : E => expMapIntrinsic gExt hExt x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm b)) =
      (fun b : E => expMap gExt x (show TangentSpace 𝓘(ℝ, E) x from b)) := by
    funext b
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply, expMap_eq_expMapIntrinsic gExt hExt x]
  have hinj' : Function.Injective
      (fderiv ℝ (fun b : E => expMap gExt x (show TangentSpace 𝓘(ℝ, E) x from b)) u) := by
    simpa only [mfderiv_eq_fderiv] using! hinj
  have hintr : Function.Injective
      (fderiv ℝ (fun b : E => expMapIntrinsic gExt hExt x
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm b)) u) := by
    rw [heq]
    exact hinj'
  intro hnot
  apply hnot
  simpa only [mfderiv_eq_fderiv, tangentSpaceModelContinuousLinearEquiv_symm_apply] using! hintr

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem intrinsicGeodesic_initial_velocity_eq_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B K a L : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita gExt) z) v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w)
    (hbudget : a + L < B) (h2aL : 2 * a < L)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2) :
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  ∀ x y u v : E, ‖x‖ ≤ a → ‖y‖ ≤ a →
    Real.sqrt (gExt.inner x u u) < L → Real.sqrt (gExt.inner x v v) < L →
    intrinsicGeodesic gExt hExt x u 1 = y →
    intrinsicGeodesic gExt hExt x v 1 = y → u = v := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  intro x y u v hx hy huL hvL huEnd hvEnd
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hLpos : 0 < L := (Real.sqrt_nonneg _).trans_lt huL
  have hsmaller {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L ^ 2) :
      K * r < (Real.pi / 2) ^ 2 := by
    by_cases hK : 0 ≤ K
    · exact (mul_le_mul_of_nonneg_left hrL hK).trans_lt hsmall
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK) hr).trans_lt
        (sq_pos_of_pos (div_pos Real.pi_pos (by norm_num)))
  have hcore : ∀ x₀ y₀ q : E, ‖x₀‖ ≤ a → ‖y₀‖ ≤ a →
      Real.sqrt (gExt.inner x₀ q q) ≤ L → intrinsicGeodesic gExt hExt x₀ q 1 = y₀ →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x₀ q t‖ ≤ a := by
    intro x₀ y₀ q hx₀ hy₀ hq hend
    exact norm_intrinsicGeodesic_le_of_pullback_extension g p gExt hcomplete hdom hmetric hcurv
      hbudget (hsmaller (sq_nonneg _) ((sq_le_sq₀ (by positivity) hLpos.le).mpr (by linarith)))
      hx₀ hy₀ q hq hend
  have hnot : ∀ x₀ q : E, ‖x₀‖ ≤ a → Real.sqrt (gExt.inner x₀ q q) ≤ L →
      ¬ IsConjVec gExt hExt x₀ q := by
    intro x₀ q hx₀ hq
    have hqnn := metric_inner_self_nonneg gExt x₀ q
    have hqSq : gExt.inner x₀ q q ≤ L ^ 2 := by
      nlinarith [Real.sq_sqrt hqnn, Real.sqrt_nonneg (gExt.inner x₀ q q)]
    apply extension_launch_not_conj gExt hcomplete hcurv x₀ q (hsmaller hqnn hqSq)
    have hf := extension_launch_fenced g p gExt hcomplete hdom hmetric x₀ q (by linarith)
    simpa only [MapsTo, Metric.mem_ball, dist_zero_right] using! hf
  by_contra huv
  obtain ⟨x₁, u₁, _, hu₁, _, T, hT, hperiod, hstay⟩ :=
    exists_periodic_geodesic_of_expMapIntrinsic_eq gExt hcomplete hcore hnot x y u v
      hx hy huL hvL huEnd hvEnd huv
  let γ := intrinsicGeodesic gExt hExt x₁ u₁
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) (2 * T))
      ((fun z : E => (1 / 2 : ℝ) * ‖z‖ ^ 2) ∘ γ) :=
    strictConvexOn_half_norm_sq_of_pullback_extension g p gExt hcomplete hdom hmetric hcurv
      (intrinsicGeodesic_contMDiff gExt hExt x₁ u₁)
      (by simpa only [interior_Icc] using
        (intrinsicGeodesic_isGeodesic gExt hExt x₁ u₁).isGeodesicOn (Ioo (0 : ℝ) (2 * T)))
      (convex_Icc (0 : ℝ) (2 * T))
      (fun t ht => (hstay t (by simpa only [interior_Icc] using ht)).trans_lt (by linarith))
      (fun t ht => hsmaller (sq_nonneg _)
        ((sq_le_sq₀ (norm_nonneg _) hLpos.le).mpr
          ((hstay t (by simpa only [interior_Icc] using ht)).trans (by linarith))))
      (fun t _ => intrinsicGeo_velocity_ne gExt hExt x₁ u₁ hu₁ t)
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  have hlt := hstrict.2 ⟨le_rfl, h2T.le⟩ ⟨h2T.le, le_rfl⟩
    (ne_of_lt h2T) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmid : (1 / 2 : ℝ) • (0 : ℝ) + (1 / 2 : ℝ) • (2 * T) = T := by
    simp only [smul_eq_mul]; ring
  rw [hmid] at hlt
  have h0T : γ 0 = γ T := by simpa only [zero_add] using (hperiod 0).symm
  have hT2 : γ T = γ (2 * T) := by simpa only [← two_mul] using (hperiod T).symm
  simp only [Function.comp_apply, smul_eq_mul] at hlt
  rw [h0T, ← hT2] at hlt
  linarith

end Injectivity

section Germ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_branchEnergy_riemannianEDistOf_germ_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M) (U : TopologicalSpace.Opens E)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (framedExpMap g p) U)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B K a L : ℝ}
    (hball : Metric.closedBall (0 : E) B ⊆ (U : Set E))
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ z : E, ‖z‖ ≤ B → ∀ v w : E,
      gExt.inner z v w = g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w))
    (hcurv : ∀ z : E, ‖z‖ < B → ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      gExt.inner z
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita gExt) z) v w w) v ≤
        K * gExt.inner z v v * gExt.inner z w w)
    (hbudget : a + L < B) (h2aL : 2 * a < L)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (pt q : U) (hpt : ‖(pt : E)‖ ≤ a) (hq : ‖(q : E)‖ ≤ a) :
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc)
  let u := minimizingVec gExt hExt (pt : E) (q : E)
  ∃ β : ExponentialInverseBranch gExt hExt (pt : E),
    (u : E) ∈ β.hom.source ∧
    (fun z : U => branchEnergy gExt β (z : E)) =ᶠ[𝓝 q]
      (fun z : U => (1 / 2 : ℝ) * (riemannianEDistOf gPull pt z).toReal ^ 2) := by
  dsimp only
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc)
  let u := minimizingVec gExt hExt (pt : E) (q : E)
  have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans hpt
  have hLpos : 0 < L := by linarith
  have haB : a < B := by linarith
  have hdist : riemannianEDistOf gExt (pt : E) (q : E) ≤ ENNReal.ofReal (2 * a) :=
    (riemannianEDistOf_le_norm_add_norm_of_pullback_extension
      g p gExt hdom hmetric (hpt.trans haB.le) (hq.trans haB.le)).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
  have hdistReal : (riemannianEDistOf gExt (pt : E) (q : E)).toReal ≤ 2 * a :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hdist
  have huLen : Real.sqrt (gExt.inner (pt : E) u u) =
      (riemannianEDistOf gExt (pt : E) (q : E)).toReal :=
    minimizingVec_len gExt hExt (pt : E) (q : E)
  have huL : Real.sqrt (gExt.inner (pt : E) u u) < L := by
    rw [huLen]
    exact hdistReal.trans_lt h2aL
  have hnot : ¬ IsConjVec gExt hExt (pt : E) (u : E) := by
    have hunn := metric_inner_self_nonneg gExt (pt : E) u
    have huSq : gExt.inner (pt : E) u u ≤ L ^ 2 := by
      nlinarith [Real.sq_sqrt hunn, Real.sqrt_nonneg (gExt.inner (pt : E) u u)]
    have hsmallu : K * gExt.inner (pt : E) u u < (Real.pi / 2) ^ 2 := by
      by_cases hK : 0 ≤ K
      · exact (mul_le_mul_of_nonneg_left huSq hK).trans_lt hsmall
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK) hunn).trans_lt
          (sq_pos_of_pos (div_pos Real.pi_pos (by norm_num)))
    apply extension_launch_not_conj gExt hcomplete hcurv (pt : E) (u : E) hsmallu
    have hfence := extension_launch_fenced g p gExt hcomplete hdom hmetric (pt : E) u
      (by linarith : ‖(pt : E)‖ + Real.sqrt (gExt.inner (pt : E) u u) < B)
    simpa only [MapsTo, Metric.mem_ball, dist_zero_right] using! hfence
  have hbranch : ∃ β : ExponentialInverseBranch gExt hExt (pt : E), (u : E) ∈ β.hom.source := by
    with_unfolding_all
      exact branch_of_not_conj gExt hExt (p := (pt : E)) (u := (u : E)) hnot
  obtain ⟨β, huβ⟩ := hbranch
  have huniq : ∀ v : TangentSpace 𝓘(ℝ, E) (pt : E),
      expMapIntrinsic gExt hExt (pt : E) v = (q : E) →
      Real.sqrt (gExt.inner (pt : E) v v) =
        (riemannianEDist 𝓘(ℝ, E) (pt : E) (q : E)).toReal → v = u := by
    intro v hv hlen
    have hvL : Real.sqrt (gExt.inner (pt : E) v v) < L := by
      rw [hlen]
      exact hdistReal.trans_lt h2aL
    exact intrinsicGeodesic_initial_velocity_eq_of_pullback_extension
      g p gExt hcomplete hdom hmetric hcurv hbudget h2aL hsmall
      (pt : E) (q : E) (v : E) (u : E) hpt hq hvL huL hv
      (minimizingVec_exp gExt hExt (pt : E) (q : E))
  have hmem : ∀ᶠ z in 𝓝 (q : E), (minimizingVec gExt hExt (pt : E) z : E) ∈ β.hom.source :=
    tendsto_minimizingVec_of_unique gExt hExt huniq (β.hom.open_source.mem_nhds huβ)
  have hgerm := Exponential.branchEnergy_min_germ gExt hExt β hmem
  have hgermSub : (fun z : U => branchEnergy gExt β (z : E)) =ᶠ[𝓝 q]
      (fun z : U => (1 / 2 : ℝ) * (riemannianEDistOf gExt (pt : E) (z : E)).toReal ^ 2) := by
    exact hgerm.comp_tendsto (continuous_subtype_val.tendsto q)
  have hbudget0 : ENNReal.ofReal ‖(pt : E)‖ + riemannianEDistOf gExt (pt : E) (q : E) <
      ENNReal.ofReal B := by
    apply (add_le_add (ENNReal.ofReal_le_ofReal hpt) hdist).trans_lt
    rw [← ENNReal.ofReal_add ha (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hed : Continuous (fun z : E => riemannianEDistOf gExt (pt : E) z) := by
    exact (continuous_riemannianEDist_to (I := 𝓘(ℝ, E)) (pt : E)).congr
      (fun _ => Manifold.riemannianEDist_comm)
  have hc : Continuous (fun z : U =>
      ENNReal.ofReal ‖(pt : E)‖ + riemannianEDistOf gExt (pt : E) (z : E)) :=
    continuous_const.add (hed.comp continuous_subtype_val)
  have hnear : ∀ᶠ (z : U) in 𝓝 q,
      ENNReal.ofReal ‖(pt : E)‖ + riemannianEDistOf gExt (pt : E) (z : E) <
        ENNReal.ofReal B := hc.continuousAt (Iio_mem_nhds hbudget0)
  refine ⟨β, huβ, ?_⟩
  filter_upwards [hgermSub, hnear] with z hz hbudgetz
  rw [riemannianEDistOf_eq_of_pullback_extension g p U hloc gExt hball hdom
    (fun z hz => hmetric z hz) pt z hbudgetz]
  exact hz

end Germ

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
