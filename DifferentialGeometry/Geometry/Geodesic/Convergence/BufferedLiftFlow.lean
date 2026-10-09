import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedGeodesicEquation
import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SmoothSpray

/-!
# The literal inverse lift is the actual source geodesic flow

An open neighborhood of the complete minimizing interval lies in the same inverse-map domain.
The native integral-curve uniqueness theorem identifies its velocity lift with the source flow,
including the endpoint and a zero-length interval, without completeness of the source metric.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem inverseIntrinsicGeodesic_isMIntegralCurveOn
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w =
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    (p : M) (v : TangentSpace I p) :
    IsMIntegralCurveOn
      (DifferentialGeometry.velocityLift (fun s => j.symm (intrinsicGeodesic g hNorm p v s)))
      h.geodesicSpray ((intrinsicGeodesic g hNorm p v) ⁻¹' j.target) := by
  let gamma := intrinsicGeodesic g hNorm p v
  have hJ : IsOpen (gamma ⁻¹' j.target) :=
    j.open_target.preimage (intrinsicGeodesic_contMDiff g hNorm p v).continuous
  have hgeo : IsGeodesicOn h (fun s => j.symm (gamma s)) (gamma ⁻¹' j.target) := by
    intro t ht
    have hAt := intrinsicGeodesic_inverse_isGeodesicAt h g hNorm j hmetric p v ht
    exact hAt.hasGeodesicEquationAt
  have hcont : ContinuousOn (fun s => j.symm (gamma s)) (gamma ⁻¹' j.target) :=
    j.symm.contMDiffOn.continuousOn.comp
      (intrinsicGeodesic_contMDiff g hNorm p v).continuous.continuousOn (fun t ht => ht)
  simpa only [h.geodesicSpray_eq_geodesicVectorField_fun] using
    isMIntegralCurveOn_velocityLift h hJ hgeo hcont

theorem inverseIntrinsicGeodesic_eq_geodesicFlow_on_interval
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w =
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    (p : M) (v : TangentSpace I p) {L : ℝ} (hL : 0 ≤ L)
    (hfull : ∀ t ∈ Icc 0 L, intrinsicGeodesic g hNorm p v t ∈ j.target) :
    let alpha := fun s => j.symm (intrinsicGeodesic g hNorm p v s)
    ∀ t ∈ Icc 0 L,
      (DifferentialGeometry.velocityLift alpha 0, t) ∈ h.geodesicFlowDomain ∧
      h.geodesicFlow (DifferentialGeometry.velocityLift alpha 0) t =
        DifferentialGeometry.velocityLift alpha t := by
  dsimp only
  let gamma := intrinsicGeodesic g hNorm p v
  let J := gamma ⁻¹' j.target
  have hJ : IsOpen J :=
    j.open_target.preimage (intrinsicGeodesic_contMDiff g hNorm p v).continuous
  have h0 : (0 : ℝ) ∈ J := hfull 0 ⟨le_rfl, hL⟩
  have hLast : L ∈ J := hfull L ⟨hL, le_rfl⟩
  obtain ⟨epsilon, hepsilon, hzero⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds h0)
  obtain ⟨delta, hdelta, hlast⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds hLast)
  have hsub : Ioo (-epsilon) (L + delta) ⊆ J := by
    intro t ht
    by_cases ht0 : t < 0
    · apply hzero
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg ht0]
      linarith [ht.1]
    · by_cases htL : L < t
      · apply hlast
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr htL)]
        linarith [ht.2]
      · exact hfull t ⟨le_of_not_gt ht0, le_of_not_gt htL⟩
  have hzeroI : (0 : ℝ) ∈ Ioo (-epsilon) (L + delta) := by
    constructor <;> linarith
  have hclosedI : Icc 0 L ⊆ Ioo (-epsilon) (L + delta) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hon := (inverseIntrinsicGeodesic_isMIntegralCurveOn h g hNorm j hmetric p v).mono hsub
  intro t ht
  refine ⟨hon.subset_maximalIntegralCurveInterval hzeroI rfl (hclosedI ht), ?_⟩
  exact hon.eqOn_maximalIntegralCurve
    ((h.contMDiff_geodesicSpray (r := ⊤)).of_le (by exact_mod_cast le_top))
    hzeroI rfl (hclosedI ht)

theorem bufferedMinimizingLift_eq_geodesicFlow
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞) (n : N) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 10)
    (hcpt : IsCompact (riemannianClosedBallOf h n 10))
    (hsrc : riemannianClosedBallOf h n 10 ⊆ j.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf h n 10, ∀ v : TangentSpace I x,
      (1 - lam) ^ 2 * h.inner x v v ≤
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v))
    (hupper : ∀ x ∈ riemannianClosedBallOf h n 10, ∀ v : TangentSpace I x,
      g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v) ≤
        (1 + lam) ^ 2 * h.inner x v v)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w =
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    {q : N} (hq : q ∈ riemannianBallOf h n 3)
    {w : TangentSpace I (j q)} (hw : w ∈ inwardMinimizingDirections g hNorm (j n) (j q)) :
    let alpha := fun s => j.symm (intrinsicGeodesic g hNorm (j q) w s)
    ∀ t ∈ Icc 0 (dist (j n) (j q)),
      (DifferentialGeometry.velocityLift alpha 0, t) ∈ h.geodesicFlowDomain ∧
      h.geodesicFlow (DifferentialGeometry.velocityLift alpha 0) t =
        DifferentialGeometry.velocityLift alpha t := by
  dsimp only
  apply inverseIntrinsicGeodesic_eq_geodesicFlow_on_interval h g hNorm j hmetric
    (j q) w dist_nonneg
  intro t ht
  obtain ⟨x, hx, heq⟩ := intrinsicMinimizingGeodesic_mem_buffered_image
    h g hNorm j n hlam0 hlam hcpt hsrc hlower hupper hq hw ht
  apply heq ▸ j.map_source (hsrc ?_)
  change riemannianEDistOf h n x ≤ ENNReal.ofReal 10
  exact le_of_lt (lt_trans hx (by norm_num))

omit [IsManifold I ∞ N] [T3Space N] in
theorem inverseIntrinsicGeodesic_velocityLift_zero
    (g : SmoothRiemannianMetric I M) (hNorm : IsMetricNorm g)
    (j : PartialDiffeomorph I I N M ∞) (q : N) (hq : q ∈ j.source)
    (w : TangentSpace I (j q)) :
    let alpha := fun s => j.symm (intrinsicGeodesic g hNorm (j q) w s)
    (DifferentialGeometry.velocityLift (I := I) alpha 0).proj = q ∧
      ((DifferentialGeometry.velocityLift (I := I) alpha 0).snd : E) =
        mfderiv I I (j.symm : M → N) (j q) w := by
  let gamma := intrinsicGeodesic g hNorm (j q) w
  have hgamma : gamma 0 = j q := intrinsicGeodesic_zero g hNorm (j q) w
  have hj : MDifferentiableAt I I (j.symm : M → N) (gamma 0) := by
    rw [hgamma]
    exact j.symm.mdifferentiableAt (by simp) (j.map_source hq)
  have hc := mfderiv_comp_apply 0 hj
    ((intrinsicGeodesic_contMDiff g hNorm (j q) w).mdifferentiable (by simp) 0) (1 : ℝ)
  refine ⟨(congrArg (j.symm : M → N) hgamma).trans (j.left_inv hq), ?_⟩
  change (mfderiv 𝓘(ℝ, ℝ) I (fun s => j.symm (gamma s)) 0 (1 : ℝ) : E) =
    (mfderiv I I (j.symm : M → N) (j q) w : E)
  have hvel : (mfderiv I I (j.symm : M → N) (gamma 0)
      (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ)) : E) =
      (mfderiv I I (j.symm : M → N) (gamma 0) w : E) :=
    congrArg (fun u : E => (mfderiv I I (j.symm : M → N) (gamma 0) u : E))
      (intrinsicGeodesic_mfderiv_zero g hNorm (j q) w)
  have hbase : (mfderiv I I (j.symm : M → N) (gamma 0) w : E) =
      (mfderiv I I (j.symm : M → N) (j q) w : E) :=
    congrArg (fun y : M => (mfderiv I I (j.symm : M → N) y : E →L[ℝ] E) w) hgamma
  exact hc.trans (hvel.trans hbase)

private instance realFinrankPositive : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realRiemannianContinuous :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realMetricNorm.isContinuousRiemannianBundle

theorem realInverse_geodesicFlow_on_interval (q : ℝ) (w : TangentSpace 𝓘(ℝ, ℝ) q)
    {T : ℝ} (hT : 0 ≤ T) :
    let g := euclideanMetric (E := ℝ)
    let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
    let alpha := fun s => j.symm (intrinsicGeodesic g realMetricNorm q w s)
    ∀ t ∈ Icc 0 T,
      (DifferentialGeometry.velocityLift alpha 0, t) ∈ g.geodesicFlowDomain ∧
      g.geodesicFlow (DifferentialGeometry.velocityLift alpha 0) t =
        DifferentialGeometry.velocityLift alpha t := by
  let g := euclideanMetric (E := ℝ)
  let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
  apply inverseIntrinsicGeodesic_eq_geodesicFlow_on_interval g g realMetricNorm j
  · intro x hx v w'
    change g.inner x v w' = g.inner x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x w')
    rw [mfderiv_id]
    rfl
  · exact hT
  · intro t ht
    trivial

end DifferentialGeometry.Geometry.Riemannian.Geodesic
