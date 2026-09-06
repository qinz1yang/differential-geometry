import DifferentialGeometry.Analysis.Sobolev.DirichletHs.EnergyDuality
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormCompletion
import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.CometricDifferenceRaisedGreenPairing
import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance smoothScalarDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (SmoothScalarDirichlet q) (SmoothScalarDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

private local instance h1ComplDirichletBilinearSeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

omit [T2Space M] [CompactSpace M] in
private lemma metricComparisonEndomorphism_gradFun
    (q h : SmoothRiemannianMetric (I_half n) M)
    (f : M → ℝ) (x : M) :
    metricComparisonEndomorphism (I := I_half n) q h x
        (gradFun (I := I_half n) q f x) =
      gradFun (I := I_half n) h f x := by
  apply gradFun_unique h f
  intro v
  rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_inner,
    cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  exact gradFun_metricDual q f x v

omit [T2Space M] [CompactSpace M] in
private lemma dirichletCometricDifferenceForm_integrand
    (q h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) (x : M) :
    h.inner x (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h v.toFun x) -
        q.inner x (gradFun (I := I_half n) q u.toFun x)
          (gradFun (I := I_half n) q v.toFun x) =
      q.inner x
        (metricComparisonDifferenceEndomorphism (I := I_half n) q h x
          (gradFun (I := I_half n) q u.toFun x))
        (gradFun (I := I_half n) q v.toFun x) := by
  rw [← metricComparisonEndomorphism_gradFun q h u.toFun x,
    ← metricComparisonEndomorphism_gradFun q h v.toFun x]
  rw [h.symm x
    (metricComparisonEndomorphism (I := I_half n) q h x
      (gradFun (I := I_half n) q u.toFun x))
    (metricComparisonEndomorphism (I := I_half n) q h x
      (gradFun (I := I_half n) q v.toFun x))]
  rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_inner,
    cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [q.symm x
    (gradFun (I := I_half n) q v.toFun x)
    (metricComparisonEndomorphism (I := I_half n) q h x
      (gradFun (I := I_half n) q u.toFun x))]
  rw [metricComparisonEndomorphism_eq_diff_add_id, map_add, add_apply]
  ring

def dirichletCometricDifferenceForm
    (q h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, q.inner x
      (metricComparisonDifferenceEndomorphism (I := I_half n) q h x
        (gradFun (I := I_half n) q u.toFun x))
      (gradFun (I := I_half n) q v.toFun x)
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)

private lemma dirichletCometricDifferenceForm_integrable
    (q h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    Integrable (fun x => q.inner x
        (metricComparisonDifferenceEndomorphism (I := I_half n) q h x
          (gradFun (I := I_half n) q u.toFun x))
        (gradFun (I := I_half n) q v.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  let uqh := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h u.smooth u.interior_support
  let vqh := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h v.smooth v.interior_support
  let uqq := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) q u.smooth u.interior_support
  let vqq := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) q v.smooth v.interior_support
  have hcont : Continuous (fun x : M => h.inner x (uqh x) (vqh x) -
      q.inner x (uqq x) (vqq x)) :=
    (TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I_half n) h uqh vqh).sub
      (TangentBundle.continuous_g_inner_of_smooth_sections
        (I := I_half n) q uqq vqq)
  have hcont' : Continuous (fun x : M =>
      h.inner x (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h v.toFun x) -
        q.inner x (gradFun (I := I_half n) q u.toFun x)
          (gradFun (I := I_half n) q v.toFun x)) := by
    simpa only [uqh, vqh, uqq, vqq,
      DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply] using
      hcont
  let _ : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) q
  have hint : Integrable (fun x : M =>
      h.inner x (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h v.toFun x) -
        q.inner x (gradFun (I := I_half n) q u.toFun x)
          (gradFun (I := I_half n) q v.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    hcont'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  exact dirichletCometricDifferenceForm_integrand q h u v x

theorem dirichletCometricDifferenceForm_time_cont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    (q : SmoothRiemannianMetric (I_half n) M)
    {K : Set ℝ} (hK : IsCompact K) (hKreg : K ⊆ D.regular)
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn
      (fun t => dirichletCometricDifferenceForm q (G.metric t) u v) K := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) q
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) q
  let c : ℝ := ∫ x, q.inner x
    (gradFun (I := I_half n) q u.toFun x)
    (gradFun (I := I_half n) q v.toFun x) ∂μ
  have hmove : ContinuousOn
      (fun t : ℝ => ∫ x, (G.metric t).inner x
        (gradFun (I := I_half n) (G.metric t) u.toFun x)
        (gradFun (I := I_half n) (G.metric t) v.toFun x) ∂μ) K :=
    integral_contOn_cpt μ
      (fun t x => (G.metric t).inner x
        (gradFun (I := I_half n) (G.metric t) u.toFun x)
        (gradFun (I := I_half n) (G.metric t) v.toFun x)) hK
      (DifferentialGeometry.Geometry.Operator.WithBoundary.gradient_inner_continuousOn_of_tsupport_subset_interior
        hG hKreg u.smooth v.smooth u.interior_support)
  have heq (t : ℝ) :
      dirichletCometricDifferenceForm q (G.metric t) u v =
        (∫ x, (G.metric t).inner x
          (gradFun (I := I_half n) (G.metric t) u.toFun x)
          (gradFun (I := I_half n) (G.metric t) v.toFun x) ∂μ) - c := by
    have hmoveInt : Integrable (fun x : M => (G.metric t).inner x
        (gradFun (I := I_half n) (G.metric t) u.toFun x)
        (gradFun (I := I_half n) (G.metric t) v.toFun x)) μ :=
      (DifferentialGeometry.Geometry.Operator.WithBoundary.continuous_g_inner_gradFun_gradFun
        (G.metric t) u.smooth v.smooth).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hqInt : Integrable (fun x : M => q.inner x
        (gradFun (I := I_half n) q u.toFun x)
        (gradFun (I := I_half n) q v.toFun x)) μ :=
      (DifferentialGeometry.Geometry.Operator.WithBoundary.continuous_g_inner_gradFun_gradFun
        q u.smooth v.smooth).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    unfold dirichletCometricDifferenceForm
    change (∫ x, q.inner x
        (metricComparisonDifferenceEndomorphism (I := I_half n) q (G.metric t) x
          (gradFun (I := I_half n) q u.toFun x))
        (gradFun (I := I_half n) q v.toFun x) ∂μ) = _
    rw [show c = ∫ x, q.inner x
      (gradFun (I := I_half n) q u.toFun x)
      (gradFun (I := I_half n) q v.toFun x) ∂μ from rfl]
    rw [← integral_sub hmoveInt hqInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (dirichletCometricDifferenceForm_integrand q (G.metric t) u v x).symm
  refine (hmove.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => c) K)).congr ?_
  intro t _
  exact heq t

theorem dirichletCometricDifferenceForm_add_left
    (q h : SmoothRiemannianMetric (I_half n) M)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceForm q h (u₁ + u₂) v =
      dirichletCometricDifferenceForm q h u₁ v +
        dirichletCometricDifferenceForm q h u₂ v := by
  unfold dirichletCometricDifferenceForm
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) q (u₁ + u₂).toFun x =
        gradFun (I := I_half n) q u₁.toFun x +
          gradFun (I := I_half n) q u₂.toFun x := by
    intro x
    exact DifferentialGeometry.Geometry.Connection.gradFun_add (I := I_half n) q
      (u₁.smooth.mdifferentiable (by simp) x)
      (u₂.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_add, add_apply]
  exact integral_add (dirichletCometricDifferenceForm_integrable q h u₁ v)
    (dirichletCometricDifferenceForm_integrable q h u₂ v)

theorem dirichletCometricDifferenceForm_smul_left
    (q h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceForm q h (c • u) v =
      c * dirichletCometricDifferenceForm q h u v := by
  unfold dirichletCometricDifferenceForm
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) q (c • u).toFun x =
        c • gradFun (I := I_half n) q u.toFun x := by
    intro x
    change gradFun (I := I_half n) q (c • u.toFun) x =
      c • gradFun (I := I_half n) q u.toFun x
    exact DifferentialGeometry.Geometry.Connection.gradFun_const_smul (I := I_half n) q c
      (u.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_smul]
  exact integral_const_mul c _

theorem dirichletCometricDifferenceForm_symm
    (q h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceForm q h u v =
      dirichletCometricDifferenceForm q h v u := by
  unfold dirichletCometricDifferenceForm
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change q.inner x
      (metricComparisonDifferenceEndomorphism (I := I_half n) q h x
        (gradFun (I := I_half n) q u.toFun x))
      (gradFun (I := I_half n) q v.toFun x) =
    q.inner x
      (metricComparisonDifferenceEndomorphism (I := I_half n) q h x
        (gradFun (I := I_half n) q v.toFun x))
      (gradFun (I := I_half n) q u.toFun x)
  rw [metricComparisonDifferenceEndomorphism_g0_self_adjoint
    (I := I_half n) q h x
    (gradFun (I := I_half n) q u.toFun x)
    (gradFun (I := I_half n) q v.toFun x)]
  exact q.symm x _ _

theorem dirichletCometricDifferenceForm_add_right
    (q h : SmoothRiemannianMetric (I_half n) M)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceForm q h u (v₁ + v₂) =
      dirichletCometricDifferenceForm q h u v₁ +
        dirichletCometricDifferenceForm q h u v₂ := by
  rw [dirichletCometricDifferenceForm_symm,
    dirichletCometricDifferenceForm_add_left,
    dirichletCometricDifferenceForm_symm q h v₁ u,
    dirichletCometricDifferenceForm_symm q h v₂ u]

theorem dirichletCometricDifferenceForm_smul_right
    (q h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceForm q h u (c • v) =
      c * dirichletCometricDifferenceForm q h u v := by
  rw [dirichletCometricDifferenceForm_symm,
    dirichletCometricDifferenceForm_smul_left,
    dirichletCometricDifferenceForm_symm q h v u]

private def dirichletCometricDifferenceFormRoot
    (q : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) (x : M) : ℝ :=
  Real.sqrt (q.inner x
    (gradFun (I := I_half n) q u.toFun x)
    (gradFun (I := I_half n) q u.toFun x))

private lemma dirichletCometricDifferenceFormRoot_memLp
    (q : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    MemLp (dirichletCometricDifferenceFormRoot q u) 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  have hcont : Continuous (dirichletCometricDifferenceFormRoot q u) :=
    Real.continuous_sqrt.comp
      (DifferentialGeometry.Geometry.Operator.WithBoundary.continuous_g_inner_gradFun_gradFun
        q u.smooth u.smooth)
  let _ : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts
      (I := I_half n) (M := M) q
  exact hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [T2Space M] [CompactSpace M] in
private lemma dirichletCometricDifferenceFormRoot_sq
    (q : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) (x : M) :
    dirichletCometricDifferenceFormRoot q u x ^ 2 = q.inner x
      (gradFun (I := I_half n) q u.toFun x)
      (gradFun (I := I_half n) q u.toFun x) := by
  apply Real.sq_sqrt
  exact WithBoundary.SmoothRiemannianMetric_inner_self_nonneg q x _

private lemma dirichletCometricDifferenceFormRoot_eLpNorm_toReal_le_norm
    (q : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    (eLpNorm (dirichletCometricDifferenceFormRoot q u) 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)).toReal ≤ ‖u‖ := by
  let hu := dirichletCometricDifferenceFormRoot_memLp q u
  let U := hu.toLp (dirichletCometricDifferenceFormRoot q u)
  have hUsq : ‖U‖ ^ 2 = dirichletEnergy q u u := by
    have hinner := real_inner_self_eq_norm_sq U
    rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)] at hinner
    have hae : (fun x : M =>
        @inner ℝ _ _ ((U : Lp ℝ 2 _) x) ((U : Lp ℝ 2 _) x)) =ᵐ[
          riemannianVolumeMeasure (I := I_half n) (M := M) q]
        (fun x => dirichletCometricDifferenceFormRoot q u x ^ 2) := by
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx]
      rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs]
      change |Real.sqrt _| ^ 2 = Real.sqrt _ ^ 2
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [integral_congr_ae hae] at hinner
    rw [show (fun x => dirichletCometricDifferenceFormRoot q u x ^ 2) = fun x =>
        q.inner x (gradFun (I := I_half n) q u.toFun x)
          (gradFun (I := I_half n) q u.toFun x) from
      funext (dirichletCometricDifferenceFormRoot_sq q u)] at hinner
    exact hinner.symm
  have hdecomp : ‖u‖ ^ 2 = dirichletMass q u u + dirichletEnergy q u u := by
    rw [u.norm_sq_eq_inner_self]
    rfl
  have henergy : dirichletEnergy q u u ≤ ‖u‖ ^ 2 := by
    have hmass := dirichletMass_self_nonneg q u
    linarith
  have hU : ‖U‖ ≤ ‖u‖ := by
    exact (abs_le_of_sq_le_sq' (hUsq.trans_le henergy) (norm_nonneg _)).2
  have hUnorm : ‖U‖ = (eLpNorm (dirichletCometricDifferenceFormRoot q u) 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)).toReal :=
    Lp.norm_toLp _ hu
  rw [hUnorm] at hU
  exact hU

theorem abs_dirichletCometricDifferenceForm_le_norm
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta)
    (u v : SmoothScalarDirichlet q) :
    |dirichletCometricDifferenceForm q h u v| ≤
      (delta / (1 - delta)) * ‖u‖ * ‖v‖ := by
  let fu := dirichletCometricDifferenceFormRoot q u
  let fv := dirichletCometricDifferenceFormRoot q v
  have hfu := dirichletCometricDifferenceFormRoot_memLp q u
  have hfv := dirichletCometricDifferenceFormRoot_memLp q v
  have hprod : Integrable (fun x => fu x * fv x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
    change Integrable (fu * fv)
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)
    exact hfu.integrable_mul hfv
  have hholder : (∫ x, fu x * fv x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)) ≤
      (eLpNorm fu 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) q)).toReal *
      (eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) q)).toReal := by
    have hbound := DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two hfu hfv
    rw [abs_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hbound
    exact hbound
  have htie : ∀ (x : M) (a b : TangentSpace (I_half n) x),
      h.inner x a b = q.inner x a b + (h.inner x - q.inner x) a b := by
    intro x a b
    simp only [sub_apply]
    ring
  have hkappa : 0 ≤ delta / (1 - delta) :=
    div_nonneg hdelta_nn (by linarith)
  unfold dirichletCometricDifferenceForm
  calc
    |∫ x, q.inner x
        (metricComparisonDifferenceEndomorphism (I := I_half n) q h x
          (gradFun (I := I_half n) q u.toFun x))
        (gradFun (I := I_half n) q v.toFun x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)| ≤
      ∫ x, |q.inner x
        (metricComparisonDifferenceEndomorphism (I := I_half n) q h x
          (gradFun (I := I_half n) q u.toFun x))
        (gradFun (I := I_half n) q v.toFun x)|
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, (delta / (1 - delta)) * (fu x * fv x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (hprod.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
      simpa only [fu, fv, dirichletCometricDifferenceFormRoot] using
        abs_inner_metricComparisonDifferenceEndomorphism_le
          q h (fun y => h.inner y - q.inner y) htie
          hdelta_lt hdelta_nn hdelta x
          (gradFun (I := I_half n) q u.toFun x)
          (gradFun (I := I_half n) q v.toFun x)
    _ = (delta / (1 - delta)) * (∫ x, fu x * fv x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)) := by
      rw [integral_const_mul]
    _ ≤ (delta / (1 - delta)) *
        ((eLpNorm fu 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) q)).toReal *
        (eLpNorm fv 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) q)).toReal) :=
      mul_le_mul_of_nonneg_left hholder hkappa
    _ ≤ (delta / (1 - delta)) * (‖u‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul
          (dirichletCometricDifferenceFormRoot_eLpNorm_toReal_le_norm q u)
          (dirichletCometricDifferenceFormRoot_eLpNorm_toReal_le_norm q v)
          ENNReal.toReal_nonneg (norm_nonneg u)) hkappa
    _ = (delta / (1 - delta)) * ‖u‖ * ‖v‖ := by ring

noncomputable def dirichletCometricDifferenceFormSmooth
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta) :
    SmoothScalarDirichlet q →L[ℝ] SmoothScalarDirichlet q →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (dirichletCometricDifferenceForm q h)
      (dirichletCometricDifferenceForm_add_left q h)
      (dirichletCometricDifferenceForm_smul_left q h)
      (dirichletCometricDifferenceForm_add_right q h)
      (dirichletCometricDifferenceForm_smul_right q h))
    (delta / (1 - delta)) ?_
  intro u v
  rw [Real.norm_eq_abs]
  exact abs_dirichletCometricDifferenceForm_le_norm q h
    hdelta_lt hdelta_nn hdelta u v

theorem dirichletCometricDifferenceFormSmooth_apply
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta)
    (u v : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceFormSmooth q h hdelta_lt hdelta_nn hdelta u v =
      dirichletCometricDifferenceForm q h u v := rfl

theorem norm_dirichletCometricDifferenceFormSmooth_le
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta) :
    ‖dirichletCometricDifferenceFormSmooth q h hdelta_lt hdelta_nn hdelta‖ ≤
      delta / (1 - delta) := by
  apply LinearMap.mkContinuous₂_norm_le
  exact div_nonneg hdelta_nn (by linarith)

noncomputable def dirichletCometricDifferenceFormCompl
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
  DifferentialGeometry.Analysis.bilinearFromCompletion
    (dirichletCometricDifferenceFormSmooth q h hdelta_lt hdelta_nn hdelta)

theorem dirichletCometricDifferenceFormCompl_apply_smooth
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta)
    (u v : SmoothScalarDirichlet q) :
    dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta
        (smoothToH1ComplDirichlet q u) (smoothToH1ComplDirichlet q v) =
      dirichletCometricDifferenceForm q h u v := by
  change DifferentialGeometry.Analysis.bilinearFromCompletion
      (dirichletCometricDifferenceFormSmooth q h hdelta_lt hdelta_nn hdelta)
      (u : UniformSpace.Completion (SmoothScalarDirichlet q))
      (v : UniformSpace.Completion (SmoothScalarDirichlet q)) = _
  rw [DifferentialGeometry.Analysis.bilinearFromCompletion_apply_coe,
    dirichletCometricDifferenceFormSmooth_apply]

theorem norm_dirichletCometricDifferenceFormCompl_le
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta) :
    ‖dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta‖ ≤
      delta / (1 - delta) := by
  rw [dirichletCometricDifferenceFormCompl]
  apply DifferentialGeometry.Analysis.norm_bilinearFromCompletion_le
  · exact div_nonneg hdelta_nn (by linarith)
  · intro u v
    rw [dirichletCometricDifferenceFormSmooth_apply, Real.norm_eq_abs]
    exact abs_dirichletCometricDifferenceForm_le_norm q h
      hdelta_lt hdelta_nn hdelta u v

noncomputable def dirichletCometricDifferenceLaplacian
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta) :
    DirichletHs q 1 →L[ℝ] DirichletHs q (-1) :=
  dirichletBilinearFormToHs q
    (-dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta)

@[simp] theorem dirichletCometricDifferenceLaplacian_apply
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta)
    (u : DirichletHs q 1) :
    dirichletCometricDifferenceLaplacian q h hdelta_lt hdelta_nn hdelta u =
      (dirichletHsNegOneEquivH1Dual q).symm
        (-dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta
          (dirichletHsOneEquivH1Compl q u)) := rfl

theorem dirichletHsNegOneEquivH1Dual_cometricDifferenceLaplacian
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta)
    (u : DirichletHs q 1) :
    dirichletHsNegOneEquivH1Dual q
        (dirichletCometricDifferenceLaplacian q h
          hdelta_lt hdelta_nn hdelta u) =
      -dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta
        (dirichletHsOneEquivH1Compl q u) := by
  exact dirichletHsNegOneEquivH1Dual_bilinearFormToHs q
    (-dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta) u

theorem norm_dirichletCometricDifferenceLaplacian_le
    (q h : SmoothRiemannianMetric (I_half n) M)
    {delta : ℝ} (hdelta_lt : delta < 1) (hdelta_nn : 0 ≤ delta)
    (hdelta : metricCauchySchwarzBound (I := I_half n) q
      (fun x => h.inner x - q.inner x) delta) :
    ‖dirichletCometricDifferenceLaplacian q h hdelta_lt hdelta_nn hdelta‖ ≤
      delta / (1 - delta) := by
  calc
    ‖dirichletCometricDifferenceLaplacian q h hdelta_lt hdelta_nn hdelta‖ ≤
        ‖-dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta‖ := by
      exact dirichletBilinearFormToHs_norm_le q
        (-dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta)
    _ = ‖dirichletCometricDifferenceFormCompl q h hdelta_lt hdelta_nn hdelta‖ :=
      norm_neg _
    _ ≤ delta / (1 - delta) :=
      norm_dirichletCometricDifferenceFormCompl_le q h
        hdelta_lt hdelta_nn hdelta

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
