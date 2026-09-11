import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [CompactSpace M]

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Integral.Measure

private noncomputable def dirichletDirectionalDerivativeSmoothScalar
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) : SmoothScalarDirichlet q where
  toFun := fun x : M => q.inner x (Y x)
    ((gradGWithBoundarySection (I := I_half n) q v.smooth v.interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x)
  smooth := contMDiff_g_inner_of_smooth_sections (I := I_half n) q Y
    (gradGWithBoundarySection (I := I_half n) q v.smooth v.interior_support)
  interior_support := by
    refine (closure_minimal ?_ (isClosed_tsupport v.toFun)).trans v.interior_support
    intro x hx
    apply support_grad_g_with_boundary_section_subset
      (I := I_half n) q v.smooth v.interior_support
    intro hzero
    apply hx
    change q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) = 0
    rw [hzero]
    exact (q.inner x (Y x)).map_zero

omit [T2Space M] [CompactSpace M] in
private lemma dirichletDirectionalDerivativeSmoothScalar_add
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v w : SmoothScalarDirichlet q) :
    dirichletDirectionalDerivativeSmoothScalar q Y (v + w) =
      dirichletDirectionalDerivativeSmoothScalar q Y v +
        dirichletDirectionalDerivativeSmoothScalar q Y w := by
  apply InteriorSmoothScalar.ext
  funext x
  change q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        (v + w).smooth (v + w).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) = _
  rw [InteriorSmoothScalar.grad_g_with_boundary_section_add_apply]
  exact (q.inner x (Y x)).map_add _ _

omit [T2Space M] [CompactSpace M] in
private lemma dirichletDirectionalDerivativeSmoothScalar_smul
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (c : ℝ) (v : SmoothScalarDirichlet q) :
    dirichletDirectionalDerivativeSmoothScalar q Y (c • v) =
      c • dirichletDirectionalDerivativeSmoothScalar q Y v := by
  apply InteriorSmoothScalar.ext
  funext x
  change q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        (c • v).smooth (c • v).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) = _
  rw [InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply]
  exact (q.inner x (Y x)).map_smul c _

noncomputable def dirichletDirectionalDerivativeSmooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
  smoothToLpDirichlet q (dirichletDirectionalDerivativeSmoothScalar q Y v)

theorem dirichletDirectionalDerivativeSmooth_coeFn
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) :
    (dirichletDirectionalDerivativeSmooth q Y v : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) q]
      fun x : M => q.inner x (Y x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) :=
  MemLp.coeFn_toLp
    (dirichletDirectionalDerivativeSmoothScalar q Y v).memLp_two

private noncomputable def dirichletDirectionalDerivativeSmoothLin
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    SmoothScalarDirichlet q →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) where
  toFun := dirichletDirectionalDerivativeSmooth q Y
  map_add' v w := by
    unfold dirichletDirectionalDerivativeSmooth
    rw [dirichletDirectionalDerivativeSmoothScalar_add, map_add]
  map_smul' c v := by
    unfold dirichletDirectionalDerivativeSmooth
    rw [dirichletDirectionalDerivativeSmoothScalar_smul, map_smul]
    rfl

omit [T2Space M] in
private lemma exists_dirichletDirectionalDerivativeBound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : M, q.inner x (Y x) (Y x) ≤ B := by
  classical
  have hcont : Continuous (fun x : M => q.inner x (Y x) (Y x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I_half n) q Y Y
  obtain ⟨B₀, hB₀⟩ := ((isCompact_univ (X := M)).image hcont).bddAbove
  refine ⟨max B₀ 0, le_max_right _ _, fun x => ?_⟩
  exact (hB₀ ⟨x, mem_univ _, rfl⟩).trans (le_max_left _ _)

private noncomputable def dirichletDirectionalDerivativeBound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) : ℝ :=
  Classical.choose (exists_dirichletDirectionalDerivativeBound q Y)

omit [T2Space M] in
private lemma dirichletDirectionalDerivativeBound_nonneg
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    0 ≤ dirichletDirectionalDerivativeBound q Y :=
  (Classical.choose_spec (exists_dirichletDirectionalDerivativeBound q Y)).1

omit [T2Space M] in
private lemma inner_Y_self_le_dirichletDirectionalDerivativeBound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) (x : M) :
    q.inner x (Y x) (Y x) ≤ dirichletDirectionalDerivativeBound q Y :=
  (Classical.choose_spec (exists_dirichletDirectionalDerivativeBound q Y)).2 x

omit [T2Space M] [CompactSpace M] in
private lemma sq_inner_Y_grad_le
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (v : SmoothScalarDirichlet q) (x : M) :
    (q.inner x (Y x)
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) ^ 2 ≤
      B * q.inner x
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) := by
  let Z := (gradGWithBoundarySection (I := I_half n) q
    v.smooth v.interior_support :
    Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) x
  have hY0 : 0 ≤ q.inner x (Y x) (Y x) :=
    SmoothRiemannianMetric_inner_self_nonneg q x _
  have hZ0 : 0 ≤ q.inner x Z Z :=
    SmoothRiemannianMetric_inner_self_nonneg q x _
  have hcs := abs_metric_inner_le_sqrt_metric_quadratic
    (I := I_half n) (M := M) q x (Y x) Z
  have hsq := mul_self_le_mul_self (abs_nonneg _) hcs
  have habs : |q.inner x (Y x) Z| * |q.inner x (Y x) Z| =
      (q.inner x (Y x) Z) ^ 2 := by rw [← sq, sq_abs]
  have hsqrt :
      (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) *
          (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) =
        q.inner x (Y x) (Y x) * q.inner x Z Z := by
    rw [show (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) *
        (Real.sqrt (q.inner x (Y x) (Y x)) * Real.sqrt (q.inner x Z Z)) =
      (Real.sqrt (q.inner x (Y x) (Y x)) *
        Real.sqrt (q.inner x (Y x) (Y x))) *
      (Real.sqrt (q.inner x Z Z) * Real.sqrt (q.inner x Z Z)) by ring]
    rw [Real.mul_self_sqrt hY0, Real.mul_self_sqrt hZ0]
  rw [habs, hsqrt] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_right (hY x) hZ0)

private lemma norm_dirichletDirectionalDerivativeSmooth_sq_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (v : SmoothScalarDirichlet q) :
    ‖dirichletDirectionalDerivativeSmooth q Y v‖ ^ 2 ≤ B * ‖v‖ ^ 2 := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) q
  let D := dirichletDirectionalDerivativeSmoothScalar q Y v
  change ‖smoothToLpLinInterior q D‖ ^ 2 ≤ B * ‖v‖ ^ 2
  rw [InteriorSmoothScalar.norm_smoothToLp_sq]
  have hgrad :
      (∫ x, q.inner x
          ((gradGWithBoundarySection (I := I_half n) q
            v.smooth v.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((gradGWithBoundarySection (I := I_half n) q
            v.smooth v.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x) ∂μ) ≤ ‖v‖ ^ 2 := by
    rw [InteriorSmoothScalar.norm_sq_eq_inner_self]
    unfold interiorSmoothScalarH1Inner
    linarith [v.integral_mul_self_nonneg]
  have hlhs : Integrable (fun x : M => D.toFun x * D.toFun x) μ :=
    D.integrable_mul D
  have hgrad_int : Integrable (fun x : M => q.inner x
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((gradGWithBoundarySection (I := I_half n) q
        v.smooth v.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) μ :=
    v.integrable_inner_grad v
  have hmono := integral_mono_ae hlhs (hgrad_int.const_mul B)
    (Filter.Eventually.of_forall fun x => by
      change (q.inner x (Y x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) *
        (q.inner x (Y x)
        ((gradGWithBoundarySection (I := I_half n) q
          v.smooth v.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) ≤ _
      rw [← sq]
      exact sq_inner_Y_grad_le q Y hY v x)
  rw [integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left hgrad hB)

private lemma norm_dirichletDirectionalDerivativeSmooth_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B)
    (v : SmoothScalarDirichlet q) :
    ‖dirichletDirectionalDerivativeSmooth q Y v‖ ≤ Real.sqrt B * ‖v‖ := by
  apply abs_le_of_sq_le_sq' _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) |>.2
  rw [mul_pow, Real.sq_sqrt hB]
  exact norm_dirichletDirectionalDerivativeSmooth_sq_le_of_bound q Y hB hY v

private noncomputable def dirichletDirectionalDerivativeOnSmooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    SmoothScalarDirichlet q →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
  (dirichletDirectionalDerivativeSmoothLin q Y).mkContinuous
    (Real.sqrt (dirichletDirectionalDerivativeBound q Y))
    (norm_dirichletDirectionalDerivativeSmooth_le_of_bound q Y
      (dirichletDirectionalDerivativeBound_nonneg q Y)
      (inner_Y_self_le_dirichletDirectionalDerivativeBound q Y))

noncomputable def dirichletDirectionalDerivativeCLM
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    H1ComplDirichlet q →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
  ContinuousLinearMap.extend (dirichletDirectionalDerivativeOnSmooth q Y)
    (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet q →L[ℝ] H1ComplDirichlet q)

theorem dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (v : SmoothScalarDirichlet q) :
    dirichletDirectionalDerivativeCLM q Y
        (smoothToH1ComplDirichlet q v) =
      dirichletDirectionalDerivativeSmooth q Y v := by
  unfold dirichletDirectionalDerivativeCLM
  exact ContinuousLinearMap.extend_eq
    (dirichletDirectionalDerivativeOnSmooth q Y)
    (denseRange_smoothToH1ComplDirichlet q)
    (UniformSpace.Completion.isUniformInducing_coe (SmoothScalarDirichlet q)) v

theorem norm_dirichletDirectionalDerivativeCLM_le
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ x : M, q.inner x (Y x) (Y x) ≤ B) :
    ‖dirichletDirectionalDerivativeCLM q Y‖ ≤ Real.sqrt B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  refine (denseRange_smoothToH1ComplDirichlet q).induction_on u
    (isClosed_le (dirichletDirectionalDerivativeCLM q Y).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro v
  rw [dirichletDirectionalDerivativeCLM_smoothToH1ComplDirichlet]
  have hnorm : ‖smoothToH1ComplDirichlet q v‖ = ‖v‖ := by
    change ‖(v : UniformSpace.Completion (SmoothScalarDirichlet q))‖ = ‖v‖
    exact UniformSpace.Completion.norm_coe v
  rw [hnorm]
  exact norm_dirichletDirectionalDerivativeSmooth_le_of_bound q Y hB hY v

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
