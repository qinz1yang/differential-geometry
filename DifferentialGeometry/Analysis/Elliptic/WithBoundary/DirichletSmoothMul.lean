import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity
import Mathlib.Analysis.Normed.Operator.Extend

open DifferentialGeometry.Geometry.Operator

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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator.WithBoundary

private noncomputable def smoothScalarDirichletMulFun
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    SmoothScalarDirichlet g where
  toFun := fun x : M => (φ : M → ℝ) x * v.toFun x
  smooth := φ.contMDiff.mul v.smooth
  interior_support := tsupport_mul_subset_right.trans v.interior_support

omit [T2Space M] [CompactSpace M] in
private lemma smoothScalarDirichletMulFun_add
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v w : SmoothScalarDirichlet g) :
    smoothScalarDirichletMulFun g φ (v + w) =
      smoothScalarDirichletMulFun g φ v + smoothScalarDirichletMulFun g φ w := by
  apply InteriorSmoothScalar.ext
  funext x
  change (φ : M → ℝ) x * (v.toFun x + w.toFun x) =
    (φ : M → ℝ) x * v.toFun x + (φ : M → ℝ) x * w.toFun x
  ring

omit [T2Space M] [CompactSpace M] in
private lemma smoothScalarDirichletMulFun_smul
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (c : ℝ) (v : SmoothScalarDirichlet g) :
    smoothScalarDirichletMulFun g φ (c • v) =
      c • smoothScalarDirichletMulFun g φ v := by
  apply InteriorSmoothScalar.ext
  funext x
  change (φ : M → ℝ) x * (c * v.toFun x) =
    c * ((φ : M → ℝ) x * v.toFun x)
  ring

private noncomputable def smoothScalarDirichletMulLin
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    SmoothScalarDirichlet g →ₗ[ℝ] SmoothScalarDirichlet g where
  toFun := smoothScalarDirichletMulFun g φ
  map_add' := smoothScalarDirichletMulFun_add g φ
  map_smul' := smoothScalarDirichletMulFun_smul g φ

omit [T2Space M] in
private lemma exists_dirichletSmoothMulBound
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      (φ : M → ℝ) x ^ 2 ≤ C ∧
      g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
        (gradFun (I := I_half n) g (φ : M → ℝ) x) ≤ C := by
  classical
  let F : M → ℝ := fun x => max ((φ : M → ℝ) x ^ 2)
    (g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
      (gradFun (I := I_half n) g (φ : M → ℝ) x))
  have hF : Continuous F :=
    (φ.contMDiff.continuous.pow 2).max
      (continuous_g_inner_gradFun_gradFun g φ.contMDiff φ.contMDiff)
  obtain ⟨C₀, hC₀⟩ := ((isCompact_univ (X := M)).image hF).bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  have hx : F x ≤ C₀ := hC₀ ⟨x, mem_univ _, rfl⟩
  have hx' : F x ≤ max C₀ 0 := hx.trans (le_max_left _ _)
  exact ⟨(le_max_left _ _).trans hx', (le_max_right _ _).trans hx'⟩

private noncomputable def dirichletSmoothMulBound
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) : ℝ :=
  Classical.choose (exists_dirichletSmoothMulBound g φ)

omit [T2Space M] in
private lemma dirichletSmoothMulBound_nonneg
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    0 ≤ dirichletSmoothMulBound g φ :=
  (Classical.choose_spec (exists_dirichletSmoothMulBound g φ)).1

omit [T2Space M] in
private lemma sq_phi_le_dirichletSmoothMulBound
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (x : M) :
    (φ : M → ℝ) x ^ 2 ≤ dirichletSmoothMulBound g φ :=
  (Classical.choose_spec (exists_dirichletSmoothMulBound g φ)).2 x |>.1

omit [T2Space M] in
private lemma inner_grad_phi_le_dirichletSmoothMulBound
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (x : M) :
    g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
        (gradFun (I := I_half n) g (φ : M → ℝ) x) ≤
      dirichletSmoothMulBound g φ :=
  (Classical.choose_spec (exists_dirichletSmoothMulBound g φ)).2 x |>.2

omit [T2Space M] [CompactSpace M] in
private lemma metric_inner_add_self_le
    (g : SmoothRiemannianMetric (I_half n) M) (x : M)
    (v w : TangentSpace (I_half n) x) :
    g.inner x (v + w) (v + w) ≤
      2 * g.inner x v v + 2 * g.inner x w w := by
  have hminus := SmoothRiemannianMetric_inner_self_nonneg g x (v - w)
  have hparallelogram :
      g.inner x (v + w) (v + w) + g.inner x (v - w) (v - w) =
        2 * g.inner x v v + 2 * g.inner x w w := by
    simp only [map_add, add_apply, map_sub, sub_apply]
    rw [g.symm x w v]
    ring
  linarith

omit [T2Space M] [CompactSpace M] in
private lemma gradFun_smoothScalarDirichletMulFun
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) (x : M) :
    gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x =
      (φ : M → ℝ) x • gradFun (I := I_half n) g v.toFun x +
        v.toFun x • gradFun (I := I_half n) g (φ : M → ℝ) x := by
  change gradientFun (I := I_half n) g
      (fun y : M => (φ : M → ℝ) y * v.toFun y) x = _
  exact gradientFun_mul g
    (φ.contMDiff.mdifferentiable (by simp) x)
    (v.smooth.mdifferentiable (by simp) x)

omit [T2Space M] in
private lemma sq_smoothScalarDirichletMulFun_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) (x : M) :
    (smoothScalarDirichletMulFun g φ v).toFun x ^ 2 ≤
      dirichletSmoothMulBound g φ * v.toFun x ^ 2 := by
  change ((φ : M → ℝ) x * v.toFun x) ^ 2 ≤ _
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right
    (sq_phi_le_dirichletSmoothMulBound g φ x) (sq_nonneg _)

omit [T2Space M] in
private lemma inner_grad_smoothScalarDirichletMulFun_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) (x : M) :
    g.inner x
        (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
        (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x) ≤
      2 * dirichletSmoothMulBound g φ *
          g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g v.toFun x) +
        2 * dirichletSmoothMulBound g φ * v.toFun x ^ 2 := by
  rw [gradFun_smoothScalarDirichletMulFun]
  have hmain := metric_inner_add_self_le g x
    ((φ : M → ℝ) x • gradFun (I := I_half n) g v.toFun x)
    (v.toFun x • gradFun (I := I_half n) g (φ : M → ℝ) x)
  have hA : g.inner x
      ((φ : M → ℝ) x • gradFun (I := I_half n) g v.toFun x)
      ((φ : M → ℝ) x • gradFun (I := I_half n) g v.toFun x) =
      (φ : M → ℝ) x ^ 2 *
        g.inner x (gradFun (I := I_half n) g v.toFun x)
          (gradFun (I := I_half n) g v.toFun x) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hB : g.inner x
      (v.toFun x • gradFun (I := I_half n) g (φ : M → ℝ) x)
      (v.toFun x • gradFun (I := I_half n) g (φ : M → ℝ) x) =
      v.toFun x ^ 2 *
        g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
          (gradFun (I := I_half n) g (φ : M → ℝ) x) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hA, hB] at hmain
  have hgradv : 0 ≤ g.inner x (gradFun (I := I_half n) g v.toFun x)
      (gradFun (I := I_half n) g v.toFun x) :=
    SmoothRiemannianMetric_inner_self_nonneg g x _
  have hfirst : (φ : M → ℝ) x ^ 2 *
      g.inner x (gradFun (I := I_half n) g v.toFun x)
        (gradFun (I := I_half n) g v.toFun x) ≤
      dirichletSmoothMulBound g φ *
        g.inner x (gradFun (I := I_half n) g v.toFun x)
          (gradFun (I := I_half n) g v.toFun x) :=
    mul_le_mul_of_nonneg_right (sq_phi_le_dirichletSmoothMulBound g φ x) hgradv
  have hsecond : v.toFun x ^ 2 *
      g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
        (gradFun (I := I_half n) g (φ : M → ℝ) x) ≤
      v.toFun x ^ 2 * dirichletSmoothMulBound g φ :=
    mul_le_mul_of_nonneg_left
      (inner_grad_phi_le_dirichletSmoothMulBound g φ x) (sq_nonneg _)
  nlinarith

private lemma integrable_inner_grad_self
    (g : SmoothRiemannianMetric (I_half n) M) (v : SmoothScalarDirichlet g) :
    Integrable (fun x : M => g.inner x
      (gradFun (I := I_half n) g v.toFun x)
      (gradFun (I := I_half n) g v.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  simpa only [grad_g_with_boundary_section_apply'] using v.integrable_inner_grad v

private lemma integrable_toFun_sq
    (g : SmoothRiemannianMetric (I_half n) M) (v : SmoothScalarDirichlet g) :
    Integrable (fun x : M => v.toFun x ^ 2)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) g
  exact (v.smooth.continuous.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private lemma integral_inner_grad_bound_rhs
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    (∫ x, 2 * dirichletSmoothMulBound g φ *
          g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g v.toFun x) +
        2 * dirichletSmoothMulBound g φ * v.toFun x ^ 2
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      2 * dirichletSmoothMulBound g φ *
          (∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
              (gradFun (I := I_half n) g v.toFun x)
            ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
        2 * dirichletSmoothMulBound g φ *
          ∫ x, v.toFun x ^ 2
            ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  rw [integral_add ((integrable_inner_grad_self g v).const_mul _)
      ((integrable_toFun_sq g v).const_mul _),
    integral_const_mul, integral_const_mul]

private lemma integral_sq_smoothScalarDirichletMulFun_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    (∫ x, (smoothScalarDirichletMulFun g φ v).toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) ≤
      dirichletSmoothMulBound g φ *
        ∫ x, v.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) g
  have : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) g
  have hlhs : Integrable (fun x : M =>
      (smoothScalarDirichletMulFun g φ v).toFun x ^ 2) μ :=
    (smoothScalarDirichletMulFun g φ v).smooth.continuous.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hrhs : Integrable (fun x : M => v.toFun x ^ 2) μ :=
    v.smooth.continuous.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono_ae hlhs (hrhs.const_mul _)
    (Filter.Eventually.of_forall (sq_smoothScalarDirichletMulFun_le g φ v))
  simpa only [integral_const_mul] using h

private lemma integral_inner_grad_smoothScalarDirichletMulFun_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    (∫ x, g.inner x
          (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
          (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) ≤
      2 * dirichletSmoothMulBound g φ *
          (∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
              (gradFun (I := I_half n) g v.toFun x)
            ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
        2 * dirichletSmoothMulBound g φ *
          ∫ x, v.toFun x ^ 2
            ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) g
  have hlhs := integrable_inner_grad_self g (smoothScalarDirichletMulFun g φ v)
  have hgrad := integrable_inner_grad_self g v
  have hl2 := integrable_toFun_sq g v
  have hrhs := (hgrad.const_mul (2 * dirichletSmoothMulBound g φ)).add
    (hl2.const_mul (2 * dirichletSmoothMulBound g φ))
  exact (integral_mono_ae hlhs hrhs
    (Filter.Eventually.of_forall (inner_grad_smoothScalarDirichletMulFun_le g φ v))).trans_eq
      (integral_inner_grad_bound_rhs g φ v)

private lemma norm_smoothScalarDirichletMulFun_sq_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    ‖smoothScalarDirichletMulFun g φ v‖ ^ 2 ≤
      (3 * dirichletSmoothMulBound g φ) * ‖v‖ ^ 2 := by
  rw [InteriorSmoothScalar.norm_sq_eq_inner_self,
    InteriorSmoothScalar.norm_sq_eq_inner_self]
  unfold interiorSmoothScalarH1Inner
  simp only [grad_g_with_boundary_section_apply']
  change (∫ x, (smoothScalarDirichletMulFun g φ v).toFun x *
      (smoothScalarDirichletMulFun g φ v).toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
    (∫ x, g.inner x
        (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
        (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) ≤
    3 * dirichletSmoothMulBound g φ *
      ((∫ x, v.toFun x * v.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
        ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g))
  have hl2 := integral_sq_smoothScalarDirichletMulFun_le g φ v
  simp only [sq] at hl2
  have hgrad := integral_inner_grad_smoothScalarDirichletMulFun_le g φ v
  simp only [sq] at hgrad
  have hl2nonneg : 0 ≤ ∫ x, v.toFun x * v.toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    exact integral_nonneg fun _ => mul_self_nonneg _
  have hgradnonneg : 0 ≤ ∫ x, g.inner x
      (gradFun (I := I_half n) g v.toFun x)
      (gradFun (I := I_half n) g v.toFun x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    exact integral_nonneg fun x => SmoothRiemannianMetric_inner_self_nonneg g x _
  have hC := dirichletSmoothMulBound_nonneg g φ
  nlinarith

private lemma norm_smoothScalarDirichletMulFun_sq_le_of_bound
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x : M, (φ : M → ℝ) x ^ 2 ≤ C)
    (hgrad : ∀ x : M,
      g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
        (gradFun (I := I_half n) g (φ : M → ℝ) x) ≤ C)
    (v : SmoothScalarDirichlet g) :
    ‖smoothScalarDirichletMulFun g φ v‖ ^ 2 ≤
      (3 * C) * ‖v‖ ^ 2 := by
  have hsq (x : M) :
      (smoothScalarDirichletMulFun g φ v).toFun x ^ 2 ≤
        C * v.toFun x ^ 2 := by
    change ((φ : M → ℝ) x * v.toFun x) ^ 2 ≤ _
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hφ x) (sq_nonneg _)
  have hgradmul (x : M) :
      g.inner x
          (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
          (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x) ≤
        2 * C * g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g v.toFun x) +
          2 * C * v.toFun x ^ 2 := by
    rw [gradFun_smoothScalarDirichletMulFun]
    have hmain := metric_inner_add_self_le g x
      ((φ : M → ℝ) x • gradFun (I := I_half n) g v.toFun x)
      (v.toFun x • gradFun (I := I_half n) g (φ : M → ℝ) x)
    have hA : g.inner x
        ((φ : M → ℝ) x • gradFun (I := I_half n) g v.toFun x)
        ((φ : M → ℝ) x • gradFun (I := I_half n) g v.toFun x) =
        (φ : M → ℝ) x ^ 2 *
          g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g v.toFun x) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hB : g.inner x
        (v.toFun x • gradFun (I := I_half n) g (φ : M → ℝ) x)
        (v.toFun x • gradFun (I := I_half n) g (φ : M → ℝ) x) =
        v.toFun x ^ 2 *
          g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
            (gradFun (I := I_half n) g (φ : M → ℝ) x) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hA, hB] at hmain
    have hgradv : 0 ≤ g.inner x (gradFun (I := I_half n) g v.toFun x)
        (gradFun (I := I_half n) g v.toFun x) :=
      SmoothRiemannianMetric_inner_self_nonneg g x _
    have hfirst : (φ : M → ℝ) x ^ 2 *
        g.inner x (gradFun (I := I_half n) g v.toFun x)
          (gradFun (I := I_half n) g v.toFun x) ≤
        C * g.inner x (gradFun (I := I_half n) g v.toFun x)
          (gradFun (I := I_half n) g v.toFun x) :=
      mul_le_mul_of_nonneg_right (hφ x) hgradv
    have hsecond : v.toFun x ^ 2 *
        g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
          (gradFun (I := I_half n) g (φ : M → ℝ) x) ≤
        v.toFun x ^ 2 * C :=
      mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg _)
    nlinarith
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) g
  have hl2 :
      (∫ x, (smoothScalarDirichletMulFun g φ v).toFun x ^ 2 ∂μ) ≤
        C * ∫ x, v.toFun x ^ 2 ∂μ := by
    have hlhs := integrable_toFun_sq g (smoothScalarDirichletMulFun g φ v)
    have hrhs := integrable_toFun_sq g v
    have hmono := integral_mono_ae hlhs (hrhs.const_mul C)
      (Filter.Eventually.of_forall hsq)
    simpa only [integral_const_mul] using hmono
  have hgradint :
      (∫ x, g.inner x
          (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
          (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x) ∂μ) ≤
        2 * C * (∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g v.toFun x) ∂μ) +
          2 * C * ∫ x, v.toFun x ^ 2 ∂μ := by
    have hlhs := integrable_inner_grad_self g (smoothScalarDirichletMulFun g φ v)
    have hgradv := integrable_inner_grad_self g v
    have hl2v := integrable_toFun_sq g v
    have hrhs := (hgradv.const_mul (2 * C)).add (hl2v.const_mul (2 * C))
    have hmono := integral_mono_ae hlhs hrhs
      (Filter.Eventually.of_forall hgradmul)
    change _ ≤ ∫ x, 2 * C * g.inner x (gradFun (I := I_half n) g v.toFun x)
        (gradFun (I := I_half n) g v.toFun x) + 2 * C * v.toFun x ^ 2 ∂μ at hmono
    rw [integral_add (hgradv.const_mul (2 * C)) (hl2v.const_mul (2 * C)),
      integral_const_mul, integral_const_mul] at hmono
    exact hmono
  rw [InteriorSmoothScalar.norm_sq_eq_inner_self,
    InteriorSmoothScalar.norm_sq_eq_inner_self]
  unfold interiorSmoothScalarH1Inner
  simp only [grad_g_with_boundary_section_apply']
  change (∫ x, (smoothScalarDirichletMulFun g φ v).toFun x *
      (smoothScalarDirichletMulFun g φ v).toFun x ∂μ) +
    (∫ x, g.inner x
      (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x)
      (gradFun (I := I_half n) g (smoothScalarDirichletMulFun g φ v).toFun x) ∂μ) ≤
    3 * C * ((∫ x, v.toFun x * v.toFun x ∂μ) +
      ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
        (gradFun (I := I_half n) g v.toFun x) ∂μ)
  simp only [sq] at hl2 hgradint
  have hl2nonneg : 0 ≤ ∫ x, v.toFun x * v.toFun x ∂μ :=
    integral_nonneg fun _ => mul_self_nonneg _
  have hgradnonneg : 0 ≤ ∫ x, g.inner x
      (gradFun (I := I_half n) g v.toFun x)
      (gradFun (I := I_half n) g v.toFun x) ∂μ :=
    integral_nonneg fun x => SmoothRiemannianMetric_inner_self_nonneg g x _
  nlinarith

private noncomputable def smoothScalarDirichletMulNormBound
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) : ℝ :=
  Real.sqrt (3 * dirichletSmoothMulBound g φ)

omit [T2Space M] in
private lemma smoothScalarDirichletMulNormBound_nonneg
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    0 ≤ smoothScalarDirichletMulNormBound g φ := Real.sqrt_nonneg _

omit [T2Space M] in
private lemma smoothScalarDirichletMulNormBound_sq
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    smoothScalarDirichletMulNormBound g φ ^ 2 =
      3 * dirichletSmoothMulBound g φ := by
  exact Real.sq_sqrt (mul_nonneg (by norm_num) (dirichletSmoothMulBound_nonneg g φ))

private lemma norm_smoothScalarDirichletMulFun_le
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    ‖smoothScalarDirichletMulFun g φ v‖ ≤
      smoothScalarDirichletMulNormBound g φ * ‖v‖ := by
  have hsq := norm_smoothScalarDirichletMulFun_sq_le g φ v
  have hrhs : 0 ≤ smoothScalarDirichletMulNormBound g φ * ‖v‖ :=
    mul_nonneg (smoothScalarDirichletMulNormBound_nonneg g φ) (norm_nonneg _)
  apply abs_le_of_sq_le_sq' _ hrhs |>.2
  rw [mul_pow, smoothScalarDirichletMulNormBound_sq]
  exact hsq

noncomputable def smoothScalarDirichletMul
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    SmoothScalarDirichlet g →L[ℝ] SmoothScalarDirichlet g :=
  (smoothScalarDirichletMulLin g φ).mkContinuous
    (smoothScalarDirichletMulNormBound g φ)
    (norm_smoothScalarDirichletMulFun_le g φ)

@[simp] theorem smoothScalarDirichletMul_toFun
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    (smoothScalarDirichletMul g φ v).toFun =
      fun x : M => (φ : M → ℝ) x * v.toFun x := rfl

private noncomputable def smoothMulH1ComplDirichletOnSmooth
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g :=
  (smoothToH1ComplDirichlet g).comp (smoothScalarDirichletMul g φ)

noncomputable def smoothMulH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) :
    H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g :=
  ContinuousLinearMap.extend (smoothMulH1ComplDirichletOnSmooth g φ)
    (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g)

theorem smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    smoothMulH1ComplDirichlet g φ (smoothToH1ComplDirichlet g v) =
      smoothToH1ComplDirichlet g (smoothScalarDirichletMul g φ v) := by
  unfold smoothMulH1ComplDirichlet
  exact ContinuousLinearMap.extend_eq
    (smoothMulH1ComplDirichletOnSmooth g φ)
    (denseRange_smoothToH1ComplDirichlet g)
    (UniformSpace.Completion.isUniformInducing_coe (SmoothScalarDirichlet g)) v

theorem norm_smoothMulH1ComplDirichlet_le_of_bound
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x : M, (φ : M → ℝ) x ^ 2 ≤ C)
    (hgrad : ∀ x : M,
      g.inner x (gradFun (I := I_half n) g (φ : M → ℝ) x)
        (gradFun (I := I_half n) g (φ : M → ℝ) x) ≤ C) :
    ‖smoothMulH1ComplDirichlet g φ‖ ≤ Real.sqrt (3 * C) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  refine (denseRange_smoothToH1ComplDirichlet g).induction_on u
    (isClosed_le (smoothMulH1ComplDirichlet g φ).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro v
  rw [smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet]
  have hnorm (w : SmoothScalarDirichlet g) :
      ‖smoothToH1ComplDirichlet g w‖ = ‖w‖ := by
    change ‖(w : UniformSpace.Completion (SmoothScalarDirichlet g))‖ = ‖w‖
    exact UniformSpace.Completion.norm_coe w
  rw [hnorm, hnorm]
  change ‖smoothScalarDirichletMulFun g φ v‖ ≤ Real.sqrt (3 * C) * ‖v‖
  have hsq := norm_smoothScalarDirichletMulFun_sq_le_of_bound g φ hC hφ hgrad v
  have hrhs : 0 ≤ Real.sqrt (3 * C) * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply abs_le_of_sq_le_sq' _ hrhs |>.2
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hC)]
  exact hsq

private lemma H1ComplDirichletToLp_smoothMulH1ComplDirichlet_on_smooth
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (v : SmoothScalarDirichlet g) :
    H1ComplDirichletToLp g
        (smoothMulH1ComplDirichlet g φ (smoothToH1ComplDirichlet g v)) =
      smoothMulLp g φ
        (H1ComplDirichletToLp g (smoothToH1ComplDirichlet g v)) := by
  rw [smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  apply MeasureTheory.Lp.ext
  have hlhs : (smoothToLpDirichlet g (smoothScalarDirichletMul g φ v) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) g]
      fun x : M => (φ : M → ℝ) x * v.toFun x := by
    exact (MemLp.coeFn_toLp (smoothScalarDirichletMul g φ v).memLp_two).trans
      (Filter.Eventually.of_forall fun x => rfl)
  have hv : (smoothToLpDirichlet g v : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I_half n) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have hrhs := smoothMulLp_apply_coeFn g φ (smoothToLpDirichlet g v)
  refine hlhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [hrhs, hv] with x hx hvx
  rw [hx, hvx]

@[simp] theorem H1ComplDirichletToLp_smoothMulH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : C^∞⟮I_half n, M; ℝ⟯) (u : H1ComplDirichlet g) :
    H1ComplDirichletToLp g (smoothMulH1ComplDirichlet g φ u) =
      smoothMulLp g φ (H1ComplDirichletToLp g u) := by
  have hmaps :
      (fun w => H1ComplDirichletToLp g (smoothMulH1ComplDirichlet g φ w)) =
        fun w => smoothMulLp g φ (H1ComplDirichletToLp g w) := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet g)
      ((H1ComplDirichletToLp g).comp (smoothMulH1ComplDirichlet g φ)).continuous
      ((smoothMulLp g φ).comp (H1ComplDirichletToLp g)).continuous
    funext v
    exact H1ComplDirichletToLp_smoothMulH1ComplDirichlet_on_smooth g φ v
  exact congrFun hmaps u

theorem smoothMulH1ComplDirichlet_mul
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ ψ : C^∞⟮I_half n, M; ℝ⟯) :
    (smoothMulH1ComplDirichlet g φ).comp (smoothMulH1ComplDirichlet g ψ) =
      smoothMulH1ComplDirichlet g (φ * ψ) := by
  apply ContinuousLinearMap.ext
  intro u
  have hmaps :
      (fun w => ((smoothMulH1ComplDirichlet g φ).comp
        (smoothMulH1ComplDirichlet g ψ)) w) =
        fun w => smoothMulH1ComplDirichlet g (φ * ψ) w := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet g)
      ((smoothMulH1ComplDirichlet g φ).comp
        (smoothMulH1ComplDirichlet g ψ)).continuous
      (smoothMulH1ComplDirichlet g (φ * ψ)).continuous
    funext v
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet]
    congr 1
    apply InteriorSmoothScalar.ext
    funext x
    simp only [smoothScalarDirichletMul_toFun, ContMDiffMap.coe_mul, Pi.mul_apply]
    ring
  exact congrFun hmaps u

@[simp] theorem smoothMulH1ComplDirichlet_one
    (g : SmoothRiemannianMetric (I_half n) M) :
    smoothMulH1ComplDirichlet g 1 = ContinuousLinearMap.id ℝ (H1ComplDirichlet g) := by
  apply ContinuousLinearMap.ext
  intro u
  have hmaps : (fun w => smoothMulH1ComplDirichlet g 1 w) =
      fun w => ContinuousLinearMap.id ℝ (H1ComplDirichlet g) w := by
    apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet g)
      (smoothMulH1ComplDirichlet g 1).continuous
      (ContinuousLinearMap.id ℝ (H1ComplDirichlet g)).continuous
    funext v
    simp only [Function.comp_apply]
    rw [smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet]
    change smoothToH1ComplDirichlet g (smoothScalarDirichletMul g 1 v) =
      smoothToH1ComplDirichlet g v
    congr 1
    apply InteriorSmoothScalar.ext
    funext x
    simp only [smoothScalarDirichletMul_toFun, ContMDiffMap.coe_one,
      Pi.one_apply, one_mul]
  exact congrFun hmaps u

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
