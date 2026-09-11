import DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import DifferentialGeometry.Geometry.Operator.WithBoundary.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Green
import DifferentialGeometry.Geometry.Operator.WithBoundary.Laplacian
import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open DifferentialGeometry.Geometry.Operator


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Operator.WithBoundary

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

structure UnrestrictedSmoothScalar (g : SmoothRiemannianMetric (I_half n) M) where
  toFun : M → ℝ
  smooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ toFun

namespace UnrestrictedSmoothScalar

variable {g : SmoothRiemannianMetric (I_half n) M}

@[ext] theorem ext {f h : UnrestrictedSmoothScalar g} (hfh : f.toFun = h.toFun) : f = h := by
  cases f; cases h; congr

instance : Zero (UnrestrictedSmoothScalar g) where
  zero :=
    { toFun := fun _ => 0
      smooth := contMDiff_const }

instance : Add (UnrestrictedSmoothScalar g) where
  add f h :=
    { toFun := f.toFun + h.toFun
      smooth := f.smooth.add h.smooth }

instance : Neg (UnrestrictedSmoothScalar g) where
  neg f :=
    { toFun := -f.toFun
      smooth := f.smooth.neg }

instance : Sub (UnrestrictedSmoothScalar g) where
  sub f h :=
    { toFun := f.toFun - h.toFun
      smooth := f.smooth.sub h.smooth }

instance : SMul ℝ (UnrestrictedSmoothScalar g) where
  smul c f :=
    { toFun := c • f.toFun
      smooth := by
        have h : (c • f.toFun) = (fun x : M => c * f.toFun x) := by
          funext x; rfl
        rw [h]
        exact contMDiff_const.mul f.smooth }

@[simp] lemma toFun_zero : (0 : UnrestrictedSmoothScalar g).toFun = (fun _ : M => 0) := rfl

@[simp] lemma toFun_zero_apply (x : M) : (0 : UnrestrictedSmoothScalar g).toFun x = 0 := rfl

@[simp] lemma toFun_add (f h : UnrestrictedSmoothScalar g) :
    (f + h).toFun = f.toFun + h.toFun := rfl

@[simp] lemma toFun_add_apply (f h : UnrestrictedSmoothScalar g) (x : M) :
    (f + h).toFun x = f.toFun x + h.toFun x := rfl

@[simp] lemma toFun_neg (f : UnrestrictedSmoothScalar g) :
    (-f).toFun = -f.toFun := rfl

@[simp] lemma toFun_neg_apply (f : UnrestrictedSmoothScalar g) (x : M) :
    (-f).toFun x = -f.toFun x := rfl

@[simp] lemma toFun_sub (f h : UnrestrictedSmoothScalar g) :
    (f - h).toFun = f.toFun - h.toFun := rfl

@[simp] lemma toFun_sub_apply (f h : UnrestrictedSmoothScalar g) (x : M) :
    (f - h).toFun x = f.toFun x - h.toFun x := rfl

@[simp] lemma toFun_smul (c : ℝ) (f : UnrestrictedSmoothScalar g) :
    (c • f).toFun = c • f.toFun := rfl

@[simp] lemma toFun_smul_apply (c : ℝ) (f : UnrestrictedSmoothScalar g) (x : M) :
    (c • f).toFun x = c * f.toFun x := rfl

lemma toFun_injective :
    Function.Injective (fun f : UnrestrictedSmoothScalar g => f.toFun) := by
  intro f h hfh
  exact ext hfh

instance : SMul ℕ (UnrestrictedSmoothScalar g) := ⟨nsmulRec⟩
instance : SMul ℤ (UnrestrictedSmoothScalar g) := ⟨zsmulRec⟩

@[simp] lemma toFun_nsmul (f : UnrestrictedSmoothScalar g) (k : ℕ) :
    (k • f).toFun = k • f.toFun := by
  induction k with
  | zero =>
    change (nsmulRec 0 f).toFun = (0 : ℕ) • f.toFun
    change (0 : UnrestrictedSmoothScalar g).toFun = (0 : ℕ) • f.toFun
    rw [toFun_zero, zero_nsmul]
    rfl
  | succ k ih =>
    change (nsmulRec (k + 1) f).toFun = (k + 1) • f.toFun
    change (nsmulRec k f + f).toFun = (k + 1) • f.toFun
    have hk : (nsmulRec k f).toFun = k • f.toFun := ih
    rw [toFun_add, hk, succ_nsmul]

@[simp] lemma toFun_zsmul (f : UnrestrictedSmoothScalar g) (z : ℤ) :
    (z • f).toFun = z • f.toFun := by
  rcases z with k | k
  · change (k • f).toFun = (Int.ofNat k) • f.toFun
    rw [toFun_nsmul]; simp
  · change (-((k + 1) • f)).toFun = (Int.negSucc k) • f.toFun
    rw [toFun_neg, toFun_nsmul]
    show -((k + 1) • f.toFun) = Int.negSucc k • f.toFun
    rw [show (Int.negSucc k : ℤ) = -((k + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (UnrestrictedSmoothScalar g) :=
  toFun_injective.addCommGroup
    (fun f => f.toFun)
    toFun_zero
    toFun_add
    toFun_neg
    toFun_sub
    toFun_nsmul
    toFun_zsmul

def toFunAddHom : UnrestrictedSmoothScalar g →+ (M → ℝ) where
  toFun := fun f => f.toFun
  map_zero' := toFun_zero
  map_add' := toFun_add

instance : Module ℝ (UnrestrictedSmoothScalar g) :=
  toFun_injective.module ℝ toFunAddHom toFun_smul

end UnrestrictedSmoothScalar

variable [T2Space M] [CompactSpace M]


omit [T2Space M] [CompactSpace M] in
lemma UnrestrictedSmoothScalar.continuous_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : UnrestrictedSmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := I_half n) g f.toFun x)
        (gradFun (I := I_half n) g h.toFun x)) :=
  continuous_g_inner_gradFun_gradFun_euclideanHalfSpace (n := n) (M := M) g f.smooth h.smooth

omit [T2Space M] [CompactSpace M] in
lemma UnrestrictedSmoothScalar.continuous_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : UnrestrictedSmoothScalar g) :
    Continuous (fun x : M => f.toFun x * h.toFun x) :=
  f.smooth.continuous.mul h.smooth.continuous

lemma UnrestrictedSmoothScalar.integrable_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : UnrestrictedSmoothScalar g) :
    Integrable (fun x : M => f.toFun x * h.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  exact (f.continuous_mul h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma UnrestrictedSmoothScalar.integrable_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : UnrestrictedSmoothScalar g) :
    Integrable (fun x : M =>
        g.inner x (gradFun (I := I_half n) g f.toFun x)
          (gradFun (I := I_half n) g h.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  integrable_g_inner_gradFun_gradFun (n := n) (M := M) g f.smooth h.smooth

def unrestrictedSmoothScalarH1Inner
    {g : SmoothRiemannianMetric (I_half n) M}
    (f h : UnrestrictedSmoothScalar g) : ℝ :=
  (∫ x, f.toFun x * h.toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
  (∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
        (gradFun (I := I_half n) g h.toFun x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g))


lemma unrestrictedSmoothScalarH1Inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : UnrestrictedSmoothScalar g) :
    unrestrictedSmoothScalarH1Inner f h =
      (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := rfl


lemma unrestrictedSmoothScalarH1Inner_symm
    {g : SmoothRiemannianMetric (I_half n) M} (f h : UnrestrictedSmoothScalar g) :
    unrestrictedSmoothScalarH1Inner f h = unrestrictedSmoothScalarH1Inner h f := by
  unfold unrestrictedSmoothScalarH1Inner
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact mul_comm _ _
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _


lemma UnrestrictedSmoothScalar.integral_mul_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    0 ≤ ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact mul_self_nonneg _

omit [T2Space M] [CompactSpace M] in
lemma SmoothRiemannianMetric_inner_self_nonneg
    (g : SmoothRiemannianMetric (I_half n) M) (x : M)
    (v : TangentSpace (I_half n) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv; simp [map_zero]
  · exact (g.pos x v hv).le


lemma UnrestrictedSmoothScalar.integral_inner_grad_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    0 ≤ ∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
          (gradFun (I := I_half n) g f.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact SmoothRiemannianMetric_inner_self_nonneg g x _


lemma unrestrictedSmoothScalarH1Inner_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : UnrestrictedSmoothScalar g) :
    0 ≤ unrestrictedSmoothScalarH1Inner f f := by
  unfold unrestrictedSmoothScalarH1Inner
  exact add_nonneg f.integral_mul_self_nonneg f.integral_inner_grad_self_nonneg

omit [T2Space M] [CompactSpace M] in
lemma UnrestrictedSmoothScalar.gradFun_add_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ : UnrestrictedSmoothScalar g) (x : M) :
    gradFun (I := I_half n) g (f₁ + f₂).toFun x =
      gradFun (I := I_half n) g f₁.toFun x +
        gradFun (I := I_half n) g f₂.toFun x := by
  have hfun : (f₁ + f₂).toFun = f₁.toFun + f₂.toFun := rfl
  rw [hfun]
  exact gradFun_add (I := I_half n) g
    (f₁.smooth.mdifferentiable (by simp) x)
    (f₂.smooth.mdifferentiable (by simp) x)

lemma unrestrictedSmoothScalar_integral_mul_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : UnrestrictedSmoothScalar g) :
    (∫ x, (f₁ + f₂).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, f₁.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, f₂.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, (f₁ + f₂).toFun x * h.toFun x =
      f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x := by
    intro x
    rw [UnrestrictedSmoothScalar.toFun_add_apply]
    ring
  rw [show (fun x : M => (f₁ + f₂).toFun x * h.toFun x) =
      (fun x : M => f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x) from
      funext hpt]
  exact integral_add (f₁.integrable_mul h) (f₂.integrable_mul h)

lemma unrestrictedSmoothScalar_integral_inner_grad_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : UnrestrictedSmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I_half n) g (f₁ + f₂).toFun x)
          (gradFun (I := I_half n) g h.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I_half n) g f₁.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x (gradFun (I := I_half n) g f₂.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, g.inner x
      (gradFun (I := I_half n) g (f₁ + f₂).toFun x)
      (gradFun (I := I_half n) g h.toFun x) =
      g.inner x (gradFun (I := I_half n) g f₁.toFun x)
        (gradFun (I := I_half n) g h.toFun x) +
      g.inner x (gradFun (I := I_half n) g f₂.toFun x)
        (gradFun (I := I_half n) g h.toFun x) := by
    intro x
    rw [UnrestrictedSmoothScalar.gradFun_add_apply f₁ f₂ x]
    rw [map_add, add_apply]
  rw [show (fun x : M => g.inner x
      (gradFun (I := I_half n) g (f₁ + f₂).toFun x)
      (gradFun (I := I_half n) g h.toFun x)) =
      (fun x : M => g.inner x (gradFun (I := I_half n) g f₁.toFun x)
          (gradFun (I := I_half n) g h.toFun x) +
        g.inner x (gradFun (I := I_half n) g f₂.toFun x)
          (gradFun (I := I_half n) g h.toFun x)) from funext hpt]
  exact integral_add (f₁.integrable_inner_grad h) (f₂.integrable_inner_grad h)

lemma unrestrictedSmoothScalarH1Inner_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : UnrestrictedSmoothScalar g) :
    unrestrictedSmoothScalarH1Inner (f₁ + f₂) h =
      unrestrictedSmoothScalarH1Inner f₁ h + unrestrictedSmoothScalarH1Inner f₂ h := by
  unfold unrestrictedSmoothScalarH1Inner
  rw [unrestrictedSmoothScalar_integral_mul_add_left,
    unrestrictedSmoothScalar_integral_inner_grad_add_left]
  ring

omit [T2Space M] [CompactSpace M] in
lemma UnrestrictedSmoothScalar.gradFun_smul_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f : UnrestrictedSmoothScalar g) (x : M) :
    gradFun (I := I_half n) g (c • f).toFun x =
      c • gradFun (I := I_half n) g f.toFun x := by
  apply metricFlatLinear_injective (I := I_half n) g x
  ext v
  change g.inner x (gradFun (I := I_half n) g (c • f.toFun) x) v =
    g.inner x (c • gradFun (I := I_half n) g f.toFun x) v
  rw [inner_gradFun (I := I_half n) g (c • f.toFun) x v]
  rw [show g.inner x (c • gradFun (I := I_half n) g f.toFun x) v =
      c * g.inner x (gradFun (I := I_half n) g f.toFun x) v from ?_]
  swap
  · rw [map_smul, smul_apply, smul_eq_mul]
  rw [inner_gradFun (I := I_half n) g f.toFun x v]
  set d_f : TangentSpace (I_half n) x →L[ℝ] ℝ :=
    mfderiv (I_half n) 𝓘(ℝ, ℝ) f.toFun x with hd_f_def
  have hHaf : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) f.toFun x d_f := by
    rw [hd_f_def]
    exact (f.smooth.mdifferentiable (by simp) x).hasMFDerivAt
  have hHa_smul : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x (c • d_f) :=
    hHaf.const_smul c
  have hd_smul : mfderiv (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x = c • d_f :=
    hHa_smul.mfderiv
  rw [hd_smul]
  change (c • d_f) v = c * d_f v
  rw [smul_apply, smul_eq_mul]


lemma unrestrictedSmoothScalar_integral_mul_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : UnrestrictedSmoothScalar g) :
    (∫ x, (c • f).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => (c • f).toFun x * h.toFun x) =
      (fun x : M => c * (f.toFun x * h.toFun x)) := by
    funext x; rw [UnrestrictedSmoothScalar.toFun_smul_apply]; ring
  rw [hpt]
  rw [integral_const_mul]


lemma unrestrictedSmoothScalar_integral_inner_grad_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : UnrestrictedSmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I_half n) g (c • f).toFun x)
          (gradFun (I := I_half n) g h.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => g.inner x
      (gradFun (I := I_half n) g (c • f).toFun x)
      (gradFun (I := I_half n) g h.toFun x)) =
      (fun x : M => c * g.inner x (gradFun (I := I_half n) g f.toFun x)
        (gradFun (I := I_half n) g h.toFun x)) := by
    funext x
    rw [UnrestrictedSmoothScalar.gradFun_smul_apply c f x]
    rw [map_smul, smul_apply, smul_eq_mul]
  rw [hpt, integral_const_mul]


lemma unrestrictedSmoothScalarH1Inner_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : UnrestrictedSmoothScalar g) :
    unrestrictedSmoothScalarH1Inner (c • f) h =
      c * unrestrictedSmoothScalarH1Inner f h := by
  unfold unrestrictedSmoothScalarH1Inner
  rw [unrestrictedSmoothScalar_integral_mul_smul_left,
    unrestrictedSmoothScalar_integral_inner_grad_smul_left]
  ring

noncomputable instance instPreInnerProductSpaceCoreUnrestrictedSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    PreInnerProductSpace.Core ℝ (UnrestrictedSmoothScalar g) where
  inner f h := unrestrictedSmoothScalarH1Inner f h
  conj_inner_symm f h := by
    change (unrestrictedSmoothScalarH1Inner h f : ℝ) =
      unrestrictedSmoothScalarH1Inner f h
    exact unrestrictedSmoothScalarH1Inner_symm h f
  re_inner_nonneg f := by
    change (0 : ℝ) ≤ unrestrictedSmoothScalarH1Inner f f
    exact unrestrictedSmoothScalarH1Inner_nonneg f
  add_left f₁ f₂ h := by
    change unrestrictedSmoothScalarH1Inner (f₁ + f₂) h =
      unrestrictedSmoothScalarH1Inner f₁ h + unrestrictedSmoothScalarH1Inner f₂ h
    exact unrestrictedSmoothScalarH1Inner_add_left f₁ f₂ h
  smul_left f h c := by
    change unrestrictedSmoothScalarH1Inner (c • f) h =
      c * unrestrictedSmoothScalarH1Inner f h
    exact unrestrictedSmoothScalarH1Inner_smul_left c f h

noncomputable instance instSeminormedAddCommGroupUnrestrictedSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup (UnrestrictedSmoothScalar g) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

noncomputable instance instInnerProductSpaceUnrestrictedSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    InnerProductSpace ℝ (UnrestrictedSmoothScalar g) :=
  InnerProductSpace.ofCore _

@[simp] lemma UnrestrictedSmoothScalar.inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : UnrestrictedSmoothScalar g) :
    @inner ℝ _ _ f h = unrestrictedSmoothScalarH1Inner f h := rfl

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
