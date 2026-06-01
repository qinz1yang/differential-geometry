import DifferentialGeometry.Geometry.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Green
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Tensor.RSTensor.TangentRiemannian
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Pre-Hilbert structure on interior-supported smooth scalar functions
(with-boundary, half-space model)

For a closed (compact, Hausdorff) smooth Riemannian manifold-with-boundary
`(M, g)` modelled on the canonical Euclidean half-space
`EuclideanHalfSpace n`, the space of *interior-supported* smooth real-valued
functions on `M` carries a natural pre-Hilbert structure whose inner product
mirrors the boundaryless case:

  ⟨f, h⟩ := ∫ f · h dμ_g + ∫ g(grad f, grad h) dμ_g

The interior-support hypothesis (`tsupport f ⊆ I.interior M`) ensures that the
gradient `gradFun g f`, which is intrinsically smooth only on the manifold
interior in the with-boundary setting, packages as a globally smooth tangent
section via `grad_g_with_boundary_section`. This makes the gradient integrand
`g.inner x (gradFun g f x) (gradFun g h x)` continuous on the whole `M`,
hence integrable against the (finite) Riemannian volume measure.

This file packages a wrapper type `InteriorSmoothScalar g`, equips it with
the standard `AddCommGroup` and `Module ℝ` structure, and installs the
pre-inner-product space structure via `InnerProductSpace.Core`. The induced
`SeminormedAddCommGroup` and `InnerProductSpace ℝ` instances follow from
`InnerProductSpace.Core`.

This shared structure underpins both the Neumann and Dirichlet variants of
the variational Laplacian on a manifold-with-boundary. The downstream files
build the corresponding Hilbert completions and resolvents.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Local abbreviation for the canonical Euclidean half-space model. -/
private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

/-- A smooth real-valued function on a half-space-modelled manifold-with-boundary
`M`, packaged together with the Riemannian-metric parameter `g`, whose
topological support lies in the manifold interior.

The metric `g` does not appear in the underlying data fields; its role is
solely to make `InteriorSmoothScalar g` a different Lean type for each metric,
so that downstream files can attach metric-dependent inner-product / norm
instances cleanly. -/
structure InteriorSmoothScalar (g : SmoothRiemannianMetric (I_half n) M) where
  /-- The underlying function. -/
  toFun : M → ℝ
  /-- The function is smooth. -/
  smooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ toFun
  /-- The function's topological support is contained in the manifold interior. -/
  interior_support : tsupport toFun ⊆ (I_half n).interior M

namespace InteriorSmoothScalar

variable {g : SmoothRiemannianMetric (I_half n) M}

/-- Two `InteriorSmoothScalar` are equal if their underlying functions are equal. -/
@[ext] theorem ext {f h : InteriorSmoothScalar g} (hfh : f.toFun = h.toFun) : f = h := by
  cases f; cases h; congr

instance : Zero (InteriorSmoothScalar g) where
  zero :=
    { toFun := fun _ => 0
      smooth := contMDiff_const
      interior_support := by
        simp [tsupport] }

instance : Add (InteriorSmoothScalar g) where
  add f h :=
    { toFun := f.toFun + h.toFun
      smooth := f.smooth.add h.smooth
      interior_support := by
        refine (tsupport_add (f := f.toFun) (g := h.toFun)).trans ?_
        exact Set.union_subset f.interior_support h.interior_support }

instance : Neg (InteriorSmoothScalar g) where
  neg f :=
    { toFun := -f.toFun
      smooth := f.smooth.neg
      interior_support := by
        rw [tsupport_neg]
        exact f.interior_support }

instance : Sub (InteriorSmoothScalar g) where
  sub f h :=
    { toFun := f.toFun - h.toFun
      smooth := f.smooth.sub h.smooth
      interior_support := by
        have h_eq : f.toFun - h.toFun = f.toFun + (-h.toFun) := by
          funext x; ring_nf
        rw [h_eq]
        refine (tsupport_add (f := f.toFun) (g := -h.toFun)).trans ?_
        refine Set.union_subset f.interior_support ?_
        rw [tsupport_neg]
        exact h.interior_support }

instance : SMul ℝ (InteriorSmoothScalar g) where
  smul c f :=
    { toFun := c • f.toFun
      smooth := by
        have h : (c • f.toFun) = (fun x : M => c * f.toFun x) := by
          funext x; rfl
        rw [h]
        exact contMDiff_const.mul f.smooth
      interior_support := by
        have h_supp : Function.support (c • f.toFun) ⊆ Function.support f.toFun := by
          intro x hx hx_zero
          apply hx
          change c * f.toFun x = 0
          rw [hx_zero, mul_zero]
        have h_tsupp : tsupport (c • f.toFun) ⊆ tsupport f.toFun :=
          closure_mono h_supp
        exact h_tsupp.trans f.interior_support }

@[simp] lemma toFun_zero : (0 : InteriorSmoothScalar g).toFun = (fun _ : M => 0) := rfl

@[simp] lemma toFun_zero_apply (x : M) : (0 : InteriorSmoothScalar g).toFun x = 0 := rfl

@[simp] lemma toFun_add (f h : InteriorSmoothScalar g) :
    (f + h).toFun = f.toFun + h.toFun := rfl

@[simp] lemma toFun_add_apply (f h : InteriorSmoothScalar g) (x : M) :
    (f + h).toFun x = f.toFun x + h.toFun x := rfl

@[simp] lemma toFun_neg (f : InteriorSmoothScalar g) :
    (-f).toFun = -f.toFun := rfl

@[simp] lemma toFun_neg_apply (f : InteriorSmoothScalar g) (x : M) :
    (-f).toFun x = -f.toFun x := rfl

@[simp] lemma toFun_sub (f h : InteriorSmoothScalar g) :
    (f - h).toFun = f.toFun - h.toFun := rfl

@[simp] lemma toFun_sub_apply (f h : InteriorSmoothScalar g) (x : M) :
    (f - h).toFun x = f.toFun x - h.toFun x := rfl

@[simp] lemma toFun_smul (c : ℝ) (f : InteriorSmoothScalar g) :
    (c • f).toFun = c • f.toFun := rfl

@[simp] lemma toFun_smul_apply (c : ℝ) (f : InteriorSmoothScalar g) (x : M) :
    (c • f).toFun x = c * f.toFun x := rfl

/-- `InteriorSmoothScalar.toFun` is injective. -/
lemma toFun_injective :
    Function.Injective (fun f : InteriorSmoothScalar g => f.toFun) := by
  intro f h hfh
  exact ext hfh

instance : SMul ℕ (InteriorSmoothScalar g) := ⟨nsmulRec⟩
instance : SMul ℤ (InteriorSmoothScalar g) := ⟨zsmulRec⟩

@[simp] lemma toFun_nsmul (f : InteriorSmoothScalar g) (k : ℕ) :
    (k • f).toFun = k • f.toFun := by
  induction k with
  | zero =>
    change (nsmulRec 0 f).toFun = (0 : ℕ) • f.toFun
    change (0 : InteriorSmoothScalar g).toFun = (0 : ℕ) • f.toFun
    rw [toFun_zero, zero_nsmul]
    rfl
  | succ k ih =>
    change (nsmulRec (k + 1) f).toFun = (k + 1) • f.toFun
    change (nsmulRec k f + f).toFun = (k + 1) • f.toFun
    have hk : (nsmulRec k f).toFun = k • f.toFun := ih
    rw [toFun_add, hk, succ_nsmul]

@[simp] lemma toFun_zsmul (f : InteriorSmoothScalar g) (z : ℤ) :
    (z • f).toFun = z • f.toFun := by
  rcases z with k | k
  · change (k • f).toFun = (Int.ofNat k) • f.toFun
    rw [toFun_nsmul]; simp
  · change (-((k + 1) • f)).toFun = (Int.negSucc k) • f.toFun
    rw [toFun_neg, toFun_nsmul]
    show -((k + 1) • f.toFun) = Int.negSucc k • f.toFun
    rw [show (Int.negSucc k : ℤ) = -((k + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (InteriorSmoothScalar g) :=
  toFun_injective.addCommGroup
    (fun f => f.toFun)
    toFun_zero
    toFun_add
    toFun_neg
    toFun_sub
    toFun_nsmul
    toFun_zsmul

/-- The natural additive monoid hom from `InteriorSmoothScalar g` to its
underlying function space. -/
def toFunAddHom : InteriorSmoothScalar g →+ (M → ℝ) where
  toFun := fun f => f.toFun
  map_zero' := toFun_zero
  map_add' := toFun_add

instance : Module ℝ (InteriorSmoothScalar g) :=
  toFun_injective.module ℝ toFunAddHom toFun_smul

end InteriorSmoothScalar

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The pointwise gradient inner product
`x ↦ g.inner x (gradFun g f x) (gradFun g h x)`
is a continuous function on `M`. -/
lemma InteriorSmoothScalar.continuous_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x ((grad_g_with_boundary_section
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I_half n) g
    (grad_g_with_boundary_section (I := I_half n) g f.smooth f.interior_support)
    (grad_g_with_boundary_section (I := I_half n) g h.smooth h.interior_support)

/-- The pointwise product `x ↦ f.toFun x * h.toFun x` is continuous. -/
lemma InteriorSmoothScalar.continuous_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    Continuous (fun x : M => f.toFun x * h.toFun x) :=
  f.smooth.continuous.mul h.smooth.continuous

/-- The product `f · h` is integrable against the Riemannian volume measure on
a closed manifold-with-boundary. -/
lemma InteriorSmoothScalar.integrable_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    Integrable (fun x : M => f.toFun x * h.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  exact (f.continuous_mul h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The pointwise inner product of gradients is integrable. -/
lemma InteriorSmoothScalar.integrable_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    Integrable (fun x : M =>
        g.inner x ((grad_g_with_boundary_section
              (I := I_half n) g f.smooth f.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((grad_g_with_boundary_section
              (I := I_half n) g h.smooth h.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  exact (f.continuous_inner_grad h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The H¹ inner product on interior-supported smooth scalars on a closed
Riemannian manifold-with-boundary. -/
def interiorSmoothScalarH1Inner
    {g : SmoothRiemannianMetric (I_half n) M}
    (f h : InteriorSmoothScalar g) : ℝ :=
  (∫ x, f.toFun x * h.toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
  (∫ x, g.inner x ((grad_g_with_boundary_section
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g))

/-- Unfolding lemma. -/
lemma interiorSmoothScalarH1Inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner f h =
      (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x ((grad_g_with_boundary_section
                (I := I_half n) g f.smooth f.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((grad_g_with_boundary_section
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := rfl

/-- The H¹ inner product is symmetric in its two arguments. -/
lemma interiorSmoothScalarH1Inner_symm
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner f h = interiorSmoothScalarH1Inner h f := by
  unfold interiorSmoothScalarH1Inner
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact mul_comm _ _
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _

/-- The L² self-integral of `f` is non-negative. -/
lemma InteriorSmoothScalar.integral_mul_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    0 ≤ ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact mul_self_nonneg _

/-- Pointwise non-negativity of the metric inner product on the diagonal. -/
lemma SmoothRiemannianMetric_inner_self_nonneg
    (g : SmoothRiemannianMetric (I_half n) M) (x : M)
    (v : TangentSpace (I_half n) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv; simp [map_zero]
  · exact (g.pos x v hv).le

/-- The Riemannian gradient self-integral is non-negative. -/
lemma InteriorSmoothScalar.integral_inner_grad_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    0 ≤ ∫ x, g.inner x ((grad_g_with_boundary_section
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((grad_g_with_boundary_section
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact SmoothRiemannianMetric_inner_self_nonneg g x _

/-- The H¹ self-pairing is non-negative. -/
lemma interiorSmoothScalarH1Inner_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    0 ≤ interiorSmoothScalarH1Inner f f := by
  unfold interiorSmoothScalarH1Inner
  exact add_nonneg f.integral_mul_self_nonneg f.integral_inner_grad_self_nonneg

/-- The packaged with-boundary gradient section's pointwise value equals
`gradFun`. -/
@[simp] lemma grad_g_with_boundary_section_apply'
    {g : SmoothRiemannianMetric (I_half n) M}
    (f : InteriorSmoothScalar g) (x : M) :
    (grad_g_with_boundary_section
        (I := I_half n) g f.smooth f.interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x =
      gradFun (I := I_half n) g f.toFun x := rfl

/-- Pointwise linearity of `gradFun`: gradient of a sum equals sum of
gradients. -/
lemma InteriorSmoothScalar.grad_g_with_boundary_section_add_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ : InteriorSmoothScalar g) (x : M) :
    (grad_g_with_boundary_section
        (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x =
      ((grad_g_with_boundary_section
            (I := I_half n) g f₁.smooth f₁.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) +
      ((grad_g_with_boundary_section
            (I := I_half n) g f₂.smooth f₂.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) := by
  rw [grad_g_with_boundary_section_apply', grad_g_with_boundary_section_apply',
    grad_g_with_boundary_section_apply']
  have hfun : (f₁ + f₂).toFun = f₁.toFun + f₂.toFun := rfl
  rw [hfun]
  exact gradFun_add (I := I_half n) g
    (f₁.smooth.mdifferentiable (by simp) x)
    (f₂.smooth.mdifferentiable (by simp) x)

/-- L² inner product is additive in the left argument. -/
lemma interiorSmoothScalar_integral_mul_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : InteriorSmoothScalar g) :
    (∫ x, (f₁ + f₂).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, f₁.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, f₂.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, (f₁ + f₂).toFun x * h.toFun x =
      f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x := by
    intro x
    rw [InteriorSmoothScalar.toFun_add_apply]
    ring
  rw [show (fun x : M => (f₁ + f₂).toFun x * h.toFun x) =
      (fun x : M => f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x) from
      funext hpt]
  exact integral_add (f₁.integrable_mul h) (f₂.integrable_mul h)

/-- Gradient inner product is additive in the left argument. -/
lemma interiorSmoothScalar_integral_inner_grad_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : InteriorSmoothScalar g) :
    (∫ x, g.inner x ((grad_g_with_boundary_section
              (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((grad_g_with_boundary_section
              (I := I_half n) g h.smooth h.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, g.inner x ((grad_g_with_boundary_section
                (I := I_half n) g f₁.smooth f₁.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((grad_g_with_boundary_section
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x ((grad_g_with_boundary_section
                (I := I_half n) g f₂.smooth f₂.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((grad_g_with_boundary_section
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, g.inner x
      ((grad_g_with_boundary_section
          (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((grad_g_with_boundary_section
          (I := I_half n) g h.smooth h.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) =
      g.inner x
        ((grad_g_with_boundary_section
            (I := I_half n) g f₁.smooth f₁.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) +
      g.inner x
        ((grad_g_with_boundary_section
            (I := I_half n) g f₂.smooth f₂.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) := by
    intro x
    rw [InteriorSmoothScalar.grad_g_with_boundary_section_add_apply f₁ f₂ x]
    rw [map_add, ContinuousLinearMap.add_apply]
  rw [show (fun x : M => g.inner x
      ((grad_g_with_boundary_section
          (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((grad_g_with_boundary_section
          (I := I_half n) g h.smooth h.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        ((grad_g_with_boundary_section
            (I := I_half n) g f₁.smooth f₁.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) +
      g.inner x
        ((grad_g_with_boundary_section
            (I := I_half n) g f₂.smooth f₂.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) from funext hpt]
  exact integral_add (f₁.integrable_inner_grad h) (f₂.integrable_inner_grad h)

/-- Additivity of the H¹ inner product in the left argument. -/
lemma interiorSmoothScalarH1Inner_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner (f₁ + f₂) h =
      interiorSmoothScalarH1Inner f₁ h + interiorSmoothScalarH1Inner f₂ h := by
  unfold interiorSmoothScalarH1Inner
  rw [interiorSmoothScalar_integral_mul_add_left,
    interiorSmoothScalar_integral_inner_grad_add_left]
  ring

/-- Pointwise scalar multiplication of `gradFun`. -/
lemma InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f : InteriorSmoothScalar g) (x : M) :
    (grad_g_with_boundary_section
        (I := I_half n) g (c • f).smooth (c • f).interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x =
      c • ((grad_g_with_boundary_section
        (I := I_half n) g f.smooth f.interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x) := by
  rw [grad_g_with_boundary_section_apply', grad_g_with_boundary_section_apply']
  apply metricFlatLinear_injective (I := I_half n) g x
  ext v
  change g.inner x (gradFun (I := I_half n) g (c • f.toFun) x) v =
    g.inner x (c • gradFun (I := I_half n) g f.toFun x) v
  rw [inner_gradFun (I := I_half n) g (c • f.toFun) x v]
  rw [show g.inner x (c • gradFun (I := I_half n) g f.toFun x) v =
      c * g.inner x (gradFun (I := I_half n) g f.toFun x) v from ?_]
  swap
  · rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [inner_gradFun (I := I_half n) g f.toFun x v]
  set d_f : TangentSpace (I_half n) x →L[ℝ] ℝ := mfderiv (I_half n) 𝓘(ℝ, ℝ) f.toFun x
    with hd_f_def
  have hHaf : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) f.toFun x d_f := by
    rw [hd_f_def]
    exact (f.smooth.mdifferentiable (by simp) x).hasMFDerivAt
  have hHa_smul : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x (c • d_f) :=
    hHaf.const_smul c
  have hd_smul : mfderiv (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x = c • d_f :=
    hHa_smul.mfderiv
  rw [hd_smul]
  change (c • d_f) v = c * d_f v
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- L² inner product is homogeneous in the left argument. -/
lemma interiorSmoothScalar_integral_mul_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : InteriorSmoothScalar g) :
    (∫ x, (c • f).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => (c • f).toFun x * h.toFun x) =
      (fun x : M => c * (f.toFun x * h.toFun x)) := by
    funext x; rw [InteriorSmoothScalar.toFun_smul_apply]; ring
  rw [hpt]
  rw [integral_const_mul]

/-- Gradient inner product is homogeneous in the left argument. -/
lemma interiorSmoothScalar_integral_inner_grad_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : InteriorSmoothScalar g) :
    (∫ x, g.inner x ((grad_g_with_boundary_section
              (I := I_half n) g (c • f).smooth (c • f).interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((grad_g_with_boundary_section
              (I := I_half n) g h.smooth h.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, g.inner x ((grad_g_with_boundary_section
                (I := I_half n) g f.smooth f.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((grad_g_with_boundary_section
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => g.inner x
      ((grad_g_with_boundary_section
          (I := I_half n) g (c • f).smooth (c • f).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((grad_g_with_boundary_section
          (I := I_half n) g h.smooth h.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) =
      (fun x : M => c * g.inner x
        ((grad_g_with_boundary_section
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((grad_g_with_boundary_section
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) := by
    funext x
    rw [InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply c f x]
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hpt, integral_const_mul]

/-- Homogeneity of the H¹ inner product in the left argument. -/
lemma interiorSmoothScalarH1Inner_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner (c • f) h =
      c * interiorSmoothScalarH1Inner f h := by
  unfold interiorSmoothScalarH1Inner
  rw [interiorSmoothScalar_integral_mul_smul_left,
    interiorSmoothScalar_integral_inner_grad_smul_left]
  ring

/-- The pre-inner-product core on interior-supported smooth scalars. -/
noncomputable instance instPreInnerProductSpaceCoreInteriorSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    PreInnerProductSpace.Core ℝ (InteriorSmoothScalar g) where
  inner f h := interiorSmoothScalarH1Inner f h
  conj_inner_symm f h := by
    change (interiorSmoothScalarH1Inner h f : ℝ) =
      interiorSmoothScalarH1Inner f h
    exact interiorSmoothScalarH1Inner_symm h f
  re_inner_nonneg f := by
    change (0 : ℝ) ≤ interiorSmoothScalarH1Inner f f
    exact interiorSmoothScalarH1Inner_nonneg f
  add_left f₁ f₂ h := by
    change interiorSmoothScalarH1Inner (f₁ + f₂) h =
      interiorSmoothScalarH1Inner f₁ h + interiorSmoothScalarH1Inner f₂ h
    exact interiorSmoothScalarH1Inner_add_left f₁ f₂ h
  smul_left f h c := by
    change interiorSmoothScalarH1Inner (c • f) h =
      c * interiorSmoothScalarH1Inner f h
    exact interiorSmoothScalarH1Inner_smul_left c f h

/-- The seminormed structure on `InteriorSmoothScalar g`. -/
noncomputable instance instSeminormedAddCommGroupInteriorSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup (InteriorSmoothScalar g) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

/-- The inner-product-space structure on `InteriorSmoothScalar g`. -/
noncomputable instance instInnerProductSpaceInteriorSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    InnerProductSpace ℝ (InteriorSmoothScalar g) :=
  InnerProductSpace.ofCore _

@[simp] lemma InteriorSmoothScalar.inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    @inner ℝ _ _ f h = interiorSmoothScalarH1Inner f h := rfl

end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
