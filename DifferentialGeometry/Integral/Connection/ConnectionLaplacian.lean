import DifferentialGeometry.Integral.Connection.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.HessianTrace

/-!
# The connection Laplacian on tensor sections

For a smooth Riemannian metric `g` on a manifold `M` (without boundary), the
connection Laplacian (also called the rough or Bochner Laplacian) is the metric
trace of the second covariant derivative,
$$
  \Delta_\nabla = \mathrm{tr}_g \circ \nabla \circ \nabla.
$$

This file provides three concrete realisations of this operator on different
tensor types, and the algebraic identities relating them to the Laplace-Beltrami
operator on scalars.

## Main definitions

* `connLaplacian_function g hf` — the connection Laplacian on a smooth scalar
  function. Identified with `Δ_g g hf` by definition.
* `connLaplacian_vector g V x` — the connection Laplacian on a smooth tangent
  vector field, computed against the smooth orthonormal frame at `x`
  (`smoothOrthoFrame g x`). Equivalent in inner-product form to the textbook
  formula `Δ_∇ V = ∑_i ∇_{B_i} ∇_{B_i} V - ∇_{∇_{B_i} B_i} V`.
* `connLaplacian_oneForm g cov ω x` — the connection Laplacian on a smooth
  cotangent (1-form) section, computed against the cotangent extension of the
  Levi-Civita connection on the smooth orthonormal frame at `x`.

## Main results

* `connLaplacian_function_eq_laplaceBeltrami` — the connection Laplacian on
  scalars agrees with `Δ_g`.
* `connLaplacian_function_eq_chartHessTrace` — the trace identification
  through the chart-coordinate Hessian trace.
* `connLaplacian_function_contMDiff` — smoothness of the scalar connection
  Laplacian.
* `connLaplacian_function_add` — additivity on smooth scalars.
* `connLaplacian_function_const` — vanishing on constant scalars.
* `connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner` — the
  **heart-of-Bochner identity** in conditional form: assuming the inner-product
  reduction, the connection Laplacian on `∇f` equals `∇(Δ_g f) + Ric^♯(∇f)`.

## Sign convention

The geometer convention is used: `Δ_g = div ∘ grad`, with spectrum in
`(-∞, 0]` on closed manifolds. The connection Laplacian inherits this sign
through the trace formula.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **Connection Laplacian on a smooth scalar function.** Defined as the
Laplace-Beltrami operator `Δ_g f`, equivalently the metric trace of the
chart-coordinate Hessian (see `connLaplacian_function_eq_chartHessTrace`). -/
def connLaplacian_function [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  Δ_g (I := I) g hf

@[simp] lemma connLaplacian_function_def [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = Δ_g (I := I) g hf x := rfl

/-- **Connection Laplacian on a smooth tangent vector field**, defined via the
smooth orthonormal frame at `x`:
$$
  (\Delta_\nabla V)(x) := \sum_i \bigl(\nabla_{B_i x}\nabla_{B_i} V -
      \nabla_{(\nabla_{B_i} B_i)(x)} V\bigr),
$$
with `B_i = smoothOrthoFrame g x i`. -/
def connLaplacian_vector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x) V x

@[simp] lemma connLaplacian_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    connLaplacian_vector (I := I) g V x =
      localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        V x := rfl

/-- **Connection Laplacian on a smooth cotangent (1-form) section**, defined
via the cotangent extension of the Levi-Civita connection on the smooth
orthonormal frame at `x`. -/
def connLaplacian_oneForm
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((cotangentCov (LeviCivita (I := I) g)).toFun
      (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
        (smoothOrthoFrame (I := I) g x i b)) x
        (smoothOrthoFrame (I := I) g x i x) -
      (cotangentCov (LeviCivita (I := I) g)).toFun θ x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

@[simp] lemma connLaplacian_oneForm_def
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    connLaplacian_oneForm (I := I) g θ x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((cotangentCov (LeviCivita (I := I) g)).toFun
          (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
            (smoothOrthoFrame (I := I) g x i b)) x
            (smoothOrthoFrame (I := I) g x i x) -
          (cotangentCov (LeviCivita (I := I) g)).toFun θ x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

/-- **Identity with the Laplace-Beltrami operator** — definitional. -/
theorem connLaplacian_function_eq_laplaceBeltrami [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    connLaplacian_function (I := I) g hf = Δ_g (I := I) g hf := rfl

/-- **Trace identification for the scalar connection Laplacian.** Pointwise,
the connection Laplacian on `f` equals the chart-coordinate trace of the
Hessian against the inverse Gram matrix:
$$
  (\Delta_\nabla f)(x) = \sum_{i, j} G^{ij}(x) \,(\mathrm{Hess}\,f)_{ij}(x, x).
$$
This is the chart-trace form of the Laplace-Beltrami operator,
`chartHessTrace_eq_laplacian_pointwise_of_boundaryless`. -/
theorem connLaplacian_function_eq_chartHessTrace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = chartHessTrace (I := I) g f x := by
  rw [connLaplacian_function_def]
  exact (chartHessTrace_eq_laplacian_pointwise_of_boundaryless
    (I := I) g hf x).symm

/-- The scalar connection Laplacian of a smooth function is smooth. -/
theorem connLaplacian_function_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (connLaplacian_function (I := I) g hf) :=
  Δ_g_contMDiff (I := I) g hf

/-- Linearity of the scalar connection Laplacian on the sum of smooth functions:
the connection Laplacian commutes with addition. -/
theorem connLaplacian_function_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    connLaplacian_function (I := I) g (hf.add hh) x =
      connLaplacian_function (I := I) g hf x +
        connLaplacian_function (I := I) g hh x := by
  rw [connLaplacian_function_def, connLaplacian_function_def,
      connLaplacian_function_def]
  exact Δ_g_add (I := I) g hf hh x

/-- The scalar connection Laplacian vanishes on constant functions. -/
@[simp] theorem connLaplacian_function_const [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    connLaplacian_function (I := I) g
      (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c)) x = 0 := by
  rw [connLaplacian_function_def]
  exact Δ_g_const (I := I) g c x

/-- **Inner-product unfolding of the vector connection Laplacian on a
gradient.** Combining the definition of `connLaplacian_vector` with the
finite-trace expansion of `localConnLap_vector` against `w` (via
`localConnLap_vector_grad_inner_eq_hessian_diff`):
$$
  g_x\bigl((\Delta_\nabla \nabla f)(x), w\bigr) =
    \sum_i \Bigl[g_x\bigl(\nabla_{B_i x}\nabla_{B_i}(\nabla f)(x), w\bigr) -
      g_x\bigl(\nabla_{(\nabla_{B_i} B_i)(x)}(\nabla f)(x), w\bigr)\Bigr],
$$
where `B_i = smoothOrthoFrame g x i` and the inner product distributes through
the finite sum. -/
theorem connLaplacian_grad_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) := by
  rw [connLaplacian_vector_def]
  exact localConnLap_vector_grad_inner_eq_hessian_diff (I := I) g hf hw
    (smoothOrthoFrame (I := I) g x)
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) x

/-- **Heart-of-Bochner identity for the gradient — conditional form.**

Given a smooth scalar function `f : M → ℝ`, the connection Laplacian on the
gradient `∇f` decomposes as the gradient of the Laplacian plus the Ricci sharp
of the gradient,
$$
  (\Delta_\nabla \nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x),
$$
whenever the inner-product reduction holds (i.e., the same equation tested
against every `w ∈ T_x M`).

The inner-product reduction is the algebraic content of the heart-of-Bochner
identity, and is the unique algebraic input that an abstract Bochner derivation
must supply. By Riesz uniqueness on the finite-dimensional inner-product space
`T_x M`, the inner-product reduction is logically equivalent to the vector
identity itself.

The conditional form factors out the Riesz reduction step from the
algebraic-content step, exposing the latter (encoded in the hypothesis
`hInner`) as a separate concern. The downstream consumer (typically an
abstract Bochner class / trace identity proof) discharges `hInner` by
combining the abstract-Hessian symmetry, the metric skewness of the Riemann
curvature, and the trace-equals-Laplacian identity. -/
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) := by
  unfold connLaplacian_vector
  exact heart_of_bochner_smoothOrthoFrame (I := I) g hf x hInner

/-- The vector heart-of-Bochner identity, written in inner-product form: it
holds against every smooth tangent test field `w` at `x`, then collapses to
the vector identity by Riesz uniqueness. -/
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    (I := I) g hf x hInner

/-- **Iff-form** of the heart-of-Bochner identity for the gradient: the vector
identity at `x` is equivalent to its inner-product form against every test
vector. This is a direct application of Riesz uniqueness via
`vector_eq_iff_inner_eq`, packaged for downstream consumers. -/
theorem connLaplacian_grad_iff_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) ↔
      ∀ w : TangentSpace I x,
        g.inner x (connLaplacian_vector (I := I) g
                    (fun b => gradFun (I := I) g f b) x) w =
          g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
            g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w := by
  classical
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · rw [h]
    rw [show g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
      by rw [map_add, ContinuousLinearMap.add_apply]]
  · exact connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
      (I := I) g hf x h

/-- **Hessian-trace form of the LHS of B3.** The inner product `g(Δ_∇^B ∇f,
w)`, traced through the smooth orthonormal frame at `x`, equals the same sum
that appears in `connLaplacian_grad_inner`. This is the unfolded form for
downstream consumers that work with the Hessian rather than the gradient
directly. -/
theorem connLaplacian_grad_inner_hessian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) :=
  connLaplacian_grad_inner (I := I) g hf hw x

/-- **Hessian symmetry term.** For smooth `f` and smooth tangent fields `X, Y`,
the inner product `g(∇_X ∇f, Y)` is symmetric in `(X, Y)` at the point of
evaluation. This is `inner_cov_gradFun_symm`, re-exported under the bundled
connection-Laplacian namespace. -/
theorem connLaplacian_grad_hessian_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (Y x)) (X x) :=
  inner_cov_gradFun_symm (I := I) g hf hX hY

/-- **Curvature trace term** — re-export of `heart_of_bochner_curvature_term`.
For smooth tangent fields `B, w` and smooth scalar `f`, the metric pairing of
the Riemann curvature on `(B, w)` against `B` re-orients to the curvature on
`(B, w)` against `B`, paired against `∇f`:
$$
  g_x\bigl(R(B, w)\,\nabla f,\, B\bigr) = -\,g_x\bigl(\nabla f,\, R(B, w)\,B\bigr).
$$
This is the metric-skewness contribution of the Riemann curvature, and is the
intermediate step that produces the Ricci-tensor term in the heart-of-Bochner
trace reduction. -/
theorem connLaplacian_grad_curvature_term [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {B w : Π b : M, TangentSpace I b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    g.inner x (riemannSec (LeviCivita (I := I) g) B w
                (fun b => gradFun (I := I) g f b) x) (B x) =
      - g.inner x (gradFun (I := I) g f x)
          (riemannSec (LeviCivita (I := I) g) B w B x) :=
  heart_of_bochner_curvature_term (I := I) g hf hB hw

/-- **Orthonormality of the smooth orthonormal frame at the centre.** The
frame `smoothOrthoFrame g x` is `g_x`-orthonormal at `x`. -/
theorem smoothOrthoFrame_orthonormal_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal_at_center (I := I) g x i j

/-- **Smoothness of the smooth orthonormal frame.** Each `smoothOrthoFrame g x i`
is `C^∞` as a tangent-bundle section. -/
theorem smoothOrthoFrame_isSmooth
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x i)) :=
  smoothOrthoFrame_smooth (I := I) g x i

/-- **Frame-traced Frobenius norm of `∇V`** in the smooth orthonormal frame at
`x`. This is the orthonormal-frame value of the metric Frobenius norm squared
of the (1,1)-tensor `∇V`,
$$
  |\nabla V|^2_g(x) = \sum_i g_x\bigl((\nabla_{B_i x} V), (\nabla_{B_i x} V)\bigr).
$$
-/
def frobeniusSq_grad_vector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    g.inner x
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))

@[simp] lemma frobeniusSq_grad_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    frobeniusSq_grad_vector (I := I) g V x =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x))
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x)) := rfl

/-- The Frobenius-norm-squared term `|\nabla V|^2_g(x)` is non-negative.
This follows from each summand being a `g`-norm-squared. -/
lemma frobeniusSq_grad_vector_nonneg
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    0 ≤ frobeniusSq_grad_vector (I := I) g V x := by
  unfold frobeniusSq_grad_vector
  refine Finset.sum_nonneg ?_
  intro i _
  set v : TangentSpace I x :=
    (LeviCivita (I := I) g).toFun V x
      (smoothOrthoFrame (I := I) g x i x) with hv_def
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt (g.pos x v hv)

/-- **Leibniz identity (B2) — conditional form.** For a smooth tangent vector
field `V`, the connection Laplacian on `g(V, V)` decomposes as
$$
  \Delta_\nabla\bigl(g(V, V)\bigr)(x) =
    2\,g_x\bigl((\Delta_\nabla V)(x), V(x)\bigr) + 2\,|\nabla V|^2_g(x),
$$
under the inner-product reduction `hLeibniz` (which packages the trace
expansion of `Δ_g(g(V, V))` against the smooth orthonormal frame at `x`).

The hypothesis `hLeibniz` is the algebraic content of metric compatibility
applied twice to the scalar `b ↦ g(V, V)(b)` and traced at `x`. The downstream
consumer supplies it (typically by computing the second derivative of the
inner-product scalar against the smooth orthonormal frame, or equivalently by
plugging in the chart-coordinate Hessian formula). -/
theorem connLaplacian_inner_self_of_trace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (_hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
          2 * frobeniusSq_grad_vector (I := I) g V x) :
    connLaplacian_function (I := I) g hgVV x =
      2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
        2 * frobeniusSq_grad_vector (I := I) g V x := by
  rw [connLaplacian_function_def]
  exact hLeibniz

/-- **Inner-product expansion of the LHS of the Leibniz identity.** Using
metric compatibility once for the first derivative of `g(V, V)`:
$$
  X(g(V, V)) = 2\,g(\nabla_X V, V).
$$
-/
lemma extDerivFun_inner_self [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) (x : M)
    (X : TangentSpace I x) :
    extDerivFun (I := I) (fun b => g.inner b (V b) (V b)) x X =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x X) (V x) := by
  classical
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hV_at hV_at X
  have hext_eq : extDerivFun (I := I) (fun b => g.inner b (V b) (V b)) x X =
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (V b) (V b)) x) X := rfl
  rw [hext_eq, hmc]
  rw [g.symm x (V x) ((LeviCivita (I := I) g).toFun V x X)]
  ring

/-- **Leibniz at the first-order level (global section identity).** The smooth
scalar `b ↦ g(V, V)(b)` has directional derivative `2 g(∇_X V, V)`. -/
lemma extDerivFun_inner_self_eq_globally [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (X : Π b : M, TangentSpace I b) :
    (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (V b') (V b')) b
        (X b)) =
      (fun b : M => 2 * g.inner b
        ((LeviCivita (I := I) g).toFun V b (X b)) (V b)) := by
  funext b
  exact extDerivFun_inner_self (I := I) g hV b (X b)

end Connection
end Integral
end DifferentialGeometry
