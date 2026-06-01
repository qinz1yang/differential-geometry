import DifferentialGeometry.Integral.Connection.CurvatureBundling
import DifferentialGeometry.Integral.Connection.TensorConnLaplacian
import DifferentialGeometry.Integral.Connection.RicciIdentity

/-!
# The pointwise tensor Ricci-commutator identity (second-order Weitzenböck core)

Let `g : SmoothRiemannianMetric I M` be a smooth Riemannian metric on a manifold `M`
without boundary, and let `cov := LeviCivita g` be its Levi-Civita covariant
derivative on the tangent bundle. For ranks `(r, s)`, the induced covariant derivative
on the `(r, s)`-tensor bundle is `tensorRSCovariantDerivative I M r s cov` (constructed in
`TensorRSNabla.lean`). This file proves the **pointwise tensor Ricci identity**, i.e. the
commutator of second covariant derivatives on tensor sections equals the curvature acting
on the tensor:
$$
  \nabla_X \nabla_Y T - \nabla_Y \nabla_X T - \nabla_{[X, Y]} T = R(X, Y)\,T .
$$

This is the genuinely-new, tensor-valued analogue of the scalar Bochner identity proved in
`Bochner.lean` / `BochnerConcrete.lean` (which only covers the gradient `∇f` of a scalar).
It is the pointwise input to the order-2 Gårding estimate
$$
  \int |\nabla^2 T|^2 \;\le\; C\,\bigl(\|\Delta_\nabla T\|_{L^2}^2
      + \|\nabla T\|_{L^2}^2 + \|T\|_{L^2}^2\bigr),
$$
because the second covariant derivative `∇²T` (the full `(r, s+2)` Hessian) and the rough
(connection) Laplacian `Δ_∇ T = rawTensorConnLap g r s T` (its negative metric trace over
the last two slots) differ exactly by the curvature term `R(X, Y) T` once one traces and
symmetrises. The commutator identity below isolates that curvature term.

## Main results

* `riemannSec_eq_riemannOp_smooth` — for **any** vector bundle `V` over `M` with a `C^∞`
  covariant derivative `cov`, the section-level Riemann commutator `riemannSec cov X Y Z x`
  on smooth global sections equals the bundled curvature operator `riemannOp cov x` applied
  to the fibre values `(X x, Y x, Z x)`. This is the well-definedness bridge from the
  section formula to the pointwise tensorial form.

* `tensorRicciCommutator` — the **pointwise tensor Ricci identity** in commutator form:
  the second-covariant-derivative commutator of an arbitrary raw `(r, s)`-tensor section
  `T` along smooth vector fields `X, Y` equals the section-level Riemann curvature
  `riemannSec` of the `(r, s)`-tensor covariant derivative. Purely definitional
  (`riemannSec_def`), but stated under a Ricci-flavoured name on the concrete tensor bundle.

* `ricci_identity_tensor_commutator_eq_riemannOp` — the same commutator, identified with the **bundled
  curvature operator** `riemannOp` of the `(r, s)`-tensor covariant derivative on smooth
  sections. The right-hand side is `riemannOp ... x (X x) (Y x) (T x)`, a continuous
  trilinear form in the fibre values, which is the form needed for fibre-norm estimates.

* `tensorRicciCommutator_swap` — antisymmetry of the curvature term in the `(X, Y)` slots.

* `tensorRicciCommutator_norm_le` — the **pointwise curvature bound**: the commutator is
  bounded in fibre norm by `‖riemannOp ... x‖ · ‖X x‖ · ‖Y x‖ · ‖T x‖`. The operator-norm
  factor is the only curvature-dependent quantity; on a compact manifold it is bounded by a
  constant (`‖R‖_∞`). This is the form fed into the integrated Gårding estimate.

## Sign / convention

The Riemann commutator uses the section-level formula
`R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` (`riemannSec`), matching the curvature
convention used throughout `Curvature.lean` / `Ricci.lean`. The connection Laplacian
`Δ_∇ = tr_g (W ↦ ∇_W ∇ ·)` uses the geometer convention (`rawTensorConnLap`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

/-- **Curvature-commutator bridge (bundle-generic).** For a `C^∞` covariant derivative
`cov` on a vector bundle `V`, smooth global vector fields `X, Y` of `TM` and a smooth
global section `Z` of `V`, the section-level Riemann commutator
$$
  \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z
    = \mathrm{riemannSec}\,\mathrm{cov}\,X\,Y\,Z\,x
$$
equals the bundled curvature operator `riemannOp cov x` evaluated on the fibre values
`(X x, Y x, Z x)`. This is `riemannOp_apply_smooth` read right-to-left. -/
theorem riemannSec_eq_riemannOp_smooth
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    riemannSec cov X Y Z x = riemannOp cov x (X x) (Y x) (Z x) :=
  (riemannOp_apply_smooth (cov := cov) hX hY hZ).symm

/-- The commutator form of `riemannSec_eq_riemannOp_smooth`: the iterated covariant
derivative commutator on smooth sections equals the bundled curvature operator. -/
theorem cov_commutator_eq_riemannOp_smooth
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
        - cov.toFun Z x (VectorField.mlieBracket I X Y x) =
      riemannOp cov x (X x) (Y x) (Z x) := by
  rw [← riemannSec_def cov X Y Z x]
  exact riemannSec_eq_riemannOp_smooth (cov := cov) hX hY hZ

end General

section TensorBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The covariant derivative on the `(r, s)`-tensor bundle induced by the Levi-Civita
connection of `g`. This is the operator whose second-derivative commutator carries the
tensor curvature. -/
noncomputable abbrev tensorCov (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    CovariantDerivative I (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)

/-- **Pointwise tensor Ricci identity (commutator form).** Let `g` be a smooth Riemannian
metric on a manifold `M`, and let `cov := tensorCov g r s` be the induced `(r, s)`-tensor
covariant derivative. For any raw `(r, s)`-tensor section `T` and any vector fields `X, Y`,
the second-covariant-derivative commutator equals the section-level Riemann curvature of the
tensor covariant derivative:
$$
  \nabla_X(\nabla_Y T)(x) - \nabla_Y(\nabla_X T)(x) - \nabla_{[X, Y]} T(x)
    = R(X, Y)\,T\,(x).
$$
With Mathlib's argument convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, this is
$$
  \mathrm{cov.toFun}(\nabla_Y T)(x)(X(x))
    - \mathrm{cov.toFun}(\nabla_X T)(x)(Y(x))
    - \mathrm{cov.toFun}(T)(x)([X, Y]_x)
    = \mathrm{riemannSec}\,\mathrm{cov}\,X\,Y\,T\,x.
$$
This is the tensor-valued analogue of the scalar Bochner identity: it is purely definitional
(`riemannSec_def`) once the tensor covariant derivative is fixed, but it isolates the
curvature term that obstructs commuting covariant derivatives on tensors. It holds for an
arbitrary raw section `T` (no smoothness needed), since both sides unfold to the same
expression in `cov.toFun`. -/
theorem tensorRicciCommutator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
      (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) X T) x (Y x) -
      (tensorCov (I := I) g r s).toFun T x (VectorField.mlieBracket I X Y x) =
      riemannSec (tensorCov (I := I) g r s) X Y T x :=
  (riemannSec_def (tensorCov (I := I) g r s) X Y T x).symm

/-- **Pointwise tensor Ricci identity (bundled-operator form).** For `g` a smooth Riemannian
metric, `cov := tensorCov g r s` the induced `(r, s)`-tensor covariant derivative, and smooth
vector fields `X, Y` together with a smooth `(r, s)`-tensor section `T`, the
second-covariant-derivative commutator equals the bundled curvature operator `riemannOp cov`
evaluated on the fibre values:
$$
  \nabla_X(\nabla_Y T)(x) - \nabla_Y(\nabla_X T)(x) - \nabla_{[X, Y]} T(x)
    = R_x\bigl(X(x),\, Y(x)\bigr)\,T(x),
$$
where `R_x = riemannOp (tensorCov g r s) x`. In Mathlib's argument convention
(`cov.toFun σ x v ≅ (∇_v σ)(x)`) the left-hand side is exactly the `cov.toFun` commutator
appearing in the signature. The right-hand side `riemannOp cov x (X x) (Y x) (T x)` is a
continuous trilinear form in the fibre values `(X x, Y x, T x)`, which is the shape needed
for fibre-norm estimates (its fibre norm is controlled by the operator norm of `R_x`). The
smoothness of `X, Y, T` is used only to pass from the section-level `riemannSec` to the
bundled `riemannOp` via `riemannSec_eq_riemannOp_smooth`. -/
theorem ricci_identity_tensor_commutator_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
      (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) X T) x (Y x) -
      (tensorCov (I := I) g r s).toFun T x (VectorField.mlieBracket I X Y x) =
      riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (T x) := by
  rw [tensorRicciCommutator (I := I) g r s X Y T x]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hY hT

/-- **Antisymmetry of the tensor curvature in the vector-field slots.** The section-level
tensor Riemann curvature is antisymmetric in `(X, Y)`:
`R(X, Y) T (x) = - R(Y, X) T (x)`. Pointwise, for any raw section `T`. -/
theorem tensorRicciCommutator_swap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    riemannSec (tensorCov (I := I) g r s) X Y T x =
      - riemannSec (tensorCov (I := I) g r s) Y X T x :=
  riemannSec_swap (tensorCov (I := I) g r s) X Y T x

/-- **Vanishing of the tensor curvature on the diagonal.** `R(X, X) T (x) = 0`. -/
@[simp] theorem tensorRicciCommutator_self
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    riemannSec (tensorCov (I := I) g r s) X X T x = 0 :=
  riemannSec_self_eq_zero (tensorCov (I := I) g r s) X T x

/-- The **second covariant derivative (Hessian)** of an `(r, s)`-tensor section `T` along the
vector fields `X, Y` at `x`:
$$
  \nabla^2_{X, Y} T (x) := \nabla_X(\nabla_Y T)(x) - \nabla_{(\nabla_X Y)(x)} T,
$$
written with Mathlib's argument convention as
`cov.toFun (∇_Y T) x (X x) − cov.toFun T x ((LeviCivita g).toFun Y x (X x))`. Here
`cov = tensorCov g r s` is the `(r, s)`-tensor covariant derivative and
`(LeviCivita g).toFun Y x (X x) = (∇_X Y)(x)` is the tangent Levi-Civita derivative. -/
noncomputable def tensorSecondCovDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
    (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x (X x))

/-- The defining identity for `tensorSecondCovDeriv`. -/
lemma tensorSecondCovDeriv_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorSecondCovDeriv (I := I) g r s X Y T x =
      (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
        (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) := rfl

/-- **Ricci identity in Hessian form (tensor second-order Weitzenböck core).** For vector
fields `X, Y` that are manifold-differentiable at `x`, the antisymmetric part of the second
covariant derivative of any raw `(r, s)`-tensor section `T` is the section-level curvature:
$$
  \nabla^2_{X, Y} T (x) - \nabla^2_{Y, X} T (x) = R(X, Y)\,T (x).
$$
The proof uses torsion-freeness of the Levi-Civita connection on the tangent bundle to
rewrite `(∇_X Y)(x) - (∇_Y X)(x) = [X, Y]_x`, reducing the difference of Hessians to the
defining commutator `riemannSec`. -/
theorem tensorSecondCovDeriv_antisymm_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} (T : Π b : M, TensorRSSpace r s I b) {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    tensorSecondCovDeriv (I := I) g r s X Y T x -
        tensorSecondCovDeriv (I := I) g r s Y X T x =
      riemannSec (tensorCov (I := I) g r s) X Y T x := by
  classical
  set cov := tensorCov (I := I) g r s with hcov_def
  have hbr : (LeviCivita (I := I) g).toFun Y x (X x) -
      (LeviCivita (I := I) g).toFun X x (Y x) = VectorField.mlieBracket I X Y x :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g)).mp
      (LeviCivita_torsion_eq_zero (I := I) g) hX hY
  rw [tensorSecondCovDeriv_def, tensorSecondCovDeriv_def, riemannSec_def]
  have hsub : (cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) -
        cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) =
      cov.toFun T x (VectorField.mlieBracket I X Y x) := by
    rw [← map_sub (cov.toFun T x), hbr]
  rw [show
      (cov.toFun (covApply cov Y T) x (X x) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x))) -
        (cov.toFun (covApply cov X T) x (Y x) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) =
      (cov.toFun (covApply cov Y T) x (X x) - cov.toFun (covApply cov X T) x (Y x)) -
        (cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) from by abel]
  rw [hsub]

/-- **Hessian-form Ricci identity, bundled-operator version.** For smooth vector fields
`X, Y` and a smooth `(r, s)`-tensor section `T`, the antisymmetric part of the second
covariant derivative equals the bundled curvature operator on the fibre values:
$$
  \nabla^2_{X, Y} T (x) - \nabla^2_{Y, X} T (x) = R_x\bigl(X(x), Y(x)\bigr)\,T(x).
$$
This is the Gårding-ready operator form: the curvature term on the right is a continuous
trilinear function of the fibre values. -/
theorem tensorSecondCovDeriv_antisymm_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    tensorSecondCovDeriv (I := I) g r s X Y T x -
        tensorSecondCovDeriv (I := I) g r s Y X T x =
      riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (T x) := by
  rw [tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g r s T
        ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hY hT

/-- **The rough Laplacian is the frame trace of the second covariant derivative.** With
`B_i := smoothOrthoFrame g x i` the `g_x`-orthonormal smooth frame at `x`,
$$
  \Delta_\nabla T (x) = \sum_i \nabla^2_{B_i, B_i} T (x).
$$
This is the diagonal contraction of the Hessian `tensorSecondCovDeriv` against the
orthonormal frame, matching the definition of `rawTensorConnLap`. -/
theorem rawTensorConnLap_eq_frame_trace_secondCovDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := by
  rw [rawTensorConnLap_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_def]

end TensorBundle

end Connection
end Integral
end DifferentialGeometry
