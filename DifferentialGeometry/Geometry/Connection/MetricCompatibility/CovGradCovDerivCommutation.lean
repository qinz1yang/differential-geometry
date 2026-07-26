import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock

/-!
# The rank-generic leading-slot gradient/covariant-derivative commutation

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
this file establishes the **rank-generic single-direction gradient-slot commutation** of the
covariant gradient `covGrad g 0 s : (0, s) → (0, s + 1)` with a directional covariant derivative
`∇_Y` along a fixed smooth tangent field `Y` — the classical Ricci identity `[∇_Y, ∇] = R(Y, ·)`
lifted to the covariant-gradient bundle formalism, where the curvature acts on the *leading*
(gradient) slot.

The mechanism is the **unit-evaluation reduction** of `GradientField.lean`: at upper rank `r = 0`,
the value of a `(0, s + 1)`-tensor is recovered by evaluating against the constant unit
`(0, 0)`-tensor, which is `∇`-parallel, so the whole computation pushes into the *abstract*
`(0, s)`-tensor covariant derivative `tensor0SCovariantDerivative I M s (LeviCivita g)`. There the
single-direction commutator is the bundle-generic first-order Ricci atom
`cov_commutator_eq_riemannOp_smooth`, whose curvature term is the bundled Riemann operator
`riemannOp` of the abstract `(0, s)`-tensor connection.

## Main result

* `covGrad_covDeriv_leadingSlot_commutation_genVal` — the rank-generic first-order commutation:
  the directional covariant derivative `∇_Y(∇S)` of the gradient field minus the covariant gradient
  `∇(∇_Y S)` of the directional covariant derivative is, at the unit-evaluation, the leading-slot
  Riemann operator `R(v 0, Y)` acting on the unit-evaluated section `V := S(·)(unit)`.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian. The covariant gradient
`covGrad g 0 s` curries the new tangent-direction slot as the leftmost (gradient) covariant slot,
the convention produced by the directional covariant derivative. The Riemann curvature uses the
section-level formula `R(X, Y) Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` (`riemannSec`/`riemannOp`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The unit-evaluated section** `V y := S(y)(unit)`, a smooth abstract `(0, s)`-tensor section
obtained by evaluating the smooth `(0, s)`-tensor `S` at the constant unit `(0, 0)`-tensor. This is
the section the abstract `(0, s)`-tensor covariant derivative differentiates in the unit-evaluation
reduction. -/
noncomputable def unitEvalSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    Π y : M, Tensor0SSpace s I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
      (unitZeroSec (I := I) (M := M) y)

set_option linter.unusedSectionVars false in
@[simp] lemma unitEvalSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (y : M) :
    unitEvalSection (I := I) (M := M) g s S y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

/-- **Slot-`0` curry of `covGradBundleEquiv` at the unit (general valence).** For a covariant-gradient
fibre element `Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x`, the slot-`0` curry of the
`(0, s + 1)`-tensor `covGradBundleEquiv 0 s x Φ`, evaluated at the unit `(0, 0)`-tensor and read along
`v`, recovers `(Φ v)` evaluated at the unit:
```
curry (covGradBundleEquiv 0 s x Φ)(unit) (v) = (Φ v)(unit).
```
This is the general-valence analogue of `tensor0S_curry_covGradBundleEquiv_unit` (its `s = 2` instance);
the proof reads both sides on a `Fin s`-tuple via the curry evaluation `tensor0S_curry_apply_eval` and
the slot-`0` evaluation `covGradBundleEquiv_apply_eval`. -/
lemma tensor0S_curry_covGradBundleEquiv_unit_genVal
    (s : ℕ) (x : M) (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x)
    (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ v)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
      (unitZeroSec (I := I) (M := M) x)) (v0 := v) (vs := m)]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 s x Φ
    (unitZeroSec (I := I) (M := M) x) (Fin.cons v m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons v m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

/-- **The slot-`0` curry of the unit-evaluated gradient field is the abstract directional covariant
derivative of the unit-evaluated section (pointwise).** For any tangent vector `w` at `x`,
```
curry (unitGradFieldGen g s S)_x (w) = ∇^{abs}_w V (x),
```
with `V := unitEvalSection g s S` and `∇^{abs}` the abstract `(0, s)`-tensor covariant derivative. The
proof combines the slot-`0` curry reading `curry_unitGradFieldGen_eq` (which gives the directional
covariant derivative of `S` evaluated at the unit) with the unit-transport `covDeriv_unit_eval_eq_genVal`
(the unit `(0, 0)`-section is `∇`-parallel). -/
lemma curriedSection_unitGradFieldGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (w : TangentSpace I x) :
    Tensor0SNabla.curriedSection I M (unitGradFieldGen (I := I) (M := M) g s S) x w =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
        (unitEvalSection (I := I) (M := M) g s S) x w := by
  rw [curry_unitGradFieldGen_eq (I := I) (M := M) g s S x w]
  rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s S x w]
  exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection x w

/-- **The unit-evaluated gradient field is the abstract covariant gradient of the unit-evaluated
section.** The slot-`0` curry of `U := unitGradFieldGen g s S` along a smooth field `Z` recovers the
abstract `(0, s)`-tensor directional covariant derivative `covApply (∇^{abs}) Z V` of the
unit-evaluated section `V := unitEvalSection g s S`:
```
(y ↦ curry U_y (Z y)) = covApply (tensor0SCovariantDerivative I M s (LeviCivita g)) Z V.
```
The unit `(0, 0)`-section is `∇`-parallel, so the directional covariant derivative of `S` evaluated at
the unit transports straight through to the abstract `(0, s)`-tensor connection of `V`. This is the
structural identity that reduces the gradient-slot commutation to a purely abstract `(0, s)` statement;
its proof combines `curry_unitGradFieldGen_eq` (the slot-`0` curry of `U` is `∇_w S(·)(unit)`) with the
unit-transport `covDeriv_unit_eval_eq_genVal`. -/
lemma curriedSection_unitGradFieldGen_eq_covApply_abstract
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Z : Π b : M, TangentSpace I b) :
    (fun y : M => Tensor0SNabla.curriedSection I M
        (unitGradFieldGen (I := I) (M := M) g s S) y (Z y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Z
        (unitEvalSection (I := I) (M := M) g s S) := by
  funext y
  rw [curriedSection_unitGradFieldGen_apply (I := I) (M := M) g s S y (Z y), covApply_apply]

/-- **Transport of the `(0, s)` second covariant derivative of `S` through the unit.** For a smooth
tangent field `B`, the second covariant derivative `tensorSecondCovDeriv g 0 s B B S` of `S`, evaluated
at the unit `(0, 0)`-tensor, equals the abstract `(0, s)`-tensor second covariant derivative of the
unit-evaluated section `V := unitEvalSection g s S`:
```
(∇²_{B, B} S)(x)(unit)
  = ∇^{abs}_B(∇^{abs}_B V)(x) − ∇^{abs}_{(∇^{TM}_B B)(x)} V (x).
```
This is the rank-`s` analogue of `tensorSecondCovDeriv_covGrad_unit_eval_genVal` (which transports the
second covariant derivative of the *gradient* field); the proof ports verbatim, the slot-uniform
`tensorSecondCovDeriv` definition combined with the unit-transports `covDeriv_unit_eval_eq_genVal` and
`covApply_unit_eval_eq_genVal` on the `(0, s)`-tensor section `S.toSection`. -/
lemma tensorSecondCovDeriv_unit_eval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorSecondCovDeriv (I := I) g 0 s B B
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (LeviCivita (I := I) g)) B
            (unitEvalSection (I := I) (M := M) g s S)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [ContinuousLinearMap.sub_apply]
  congr 1
  · set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
      ContMDiffSection.mk
        (fun y : M => covApply (tensorCov (I := I) g 0 s) B (fun z : M => S.toSection z) y)
        (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hB) with hσ
    have h1 := covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s σ x (B x)
    have hσapp : ∀ y, σ y =
        covApply (tensorCov (I := I) g 0 s) B (fun z : M => S.toSection z) y := fun y => rfl
    simp only [hσapp] at h1
    rw [h1]
    rw [covApply_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection B]
    rfl
  · rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection x
      ((LeviCivita (I := I) g).toFun B x (B x))]
    rfl

/-- **Smoothness of the unit-evaluated section.** `V := unitEvalSection g s S` is a smooth section of
the `(0, s)`-tensor bundle, as the application of the smooth `(0, s)`-tensor section `S` (in
Hom-bundle form `Tensor0SSpace 0 →L Tensor0SSpace s`) to the smooth unit `(0, 0)`-section. -/
lemma contMDiff_unitEvalSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (unitEvalSection (I := I) (M := M) g s S y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace s I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y))) :=
    S.toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace s I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel s ℝ E) hϕ hv

/-- **The leading-slot reading of the directionally-derived gradient field is the abstract second
covariant derivative (the curvature-free `A`-side reduction).** For smooth fields `Y, Z` and a smooth
`(0, s)`-tensor `S`, the slot-`0` curry at `Z` of the unit-evaluation of the directional covariant
derivative `∇_Y(∇S)` of the gradient field equals the abstract `(0, s)`-tensor second covariant
derivative of `V := unitEvalSection g s S` along `(Y, Z)`:
```
curry (∇_Y(∇S))(x)(unit) (Z x)
  = ∇^{abs}_Y(∇^{abs}_Z V)(x) − ∇^{abs}_{(∇^{TM}_Y Z)(x)} V (x).
```
The proof transports the outer covariant derivative through the unit (`covDeriv_unit_eval_eq_genVal`),
identifying `(∇_Y(∇S))(x)(unit)` with the abstract `(0, s + 1)` directional derivative of the abstract
gradient field `U := unitGradFieldGen g s S`, then exposes the slot-`0` Christoffel correction
(`abstract_succ_covDeriv_unfold_at_genVal`) and reads each slot-`0` curry of `U` as the abstract
directional derivative of `V` (`curriedSection_unitGradFieldGen_eq_covApply_abstract`,
`curriedSection_unitGradFieldGen_apply`). No curvature appears: this is the genuine Hessian-form
reduction, the workhorse of the leading-slot commutation. -/
lemma covGrad_covDeriv_leadingSlot_eq_abstractHess
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (tensorCov (I := I) g 0 (s + 1)).toFun
            (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
          (unitZeroSec (I := I) (M := M) x)) (Z x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Z
            (unitEvalSection (I := I) (M := M) g s S)) x (Y x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun Z x (Y x)) := by
  classical

  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (tensorCov (I := I) g 0 (s + 1)).toFun
          (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x (Y x) from
    covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection x (Y x)]

  rw [abstract_succ_covDeriv_unfold_at_genVal (I := I) (M := M) g s
    (unitGradFieldGen (I := I) (M := M) g s S) (Vfield := Y) (Y := Z) (x := x)
    ((contMDiff_curried_unitGradFieldGen (I := I) (M := M) g s S x).mdifferentiableAt (by simp))
    ((hY x).mdifferentiableAt (by simp)) ((hZ x).mdifferentiableAt (by simp))]

  rw [curriedSection_unitGradFieldGen_eq_covApply_abstract (I := I) (M := M) g s S Z]
  rw [curriedSection_unitGradFieldGen_apply (I := I) (M := M) g s S x
    ((LeviCivita (I := I) g).toFun Z x (Y x))]

/-- **The leading-slot reading of the covariant gradient of the directional derivative is the abstract
iterated covariant derivative (the curvature-free `D`-side reduction).** For a smooth field `Y`, a
smooth `(0, s)`-tensor `S`, and a tangent vector `w` at `x`, the slot-`0` curry at `w` of the
unit-evaluation of the covariant gradient `∇(∇_Y S)` of the directional covariant derivative equals the
abstract `(0, s)`-tensor iterated covariant derivative `∇^{abs}_w(∇^{abs}_Y V)(x)`:
```
curry (∇(∇_Y S))(x)(unit) (w) = ∇^{abs}_w(∇^{abs}_Y V)(x).
```
The slot-`0` curry at the unit of `covGradBundleEquiv` reads the directional covariant derivative
(`tensor0S_curry_covGradBundleEquiv_unit_genVal`); the unit-transport `covDeriv_unit_eval_eq_genVal`
then pushes both the inner `∇_Y` and the outer `∇_w` into the abstract `(0, s)`-tensor connection of
`V := unitEvalSection g s S`. No curvature appears: `Y` is a fixed differentiation direction (no
slot-`0` Christoffel), so the outer covariant gradient passes straight to the abstract iterated
derivative. -/
lemma covGrad_covDeriv_inner_leadingSlot_eq_abstractIter
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Y : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x))
          (unitZeroSec (I := I) (M := M) x)) w =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Y
            (unitEvalSection (I := I) (M := M) g s S)) x w := by
  classical

  rw [tensor0S_curry_covGradBundleEquiv_unit_genVal (I := I) (M := M) s x
    ((tensorCov (I := I) g 0 s).toFun
      (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x) w]

  set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
    ContMDiffSection.mk
      (fun y : M => covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hY) with hσ
  have hσapp : ∀ y, σ y =
      covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y := fun y => rfl
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x w)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => σ y) x w)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [show (fun y : M => σ y) =
      (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) from
      funext (fun y => hσapp y)]]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s σ x w]

  rw [show (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Y
        (unitEvalSection (I := I) (M := M) g s S) from by
    funext y
    rw [hσapp y, covApply_apply, covApply_apply]
    rw [show (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          (tensorCov (I := I) g 0 s) (fun z : M => S.toSection z) y (Y y))
          (unitZeroSec (I := I) (M := M) y) =
        ((tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g))
          (fun z : M => S.toSection z) y (Y y))
          (unitZeroSec (I := I) (M := M) y) from rfl]
    rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection y (Y y)]
    rfl]

/-- **The rank-generic leading-slot covGrad/covDeriv commutation (the K-A linchpin).** For a smooth
`(0, s)`-tensor `S` and smooth tangent fields `Y, Z`, the difference of the two leading-slot readings —
the directional covariant derivative `∇_Y(∇S)` of the gradient field, and the covariant gradient
`∇(∇_Y S)` of the directional covariant derivative — both curried at `Z` and read at the unit, is the
**leading-slot Riemann curvature** `R(Y, Z)` acting on `V := unitEvalSection g s S`, modulo the
single-direction slot-`0` Christoffel correction `∇^{abs}_{(∇^{TM}_Z Y)} V`:
```
curry (∇_Y(∇S))(x)(unit) (Z x) − curry (∇(∇_Y S))(x)(unit) (Z x)
  = R(Y, Z)(V)(x) − ∇^{abs}_{(∇^{TM}_Z Y)(x)} V (x),
```
with `R = riemannSec (tensor0SCovariantDerivative I M s (LeviCivita g))` the abstract `(0, s)`-tensor
Riemann curvature and `(∇^{TM}_Z Y)(x) = (LeviCivita g).toFun Y x (Z x)`.

This is the classical Ricci identity `[∇_Y, ∇] = R(Y, ·)` lifted to the covariant-gradient bundle: the
curvature is genuinely **off-diagonal** — `R(Y, Z)` with `Y` the differentiation direction and `Z` the
leading (gradient) slot direction, distinct slots, never the antisymmetric `R(Y, Y) = 0`. The honest
slot-`0` Christoffel term `∇^{abs}_{∇_Z Y} V` is the non-tensorial single-direction correction (it
reads the first jet of the slot direction `Z` along `Y`); it cancels when the atom is applied within
the symmetric Hessian (frame trace) of the order-`2` Bochner defect, leaving the genuine curvature.

**Proof.** The two leading-slot readings reduce — curvature-free — to the abstract `(0, s)`-tensor
Hessian `∇^{abs}_Y(∇^{abs}_Z V) − ∇^{abs}_{∇_Y Z} V` (`covGrad_covDeriv_leadingSlot_eq_abstractHess`)
and the abstract iterated derivative `∇^{abs}_Z(∇^{abs}_Y V)`
(`covGrad_covDeriv_inner_leadingSlot_eq_abstractIter`). Their difference is the abstract Ricci
commutator `riemannSec` (`riemannSec_def` on the abstract connection) plus the bracket term, which the
torsion-freeness of the Levi-Civita connection (`LeviCivita_torsion_eq_zero`) folds together with the
two Christoffel corrections into the single residual `−∇^{abs}_{∇_Z Y} V`. -/
theorem covGrad_covDeriv_leadingSlot_commutation
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (tensorCov (I := I) g 0 (s + 1)).toFun
            (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
          (unitZeroSec (I := I) (M := M) x)) (Z x) -
      tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x))
          (unitZeroSec (I := I) (M := M) x)) (Z x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Y Z
          (unitEvalSection (I := I) (M := M) g s S) x -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun Y x (Z x)) := by
  classical
  set nab := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) with hnab
  set V := unitEvalSection (I := I) (M := M) g s S with hV

  rw [covGrad_covDeriv_leadingSlot_eq_abstractHess (I := I) (M := M) g s S hY hZ x]
  rw [covGrad_covDeriv_inner_leadingSlot_eq_abstractIter (I := I) (M := M) g s S hY x (Z x)]

  rw [riemannSec_def nab Y Z V x]

  have hbr : (LeviCivita (I := I) g).toFun Z x (Y x) -
      (LeviCivita (I := I) g).toFun Y x (Z x) = VectorField.mlieBracket I Y Z x :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g)).mp
      (LeviCivita_torsion_eq_zero (I := I) g)
      ((hY x).mdifferentiableAt (by simp)) ((hZ x).mdifferentiableAt (by simp))

  have hdir : (LeviCivita (I := I) g).toFun Z x (Y x) =
      VectorField.mlieBracket I Y Z x + (LeviCivita (I := I) g).toFun Y x (Z x) := by
    rw [← hbr]; abel

  rw [hdir, map_add]
  abel

end Connection
end Integral
end DifferentialGeometry

end
