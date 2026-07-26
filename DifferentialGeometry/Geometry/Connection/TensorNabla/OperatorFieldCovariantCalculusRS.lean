import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldDifferentiatedTowerNormalForm
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval

/-! # The operator-field covariant calculus at a generic contravariant valence

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the operator-field calculus of `OperatorFieldCovariantCalculus` and the
differentiated-tower normal-form engine of `OperatorFieldDifferentiatedTowerNormalForm` act on a
**contravariant-rank-`0`** contracted section: `appCc Φ W` post-composes an `(r, s)`-operator field
`Φ` after a `(0, r)`-tensor `W`.  This file lifts the entire engine to a section whose contravariant
valence is a *generic* `a` (R7 — extend, do not duplicate), so that a contravariant-valence-`r`
differentiated curvature tower can consume the same normal-form jet envelope the rank-`0` tower
consumes.

The operator-field action at valence `a` is the fibrewise composition
```
(appCcRS Φ W) x := (Φ x).comp (W x) : Tensor0SSpace a I x →L Tensor0SSpace c I x = TensorRSSpace a c I x,
```
where `Φ x : Tensor0SSpace b I x →L Tensor0SSpace c I x` is the fibre of a `(b, c)`-operator field and
`W x : Tensor0SSpace a I x →L Tensor0SSpace b I x` is the fibre of an `(a, b)`-tensor.  The rank-`0`
action `appCc g r s Φ W` is the special case `appCcRS g 0 r s Φ W` (`appCcRS_zero_eq_appCc`).

## What this file provides

* `appCcRS` / `appCcRS_toSection` — the operator-field action at generic contravariant valence, and
  its definitional fibre-value formula; smoothness through the same two `ContMDiff.clm_bundle_apply`
  evaluations as the rank-`0` action;
* `appCcRS_add_left`, `appCcRS_add_right`, `appCcRS_smul_left`, `appCcRS_smul_right`,
  `appCcRS_zero_left`, `appCcRS_neg_left`, `appCcRS_sub_left` — `ℝ`-bilinearity of the action;
* `covGrad_appCcRS_eq` — the slot-augmented covariant product rule (the B-rule) at valence `a`:
  `covGrad (appCcRS Φ W) = appCcRS (covGrad Φ) W + appCcRS (slotExtend Φ) (covGrad W)`, the carrier
  on which the differentiated-curvature operator-field double induction runs;
* `riemannianFiberNormSq_compRS_le_mul` / `exists_uniform_riemannianFiberNormSq_appCcRS_le` — the
  intrinsic partial-contraction Cauchy–Schwarz and the uniform section-proportional fibre envelope
  for the action at valence `a`;
* `NormalFormRS`, `normalForm_of_baseRS`, `exists_jet_bound_of_normalFormRS` — the operator-field
  normal form of a recursively-differentiated tower and its jet envelope, at generic contravariant
  valence.

Every result mirrors its rank-`0` original sorry-free; the lift is mechanical because the underlying
covariant gradient `covGrad`, directional covariant derivative `tensorCovDerivAt`, and Hom-connection
product rule `tensorRSCovariantDerivative_apply` are all stated at generic valence, and the
passenger-slot extension `slotExtend g b c : SmoothCcTensor g b c → SmoothCcTensor g (b + 1) (c + 1)`
is itself already valence-generic (it inserts a covariant slot, untouched by the contravariant input).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## The operator-field action at generic contravariant valence -/

set_option backward.isDefEq.respectTransparency false in
/-- **The fibrewise operator-field action value at valence `a`.** The fibre value at `x` of the action
of a `(b, c)`-operator field `Φ` on an `(a, b)`-tensor `W`: the fibrewise composition
`(Φ x).comp (W x) : Tensor0SSpace a I x →L Tensor0SSpace c I x = TensorRSSpace a c I x`. -/
def appCcRSFib (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (x : M) :
    TensorRSSpace a c I x :=
  (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the operator-field action fibre field at valence `a`.** The
`(a, c)`-tensor fibre field `x ↦ appCcRSFib g a b c Φ W x = (Φ x).comp (W x)` is a smooth section:
pointwise on any smooth `(0, a)`-tensor `Y`, its value `Φ x (W x (Y x))` is smooth by two
applications of `ContMDiff.clm_bundle_apply`, and `contMDiff_clm_section_of_pointwise` lifts that
per-vector smoothness to the operator-valued section. -/
theorem appCcRSFib_contMDiff (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel a c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel a c ℝ E)
        (E := fun z : M => TensorRSSpace a c I z) x
        (appCcRSFib (I := I) (M := M) g a b c Φ W x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun x => appCcRSFib (I := I) (M := M) g a b c Φ W x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel c ℝ E)
      (E := fun z : M => Tensor0SSpace c I z) x
      (appCcRSFib (I := I) (M := M) g a b c Φ W x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel c ℝ E)
      (E := fun z : M => Tensor0SSpace c I z) x
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) (Y x)))) := by
    funext x; rfl
  rw [heq]
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel b ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel b ℝ E)
        (E := fun z : M => Tensor0SSpace b I z) x
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff Y.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hWY

set_option backward.isDefEq.respectTransparency false in
/-- **The operator-field action of a `(b, c)`-tensor field on an `(a, b)`-tensor**, as a smooth
compactly-supported `(a, c)`-tensor. The fibre value at `x` is the fibrewise composition
`(Φ x).comp (W x)` (`appCcRSFib`), smooth by `appCcRSFib_contMDiff`; on the closed manifold it has
compact support. This is the contravariant-valence-`a` lift of `appCc` (`appCc g r s Φ W` is the
special case `a = 0`, `b = r`, `c = s`). -/
def appCcRS (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) : SmoothCcTensor g a c where
  toSection :=
    { toFun := fun x : M => appCcRSFib (I := I) (M := M) g a b c Φ W x
      contMDiff_toFun := appCcRSFib_contMDiff (I := I) (M := M) g a b c Φ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `appCcRS g a b c Φ W` at `x` is the fibrewise composition
`(Φ x).comp (W x)`. Definitional. -/
@[simp] lemma appCcRS_toSection (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (x : M) :
    (appCcRS (I := I) (M := M) g a b c Φ W).toSection x =
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) := rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The rank-`0` operator-field action is the `a = 0` case of `appCcRS`.** -/
theorem appCcRS_zero_eq_appCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCcRS (I := I) (M := M) g 0 r s Φ W = appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, appCc_toSection]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- Fibrewise operator-field application is associative with generic-valence composition. -/
theorem appCc_assoc (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (C : SmoothCcTensor g a b)
    (W : SmoothCcTensor g 0 a) :
    appCc (I := I) (M := M) g b c Φ (appCc (I := I) (M := M) g a b C W) =
      appCc (I := I) (M := M) g a c (appCcRS (I := I) (M := M) g a b c Φ C) W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection, appCc_toSection, appCcRS_toSection,
    ContinuousLinearMap.comp_assoc]

/-! ## Bilinearity of the operator-field action at valence `a` -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is additive in the contracted `(a, b)`-tensor. -/
theorem appCcRS_add_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c Φ (W₁ + W₂) =
      appCcRS (I := I) (M := M) g a b c Φ W₁ + appCcRS (I := I) (M := M) g a b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ W₁ + appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x) =
      (appCcRS (I := I) (M := M) g a b c Φ W₁).toSection x +
        (appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x from rfl]
  rw [appCcRS_toSection, appCcRS_toSection, appCcRS_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace a b I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.comp_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is `ℝ`-homogeneous in the contracted `(a, b)`-tensor. -/
theorem appCcRS_smul_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (k : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c Φ (k • W) =
      k • appCcRS (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • appCcRS (I := I) (M := M) g a b c Φ W).toSection x) =
      k • (appCcRS (I := I) (M := M) g a b c Φ W).toSection x from rfl]
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [show ((k • W).toSection x : TensorRSSpace a b I x) = k • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.comp_smul]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action distributes over subtraction in the contracted factor. -/
theorem appCcRS_sub_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c Φ (W₁ - W₂) =
      appCcRS (I := I) (M := M) g a b c Φ W₁ -
        appCcRS (I := I) (M := M) g a b c Φ W₂ := by
  calc
    appCcRS (I := I) (M := M) g a b c Φ (W₁ - W₂) =
        appCcRS (I := I) (M := M) g a b c Φ (W₁ + (-W₂)) := by
      rw [sub_eq_add_neg]
    _ = appCcRS (I := I) (M := M) g a b c Φ W₁ +
        appCcRS (I := I) (M := M) g a b c Φ (-W₂) :=
      appCcRS_add_right (I := I) (M := M) g a b c Φ W₁ (-W₂)
    _ = appCcRS (I := I) (M := M) g a b c Φ W₁ +
        -appCcRS (I := I) (M := M) g a b c Φ W₂ := by
      rw [show -W₂ = (-1 : ℝ) • W₂ by rw [neg_one_smul],
        appCcRS_smul_right, neg_one_smul]
    _ = appCcRS (I := I) (M := M) g a b c Φ W₁ -
        appCcRS (I := I) (M := M) g a b c Φ W₂ := by
      rw [sub_eq_add_neg]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is additive in the operator-field factor. -/
theorem appCcRS_add_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (Φ₁ + Φ₂) W =
      appCcRS (I := I) (M := M) g a b c Φ₁ W + appCcRS (I := I) (M := M) g a b c Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ₁ W + appCcRS (I := I) (M := M) g a b c Φ₂ W).toSection x) =
      (appCcRS (I := I) (M := M) g a b c Φ₁ W).toSection x +
        (appCcRS (I := I) (M := M) g a b c Φ₂ W).toSection x from rfl]
  rw [appCcRS_toSection, appCcRS_toSection, appCcRS_toSection]
  rw [show ((Φ₁ + Φ₂).toSection x : TensorRSSpace b c I x) = Φ₁.toSection x + Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_comp]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is zero in the zero operator-field factor. -/
theorem appCcRS_zero_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W = 0 := by
  have h := appCcRS_add_left (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) 0 W
  rw [add_zero] at h
  have h2 : appCcRS (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W -
      appCcRS (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W =
      appCcRS (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W := by
    nth_rewrite 1 [h]; abel
  rwa [sub_self] at h2

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is homogeneous under negation in the operator-field factor. -/
theorem appCcRS_neg_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (-Φ) W = -appCcRS (I := I) (M := M) g a b c Φ W := by
  have h := appCcRS_add_left (I := I) (M := M) g a b c Φ (-Φ) W
  rw [add_neg_cancel, appCcRS_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action distributes over subtraction in the operator-field factor. -/
theorem appCcRS_sub_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (Φ₁ - Φ₂) W =
      appCcRS (I := I) (M := M) g a b c Φ₁ W - appCcRS (I := I) (M := M) g a b c Φ₂ W := by
  rw [sub_eq_add_neg, appCcRS_add_left, appCcRS_neg_left, sub_eq_add_neg]

/-! ## The directional covariant product rule for the operator-field composition at valence `a`

The covariant derivative of the fibrewise composition `(Φ y).comp (W y)` (the value of `appCcRS Φ W`)
splits — directionally and at a point — into the standard composition Leibniz
```
∇_v ((Φ).comp W) = (∇_v Φ).comp (W x) + (Φ x).comp (∇_v W),
```
an equation of `(a, c)`-tensors, where `∇_v Φ = tensorCovDerivAt g b c Φ x v : TensorRSSpace b c I x`
and `∇_v W = tensorCovDerivAt g a b W x v : TensorRSSpace a b I x`.  The proof tests on an
`(0, a)`-tensor `d` (a local smooth section through it) and applies the Hom-connection product-rule
`tensorRSCovariantDerivative_apply` three times — to the `(a, c)`-section `appCcRS Φ W` paired with
`d`, to the `(b, c)`-section `Φ` paired with the `(0, b)`-section `y ↦ W y (d y)`, and to the
`(a, b)`-section `W` paired with `d` — the shared middle term cancelling, the surviving correction
matching on both sides. -/
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
theorem tensorCovDerivAt_appCcRS_eq (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (x : M) (v : E) :
    (show TensorRSSpace a c I x from
        tensorCovDerivAt (I := I) (M := M) g a c (appCcRS (I := I) (M := M) g a b c Φ W) x v) =
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g b c Φ x v).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) +
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
            tensorCovDerivAt (I := I) (M := M) g a b W x v) := by
  apply ContinuousLinearMap.ext
  intro d
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel a ℝ E) (V := fun y : M => Tensor0SSpace a I y) (n := (⊤ : ℕ∞)) x d
  have hWd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel b ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel b ℝ E)
        (E := fun z : M => Tensor0SSpace b I z) y
        ((show Tensor0SSpace a I y →L[ℝ] Tensor0SSpace b I y from W.toSection y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff dSec.contMDiff
  let Wd : Cₛ^∞⟮I; Tensor0SModel b ℝ E, (fun y : M => Tensor0SSpace b I y)⟯ :=
    ⟨fun y : M => (show Tensor0SSpace a I y →L[ℝ] Tensor0SSpace b I y from W.toSection y) (dSec y),
      hWd_smooth⟩

  have hLHS :
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g a c (appCcRS (I := I) (M := M) g a b c Φ W) x v) d =
        (Tensor0SNabla.tensor0SCovariantDerivative I M c (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace b I y →L[ℝ] Tensor0SSpace c I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
            ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M a (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    have hval : (fun y : M =>
          (show Tensor0SSpace a I y →L[ℝ] Tensor0SSpace c I y from
            (appCcRS (I := I) (M := M) g a b c Φ W).toSection y) (dSec y)) =
        (fun y : M =>
          (show Tensor0SSpace b I y →L[ℝ] Tensor0SSpace c I y from Φ.toSection y) (Wd y)) := by
      funext y
      rw [appCcRS_toSection (I := I) (M := M) g a b c Φ W y]
      rfl
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g a c (appCcRS (I := I) (M := M) g a b c Φ W) x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) a c (LeviCivita (I := I) g)
        (appCcRS (I := I) (M := M) g a b c Φ W).toSection dSec x v, hval,
      appCcRS_toSection (I := I) (M := M) g a b c Φ W x, ContinuousLinearMap.comp_apply]

  have hT1 :
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g b c Φ x v)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) d) =
        (Tensor0SNabla.tensor0SCovariantDerivative I M c (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace b I y →L[ℝ] Tensor0SSpace c I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M b (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) := by
    rw [show (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) d = Wd x from by
      rw [show d = dSec x from hdSec.symm]; rfl,
      tensorCovDerivAt_def (I := I) (M := M) g b c Φ x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) b c (LeviCivita (I := I) g)
        Φ.toSection Wd x v]

  have hT2 :
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
          tensorCovDerivAt (I := I) (M := M) g a b W x v) d) =
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M b (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) -
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
            ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M a (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g a b W x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) a b (LeviCivita (I := I) g)
        W.toSection dSec x v]
    rw [map_sub (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)]
    rfl
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hLHS, hT1, hT2]
  abel

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Slot-`0` reading of the slot-extended operator field on a curried `(a, b + 1)`-tensor at valence
`a`.** The leading covariant passenger slot of `tensor0S_curry b x D v0` (the slot read first by
`slotExtendFib_apply_eval`) recovers, for `D = (covGrad g a b W).toSection x d` the covariant gradient
of the contracted `(a, b)`-section, the directional covariant derivative `(tensorCovDerivAt g a b W x
v0) d`. -/
theorem tensor0S_curry_covGrad_appCcRS_eq (g : SmoothRiemannianMetric I M) (a b : ℕ)
    (W : SmoothCcTensor g a b) (x : M) (d : Tensor0SSpace a I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) b x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (b + 1) I x from
          (covGrad (I := I) (M := M) g a b W).toSection x) d) v0 =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
        tensorCovDerivAt (I := I) (M := M) g a b W x v0) d := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (b + 1) I x from
      (covGrad (I := I) (M := M) g a b W).toSection x) d) (v0 := v0) (vs := m)]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g a b W x d (Fin.cons v0 m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons v0 m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

/-! ## The slot-augmented covariant product rule (B-rule) for the operator-field action at valence `a`

The covariant gradient of the operator-field action `appCcRS Φ W` of a `(b, c)`-operator field `Φ` on
an `(a, b)`-tensor `W` splits into two operator-field actions: the action of the gradient
`covGrad g b c Φ` (a `(b, c + 1)`-operator field) on `W`, plus the action of the passenger-slot
extension `slotExtend Φ` (a `(b + 1, c + 1)`-operator field) on the gradient `covGrad g a b W` (an
`(a, b + 1)`-tensor):
```
covGrad g a c (appCcRS Φ W) = appCcRS (covGrad g b c Φ) W + appCcRS (slotExtend Φ) (covGrad g a b W).
```
This is the section-level packaging of the directional rule `tensorCovDerivAt_appCcRS_eq`.  It is the
carrier on which the differentiated-curvature operator-field double induction expresses `∇(op p rr W)`
as `appCcRS (∇Φ_{p,rr}) W`. -/
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
theorem covGrad_appCcRS_eq (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    covGrad (I := I) (M := M) g a c (appCcRS (I := I) (M := M) g a b c Φ W) =
      appCcRS (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W +
        appCcRS (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCcRS (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W +
        appCcRS (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b W)).toSection x) =
      (appCcRS (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W).toSection x +
        (appCcRS (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g a c (appCcRS (I := I) (M := M) g a b c Φ W) x d v]

  rw [appCcRS_toSection (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W x,
    ContinuousLinearMap.comp_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g b c Φ x
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) d) v]

  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (appCcRS (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
            (covGrad (I := I) (M := M) g a b W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
          ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
            tensorCovDerivAt (I := I) (M := M) g a b W x (v 0)) d))
        (Matrix.vecTail v) := by
    rw [appCcRS_toSection (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
        (covGrad (I := I) (M := M) g a b W) x, ContinuousLinearMap.comp_apply,
      slotExtend_toSection (I := I) (M := M) g b c Φ x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g b c x
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (b + 1) I x from
        (covGrad (I := I) (M := M) g a b W).toSection x) d) (v 0) (Matrix.vecTail v)]
    rw [tensor0S_curry_covGrad_appCcRS_eq (I := I) (M := M) g a b W x d (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]

  rw [show (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from
        tensorCovDerivAt (I := I) (M := M) g a c (appCcRS (I := I) (M := M) g a b c Φ W) x (v 0)) =
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g b c Φ x (v 0)).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) +
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
            tensorCovDerivAt (I := I) (M := M) g a b W x (v 0)) from
    tensorCovDerivAt_appCcRS_eq (I := I) (M := M) g a b c Φ W x (v 0)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

/-! ## The intrinsic partial-contraction Cauchy–Schwarz at valence `a`

The fibre value of the operator-field action `appCcRS Φ W` is the fibrewise composition
`(Φ x).comp (W x) : Tensor0SSpace a I x →L Tensor0SSpace c I x`, an `(a, c)`-tensor.  Its frame
components are the matrix–vector product of the contracted tensor's components against the operator
field's components, and a per-row discrete Cauchy–Schwarz over the contracted multi-index gives the
Hilbert–Schmidt submultiplicativity of tensor contraction, phrased intrinsically:
```
rfns_{(a,c)}((Φ x).comp (W x)) ≤ rfns_{(b,c)}(Φ x) · rfns_{(a,b)}(W x).
```
The lift from rank `0` (`riemannianFiberNormSq_comp_le_mul`) replaces the empty contravariant index by
a generic `K : Fin a → Fin n`, untouched by the composition. -/

set_option linter.unusedSectionVars false in
/-- **A single `g_x`-orthonormal tensor frame represents the fibre norm at every valence.** The frame
`e := stdOrthonormalBasis ℝ (TangentSpace I x)` (the one inside `riemannianFiberNormSq`) is
`g_x`-orthonormal, arises from a `Module.Basis`, and represents `riemannianFiberNormSq` at *every*
valence `(p, q)` as the frame double sum — the last clause is definitional (`rfl`).  This packages the
multi-valence frame data the partial-contraction Cauchy–Schwarz needs (the operator field, the
contracted section, and their composition are read in one common frame). -/
private lemma exists_orthoFrameRS_repr_anyvalence
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (p q : ℕ) (S : TensorRSSpace p q I x),
        riemannianFiberNormSq (I := I) (M := M) g p q x S =
          ∑ K : Fin p → Fin n, ∑ J : Fin q → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x p q S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, eob.toBasis, ?_, ?_, ?_⟩
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth i j
    rw [← hinner_eq (eob i) (eob j)]
    exact hite
  · intro p q S
    rfl

set_option linter.unusedSectionVars false in
/-- **The operator-field action's frame components are the matrix–vector product, at valence `a`.** For
a `g_x`-orthonormal tensor frame `e` (built from a `Module.Basis`), the `(a, c)`-component of the
fibrewise composition `(Φ x).comp (W x)` along the contravariant multi-index `K` and the output index
`J` is the contraction sum, over the rank-`b` multi-index `P`, of the `(a, b)`-component of `W x` along
`(K, P)` against the `(b, c)`-component of `Φ x` along `(P, J)`.  The proof expands `W x` applied to the
contravariant coframe covector through the coframe basis (`tensorS_coframe_expansion`), distributes the
operator field linearly, and reads each summand off as the product of the two component scalars. -/
private lemma fiberNormSqComponent_compRS_eq
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (x : M)
    (Φx : TensorRSSpace b c I x) (Wx : TensorRSSpace a b I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin a → Fin n) (J : Fin c → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x a c
        (show TensorRSSpace a c I x from
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
            (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) n e K J =
      ∑ P : Fin b → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
          fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := by
  classical
  change (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K k)))))
      (fun k => e (J k)) = _
  set wval : Tensor0SSpace b I x :=
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) with hwval
  have hexp := tensorS_coframe_expansion (I := I) (M := M) g x b e bse hbse horth wval
  conv_lhs => rw [hexp]
  rw [map_sum]
  rw [show (∑ P : Fin b → Fin n,
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          ((wval (fun k : Fin b => e (P k))) • coframeS (I := I) (M := M) g x b e P)) =
      ∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P) from by
    refine Finset.sum_congr rfl (fun P _ => ?_); rw [map_smul]]
  rw [show ((∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel (∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) from rfl]
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply]
  have hΦcomp : Tensor0SSpace.toModel
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
        (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) =
      fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := rfl
  rw [hΦcomp]
  have hwcomp : wval (fun k : Fin b => e (P k)) =
      fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P := rfl
  rw [hwcomp, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- **The intrinsic partial-contraction Cauchy–Schwarz for the operator-field action at valence `a`.**
The intrinsic squared Riemannian fibre norm of the fibrewise composition `(Φ x).comp (W x)` is bounded
by the product of the fibre norms of the operator field and the contracted section:
```
rfns_{(a,c)}((Φ x).comp (W x)) ≤ rfns_{(b,c)}(Φ x) · rfns_{(a,b)}(W x).
```
Parseval-expanding all three fibre norms in a single `g_x`-orthonormal tensor frame, the composition's
frame components are the matrix–vector product `∑_P (W x)_{K,P} · (Φ x)_{P,J}`
(`fiberNormSqComponent_compRS_eq`), and a per-row discrete Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) over the contracted index `P`, summed over the output index `J` and
the contravariant index `K`, gives the Hilbert–Schmidt bound. -/
theorem riemannianFiberNormSq_compRS_le_mul
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (x : M)
    (Φx : TensorRSSpace b c I x) (Wx : TensorRSSpace a b I x) :
    riemannianFiberNormSq (I := I) (M := M) g a c x
        (show TensorRSSpace a c I x from
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
            (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) ≤
      riemannianFiberNormSq (I := I) (M := M) g b c x Φx *
        riemannianFiberNormSq (I := I) (M := M) g a b x Wx := by
  classical
  obtain ⟨n, e, bse, hbse, horth, hrepr⟩ :=
    exists_orthoFrameRS_repr_anyvalence (I := I) (M := M) g x

  have hreprAC : ∀ S : TensorRSSpace a c I x,
      riemannianFiberNormSq (I := I) (M := M) g a c x S =
        ∑ K : Fin a → Fin n, ∑ J : Fin c → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x a c S n e K J := hrepr a c
  have hreprAB : ∀ S : TensorRSSpace a b I x,
      riemannianFiberNormSq (I := I) (M := M) g a b x S =
        ∑ K : Fin a → Fin n, ∑ P : Fin b → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x a b S n e K P := hrepr a b
  have hreprBC : ∀ S : TensorRSSpace b c I x,
      riemannianFiberNormSq (I := I) (M := M) g b c x S =
        ∑ P : Fin b → Fin n, ∑ J : Fin c → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x b c S n e P J := hrepr b c
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x a c e hreprAC _]
  have hWrepr : (∑ K : Fin a → Fin n, ∑ P : Fin b → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g a b x Wx := by
    rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x a b e hreprAB Wx]
  have hΦrepr : (∑ P : Fin b → Fin n, ∑ J : Fin c → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g b c x Φx := by
    rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x b c e hreprBC Φx]

  have hcomp_eq : ∀ (K : Fin a → Fin n) (J : Fin c → Fin n),
      fiberNormSqComponent (I := I) (M := M) g x a c
          (show TensorRSSpace a c I x from
            (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
              (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) n e K J =
        ∑ P : Fin b → Fin n,
          fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
            fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J :=
    fun K J => fiberNormSqComponent_compRS_eq (I := I) (M := M) g a b c x Φx Wx e bse hbse horth K J
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun J (_ : J ∈ Finset.univ) => by rw [hcomp_eq K J]))]

  set rfnsΦ : ℝ := riemannianFiberNormSq (I := I) (M := M) g b c x Φx with hrfnsΦ_def
  have hrfnsΦ_nonneg : 0 ≤ rfnsΦ := riemannianFiberNormSq_nonneg (I := I) (M := M) g b c x Φx

  have hper_row : ∀ K : Fin a → Fin n,
      (∑ J : Fin c → Fin n,
          (∑ P : Fin b → Fin n,
            fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
              fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J) ^ 2) ≤
        (∑ P : Fin b → Fin n, (fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P) ^ 2) *
          rfnsΦ := by
    intro K
    refine le_trans (Finset.sum_le_sum (fun J (_ : J ∈ Finset.univ) =>
      Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
        (fun P : Fin b → Fin n => fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P)
        (fun P : Fin b → Fin n => fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J))) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun P _ => sq_nonneg _))
    rw [← hΦrepr]
    exact le_of_eq Finset.sum_comm

  refine le_trans (Finset.sum_le_sum (fun K (_ : K ∈ Finset.univ) => hper_row K)) ?_
  rw [← Finset.sum_mul, hWrepr, mul_comm]

set_option linter.unusedSectionVars false in
/-- **The uniform section-proportional fibre envelope for the operator-field action at valence `a`.**
For a *fixed* smooth compactly-supported `(b, c)`-operator field `Φ` on a closed Riemannian manifold,
there is a single nonnegative constant `C`, uniform over `M`, with
```
rfns(appCcRS Φ W)(x) ≤ C · rfns(W)(x)
```
for every smooth compactly-supported `(a, b)`-tensor `W` and every point `x`.  The constant `C` is the
global fibre-norm bound for the *fixed* smooth section `Φ`
(`exists_bound_riemannianFiberNormSq_smoothCcTensor`); it depends only on `Φ`, never on `W`.  The
pointwise step is the intrinsic partial-contraction Cauchy–Schwarz `riemannianFiberNormSq_compRS_le_mul`
followed by the uniform bound on `rfns(Φ x)`.

This is the bridge by which the iterated covariant gradient `∇^p Φ₀` of a curvature-coefficient
operator field — itself a fixed smooth `(b, b + p)`-tensor with a uniform fibre-norm bound — yields the
section-proportional high-order envelope of a contravariant-valence-`a` differentiated curvature tower
with no chart-selection-unbounded data. -/
theorem exists_uniform_riemannianFiberNormSq_appCcRS_le
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (Φ : SmoothCcTensor g b c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g a b) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g a c x
          ((appCcRS (I := I) (M := M) g a b c Φ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x) := by
  obtain ⟨K, hK_nn, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor g b c Φ
  refine ⟨K, hK_nn, fun W x => ?_⟩
  rw [appCcRS_toSection (I := I) (M := M) g a b c Φ W x]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g a b c x
    (Φ.toSection x) (W.toSection x)) ?_
  exact mul_le_mul_of_nonneg_right (hK x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g a b x (W.toSection x))

/-! ## The operator-field normal form of a differentiated tower at contravariant valence `r`

For a recursively-differentiated tower `op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r
(rr + p)` whose single-step covariant Leibniz is the exact remainder
```
∇(op p rr W) = op (p + 1) rr W + (rank-cast) op p (rr + 1) (∇W),
```
the order-`p` value decomposes as a finite sum of operator-field actions of *fixed* smooth operator
fields `Ψ_{p,rr,k} : SmoothCcTensor g (rr + k) (rr + p)` on the covariant jets `∇^k W` of the
contracted `(r, rr)`-section (`NormalFormRS`).  This is the contravariant-valence-`r` lift of
`NormalForm`; the operator fields `Ψ` are themselves contravariant-rank `rr + k` (curvature data), and
the action `appCcRS` post-composes them after the `(r, rr + k)`-jet `∇^k W`.  The jet envelope follows
exactly as at rank `0`. -/

set_option linter.unusedSectionVars false in
/-- **Recast of an operator-field action through source- and target-rank equalities, at valence `r`.**
The rank-cast of an action `appCcRS Φ V` along an output-rank equality equals the action of the
doubly-recast operator field on the recast section. -/
theorem appCcRS_castRankCc_db {a a' b b' : ℕ} (g : SmoothRiemannianMetric I M) (r : ℕ)
    (ha : a = a') (hb : b = b')
    (Φ : SmoothCcTensor g a b) (V : SmoothCcTensor g r a) :
    castRankCc_db g r hb (appCcRS (I := I) (M := M) g r a b Φ V) =
      appCcRS (I := I) (M := M) g r a' b' (castSrcCc g b' ha (castRankCc_db g a hb Φ))
        (castRankCc_db g r ha V) := by
  subst ha; subst hb; rfl

/-- **The operator-field normal form of a differentiated tower at order `p`, valence `r`, width `rr`.**
The order-`p` tower value `op p rr W` decomposes as a finite sum of operator-field actions of fixed
smooth operator fields `Ψ k : SmoothCcTensor g (rr + k) (rr + p)` on the covariant jets `∇^k W` of the
contracted `(r, rr)`-section, `k < p + 1`. -/
def NormalFormRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (p rr : ℕ) : Prop :=
  ∃ Ψ : (k : ℕ) → SmoothCcTensor g (rr + k) (rr + p),
    ∀ W : SmoothCcTensor g r rr,
      op p rr W =
        ∑ k ∈ Finset.range (p + 1),
          appCcRS (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k) (iteratedCovGrad g r rr k W)

set_option linter.unusedSectionVars false in
/-- **The gradient of a normal-form sum expands termwise** through the operator-field covariant product
rule: each `appCcRS (Ψ k) (∇^k W)` contributes the differentiated-coefficient action `appCcRS (∇Ψ k)
(∇^k W)` plus the slot-extended action `appCcRS (slotExtend Ψ k) (∇^{k+1} W)`. -/
theorem covGrad_normalFormRS_sum (g : SmoothRiemannianMetric I M) (r p rr : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g (rr + k) (rr + p)) (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + p)
        (∑ k ∈ Finset.range (p + 1),
          appCcRS (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k) (iteratedCovGrad g r rr k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (appCcRS (I := I) (M := M) g r (rr + k) (rr + (p + 1))
            (covGrad (I := I) (M := M) g (rr + k) (rr + p) (Ψ k)) (iteratedCovGrad g r rr k W) +
          appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
            (slotExtend (I := I) (M := M) g (rr + k) (rr + p) (Ψ k))
            (iteratedCovGrad g r rr (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appCcRS_eq (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k) (iteratedCovGrad g r rr k W)]
  rw [show covGrad (I := I) (M := M) g r (rr + k) (iteratedCovGrad g r rr k W) =
      iteratedCovGrad g r rr (k + 1) W from (iteratedCovGrad_succ g r rr k W).symm]
  rfl

set_option linter.unusedSectionVars false in
/-- **The rank-cast lower-tower normal form on `∇W` re-expressed in canonical jets, at valence `r`.**
Each summand `cast(appCcRS (Ψ k) (∇^k(∇W)))` of `cast(op p (rr + 1) (∇W))` recasts to an operator-field
action on the canonical jet `∇^{k+1} W`. -/
theorem castRankCc_appCcRS_iteratedCovGrad_covGrad (g : SmoothRiemannianMetric I M) (r p rr k : ℕ)
    (Ψ : SmoothCcTensor g ((rr + 1) + k) ((rr + 1) + p)) (W : SmoothCcTensor g r rr) :
    castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1))
        (appCcRS (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + p) Ψ
          (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))) =
      appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
        (castSrcCc g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
          (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) Ψ))
        (iteratedCovGrad g r rr (k + 1) W) := by
  rw [appCcRS_castRankCc_db g r (by omega : (rr + 1) + k = rr + (k + 1))
    (by omega : (rr + 1) + p = rr + (p + 1)) Ψ (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g r rr k W)
  exact castRankCc_db_heq g r (by omega : (rr + 1) + k = rr + (k + 1))
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))

set_option linter.unusedSectionVars false in
/-- **The normal form propagates up the differentiated tower, at valence `r`.** If order `p` admits the
operator-field normal form at *every* width, then so does order `p + 1` at width `rr`.  The new operator
fields are built from the order-`p` ones by one covariant gradient, one passenger-slot extension, and
the rank-cast lower-tower coefficient — the three contributions of the exact covariant Leibniz, with the
non-cancelling slot-mismatch term landing on the new top jet `∇^{p+1} W`. -/
theorem normalFormRS_succ (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + p) (op p rr W) =
        op (p + 1) rr W +
          castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1)) (op p (rr + 1) (covGrad g r rr W)))
    (p : ℕ) (hp : ∀ rr, NormalFormRS (I := I) (M := M) g r op p rr) (rr : ℕ) :
    NormalFormRS (I := I) (M := M) g r op (p + 1) rr := by
  classical
  obtain ⟨Ψr, hΨr⟩ := hp rr
  obtain ⟨Ψr1, hΨr1⟩ := hp (rr + 1)

  set Tk : (k : ℕ) → SmoothCcTensor g (rr + (k + 1)) (rr + (p + 1)) := fun k =>
    slotExtend (I := I) (M := M) g (rr + k) (rr + p) (Ψr k) -
      castSrcCc g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
        (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) (Ψr1 k))
    with hTk_def

  refine ⟨fun j => match j with
    | 0 => covGrad (I := I) (M := M) g (rr + 0) (rr + p) (Ψr 0)
    | (k + 1) =>
        (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1)) else 0)
          + Tk k, ?_⟩
  intro W

  have hrec : op (p + 1) rr W =
      covGrad g r (rr + p) (op p rr W) -
        castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1))
          (op p (rr + 1) (covGrad g r rr W)) := by
    rw [covGrad_op p rr W]; abel
  rw [hrec, hΨr W]

  rw [covGrad_normalFormRS_sum (I := I) (M := M) g r p rr Ψr W]

  rw [hΨr1 (covGrad g r rr W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1))
          (appCcRS (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + p) (Ψr1 k)
            (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W)))) =
      ∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (castSrcCc g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g r rr (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appCcRS_iteratedCovGrad_covGrad (I := I) (M := M) g r p rr k (Ψr1 k) W)]

  rw [Finset.sum_add_distrib]

  rw [Finset.sum_range_succ' (fun j =>
    appCcRS (I := I) (M := M) g r (rr + j) (rr + (p + 1))
      ((match j with
        | 0 => covGrad (I := I) (M := M) g (rr + 0) (rr + p) (Ψr 0)
        | (k + 1) =>
            (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g r rr j W)) (p + 1)]

  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          ((if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appCcRS_add_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (slotExtend (I := I) (M := M) g (rr + k) (rr + p) (Ψr k))
          (iteratedCovGrad g r rr (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (castSrcCc g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appCcRS_sub_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1)))
          (iteratedCovGrad g r rr (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCcRS_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]

  rw [Finset.sum_range_succ' (fun k =>
    appCcRS (I := I) (M := M) g r (rr + k) (rr + (p + 1))
      (covGrad (I := I) (M := M) g (rr + k) (rr + p) (Ψr k)) (iteratedCovGrad g r rr k W)) p]

  abel

set_option linter.unusedSectionVars false in
/-- **The order-`0` base factorisation is the order-`0` normal form, at valence `r`.** If
`op 0 rr W = appCcRS Φ₀ W` for a fixed smooth operator field `Φ₀ : SmoothCcTensor g (rr + 0) (rr + 0)`,
then `op` admits the operator-field normal form at order `0`, width `rr`. -/
theorem normalForm_zeroRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (rr : ℕ) (Φ₀ : SmoothCcTensor g (rr + 0) (rr + 0))
    (hbase : ∀ W : SmoothCcTensor g r rr,
      op 0 rr W = appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0) Φ₀ W) :
    NormalFormRS (I := I) (M := M) g r op 0 rr := by
  refine ⟨fun k => match k with | 0 => Φ₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl

set_option linter.unusedSectionVars false in
/-- **The operator-field normal form holds at every order, at valence `r`.** A recursively-differentiated
tower `op` whose single-step covariant Leibniz is the exact remainder (`covGrad_op`) and whose order-`0`
base is a fixed-operator-field action at every width (`hbase`) admits the operator-field normal form at
every order `p` and width `rr`. -/
theorem normalForm_of_baseRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + p) (op p rr W) =
        op (p + 1) rr W +
          castRankCc_db g r (by omega : (rr + 1) + p = rr + (p + 1)) (op p (rr + 1) (covGrad g r rr W)))
    (Φ₀ : ∀ rr : ℕ, SmoothCcTensor g (rr + 0) (rr + 0))
    (hbase : ∀ (rr : ℕ) (W : SmoothCcTensor g r rr),
      op 0 rr W = appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0) (Φ₀ rr) W)
    (p : ℕ) : ∀ rr : ℕ, NormalFormRS (I := I) (M := M) g r op p rr := by
  induction p with
  | zero => exact fun rr => normalForm_zeroRS (I := I) (M := M) g r op rr (Φ₀ rr) (hbase rr)
  | succ p ih => exact fun rr => normalFormRS_succ (I := I) (M := M) g r op covGrad_op p ih rr

set_option linter.unusedSectionVars false in
/-- **The per-order, per-width jet envelope of a differentiated tower from its operator-field normal
form, at valence `r`.** If `op p rr` admits the operator-field normal form, then its intrinsic squared
fibre norm is bounded, uniformly over the compact `M`, by a nonnegative constant times the order-`≤ p`
covariant jet of the contracted section:
```
rfns(op p rr W)(x) ≤ kappa · ∑_{q < p + 1} rfns(∇^q W)(x).
```
Each `appCcRS (Ψ k)` summand is bounded by the uniform fibre-norm bound of the fixed smooth operator
field `Ψ k` (`exists_uniform_riemannianFiberNormSq_appCcRS_le`); the finite sum is accumulated by
`riemannianFiberNormSq_sum_le_card_mul`. -/
theorem exists_jet_bound_of_normalFormRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (p rr : ℕ) (hNF : NormalFormRS (I := I) (M := M) g r op p rr) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + p) x ((op p rr W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := hNF

  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k)
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩

  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g r (rr + k) x
    ((iteratedCovGrad g r rr k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + k) x _

  rw [hΨ W, SmoothCcTensor.toSection_sum_apply]

  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (rr + p) x
    (Finset.range (p + 1))
    (fun k => (appCcRS (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k)
      (iteratedCovGrad g r rr k W)).toSection x)) ?_
  rw [Finset.card_range]

  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + p) x
          ((appCcRS (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k)
            (iteratedCovGrad g r rr k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_

  have hCa_le : (∑ k ∈ Finset.range (p + 1), C k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by ring

end Connection
end Integral
end DifferentialGeometry

end
