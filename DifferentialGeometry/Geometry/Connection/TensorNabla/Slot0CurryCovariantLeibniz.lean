import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval

/-!
# The directional slot-`0` curry covariant Leibniz rule

For a smooth compactly-supported `(0, s + 1)`-tensor section `Z` and smooth tangent
vector fields `V, X` on a closed manifold, reading slot `0` of the directional
covariant derivative `∇_V Z` along `X` obeys the covariant Leibniz rule: it is the
directional covariant derivative along `V` of the slot-`0` `X`-read of `Z`, minus
the slot-`0` read of `Z` along the Christoffel correction `(∇_V X)(x)`.

* `tensor0S_curry_covApply_slot0_leibniz_fib` — the fibre-level form, an identity in
  the `(0, s)`-tensor fibre `Tensor0SSpace s I x`.
* `tensor0S_curry_covApply_slot0_leibniz` — the model-evaluated form on a
  `Fin s`-tuple, the shape consumed by the slot-`0` Parseval expansions of the
  integrated Bochner identities.

The proof is the Hom-bundle product rule: the `(0, s + 1)`-tensor covariant
derivative is the Hom-connection through the slot-`0` currying isomorphism
(`tensor0SCovariantDerivative_succ_fun`), so reading the unit-evaluated covariant
derivative along `X x` peels into the abstract `(0, s)`-covariant derivative of the
read section minus the Christoffel-corrected read
(`tensor0SCovariantDerivative_curriedSection_hom_leibniz`). The unit-evaluation
transfers between the `(0, s)`-Hom-bundle (`TensorRSSpace 0 s`) presentation and the
abstract `(0, s)`-tensor presentation with no correction term, since the unit
`(0, 0)`-section is parallel (`tensorRSCovariantDerivative_apply_of_mdifferentiableAt`
against `tensor0SCovariantDerivative_unitZero_eq_zero`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
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

set_option linter.unusedSectionVars false in
/-- The scalar-extraction functional evaluates to `1` on the unit `(0, 0)`-tensor. -/
private lemma tensor00Scalar_unitZeroSec (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper of a fibre tensor evaluates at the unit to the tensor itself. -/
private lemma tensor0SAsRS_unit_eval (t : ℕ) (x : M) (C : Tensor0SSpace t I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) = C := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) =
      tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) • C from
    tensor0SAsRS_apply (I := I) (M := M) x C (unitZeroSec (I := I) (M := M) x)]
  rw [tensor00Scalar_unitZeroSec (I := I) (M := M) x, one_smul]

set_option linter.unusedSectionVars false in
/-- The scalar read of a smooth `(0, 0)`-tensor section is a smooth real function. -/
private lemma contMDiff_tensor00Scalar_read
    (Y : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun z : M => Tensor0SSpace 0 I z)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) := by
  have heq : (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) =
      Tensor0SNabla.scalarFn I M (fun y : M => Y y) := by
    funext y
    rfl
  rw [heq]
  exact (Tensor0SNabla.contMDiff_scalarFn_iff_section I M (fun y : M => Y y)).mpr Y.contMDiff

/-- **Smoothness of the `tensor0SAsRS`-wrapped section.** If `C` is a smooth section of the
`(0, t)`-tensor bundle, then `y ↦ tensor0SAsRS y (C y)` is a smooth section of the
`(0, t)`-Hom-tensor bundle `TensorRSSpace 0 t`. By the pointwise smoothness criterion for
continuous-linear-map bundle sections it suffices that the application to every smooth
`(0, 0)`-section `Y` is smooth; that application is the scalar read of `Y` times `C`. -/
private lemma contMDiff_tensor0SAsRS_wrap (t : ℕ) {C : Π y : M, Tensor0SSpace t I y}
    (hC : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel t ℝ E)
        (E := fun z : M => Tensor0SSpace t I z) y (C y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y
        (tensor0SAsRS (I := I) (M := M) y (C y))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun z : M => Tensor0SSpace 0 I z)
    (F₂ := Tensor0SModel t ℝ E) (V₂ := fun z : M => Tensor0SSpace t I z)
    (φ := fun y : M => tensor0SAsRS (I := I) (M := M) y (C y))
  intro Y
  have hsmul := ContMDiff.smul_section (n := (∞ : WithTop ℕ∞))
    (contMDiff_tensor00Scalar_read (I := I) (M := M) Y) hC
  refine hsmul.congr fun y => ?_
  rw [show ((fun z : M => tensor00Scalar (I := I) (M := M) z (Y z)) • C) y =
      tensor00Scalar (I := I) (M := M) y (Y y) • C y from rfl]
  rw [← tensor0SAsRS_apply (I := I) (M := M) y (C y) (Y y)]

set_option linter.unusedSectionVars false in
/-- **Smoothness of the unit-evaluated section of a smooth compactly-supported
`(0, k)`-tensor.** The section `y ↦ (Z y)(unitZeroSec y)` of the `(0, k)`-tensor bundle is
smooth, as the application of the smooth Hom-bundle section `Z.toSection` to the smooth
unit `(0, 0)`-section. -/
private lemma contMDiff_unitEvalSection (g : SmoothRiemannianMetric I M) (k : ℕ)
    (Z : SmoothCcTensor g 0 k) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SSpace k I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from Z.toSection y)
          (unitZeroSec (I := I) (M := M) y))) := by
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel k ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace k I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from Z.toSection y))) :=
    Z.toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace k I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel k ℝ E) hϕ hv

set_option linter.unusedSectionVars false in
/-- **Smoothness of the slot-`0` `X`-read of a smooth compactly-supported
`(0, s + 1)`-tensor**, in `tensor0SAsRS`-wrapped Hom-bundle form: the section
`y ↦ tensor0SAsRS y ((curry (Z y)(unit))(X y))` is a smooth section of the
`(0, s)`-Hom-tensor bundle. -/
private lemma contMDiff_slot0Read (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 (s + 1)) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (tensor0SAsRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))) := by
  have hUzS := contMDiff_unitEvalSection (I := I) (M := M) g (s + 1) Z
  have hcur : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y)))) :=
    fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
      (I := I) (M := M)
      (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (s + 1) I z from
        Z.toSection z) (unitZeroSec (I := I) (M := M) z)) y (hUzS y)
  have hCs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) :=
    ContMDiff.clm_bundle_apply (b := fun y : M => y)
      (E₁ := TangentSpace I) (E₂ := fun z : M => Tensor0SSpace s I z)
      (F₁ := E) (F₂ := Tensor0SModel s ℝ E) hcur hX
  exact contMDiff_tensor0SAsRS_wrap (I := I) (M := M) s hCs

/-- **Directional slot-`0` curry covariant Leibniz rule (fibre form).** For a smooth
compactly-supported `(0, s + 1)`-tensor `Z` and smooth tangent fields `V, X`, reading
slot `0` of the unit-evaluated directional covariant derivative `(∇_V Z)(x)(unit)` along
`X x` equals the unit-evaluated directional covariant derivative along `V` of the
slot-`0` `X`-read section, minus the slot-`0` read of `Z` at `x` along the Christoffel
correction `(∇_V X)(x) = (LeviCivita g).toFun X x (V x)`. This is the identity in the
`(0, s)`-tensor fibre at `x`; `tensor0S_curry_covApply_slot0_leibniz` is its model
evaluation. -/
theorem tensor0S_curry_covApply_slot0_leibniz_fib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (Z : SmoothCcTensor g 0 (s + 1))
    {V X : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covApply (tensorCov (I := I) g 0 (s + 1)) V
            (fun y : M => Z.toSection y) x)
          (unitZeroSec (I := I) (M := M) x))) (X x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        covApply (tensorCov (I := I) g 0 s) V
          (fun y : M => tensor0SAsRS (I := I) (M := M) y
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
              ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) x)
        (unitZeroSec (I := I) (M := M) x) -
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          Z.toSection x) (unitZeroSec (I := I) (M := M) x)))
        ((LeviCivita (I := I) g).toFun X x (V x)) := by
  classical
  have hVAt : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (V b)) x :=
    (hV x).mdifferentiableAt (by simp)
  have hunitAt : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) x :=
    ((contMDiff_unitZeroSection (I := I) (M := M)) x).mdifferentiableAt (by simp)
  have hZAt : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y (Z.toSection y)) x :=
    (Z.toSection.contMDiff x).mdifferentiableAt (by simp)
  have hA : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        covApply (tensorCov (I := I) g 0 (s + 1)) V
          (fun y : M => Z.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
        (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Z.toSection y) (unitZeroSec (I := I) (M := M) y)) x (V x) := by
    have happ := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M)
      0 (s + 1) (LeviCivita (I := I) g) (fun y : M => Z.toSection y)
      (fun y : M => unitZeroSec (I := I) (M := M) y) V hZAt hunitAt hVAt
    rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
          (fun y : M => unitZeroSec (I := I) (M := M) y) x (V x)) = 0 from
      tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
        (LeviCivita (I := I) g) x (V x)] at happ
    rw [map_zero, sub_zero] at happ
    exact happ
  have hUzS := contMDiff_unitEvalSection (I := I) (M := M) g (s + 1) Z
  have hUzAt : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        Z.toSection y) (unitZeroSec (I := I) (M := M) y)) x :=
    (hUzS x).mdifferentiableAt (by simp)
  have hB := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M)
    g s (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
      Z.toSection y) (unitZeroSec (I := I) (M := M) y)) hUzAt ⟨X, hX⟩ (V x)
  have hρS := contMDiff_slot0Read (I := I) (M := M) g s Z hX
  have hρAt : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (tensor0SAsRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))) x :=
    (hρS x).mdifferentiableAt (by simp)
  have happ2 := tensorRSCovariantDerivative_apply_of_mdifferentiableAt (I := I) (M := M)
    0 s (LeviCivita (I := I) g)
    (fun y : M => tensor0SAsRS (I := I) (M := M) y
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))
    (fun y : M => unitZeroSec (I := I) (M := M) y) V hρAt hunitAt hVAt
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x (V x)) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x (V x)] at happ2
  rw [map_zero, sub_zero] at happ2
  have hsec : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        tensor0SAsRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))
        (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)) := by
    funext y
    exact tensor0SAsRS_unit_eval (I := I) (M := M) s y _
  rw [hsec] at happ2
  have hC2 : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      covApply (tensorCov (I := I) g 0 s) V
        (fun y : M => tensor0SAsRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) x)
      (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)) x (V x) :=
    happ2
  rw [hA]
  have hfinal := eq_sub_of_add_eq hB.symm
  simp only [ContMDiffSection.coeFn_mk, Tensor0SNabla.curriedSection_apply] at hfinal
  rw [hfinal, ← hC2]

/-- **Directional slot-`0` curry covariant Leibniz rule.** Reading slot `0` of the
unit-evaluated directional covariant derivative `(∇_V Z)(x)(unit)` along a smooth field
`X` and a `Fin s`-tuple `m` is the derivative of the slot-`0` `X`-read minus the
`(∇_V X)(x)`-read of `Z`. Model-evaluated form of
`tensor0S_curry_covApply_slot0_leibniz_fib`. -/
theorem tensor0S_curry_covApply_slot0_leibniz
    (g : SmoothRiemannianMetric I M) (s : ℕ) (Z : SmoothCcTensor g 0 (s + 1))
    {V X : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            covApply (tensorCov (I := I) g 0 (s + 1)) V
              (fun y : M => Z.toSection y) x)
            (unitZeroSec (I := I) (M := M) x))) (X x)) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          covApply (tensorCov (I := I) g 0 s) V
            (fun y : M => tensor0SAsRS (I := I) (M := M) y
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
                ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                  Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) x)
          (unitZeroSec (I := I) (M := M) x)) m -
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            Z.toSection x) (unitZeroSec (I := I) (M := M) x)))
          ((LeviCivita (I := I) g).toFun X x (V x))) m := by
  rw [tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s Z hV hX x]
  rw [Tensor0SSpace.toModel_sub]
  rfl

end Connection
end Integral
end DifferentialGeometry

end
