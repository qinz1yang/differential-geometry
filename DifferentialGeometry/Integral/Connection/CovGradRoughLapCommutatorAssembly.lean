import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorAbstract
import DifferentialGeometry.Integral.Connection.Tensor0SRSCovariantDerivativeAgreement

/-!
# Closing the `(0, 2) → (0, 3)` rough-Laplacian / covariant-gradient commutator

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, this file
assembles the previously-reduced pieces into the full order-`2` Gårding
commutator: the rough (connection) Laplacian of the `(0, 3)`-tensor covariant
gradient `∇T₀ = covGrad g 0 2 T₀` equals the covariant gradient of the rough
Laplacian `Δ_∇ T₀ = rawTensorConnLapSmooth g 0 2 T₀`, up to an explicit curvature
field:
```
Δ_∇(∇T₀) (x) = ∇(Δ_∇ T₀) (x) + Curv x.
```

## The reduction to a single covariant slot

Both sides are `(0, 3)`-tensors, i.e. continuous linear maps
`Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x`. The `(0, 0)`-fibre
`Tensor0SSpace 0 I x` is canonically `≃L[ℝ] ℝ` via `tensor0Iso`, with the unit
`(0, 0)`-tensor mapping to `1`. Hence the unit `(0, 0)`-tensor spans the fibre,
and a `(0, 3)`-tensor (as a continuous linear map out of `Tensor0SSpace 0`) is
**determined by its value at the unit**. The headline identity is therefore
proved by evaluating both sides at the unit `(0, 0)`-tensor.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (the frame trace), matching
`TensorThirdOrderWeitzenbock.lean`, `CovGradRoughLapCommutator.lean`, and
`CovGradRoughLapCommutatorAbstract.lean`. The covariant gradient `covGrad g 0 s`
curries the new tangent-direction slot as the leftmost covariant slot.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
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

/-- Every `(0, 0)`-tensor `D` is `tensor0Iso x D` times the unit `(0, 0)`-tensor:
`D = (tensor0Iso x D) • unit`. -/
lemma zeroTensor_eq_smul_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (tensor0Iso (I := I) M x D) • unitZeroSec (I := I) (M := M) x := by
  classical
  have hunit : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := scalarFn_unitZero (I := I) (M := M)
    have := congrFun h x
    simpa [scalarFn_apply, unitZeroSec_apply] using this
  apply (tensor0Iso (I := I) M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

/-- **Unit-extensionality for `(0, 3)`-tensors.** Two continuous linear maps
`φ, ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x` (i.e. two `(0, 3)`-tensors)
that agree on the unit `(0, 0)`-tensor are equal. -/
lemma tensor03_ext_unit {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D]
  rw [map_smul, map_smul, h]

/-- **Slot-`0` reading of the unit-evaluated gradient field.** The currying of the
unit-evaluated gradient field `unitGradField g T₀ y` along the slot-`0` tangent
direction `w` recovers the directional covariant derivative of `T₀`, evaluated at
the unit `(0, 0)`-tensor:
```
tensor0S_curry 2 y (U y) w = (∇_w T₀)(y)(unit).
```
-/
lemma curry_unitGradField_eq (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) (y : M) (w : TangentSpace I y) :
    tensor0S_curry (I := I) (M := M) 2 y (unitGradField (I := I) (M := M) g T₀ y) w =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y w)
        (unitZeroSec (I := I) (M := M) y) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) 2 y (unitGradField (I := I) (M := M) g T₀ y) w) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y w)
        (unitZeroSec (I := I) (M := M) y)) m
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := unitGradField (I := I) (M := M) g T₀ y) (v0 := w) (vs := m)]
  rw [unitGradField_apply]
  rw [covGrad_apply_unit_eval (I := I) (M := M) g T₀ y (Fin.cons w m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons w m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

/-- **Slot-`0` reading of the unit-evaluated gradient of any smooth `(0, 2)`-tensor
field.** The currying of `(covGrad g 0 2 S).toSection x (unit)` along the slot-`0`
tangent direction `w` recovers the directional covariant derivative of `S`,
evaluated at the unit `(0, 0)`-tensor:
```
tensor0S_curry 2 x ((covGrad g 0 2 S).toSection x (unit)) w = (∇_w S)(x)(unit).
```
The right-hand-side `covGrad g 0 2 (Δ_∇ T₀)` reading is the instance `S := Δ_∇ T₀`. -/
lemma curry_covGrad_unit_eval (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 S x w)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 S x w)
        (unitZeroSec (I := I) (M := M) x)) m
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (covGrad (I := I) (M := M) g 0 2 S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (v0 := w) (vs := m)]
  rw [covGrad_apply_unit_eval_generic (I := I) (M := M) g S x (Fin.cons w m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons w m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

/-- **Slot-`0` naturality, one level.** With `U := unitGradField g T₀`, smooth
fields `X, Y`, and the differentiability witnesses `hC` (curried `U`), `hX`, `hY`,
the slot-`0` currying of `∇^{(0,3)abs}_X U`, read along `Y`, is
```
cov₂ₐ.toFun (y ↦ (∇_{Y y} T₀)(y)(unit)) x (X x)
  − (∇_{(∇^{TM}_X Y)(x)} T₀)(x)(unit).
```
This combines `abstract_succ_covDeriv_unfold_at` (the Hom-bundle product rule for
the abstract `(0, 3) = T^*M ⊗ (0, 2)` covariant derivative) with the slot-`0`
reading `curry_unitGradField_eq` of `U`. -/
lemma curry_abstract_covDeriv_unitGrad_unfold
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M (unitGradField (I := I) (M := M) g T₀) y)) x)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (X y)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x (X x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (Y y))
              (unitZeroSec (I := I) (M := M) y)) x (X x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
            ((LeviCivita (I := I) g).toFun Y x (X x)))
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hstep := abstract_succ_covDeriv_unfold_at (I := I) (M := M) g
    (unitGradField (I := I) (M := M) g T₀) (Vfield := X) (Y := Y) (x := x) hC hX hY
  rw [hstep]
  have hsec : (fun y : M => curriedSection I M (unitGradField (I := I) (M := M) g T₀) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (Y y))
          (unitZeroSec (I := I) (M := M) y)) := by
    funext y
    rw [curriedSection_apply]
    exact curry_unitGradField_eq (I := I) (M := M) g T₀ y (Y y)
  have hchr : curriedSection I M (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun Y x (X x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
          ((LeviCivita (I := I) g).toFun Y x (X x)))
        (unitZeroSec (I := I) (M := M) x) := by
    rw [curriedSection_apply]
    exact curry_unitGradField_eq (I := I) (M := M) g T₀ x
      ((LeviCivita (I := I) g).toFun Y x (X x))
  rw [hsec, hchr]

/-- **Smoothness of the unit-evaluated gradient field.** `U y := unitGradField g T₀ y`
is a smooth section of the `(0, 3)`-tensor bundle, as the application of the smooth
gradient Hom-bundle section `covGrad g 0 2 T₀` to the smooth unit `(0, 0)`-section. -/
lemma contMDiff_unitGradField (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        (unitGradField (I := I) (M := M) g T₀ y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel 3 ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 3 I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g 0 2 T₀).toSection y))) :=
    covGrad_contMDiff_mk' (I := I) (M := M) g T₀
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace 3 I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 3 ℝ E) hϕ hv

/-- **Smoothness of the curried unit-evaluated gradient field.** The curried
Hom-bundle section `y ↦ tensor0S_curry 2 y (U y)` of the unit-evaluated gradient
field `U := unitGradField g T₀` is smooth as a section of the Hom-bundle
`TM →L[ℝ] T^{(0,2)}`. This is `contMDiff_curriedSection_iff_section` applied to
the smoothness of `U`. -/
lemma contMDiff_curried_unitGradField (g : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M (unitGradField (I := I) (M := M) g T₀) y)) :=
  (contMDiff_curriedSection_iff_section (I := I) (M := M)
    (unitGradField (I := I) (M := M) g T₀)).mp
    (contMDiff_unitGradField (I := I) (M := M) g T₀)

/-- **Slot-`0` naturality, one level (smoothness-discharged form).** Same as
`curry_abstract_covDeriv_unitGrad_unfold`, but with the differentiability of the
curried gradient field discharged from the proven smoothness of `U`; only the
smoothness of the two vector fields `X, Y` is required. -/
lemma curry_abstract_covDeriv_unitGrad_unfold'
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x (X x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (Y y))
              (unitZeroSec (I := I) (M := M) y)) x (X x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
            ((LeviCivita (I := I) g).toFun Y x (X x)))
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  refine curry_abstract_covDeriv_unitGrad_unfold (I := I) (M := M) g T₀ ?_ ?_ ?_
  · exact (contMDiff_curried_unitGradField (I := I) (M := M) g T₀ x).mdifferentiableAt (by simp)
  · exact (hX x).mdifferentiableAt (by simp)
  · exact (hY x).mdifferentiableAt (by simp)

end Connection
end Integral
end DifferentialGeometry

end
