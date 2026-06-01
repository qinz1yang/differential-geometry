import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorAssembly

/-!
# The double unfold of the abstract `(0, 3)` rough Laplacian of the gradient field

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, this file
performs the **two-level naturality unfold** of the abstract `(0, 3)` rough
Laplacian `unitGradAbstractRoughLap g T₀` of the unit-evaluated gradient field
`U y := (covGrad g 0 2 T₀)(y)(unit)`, read off the slot-`0` (gradient) direction.

The slot-`0` reading of `unitGradAbstractRoughLap g T₀ x` along a tangent direction
`w = Y x` (with `Y` a smooth extension field) is, by `tensor0S_curry 2 x · (Y x)`,
the frame sum of slot-`0` curryings of the abstract `(0, 3)` second covariant
derivatives of `U`. Each summand `cov₃ₐ.toFun (covApply cov₃ₐ Bᵢ U) x (Bᵢ x)` and
`cov₃ₐ.toFun U x ((∇^{TM}_{Bᵢ} Bᵢ)(x))` is unfolded by the slot-`0` naturality
`abstract_succ_covDeriv_unfold_at` / `curry_abstract_covDeriv_unitGrad_unfold'`.

The genuinely new step here is the **inner-level naturality for the derived section
`W := covApply cov₃ₐ Bᵢ U`** (not `U` itself): its curried-section smoothness and
its slot-`0` currying reading, the mirror of `contMDiff_curried_unitGradField` and
`curry_abstract_covDeriv_unitGrad_unfold'` for the once-differentiated section.

## Main results

* `contMDiff_covApply_unitGradField` — smoothness of the derived section
  `covApply cov₃ₐ X U` for a smooth field `X`.
* `contMDiff_curried_covApply_unitGradField` — smoothness of its slot-`0` curried
  Hom-bundle section.
* `curriedSection_covApply_unitGradField_eq` — the inner-level slot-`0` currying
  reading of `covApply cov₃ₐ X U`, as a section identity:
  `curriedSection (covApply cov₃ₐ X U) y (Y y) =
     cov₂ₐ.toFun (z ↦ (∇_{Y z} T₀)(z)(unit)) y (X y) − (∇_{(∇^{TM}_X Y)(y)} T₀)(y)(unit)`.
* `curry_abstract_covDeriv_covApply_unitGrad_unfold` — the slot-`0` naturality, one
  level, for the derived section `W := covApply cov₃ₐ X U`.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (the frame trace), matching
`CovGradRoughLapCommutatorAbstract.lean` and `CovGradRoughLapCommutatorAssembly.lean`.
The covariant gradient `covGrad g 0 s` curries the new tangent-direction slot as the
leftmost covariant slot.
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

/-- **Smoothness of the derived section.** For a smooth tangent vector field `X`, the
directional abstract `(0, 3)`-tensor covariant derivative `W := covApply cov₃ₐ X U`
of the unit-evaluated gradient field `U := unitGradField g T₀` is a smooth section of
the abstract `(0, 3)`-tensor bundle. -/
lemma contMDiff_covApply_unitGradField
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
          (unitGradField (I := I) (M := M) g T₀) y)) := by
  classical
  have hU : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        (unitGradField (I := I) (M := M) g T₀ y)) :=
    contMDiff_unitGradField (I := I) (M := M) g T₀
  exact covApply_contMDiff
    (cov := Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) hX hU

/-- **Smoothness of the curried derived section.** The slot-`0` curried Hom-bundle
section `y ↦ tensor0S_curry 2 y (W y)` of the derived section `W := covApply cov₃ₐ X U`
is smooth as a section of the Hom-bundle `TM →L[ℝ] T^{(0,2)}`. -/
lemma contMDiff_curried_covApply_unitGradField
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) y)) :=
  (contMDiff_curriedSection_iff_section (I := I) (M := M)
    (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
      (unitGradField (I := I) (M := M) g T₀))).mp
    (contMDiff_covApply_unitGradField (I := I) (M := M) g T₀ hX)

/-- **Inner-level slot-`0` currying reading of the derived section.** For smooth fields
`X, Y`, the curried section of `W := covApply cov₃ₐ X U`, read along `Y`, is the
section
```
y ↦ cov₂ₐ.toFun (z ↦ (∇_{Y z} T₀)(z)(unit)) y (X y)
      − (∇_{(∇^{TM}_X Y)(y)} T₀)(y)(unit).
```
This is `curry_abstract_covDeriv_unitGrad_unfold'` applied pointwise to `U`. -/
lemma curriedSection_covApply_unitGradField_eq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (fun y : M =>
      curriedSection I M
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
          (unitGradField (I := I) (M := M) g T₀)) y (Y y)) =
      (fun y : M =>
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
            (fun z : M =>
              (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ z (Y z))
                (unitZeroSec (I := I) (M := M) z)) y (X y) -
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
            tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y
              ((LeviCivita (I := I) g).toFun Y y (X y)))
            (unitZeroSec (I := I) (M := M) y)) := by
  classical
  funext y
  rw [curriedSection_apply]
  rw [covApply_apply]
  exact curry_abstract_covDeriv_unitGrad_unfold' (I := I) (M := M) g T₀ hX hY

/-- **Slot-`0` naturality, one level, for the derived section.** With `W := covApply
cov₃ₐ X U` the once-differentiated unit-evaluated gradient field, and smooth fields
`X, Vfield, Y`, the slot-`0` currying of `cov₃ₐ.toFun W x (Vfield x)`, read along
`Y x`, decomposes as
```
cov₂ₐ.toFun (z ↦ curriedSection W z (Y z)) x (Vfield x)
  − curriedSection W x ((∇^{TM}_{Vfield} Y)(x)),
```
where the inner-curried section `z ↦ curriedSection W z (Y z)` equals, by
`curriedSection_covApply_unitGradField_eq`,
```
z ↦ cov₂ₐ.toFun (u ↦ (∇_{Y u} T₀)(u)(unit)) z (X z) − (∇_{(∇^{TM}_X Y)(z)} T₀)(z)(unit).
```
This is `abstract_succ_covDeriv_unfold_at` applied to the smooth section `W`, with the
curried-section reading substituted. -/
lemma curry_abstract_covDeriv_covApply_unitGrad_unfold
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hVfield : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Vfield))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun z : M =>
            curriedSection I M
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
                (unitGradField (I := I) (M := M) g T₀)) z (Y z)) x (Vfield x) -
        curriedSection I M
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  exact abstract_succ_covDeriv_unfold_at (I := I) (M := M) g
    (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
      (unitGradField (I := I) (M := M) g T₀))
    (Vfield := Vfield) (Y := Y) (x := x)
    ((contMDiff_curried_covApply_unitGradField (I := I) (M := M) g T₀ hX x).mdifferentiableAt
      (by simp))
    ((hVfield x).mdifferentiableAt (by simp))
    ((hY x).mdifferentiableAt (by simp))

/-- **Double unfold, inner-curried section substituted.** With `W := covApply cov₃ₐ X U`,
the slot-`0` currying of `cov₃ₐ.toFun W x (Vfield x)`, read along `Y x`, equals
```
cov₂ₐ.toFun
    (z ↦ cov₂ₐ.toFun (u ↦ (∇_{Y u} T₀)(u)(unit)) z (X z)
          − (∇_{(∇^{TM}_X Y)(z)} T₀)(z)(unit))
    x (Vfield x)
  − curriedSection W x ((∇^{TM}_{Vfield} Y)(x)).
```
The outer `cov₂ₐ` covariant derivative now acts on the explicit inner-curried section
(the difference of an abstract `(0, 2)` second derivative of the directionally-derived
field and a slot-`0` Christoffel correction), via
`curriedSection_covApply_unitGradField_eq`. -/
lemma curry_abstract_covDeriv_covApply_unitGrad_unfold_inner
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hVfield : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Vfield))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun z : M =>
            (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
                (fun u : M =>
                  (show Tensor0SSpace 0 I u →L[ℝ] Tensor0SSpace 2 I u from
                    tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ u (Y u))
                    (unitZeroSec (I := I) (M := M) u)) z (X z) -
              (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ z
                  ((LeviCivita (I := I) g).toFun Y z (X z)))
                (unitZeroSec (I := I) (M := M) z)) x (Vfield x) -
        curriedSection I M
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
            (unitGradField (I := I) (M := M) g T₀)) x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  rw [curry_abstract_covDeriv_covApply_unitGrad_unfold (I := I) (M := M) g T₀ hX hVfield hY]
  rw [curriedSection_covApply_unitGradField_eq (I := I) (M := M) g T₀ hX hY]

end Connection
end Integral
end DifferentialGeometry

end
