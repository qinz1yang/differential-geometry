import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutator

/-!
# The rough-Laplacian / covariant-gradient commutator: abstract `(0, 3)` reduction

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, this file
continues the reduction of the order-`2` Gårding commutator begun in
`CovGradRoughLapCommutator.lean`.

That file reduces the left-hand side of the target commutator
```
Δ_∇(∇T₀) (x) = ∇(Δ_∇ T₀) (x) + Curv x
```
in two steps: `rawTensorConnLap_covGrad_eq_frame_trace` writes the rough
Laplacian of the `(0, 3)`-tensor gradient field as the frame trace
`∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇T₀)` of its second covariant derivative, and
`tensorSecondCovDeriv_covGrad_unit_eval` transports each summand, after evaluation
at the unit `(0, 0)`-tensor, into the abstract `(0, 3)`-tensor second covariant
derivative of the unit-evaluated gradient field
`U y := (∇T₀) y (unit)`.

## What this file establishes

* `unitGradAbstractRoughLap` — the **abstract `(0, 3)` rough Laplacian** of the
  unit-evaluated gradient field `U`: the frame sum
  `∑ᵢ (∇^{(0,3)abs}_{Bᵢ} ∇^{(0,3)abs}_{Bᵢ} U - ∇^{(0,3)abs}_{(∇_{Bᵢ} Bᵢ)} U)(x)`,
  written entirely in the abstract recursive `(0, 3)`-tensor covariant derivative
  `tensor0SCovariantDerivative I M 3 (LeviCivita g)`.

* `rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap` — the **complete
  combined section reduction**: the unit-`(0, 0)`-evaluation of the rough
  Laplacian of the `(0, 3)`-tensor gradient field equals the abstract `(0, 3)`
  rough Laplacian of `U`:
  ```
  (Δ_∇(∇T₀))(x)(unit) = unitGradAbstractRoughLap g T₀ x.
  ```
  This is the conjunction of `rawTensorConnLap_covGrad_eq_frame_trace` and
  `tensorSecondCovDeriv_covGrad_unit_eval`, packaged as a single identity. It is
  the exact form consumed by the remaining curvature-reconciliation step.

* `abstract_succ_covDeriv_unfold_at` — the **slot-`0` Christoffel exposure** for
  the abstract `(0, 3) = T^*M ⊗ (0, 2)` covariant derivative. Applying the
  product rule of the Hom-bundle covariant derivative
  (`homBundleCovariantDerivativeFun_apply_eq`) to a smooth `(0, 3)`-tensor
  section `W`, the directional covariant derivative `∇^{(0,3)abs}_{Vfield} W`,
  read on the leftmost slot direction `Y`, decomposes as the abstract `(0, 2)`
  covariant derivative of the partial evaluation `y ↦ W y · (Y y)` minus the
  slot-`0` Christoffel correction `W x · (∇^{TM}_{Vfield} Y)(x)`:
  ```
  (tensor0S_curry 2 x) (∇^{(0,3)abs}_{Vfield} W (x)) (Y x)
    = ∇^{(0,2)abs}_{Vfield}(y ↦ curriedSection W y (Y y)) (x)
      - curriedSection W x ((∇^{TM} Y)(x)(Vfield x)).
  ```
  The term `curriedSection W x ((∇^{TM} Y)(x)(Vfield x))` is precisely the
  slot-`0` Christoffel contribution that, in the full commutator, recombines with
  the `covGrad`-reindex of the lower-rank rough Laplacian; this is the structural
  input to the slot-`0`-Christoffel-vs-field-direction matching.

## Remaining piece (documented, not assumed)

The full curvature reconciliation — identifying `unitGradAbstractRoughLap g T₀ x`
with the unit-evaluation of `covGrad g 0 2 (Δ_∇ T₀)` plus the explicit curvature
field `Tensor3rdCurv` — chains two `abstract_succ_covDeriv_unfold_at` unfoldings
(one per abstract differentiation in each frame summand), identifies the
abstract `(0, 2)` partial evaluations with the rank-`2` Levi-Civita / abstract
covariant derivative of `T₀` (the rank-`2` abstract-vs-`tensorRSCovariantDerivative`
chart-frame agreement), sums over the orthonormal frame, and matches the residual
to the frame-trace third-order Weitzenböck swap `frame_trace_thirdCovDeriv_swap`.
That rank-`2` general-section abstract-vs-`RS` bridge is the sole remaining
structural input; it is not assumed here.

## Sign / convention

Geometer convention `Δ_∇ = -∇*∇` (the frame trace `∑ᵢ ∇²_{Bᵢ, Bᵢ}`), matching
`CovGradRoughLapCommutator.lean`, `TensorThirdOrderWeitzenbock.lean`, and
`TensorConnLaplacian.lean`. The covariant gradient `covGrad g 0 s` curries the new
tangent-direction slot as the leftmost covariant slot.
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

/-- **The abstract `(0, 3)` rough Laplacian of the unit-evaluated gradient
field.** With `B_i := smoothOrthoFrame g x i` the `g_x`-orthonormal smooth frame,
`cov₃ := tensor0SCovariantDerivative I M 3 (LeviCivita g)` the abstract recursive
`(0, 3)`-tensor covariant derivative, and `U := unitGradField g T₀` the
unit-evaluated gradient field, this is the frame sum of abstract second covariant
derivatives:
$$
  \sum_i \Bigl(\nabla^{(0,3)\mathrm{abs}}_{B_i}\nabla^{(0,3)\mathrm{abs}}_{B_i} U (x)
    - \nabla^{(0,3)\mathrm{abs}}_{(\nabla_{B_i} B_i)(x)} U (x)\Bigr).
$$
It is the right-hand side of the committed transport
`tensorSecondCovDeriv_covGrad_unit_eval`, summed over the frame. -/
noncomputable def unitGradAbstractRoughLap
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    Tensor0SSpace 3 I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
        (smoothOrthoFrame (I := I) g x i x) -
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

/-- The defining frame sum for `unitGradAbstractRoughLap`. -/
lemma unitGradAbstractRoughLap_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    unitGradAbstractRoughLap (I := I) (M := M) g T₀ x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
            (smoothOrthoFrame (I := I) g x i x) -
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
            (unitGradField (I := I) (M := M) g T₀) x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

/-- **Combined section reduction of the commutator LHS.** For a smooth
compactly-supported `(0, 2)`-tensor field `T₀`, the unit-`(0, 0)`-evaluation of
the rough Laplacian of the `(0, 3)`-tensor gradient field `∇T₀ = covGrad g 0 2 T₀`
equals the abstract `(0, 3)` rough Laplacian of the unit-evaluated gradient field
`U := unitGradField g T₀`:
```
(Δ_∇(∇T₀))(x)(unit) = unitGradAbstractRoughLap g T₀ x.
```
This conjoins `rawTensorConnLap_covGrad_eq_frame_trace` with the frame sum of
`tensorSecondCovDeriv_covGrad_unit_eval`; it is the exact reduced form of the
left-hand side consumed by the remaining curvature reconciliation. -/
theorem rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        rawTensorConnLap (I := I) g 0 3
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      unitGradAbstractRoughLap (I := I) (M := M) g T₀ x := by
  classical
  rw [rawTensorConnLap_covGrad_eq_frame_trace (I := I) (M := M) g T₀ x]
  rw [unitGradAbstractRoughLap_def]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          ∑ i : Fin (Module.finrank ℝ E),
            tensorSecondCovDeriv (I := I) g 0 3
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
          (unitZeroSec (I := I) (M := M) x) =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            tensorSecondCovDeriv (I := I) g 0 3
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
            (unitZeroSec (I := I) (M := M) x) from by
        rw [ContinuousLinearMap.sum_apply]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  exact tensorSecondCovDeriv_covGrad_unit_eval (I := I) (M := M) g T₀ hB x

/-- **Slot-`0` Christoffel exposure for the abstract `(0, 3)` covariant
derivative.** Let `cov₂ := tensor0SCovariantDerivative I M 2 (LeviCivita g)` and
`cov₃ := tensor0SCovariantDerivative I M 3 (LeviCivita g)` be the abstract `(0, 2)`
and `(0, 3)` covariant derivatives. For a smooth `(0, 3)`-tensor section `W` and
smooth vector fields `Vfield`, `Y`, the curry of the directional covariant
derivative `cov₃.toFun W x (Vfield x)`, read on the leftmost slot direction `Y x`,
decomposes by the Hom-bundle product rule as
$$
  (\text{curry } cov₃.\mathrm{toFun}\,W\,x\,(Vfield_x))(Y_x)
    = cov₂.\mathrm{toFun}(y \mapsto \text{curry}\,W_y\,(Y_y))\,x\,(Vfield_x)
      - (\text{curry}\,W_x)\bigl((\nabla^{TM}_{Vfield} Y)(x)\bigr),
$$
where `curry W_y := curriedSection I M W y` reads slot `0` off the `(0, 3)`-tensor
`W_y`, and `(∇^{TM}_{Vfield} Y)(x) = (LeviCivita g).toFun Y x (Vfield x)` is the
slot-`0` Christoffel direction. The hypotheses are the manifold-differentiability,
at `x`, of the curried section, of `Vfield`, and of `Y`. -/
theorem abstract_succ_covDeriv_unfold_at
    (g : SmoothRiemannianMetric I M)
    (W : Π y : M, Tensor0SSpace 3 I y)
    {Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 2 ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 2 ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace 2 I z)) y
        (curriedSection I M W y)) x)
    (hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x)
    (hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0S_curry (I := I) (M := M) 2 x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          W x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => curriedSection I M W y (Y y)) x (Vfield x) -
        curriedSection I M W x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (F := Tensor0SModel 2 ℝ E)
    (V := fun z : M => Tensor0SSpace 2 I z)
    (cov_TM := LeviCivita (I := I) g)
    (cov_V := tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
    (τ := curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  have hsucc : tensor0S_curry (I := I) (M := M) 2 x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        W x (Vfield x)) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M)
        (F := Tensor0SModel 2 ℝ E)
        (V := fun z : M => Tensor0SSpace 2 I z)
        (cov_TM := LeviCivita (I := I) g)
        (cov_V := tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
        (τ := curriedSection I M W) x (Vfield x) := by
    rw [show
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          W x (Vfield x) =
        (Tensor0SNabla.tensor0SCovariantDerivative_succ I M (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))).toFun
          W x (Vfield x) from by
      rw [tensor0SCovariantDerivative_succ_eq]]
    rw [tensor0SCovariantDerivative_succ_apply]
    exact (tensor0S_curry (I := I) (M := M) 2 x).apply_symm_apply _
  rw [hsucc]
  exact hHom
end Connection
end Integral
end DifferentialGeometry

end
