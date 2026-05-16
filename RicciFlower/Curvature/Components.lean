import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Tensor.RicciIdentity
import RicciFlower.LeviCivita.Koszul
import RicciFlower.Coordinates.NablaComponents.Basic
import RicciFlower.Tensor.RSTensor.Components

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Pointwise curvature components

This file records the metric-free, pointwise component layer used by curvature
calculations.  A tangent `Module.Basis` at one point is the primitive coordinate
object; local-frame statements are thin wrappers through `hframe.toBasisAt hx`.

No Christoffel or derivative curvature formula is stated here: those formulas
need either structure coefficients for a general frame or a holonomic-frame
hypothesis.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

/-- Two tensor slots encoded as a `Fin 2` index function. -/
def slots2 (i j : Idx) : Fin 2 -> Idx :=
  fun a => if a = 0 then i else j

/-- Four tensor slots encoded as a `Fin 4` index function. -/
def slots4 (i j k l : Idx) : Fin 4 -> Idx :=
  fun a => if a = 0 then i else if a = 1 then j else if a = 2 then k else l

/-- Pointwise Ricci component in a tangent basis. -/
def ricciCompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) : Real :=
  component0S (I := I) basis Ric (slots2 i j)

/-- Pointwise lowered Riemann component in a tangent basis. -/
def rm04CompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) : Real :=
  component0S (I := I) basis Rm04 (slots4 i j k l)

@[simp]
theorem ricciCompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      Ric (vec2 (basis i) (basis j)) := by
  unfold ricciCompAt component0S slots2 vec2 RicciFlower.Curvature.vec2
  congr 1
  funext a
  fin_cases a <;> simp

@[simp]
theorem rm04CompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) :
    rm04CompAt (I := I) basis Rm04 i j k l =
      Rm04 (vec4 (basis i) (basis j) (basis k) (basis l)) := by
  unfold rm04CompAt component0S slots4 vec4 RicciFlower.Curvature.vec4
  congr 1
  funext a
  fin_cases a <;> simp

private theorem tensor0SSpace_sum_apply {ι : Type*} [Fintype ι] {s : ℕ}
    (T : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  let S : Finset ι := Finset.univ
  change ((∑ i ∈ S, T i) v) = ∑ i ∈ S, (T i) v
  induction S using Finset.induction_on with
  | empty =>
      change (0 : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) v = 0
      simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (((T a : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) +
          (∑ i ∈ S, (T i : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real))) v) =
        (T a : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) v +
          ∑ i ∈ S, (T i : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) v
      rw [ContinuousMultilinearMap.add_apply, ih]

private theorem basisTensor0S_empty_eq_scalarOne
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (slots : Fin 0 -> Idx) :
    basisTensor0S (I := I) basis slots = scalarOne0S (I := I) x := by
  ext v
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  rw [hv]
  have hcomp := basisTensor0S_component (I := I) basis slots slots
  have harg : (fun a : Fin 0 => basis (slots a)) = Fin.elim0 := Subsingleton.elim _ _
  change (basisTensor0S (I := I) basis slots) (fun a : Fin 0 => basis (slots a)) = 1
    at hcomp
  rw [harg] at hcomp
  simpa [scalarOne0S] using hcomp

/-- Components of the symbolically defined Ricci tensor are the components of
the tensor trace contraction of the `(1,3)` curvature tensor. -/
theorem ricciCompAt_eq_contractTrace
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      componentRS (I := I) basis
        (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        Fin.elim0 (slots2 i j) := by
  unfold ricciCompAt componentRS ricciFromRm13At RicciFlower.Curvature.ricciFromRm13At
    component0S
  rw [basisTensor0S_empty_eq_scalarOne (I := I) basis Fin.elim0]

/-- Basis-coordinate evaluation of the intrinsic trace contraction defining
Ricci from a `(1,3)` tensor. -/
theorem contract_trace13_component_basis
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x) (i j : Idx) :
    ((contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        (scalarOne0S (I := I) x)) (vec2 (basis i) (basis j)) =
      ∑ a : Idx,
        Rm13 (dualToCotangent (I := I) (basis.coord a))
          (vec3 (basis a) (basis i) (basis j)) := by
  haveI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by simp)
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3
  unfold contract_trace
  change ((model_contract_trace (𝕜 := Real) (E := E) 0 2
      (TensorRSSpace.toModel (I := I) Rm13))
      (Tensor0SSpace.toModel (I := I) (scalarOne0S (I := I) x)))
      (vec2 (basis i) (basis j)) = _
  rw [model_contract_trace_apply_basis (𝕜 := Real) (E := E) basis 0 2]
  refine Finset.sum_congr rfl fun a _ => ?_
  let covM : Tensor0SModel 1 Real E :=
    (continuousMultilinearCurryFin1 Real E Real).symm
      (LinearMap.toContinuousLinearMap (basis.coord a))
  have hinput :
      Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1) =
        covM := by
    ext v
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    change (basis.coord a) (v 0) * 1 = (basis.coord a) (v 0)
    ring
  simp only [model_interior_product, model_tensorWithCovector_first, model_covectorOfCLM,
    scalarOne0S, TensorRSSpace.toModel, Tensor0SSpace.toModel,
    tensorRSSpace_continuousLinearEquiv]
  change (Rm13
      (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
        (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
      (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) (basis i) (basis j))
  have hleft :
      (Rm13
        (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
        (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
      (Rm13 covM) (Fin.cons (basis a) (vec2 (basis i) (basis j))) := by
    exact congrArg
      (fun U => (Rm13 U) (Fin.cons (basis a) (vec2 (basis i) (basis j)))) hinput
  rw [hleft]
  change (Rm13 (dualToCotangent (I := I) (basis.coord a)))
      (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) (basis i) (basis j))
  congr 1
  funext q
  fin_cases q
  · rfl
  · rfl
  · change vec2 (basis i) (basis j) 1 = basis j
    simp [vec2, RicciFlower.Curvature.vec2]

/-- Basis-coordinate evaluation of the intrinsic trace contraction defining
Ricci from a `(1,3)` tensor, with arbitrary second and third inputs. -/
theorem ricciFromRm13At_apply_basis_trace
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Y Z : TangentSpace I x) :
    ricciFromRm13At (I := I) (M := M) Rm13 (vec2 Y Z) =
      ∑ a : Idx,
        Rm13 (dualToCotangent (I := I) (basis.coord a))
          (vec3 (basis a) Y Z) := by
  haveI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by simp)
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3
  change ((contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
      (scalarOne0S (I := I) x)) (vec2 Y Z) = _
  unfold contract_trace
  change ((model_contract_trace (𝕜 := Real) (E := E) 0 2
      (TensorRSSpace.toModel (I := I) Rm13))
      (Tensor0SSpace.toModel (I := I) (scalarOne0S (I := I) x)))
      (vec2 Y Z) = _
  rw [model_contract_trace_apply_basis (𝕜 := Real) (E := E) basis 0 2]
  refine Finset.sum_congr rfl fun a _ => ?_
  let covM : Tensor0SModel 1 Real E :=
    (continuousMultilinearCurryFin1 Real E Real).symm
      (LinearMap.toContinuousLinearMap (basis.coord a))
  have hinput :
      Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1) =
        covM := by
    ext v
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    change (basis.coord a) (v 0) * 1 = (basis.coord a) (v 0)
    ring
  simp only [model_interior_product, model_tensorWithCovector_first, model_covectorOfCLM,
    scalarOne0S, TensorRSSpace.toModel, Tensor0SSpace.toModel,
    tensorRSSpace_continuousLinearEquiv]
  change (Rm13
      (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
        (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
      (Fin.cons (basis a) (vec2 Y Z)) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) Y Z)
  have hleft :
      (Rm13
        (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
        (Fin.cons (basis a) (vec2 Y Z)) =
      (Rm13 covM) (Fin.cons (basis a) (vec2 Y Z)) := by
    exact congrArg
      (fun U => (Rm13 U) (Fin.cons (basis a) (vec2 Y Z))) hinput
  rw [hleft]
  change (Rm13 (dualToCotangent (I := I) (basis.coord a)))
      (Fin.cons (basis a) (vec2 Y Z)) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) Y Z)
  congr 1
  funext q
  fin_cases q
  · rfl
  · rfl
  · change vec2 Y Z 1 = Z
    simp [vec2, RicciFlower.Curvature.vec2]

/-- A lowered `(0,4)` tensor is obtained from a `(1,3)` tensor by lowering the
output slot with the metric. -/
def Rm04LowersRm13At
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) =
      Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)

/-- Realized `(1,3)` and lowered `(0,4)` curvature tensors are related by
metric lowering at a point. -/
theorem rm04LowersRm13At_of_realizes
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) :
    Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x) := by
  intro W X Y Z
  let Wsec : (p : M) -> TangentSpace I p := RicciFlower.LeviCivita.tangentConstAt (I := I) x W
  let Xsec : (p : M) -> TangentSpace I p := RicciFlower.LeviCivita.tangentConstAt (I := I) x X
  let Ysec : (p : M) -> TangentSpace I p := RicciFlower.LeviCivita.tangentConstAt (I := I) x Y
  let Zsec : (p : M) -> TangentSpace I p := RicciFlower.LeviCivita.tangentConstAt (I := I) x Z
  let alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
    dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W)
  have h04 := hRm04 Wsec Xsec Ysec Zsec x
  have h13 := hRm13 Xsec Ysec Zsec x alpha
  have h04' :
      Rm04 x (vec4 W X Y Z) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov Xsec Ysec Zsec) x) := by
    dsimp [Wsec, Xsec, Ysec, Zsec] at h04
    rw [RicciFlower.LeviCivita.tangentConstAt_self] at h04
    rw [RicciFlower.LeviCivita.tangentConstAt_self] at h04
    rw [RicciFlower.LeviCivita.tangentConstAt_self] at h04
    rw [RicciFlower.LeviCivita.tangentConstAt_self] at h04
    exact h04
  have h13' :
      Rm13 x
          (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
          (vec3 X Y Z) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov Xsec Ysec Zsec) x) := by
    dsimp [Xsec, Ysec, Zsec, alpha] at h13
    rw [RicciFlower.LeviCivita.tangentConstAt_self] at h13
    rw [RicciFlower.LeviCivita.tangentConstAt_self] at h13
    rw [RicciFlower.LeviCivita.tangentConstAt_self] at h13
    simpa [tangentFlatLinear_apply, cotangentToDual_apply] using h13
  exact h04'.trans h13'.symm

/-- Metric skew-adjointness of the curvature endomorphism in `(1,3)` form:
`g(W,R(X,Y)Z) = -g(Z,R(X,Y)W)`. -/
def Rm13MetricSkewAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z) =
      -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W)

/-- Last-pair metric skew for a lowered Riemann tensor in RicciFlower's slot
order `Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)`. -/
def Rm04OutputSkewAt
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) = -Rm04 (vec4 Z X Y W)

theorem rm13MetricSkewAt_of_rm04_outputSkew
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (hSkew : Rm04OutputSkewAt (I := I) Rm04) :
    Rm13MetricSkewAt (I := I) g x Rm13 := by
  intro W X Y Z
  calc
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)
        = Rm04 (vec4 W X Y Z) := (hLower W X Y Z).symm
    _ = -Rm04 (vec4 Z X Y W) := hSkew W X Y Z
    _ = -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W) := by rw [hLower Z X Y W]

/-- Metric skew-adjointness of `(1,3)` curvature follows from a lowered
realization and output skew-adjointness of the lowered tensor. -/
theorem rm13MetricSkewAt_of_realizes_outputSkew
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M}
    (hSkew : Rm04OutputSkewAt (I := I) (Rm04 x)) :
    Rm13MetricSkewAt (I := I) g x (Rm13 x) :=
  rm13MetricSkewAt_of_rm04_outputSkew (I := I) g (Rm13 x) (Rm04 x)
    (rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 x)
    hSkew

/-- The signed curvature trace appearing when commuting the first two slots of
`∇²α` for a one-form `α`.

The leading minus sign matches the realized convention
`Rm13 alpha X Y Z = alpha (R(X,Y)Z)`, since covectors see the negative
curvature action. -/
def curvatureTraceOneFormAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Y : TangentSpace I x) : Real :=
  -∑ i : Idx, ∑ j : Idx,
    gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j))

/-- The metric trace of the one-form curvature commutator realizes a Ricci
pairing with a supplied vector.  In the scalar specialization, the vector is
`∇u`. -/
def CurvatureTraceOneFormEqRicVectorAt
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x) : Prop :=
  ∀ Y : TangentSpace I x,
    curvatureTraceOneFormAt (I := I) Rm13 alpha basis gInv Y =
      Ric x (vec2 Y curvatureVector)

theorem curvatureActionTraceEqualsRicVectorCoord_of_tensor
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (hcurv : CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13 alpha
      basis gInv curvatureVector) :
    CurvatureActionTraceEqualsRicGradCoord gInv
      (fun i k j => -Rm13 x alpha (vec3 (basis i) (basis k) (basis j)))
      (fun k => Ric x (vec2 (basis k) curvatureVector)) := by
  intro k
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * -Rm13 x alpha (vec3 (basis i) (basis k) (basis j)))
        = curvatureTraceOneFormAt (I := I) Rm13 alpha basis gInv (basis k) := by
          unfold curvatureTraceOneFormAt
          simp_rw [mul_neg, Finset.sum_neg_distrib]
    _ = Ric x (vec2 (basis k) curvatureVector) := hcurv (basis k)

/-- Coordinate covectors are inverse-metric contractions of metric-lowered basis
covectors. -/
theorem basis_coord_eq_sum_inv_inner
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V =
      ∑ k : Idx, gInv a k * g.inner x (basis k) V := by
  symm
  calc
    (∑ k : Idx, gInv a k * g.inner x (basis k) V)
        = ∑ k : Idx, gInv a k *
            g.inner x (basis k) (∑ j : Idx, basis.coord j V • basis j) := by
          rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
    _ = ∑ k : Idx, ∑ j : Idx,
          gInv a k * (basis.coord j V * g.inner x (basis k) (basis j)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_sum]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul]
          simp [smul_eq_mul]
    _ = ∑ j : Idx, basis.coord j V *
          (∑ k : Idx, gInv a k * g.inner x (basis k) (basis j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ = ∑ j : Idx, basis.coord j V * (if a = j then 1 else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [(hinv a j).1]
    _ = basis.coord a V := by
          simp

theorem rm13_dualCoord_apply_eq_sum_inv_flat
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (a : Idx) (X Y Z : TangentSpace I x) :
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 X Y Z) =
      ∑ k : Idx,
        gInv a k *
          Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis k)))
            (vec3 X Y Z) := by
  have hdual :
      dualToCotangent (I := I) (basis.coord a) =
        ∑ k : Idx, gInv a k •
          dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis k)) := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext V
    simp [tangentFlatLinear_apply,
      basis_coord_eq_sum_inv_inner (I := I) g basis gInv hinv a V]
  rw [hdual]
  rw [_root_.map_sum Rm13]
  rw [tensor0SSpace_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [ContinuousMultilinearMap.smul_apply]
  simp [smul_eq_mul]

theorem curvatureTraceOneFormEqRicVectorAt_of_metric_dual
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x))
    (hAlpha :
      alpha =
        dualToCotangent (I := I)
          ((tangentFlatLinear (I := I) g x) curvatureVector)) :
    CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13 alpha basis gInv
      curvatureVector := by
  intro Y
  unfold curvatureTraceOneFormAt
  rw [hAlpha]
  calc
    -(∑ i : Idx, ∑ j : Idx,
        gInv i j *
          Rm13 x
            (dualToCotangent (I := I)
              ((tangentFlatLinear (I := I) g x) curvatureVector))
            (vec3 (basis i) Y (basis j)))
        = ∑ i : Idx, ∑ j : Idx,
            gInv i j *
              Rm13 x
                (dualToCotangent (I := I)
                  ((tangentFlatLinear (I := I) g x) (basis j)))
                (vec3 (basis i) Y curvatureVector) := by
          have hrewrite : ∀ i j : Idx,
              Rm13 x
                (dualToCotangent (I := I)
                  ((tangentFlatLinear (I := I) g x) curvatureVector))
                (vec3 (basis i) Y (basis j)) =
              -Rm13 x
                (dualToCotangent (I := I)
                  ((tangentFlatLinear (I := I) g x) (basis j)))
                (vec3 (basis i) Y curvatureVector) := by
            intro i j
            exact hSkew curvatureVector (basis i) Y (basis j)
          simp_rw [hrewrite]
          simp_rw [mul_neg, Finset.sum_neg_distrib]
          ring
    _ = ∑ i : Idx,
          Rm13 x (dualToCotangent (I := I) (basis.coord i))
            (vec3 (basis i) Y curvatureVector) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (rm13_dualCoord_apply_eq_sum_inv_flat (I := I) g basis gInv hinv
            (Rm13 x) i (basis i) Y curvatureVector).symm
    _ = ricciFromRm13At (I := I) (M := M) (Rm13 x)
          (vec2 Y curvatureVector) := by
          rw [ricciFromRm13At_apply_basis_trace (I := I) basis (Rm13 x)
            Y curvatureVector]
    _ = Ric x (vec2 Y curvatureVector) := by
          rw [hRic x]

/-- Coordinate form of `Ric(Y,Z) = trace (X |-> R(X,Y)Z)`, rewritten through a
lowered `(0,4)` Riemann tensor. With the convention
`Rm04(W,X,Y,Z) = g(W, R(X,Y)Z)`, the traced component is
`sum_{a,k} gInv a k * Rm04(e_k,e_a,e_i,e_j)`. -/
theorem ricciFromRm13_comp_eq_rm04_trace
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (i j : Idx) :
    ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 k a i j := by
  rw [ricciCompAt_apply]
  change ((contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
      (scalarOne0S (I := I) x)) (vec2 (basis i) (basis j)) = _
  rw [contract_trace13_component_basis (I := I) basis Rm13 i j]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hdual :
      dualToCotangent (I := I) (basis.coord a) =
        ∑ k : Idx, gInv a k •
          dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis k)) := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext V
    simp [tangentFlatLinear_apply,
      basis_coord_eq_sum_inv_inner (I := I) g basis gInv hinv a V]
  rw [hdual]
  rw [_root_.map_sum Rm13]
  rw [tensor0SSpace_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [ContinuousMultilinearMap.smul_apply]
  simp only [smul_eq_mul]
  rw [← hLower (basis k) (basis a) (basis i) (basis j)]
  rw [rm04CompAt_apply]

/-- Coordinate form of a Ricci tensor that is intrinsically the trace of a
`(1,3)` tensor, after lowering that `(1,3)` tensor to a `(0,4)` tensor. -/
theorem ricciComp_eq_rm04_trace_of_rm13
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hRic : Ric = ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 k a i j := by
  rw [hRic]
  exact ricciFromRm13_comp_eq_rm04_trace (I := I) g basis gInv hinv Rm13 Rm04 hLower i j

theorem ricciComp_eq_rm04_trace_of_rm13_section
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x))
    (i j : Idx) :
    ricciCompAt (I := I) basis (Ric x) i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis (Rm04 x) k a i j := by
  exact ricciComp_eq_rm04_trace_of_rm13 (I := I) g basis gInv hinv (Ric x) (Rm13 x)
    (Rm04 x) (hRic x) hLower i j

theorem ricciCompAt_eq_contractTrace_of_realizes
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (i j : Idx) :
    ricciCompAt (I := I) basis (Ric x) i j =
      componentRS (I := I) basis
        (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x (Rm13 x))
        Fin.elim0 (slots2 i j) := by
  rw [hRic x]
  exact ricciCompAt_eq_contractTrace (I := I) basis (Rm13 x) i j

/-- Convention-correct pointwise Ricci trace from a lowered Riemann tensor.

This is the lowered form of the intrinsic `Rm13` trace:
`Ric_ab = g^{kl} Rm04(e_k,e_l,e_a,e_b)`.  It is the convention used by
`ricciFromRm13_comp_eq_rm04_trace`. -/
def RicciRealizesRm04FirstTraceAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  forall a b : Idx,
    Ric (vec2 (basis a) (basis b)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) (basis l) (basis a) (basis b))

/-- The intrinsic `Rm13` trace plus output lowering realizes the
convention-correct lowered `Rm04` first trace. -/
theorem ricciFirstTraceAt_of_rm13
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hRic : Ric = ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (hInvSym : forall i j : Idx, gInv i j = gInv j i) :
    RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04 gInv basis := by
  intro i j
  have hcomp := ricciComp_eq_rm04_trace_of_rm13
    (I := I) g basis gInv hinv Ric Rm13 Rm04 hRic hLower i j
  rw [ricciCompAt_apply] at hcomp
  rw [hcomp]
  calc
    (∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 k a i j)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 k a i j := by
        rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) (basis l) (basis i) (basis j)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hInvSym l k, rm04CompAt_apply]

/-- Section form of `ricciFirstTraceAt_of_rm13`. -/
theorem ricciFirstTraceAt_of_rm13_section
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x))
    (hInvSym : forall i j : Idx, gInv i j = gInv j i) :
    RicciRealizesRm04FirstTraceAt (I := I) (Ric x) (Rm04 x) gInv basis := by
  exact ricciFirstTraceAt_of_rm13 (I := I) g basis gInv hinv
    (Ric x) (Rm13 x) (Rm04 x) (hRic x) hLower hInvSym

/-- Legacy pointwise trace realization of Ricci from a lowered Riemann tensor
in a tangent basis.

This traces the last lowered slot, `Rm04(e_k,X,Y,e_l)`.  It is kept for
compatibility with older wrappers; new curvature/Ricci-flow convention work
should use `RicciRealizesRm04FirstTraceAt`. -/
def RicciRealizesRm04TraceAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  forall X Y : TangentSpace I x,
    Ric (vec2 X Y) =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) X Y (basis l))

/-- Pointwise trace realization of scalar curvature from a Ricci tensor in a
tangent basis. -/
def ScalarRealizesRicciTraceAt
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  scalar =
    ∑ i : Idx, ∑ j : Idx, gInv i j * Ric (vec2 (basis i) (basis j))

theorem ricciComp_eq_trace_rm04
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hRic : RicciRealizesRm04TraceAt (I := I) Ric Rm04 gInv basis)
    (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * rm04CompAt (I := I) basis Rm04 k i j l := by
  rw [ricciCompAt_apply]
  simp_rw [rm04CompAt_apply]
  exact hRic (basis i) (basis j)

theorem scalar_eq_trace_ricci
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hScalar : ScalarRealizesRicciTraceAt (I := I) scalar Ric gInv basis) :
    scalar =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * ricciCompAt (I := I) basis Ric i j := by
  rw [hScalar]
  simp_rw [ricciCompAt_apply]

section LocalFrame

variable {u : Set M}

theorem ricciCompAt_eq_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ricciComp (I := I) Ric frame x i j := by
  unfold ricciCompAt ricciComp RicciFlower.Curvature.ricciComp component0S slots2
    RicciFlower.Curvature.vec2
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

theorem rm04CompAt_eq_frame
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j k l : Idx) :
    rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) i j k l =
      rm04Comp (I := I) Rm04 frame x i j k l := by
  unfold rm04CompAt rm04Comp RicciFlower.Curvature.rm04Comp component0S slots4
    RicciFlower.Curvature.vec4
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

theorem ricciTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04TraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro X Y
  simpa [RicciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    IsLocalFrameOn.toBasisAt_coe] using hRic x X Y

/-- Convention-correct frame Ricci trace:
`Ric_ij = g^{kl} Rm04(e_k,e_l,e_i,e_j)`. -/
def RicciTensorRealizesRm04FirstTraceInFrame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    Ric x (vec2 (frame i x) (frame j x)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Rm04 x (vec4 (frame k x) (frame l x) (frame i x) (frame j x))

/-- A local frame turns the convention-correct frame trace into the pointwise
basis trace. -/
theorem ricciFirstTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04FirstTraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04FirstTraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro i j
  simpa [RicciTensorRealizesRm04FirstTraceInFrame, IsLocalFrameOn.toBasisAt_coe]
    using hRic x i j

/-- Component form of the convention-correct frame Ricci trace. -/
theorem ricciComp_eq_firstTrace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04FirstTraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k l i j := by
  have hAt := ricciFirstTraceAt_of_frame
    (I := I) Ric Rm04 gInv frame hframe hRic hx
  rw [ricciCompAt_apply]
  simp_rw [rm04CompAt_apply]
  exact hAt i j

theorem scalarTraceAt_of_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    ScalarRealizesRicciTraceAt (I := I) (scalar x) (Ric x) (gInv x)
      (hframe.toBasisAt hx) := by
  simpa [ScalarRealizesRicciTraceAt, ScalarSectionRealizesRicciTraceInFrame,
    tensor02ToField, IsLocalFrameOn.toBasisAt_coe] using hScalar x

theorem ricciComp_eq_trace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l := by
  exact ricciComp_eq_trace_rm04 (I := I) (hframe.toBasisAt hx) (Ric x) (Rm04 x)
    (gInv x) (ricciTraceAt_of_frame (I := I) Ric Rm04 gInv frame hframe hRic hx) i j

theorem scalar_eq_trace_ricci_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j := by
  exact scalar_eq_trace_ricci (I := I) (hframe.toBasisAt hx) (scalar x) (Ric x)
    (gInv x) (scalarTraceAt_of_frame (I := I) scalar Ric gInv frame hframe hScalar hx)

end LocalFrame

section CoordinateChristoffelCurvature

open RicciFlower.Coordinates

variable [Module.Finite Real E] [CompleteSpace Real]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Christoffel coefficients in the chart-induced coordinate frame at `x₀`.

With this convention `christoffelCoordAt cov x₀ i j k` is `Γ^k_{ij}(x₀)`. -/
def christoffelCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j k : CoordinateIdx (𝕜 := Real) E) : Real :=
  christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i j k

/-- The coordinate-frame Christoffel coefficient as a scalar function near `x₀`. -/
def christoffelCoordFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j k : CoordinateIdx (𝕜 := Real) E) (x : M) : Real :=
  christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x i j k

/-- Directional derivative of a coordinate-frame Christoffel coefficient at `x₀`. -/
def christoffelCoordDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (dir i j k : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (christoffelCoordFun (I := I) cov x₀ i j k) x₀
    (coordinateFrameAt (I := I) x₀ dir x₀)

/-- Coordinate curvature coefficient for the chart-induced coordinate frame.

The convention is
`R^m_{j i k} = ∂ᵢ Γ^m_{k j} - ∂ₖ Γ^m_{i j}
  + Γ^a_{k j} Γ^m_{i a} - Γ^a_{i j} Γ^m_{k a}`.
The bracket term is absent only for this coordinate frame. -/
def christoffelCurvCoeffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i k j m : CoordinateIdx (𝕜 := Real) E) : Real :=
  christoffelCoordDerivAt (I := I) cov x₀ i k j m -
    christoffelCoordDerivAt (I := I) cov x₀ k i j m +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelCoordAt (I := I) cov x₀ k j a *
        christoffelCoordAt (I := I) cov x₀ i a m) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelCoordAt (I := I) cov x₀ i j a *
        christoffelCoordAt (I := I) cov x₀ k a m)

/-- Coordinate Ricci coefficient obtained by tracing the output of
`R(∂ₖ, ∂ᵢ) ∂ⱼ` against the first input.

With RicciFlower's convention this is the coordinate trace
`Ricᵢⱼ = ∑ₖ Rᵏ{}_{j k i}`. This is the first-input trace compatible with
`ricciFromRm13At`; alternate displays that use `R(∂ₖ, ∂ⱼ) ∂ᵢ` have the last two
Ricci slots swapped before any Levi-Civita symmetry is applied. -/
def christoffelRicciCoeffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ k : CoordinateIdx (𝕜 := Real) E,
    christoffelCurvCoeffAt (I := I) cov x₀ k i j k

/-- Expanded local-coordinate Ricci formula in RicciFlower's curvature
convention.

This is the trace of the coordinate curvature formula for `R(∂ₖ, ∂ᵢ) ∂ⱼ`:
`Ricᵢⱼ = ∂ₖ Γᵏᵢⱼ - ∂ᵢ Γᵏₖⱼ + Γᵃᵢⱼ Γᵏₖₐ - Γᵃₖⱼ Γᵏᵢₐ`, summed over the
repeated indices. -/
theorem christoffelRicciCoeffAt_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    christoffelRicciCoeffAt (I := I) cov x₀ i j =
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        christoffelCoordDerivAt (I := I) cov x₀ k i j k) -
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        christoffelCoordDerivAt (I := I) cov x₀ i k j k) +
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelCoordAt (I := I) cov x₀ i j a *
            christoffelCoordAt (I := I) cov x₀ k a k) -
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelCoordAt (I := I) cov x₀ k j a *
            christoffelCoordAt (I := I) cov x₀ i a k) := by
  classical
  simp [christoffelRicciCoeffAt, christoffelCurvCoeffAt,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Coordinate-frame expansion of the connection curvature vector.

This is the geometric Christoffel-expansion frontier: it is where the product
rule for `∇_{eᵢ}(Γ^a_{kj} e_a)` and the coordinate-frame bracket-zero theorem
belong.  Downstream tensor statements should consume this predicate rather than
re-expanding vector-field covariant derivatives. -/
def ConnectionCurvatureCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) : Prop :=
  ∀ i k j : CoordinateIdx (𝕜 := Real) E,
    (connectionRiemannCurvatureField (I := I) cov
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ k)
      (coordinateFrameAt (I := I) x₀ j)) x₀ =
        ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m •
            coordinateFrameAt (I := I) x₀ m x₀

/-- Finite additivity of a covariant derivative in the section slot. -/
private theorem covariantDerivative_finset_sum
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Finset ι) (σ : ι -> (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov ((insert i t).sum σ) x) v
            = (cov (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov (σ i) x + cov (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov (σ i) x) v + (cov (t.sum σ) x) v := by
              simp
        _ = (insert i t).sum (fun j => (cov (σ j) x) v) := by
              rw [ih]
              simp [Finset.sum_insert, hit]

/-- Coordinate-frame component formula for the covariant derivative of an
arbitrary tangent field.

This is the vector analogue of the tensor `nabla0S` coordinate formulas: expand
`V` locally in the coordinate frame and apply the connection Leibniz rule. -/
private theorem covariantDerivative_coordFrame_coeff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (V : (x : M) -> TangentSpace I x)
    (i m : CoordinateIdx (𝕜 := Real) E)
    (hV : MDiffAt (T% V) x₀)
    (hcoeff : ∀ a : CoordinateIdx (𝕜 := Real) E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff a p (V p)) x₀) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff m x₀
        ((cov V x₀) (coordinateFrameAt (I := I) x₀ i x₀)) =
      extDerivFun (I := I)
        (fun p : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff m p (V p)) x₀
        (coordinateFrameAt (I := I) x₀ i x₀) +
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff a x₀ (V x₀) *
            christoffelCoordAt (I := I) cov x₀ i a m := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let z : CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun a p => hframe.coeff a p (V p)
  let term : CoordinateIdx (𝕜 := Real) E -> (p : M) -> TangentSpace I p :=
    fun a => z a • frame a
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hframe_mdiff (a : CoordinateIdx (𝕜 := Real) E) :
      MDiffAt (T% (frame a)) x₀ :=
    coordinateFrameAt_mdifferentiableAt (I := I) x₀ a
  have hterm_diff (a : CoordinateIdx (𝕜 := Real) E) : MDiffAt (T% (term a)) x₀ := by
    exact (hcoeff a).smul_section (hframe_mdiff a)
  have hsum_diff : MDiffAt
      (T% ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum term)) x₀ := by
    simpa using MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E))) (t := term) hterm_diff
  have hV_ev :
      V =ᶠ[nhds x₀]
        fun p : M => ∑ a : CoordinateIdx (𝕜 := Real) E, z a p • frame a p := by
    filter_upwards
      [(coordinateFrameSet_open (I := I) x₀).mem_nhds hx₀] with p hp
    simpa [z, frame, hframe] using (hframe.coeff_sum_eq V hp)
  have hcov_congr :
      cov V x₀ = cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum term) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hV hsum_diff
      (by simp) (by simpa [term] using hV_ev)
  have hcov_sum :
      (cov V x₀) (frame i x₀) =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          (extDerivFun (I := I) (z a) x₀ (frame i x₀) • frame a x₀ +
            z a x₀ • (cov (frame a) x₀) (frame i x₀)) := by
    calc
      (cov V x₀) (frame i x₀)
          = (cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum term) x₀)
              (frame i x₀) := by
            rw [hcov_congr]
      _ = ∑ a : CoordinateIdx (𝕜 := Real) E, (cov (term a) x₀) (frame i x₀) := by
            exact covariantDerivative_finset_sum (I := I) cov
              (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)) term (frame i x₀) hterm_diff
      _ = ∑ a : CoordinateIdx (𝕜 := Real) E,
            (extDerivFun (I := I) (z a) x₀ (frame i x₀) • frame a x₀ +
              z a x₀ • (cov (frame a) x₀) (frame i x₀)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame a) (g := z a) (x := x₀)
              (hframe_mdiff a) (hcoeff a)) (frame i x₀))
            simpa [term, z, Pi.smul_apply, add_comm] using hleib
  rw [hcov_sum]
  rw [map_sum]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  have hdiag :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I) (z a) x₀ (frame i x₀) *
            hframe.coeff m x₀ (frame a x₀)) =
        extDerivFun (I := I) (z m) x₀ (frame i x₀) := by
    have hcoeff_frame (a : CoordinateIdx (𝕜 := Real) E) :
        hframe.coeff m x₀ (frame a x₀) = if a = m then 1 else 0 := by
      rw [coordinateFrameAt_coeff_eq_toBasis_coord (I := I) x₀ (frame a x₀) m]
      rw [show frame a x₀ = coordinateFrameAt_toBasis (I := I) x₀ a by
        simp [frame]]
      change ((coordinateFrameAt_toBasis (I := I) x₀).repr
          ((coordinateFrameAt_toBasis (I := I) x₀) a)) m =
        if a = m then 1 else 0
      by_cases ham : a = m
      · subst ham
        have hb := congrArg (fun f => f a)
          (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) a)
        simpa [coordinateFrameAt_toBasis_apply] using hb
      · have hb := congrArg (fun f => f m)
          (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) a)
        simpa [coordinateFrameAt_toBasis_apply, Finsupp.single_apply, ham] using hb
    rw [show
      (∑ a : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I) (z a) x₀ (frame i x₀) *
            hframe.coeff m x₀ (frame a x₀)) =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          (if a = m then extDerivFun (I := I) (z m) x₀ (frame i x₀) else 0) by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hcoeff_frame a]
        by_cases ham : a = m
        · subst ham
          simp
        · simp [ham]]
    simp
  have hconn :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
          z a x₀ * hframe.coeff m x₀ ((cov (frame a) x₀) (frame i x₀))) =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          hframe.coeff a x₀ (V x₀) * christoffelCoordAt (I := I) cov x₀ i a m := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [z, christoffelCoordAt, frame]
  rw [hdiag, hconn]

/-- Local smoothness of `∇_{e_k} e_j` in the coordinate frame. -/
private theorem coordinateFrame_covariantDeriv_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (x₀ : M) (k j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (coordinateFrameAt (I := I) x₀ j) p)
          (coordinateFrameAt (I := I) x₀ k p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let u := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hframe_j :
      CMDiff[u] ((∞ : WithTop ℕ∞) + 1) (T% (frame j)) := by
    exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn j).of_le
      (by simp)
  have hcov_j :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (frame j) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
        u := by
    simpa [u, frame] using (hcov hu).contMDiff hframe_j
  have hframe_k :
      CMDiff[u] (∞ : WithTop ℕ∞) (T% (frame k)) :=
    ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn k).of_le
      (by simp)
  have hW_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, (cov (frame j) p) (frame k p)⟩ :
            TotalSpace E (TangentSpace I : M -> Type _)))
        u := by
    simpa [frame] using hcov_j.clm_bundle_apply hframe_k
  simpa [u, frame] using (hW_on x₀ hx₀).contMDiffAt (hu.mem_nhds hx₀)

/-- Coordinate coefficients of a locally smooth tangent field are smooth at the
base point. -/
private theorem coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
    (Z : (x : M) -> TangentSpace I x) {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun y : M => (⟨y, Z y⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis Real E) (s := Z)
      (k := (∞ : WithTop ℕ∞)) hx hZ j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff

/-- Producer theorem for `ConnectionCurvatureCoordAt`.

The proof is the coordinate-frame calculation
`∇ᵢ(Γ^a_{kj}e_a) - ∇ₖ(Γ^a_{ij}e_a)`, with the coordinate-frame bracket term
removed by `coordinateFrameAt_bracket_zero`.  Smoothness of the connection is
required explicitly. -/
theorem connection_curvature_coord_of_christoffel
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (x₀ : M) :
    ConnectionCurvatureCoordAt (I := I) cov x₀ := by
  classical
  intro i k j
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let Vkj : (x : M) -> TangentSpace I x :=
    fun p => (cov (frame j) p) (frame k p)
  let Vij : (x : M) -> TangentSpace I x :=
    fun p => (cov (frame j) p) (frame i p)
  have hVkj_smooth :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, Vkj p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    simpa [Vkj, frame] using
      coordinateFrame_covariantDeriv_contMDiffAt (I := I) cov hcov x₀ k j
  have hVij_smooth :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, Vij p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    simpa [Vij, frame] using
      coordinateFrame_covariantDeriv_contMDiffAt (I := I) cov hcov x₀ i j
  have hVkj : MDiffAt (T% Vkj) x₀ :=
    hVkj_smooth.mdifferentiableAt (by simp)
  have hVij : MDiffAt (T% Vij) x₀ :=
    hVij_smooth.mdifferentiableAt (by simp)
  have hcoeff_kj (a : CoordinateIdx (𝕜 := Real) E) :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => hframe.coeff a p (Vkj p)) x₀ :=
    (coordinateFrame_coeff_contMDiffAt_of_contMDiffAt (I := I) Vkj
      hVkj_smooth a).mdifferentiableAt (by simp)
  have hcoeff_ij (a : CoordinateIdx (𝕜 := Real) E) :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => hframe.coeff a p (Vij p)) x₀ :=
    (coordinateFrame_coeff_contMDiffAt_of_contMDiffAt (I := I) Vij
      hVij_smooth a).mdifferentiableAt (by simp)
  have hcov_i (m : CoordinateIdx (𝕜 := Real) E) :=
    covariantDerivative_coordFrame_coeff (I := I) cov x₀ Vkj i m hVkj
      hcoeff_kj
  have hcov_k (m : CoordinateIdx (𝕜 := Real) E) :=
    covariantDerivative_coordFrame_coeff (I := I) cov x₀ Vij k m hVij
      hcoeff_ij
  have hbracket :
      (cov (frame j) x₀) (VectorField.mlieBracket I (frame i) (frame k) x₀) = 0 := by
    rw [coordinateFrameAt_bracket_zero (I := I) x₀ i k]
    simp
  calc
    (connectionRiemannCurvatureField (I := I) cov (frame i) (frame k) (frame j)) x₀
        = (cov Vkj x₀) (frame i x₀) - (cov Vij x₀) (frame k x₀) := by
          simp [connectionRiemannCurvatureField,
            RicciFlower.Curvature.connectionRiemannCurvatureField, Vkj, Vij, frame, hbracket]
    _ = ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m • frame m x₀ := by
          have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
            coordinateFrameAt_mem (I := I) x₀
          rw [show
            (cov Vkj x₀) (frame i x₀) - (cov Vij x₀) (frame k x₀) =
              ∑ m : CoordinateIdx (𝕜 := Real) E,
                hframe.coeff m x₀
                  ((cov Vkj x₀) (frame i x₀) - (cov Vij x₀) (frame k x₀)) •
                  frame m x₀ by
            simpa [frame, hframe] using
              (hframe.coeff_sum_eq
                (fun _ : M => (cov Vkj x₀) (frame i x₀) -
                  (cov Vij x₀) (frame k x₀)) hx₀)]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_sub]
          rw [hcov_i m, hcov_k m]
          unfold christoffelCurvCoeffAt
          unfold christoffelCoordDerivAt
          unfold christoffelCoordFun
          unfold christoffelSymbolInFrame
          congr 1
          have hVkj_coeff (a : CoordinateIdx (𝕜 := Real) E) :
              hframe.coeff a x₀ (Vkj x₀) =
                christoffelCoordAt (I := I) cov x₀ k j a := by
            simp [Vkj, christoffelCoordAt, frame]

          have hVij_coeff (a : CoordinateIdx (𝕜 := Real) E) :
              hframe.coeff a x₀ (Vij x₀) =
                christoffelCoordAt (I := I) cov x₀ i j a := by
            simp [Vij, christoffelCoordAt, frame]

          simp_rw [hVkj_coeff, hVij_coeff]
          simp
          ring


/-- The supplied `(1,3)` curvature tensor evaluates to the Christoffel
curvature coefficients in the chart-induced coordinate frame. -/
theorem rm13_eval_eq_christoffelCurvCoord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (i k j : CoordinateIdx (𝕜 := Real) E) :
    Rm13 x₀ alpha
        (vec3 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
      ∑ m : CoordinateIdx (𝕜 := Real) E,
        christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
          alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀) := by
  rw [hRm (coordinateFrameAt (I := I) x₀ i)
    (coordinateFrameAt (I := I) x₀ k) (coordinateFrameAt (I := I) x₀ j)
    x₀ alpha]
  rw [hcurv i k j]
  change cotangentToDual (I := I) alpha
      (∑ m : CoordinateIdx (𝕜 := Real) E,
        christoffelCurvCoeffAt (I := I) cov x₀ i k j m •
          coordinateFrameAt (I := I) x₀ m x₀) =
    ∑ m : CoordinateIdx (𝕜 := Real) E,
      christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
        alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀)
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [cotangentToDual_apply, smul_eq_mul]

/-- The intrinsic Ricci trace of a realized `(1,3)` curvature tensor is the
coordinate Christoffel trace in the chart-induced coordinate frame. -/
theorem ricciFromRm13At_coordFrame_eq_christoffelRicciCoeffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ricciFromRm13At (I := I) (M := M) (Rm13 x₀)
        (vec2 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
      christoffelRicciCoeffAt (I := I) cov x₀ i j := by
  classical
  let basis := coordinateFrameAt_toBasis (I := I) x₀
  rw [show coordinateFrameAt (I := I) x₀ i x₀ = basis i by
    simp [basis, coordinateFrameAt_toBasis_apply]]
  rw [show coordinateFrameAt (I := I) x₀ j x₀ = basis j by
    simp [basis, coordinateFrameAt_toBasis_apply]]
  rw [ricciFromRm13At_apply_basis_trace (I := I) basis (Rm13 x₀) (basis i) (basis j)]
  unfold christoffelRicciCoeffAt
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := rm13_eval_eq_christoffelCurvCoord (I := I) cov Rm13 x₀
    (dualToCotangent (I := I) (basis.coord a)) hRm hcurv a i j
  have hcoord (m : CoordinateIdx (𝕜 := Real) E) :
      ((coordinateFrameAt_toBasis (I := I) x₀).repr
          (coordinateFrameAt (I := I) x₀ m x₀)) a =
        if m = a then 1 else 0 := by
    rw [show coordinateFrameAt (I := I) x₀ m x₀ =
        (coordinateFrameAt_toBasis (I := I) x₀) m by
      simp [coordinateFrameAt_toBasis_apply]]
    by_cases hma : m = a
    · rw [hma]
      have hb := congrArg (fun f => f a)
        (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) a)
      simpa [coordinateFrameAt_toBasis_apply] using hb
    · have hb := congrArg (fun f => f a)
        (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) m)
      simpa [coordinateFrameAt_toBasis_apply, Finsupp.single_apply, hma] using hb
  have hsum :
      (∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ a i j m *
            ((coordinateFrameAt_toBasis (I := I) x₀).repr
              (coordinateFrameAt (I := I) x₀ m x₀)) a) =
        christoffelCurvCoeffAt (I := I) cov x₀ a i j a := by
    rw [show
        (∑ m : CoordinateIdx (𝕜 := Real) E,
            christoffelCurvCoeffAt (I := I) cov x₀ a i j m *
              ((coordinateFrameAt_toBasis (I := I) x₀).repr
                (coordinateFrameAt (I := I) x₀ m x₀)) a) =
          ∑ m : CoordinateIdx (𝕜 := Real) E,
            (if m = a then christoffelCurvCoeffAt (I := I) cov x₀ a i j a
              else 0) by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hcoord m]
      by_cases hma : m = a
      · subst hma
        simp
      · simp [hma]]
    simp
  have h' :
      ((Rm13 x₀) (dualToCotangent (I := I) (basis.coord a)))
          (vec3 (basis a) (basis i) (basis j)) =
        ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ a i j m *
            ((coordinateFrameAt_toBasis (I := I) x₀).repr
              (coordinateFrameAt (I := I) x₀ m x₀)) a := by
    simpa [basis, coordinateFrameAt_toBasis_apply, dualToCotangent_apply] using h
  rw [h']
  exact hsum

/-- Coordinate inputs for the textbook `(0,s)` Ricci-identity component
commutator. The first two slots are the derivative slots. -/
def tensor0SRicciIdentityCoordInput {s : ℕ}
    (i j : CoordinateIdx (𝕜 := Real) E)
    (ks : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    Fin (s + 2) -> CoordinateIdx (𝕜 := Real) E :=
  Fin.cases i (Fin.cases j ks)

/-- Coordinate projection of the invariant `(0,s)` curvature action.

This is the coordinate layer's only expansion of the slotwise curvature action
into Christoffel curvature components. -/
theorem curvatureAction0SAt_coordFrame_of_christoffelCurv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x0 : M) {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x0)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (ks : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    curvatureAction0SAt (I := I) Rm13 alpha
        (coordinateFrameAt (I := I) x0 i x0)
        (coordinateFrameAt (I := I) x0 j x0)
        (fun q : Fin s => coordinateFrameAt (I := I) x0 (ks q) x0)
      =
        -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
  classical
  let slots : Fin s -> TangentSpace I x0 :=
    fun q => coordinateFrameAt (I := I) x0 (ks q) x0
  have hslot (q : Fin s) (m : CoordinateIdx (𝕜 := Real) E) :
      oneFormAtSlot0S (I := I) alpha slots q
          (fun _ : Fin 1 => coordinateFrameAt (I := I) x0 m x0) =
        coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
    rw [oneFormAtSlot0S_apply, coordComponent0SAt_apply]
    congr 1
    funext a
    by_cases ha : a = q
    · subst ha
      simp [slots]
    · simp [slots, Function.update, ha]
  change
    -∑ q : Fin s,
      Rm13 x0 (oneFormAtSlot0S (I := I) alpha slots q)
        (vec3 (coordinateFrameAt (I := I) x0 i x0)
          (coordinateFrameAt (I := I) x0 j x0) (slots q))
      =
        -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m)
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [rm13_eval_eq_christoffelCurvCoord
    (I := I) cov Rm13 x0 (oneFormAtSlot0S (I := I) alpha slots q)
    hRm hcurv i j (ks q)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hslot q m]

/-- Coordinate-frame component form of the invariant `(0,s)` Ricci identity.

This is the book-facing specialization: evaluate the invariant identity on
coordinate vector fields and expand each curvature action in the replaced
slot through the coordinate curvature coefficients. -/
theorem tensor0S_ricciIdentity_coordFrame_of_christoffelCurv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x0 : M) {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x0)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x0)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x0)
    (hRicci : Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (ks : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) i j ks) -
      coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) j i ks)
      =
        -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
  classical
  let slots : Fin s -> TangentSpace I x0 :=
    fun q => coordinateFrameAt (I := I) x0 (ks q) x0
  have hleft :
      coordComponent0SAt (I := I) nabla2Alpha
          (tensor0SRicciIdentityCoordInput (E := E) i j ks) =
        nabla2Alpha
          (metricTraceInput (I := I) (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0) slots) := by
    rw [coordComponent0SAt_apply]
    congr 1
    funext a
    refine Fin.cases ?_ ?_ a
    · simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
    · intro a
      refine Fin.cases ?_ ?_ a
      · change (coordinateFrameAt_toBasis (I := I) x0) j =
          coordinateFrameAt (I := I) x0 j x0
        rw [coordinateFrameAt_toBasis_apply]
      · intro a
        simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
  have hright :
      coordComponent0SAt (I := I) nabla2Alpha
          (tensor0SRicciIdentityCoordInput (E := E) j i ks) =
        nabla2Alpha
          (metricTraceInput (I := I) (coordinateFrameAt (I := I) x0 j x0)
            (coordinateFrameAt (I := I) x0 i x0) slots) := by
    rw [coordComponent0SAt_apply]
    congr 1
    funext a
    refine Fin.cases ?_ ?_ a
    · simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
    · intro a
      refine Fin.cases ?_ ?_ a
      · change (coordinateFrameAt_toBasis (I := I) x0) i =
          coordinateFrameAt (I := I) x0 i x0
        rw [coordinateFrameAt_toBasis_apply]
      · intro a
        simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
  calc
    coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) i j ks) -
      coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) j i ks)
        = curvatureAction0SAt (I := I) Rm13 alpha
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0) slots := by
          rw [hleft, hright]
          exact hRicci (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0) slots
    _ = -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
          simpa [slots] using
            curvatureAction0SAt_coordFrame_of_christoffelCurv
              (I := I) cov Rm13 x0 alpha hRm hcurv i j ks

/-- Coordinate Christoffel-form one-form Ricci identity.

This is the scalar-coordinate producer that should be discharged by expanding
`nabla0SFun` with the coordinate Christoffel formulas and commuting the scalar
second derivatives. -/
def OneFormThirdCommChristoffelCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀) :
    Prop :=
  ∀ i k j : CoordinateIdx (𝕜 := Real) E,
    nabla2Alpha
        (vec3 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) -
      nabla2Alpha
        (vec3 (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
        -∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
            alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀)

/-- The Christoffel-coordinate commutator implies the tensor one-form Ricci
identity once the supplied `Rm13` tensor is known to realize connection
curvature and the connection curvature has the Christoffel-coordinate expansion. -/
theorem one_form_third_comm_coord_of_christoffelCurv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x₀ alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  refine one_form_third_comm_of_coord_ijk (I := I) Rm13 alpha
    (coordinateFrameAt_toBasis (I := I) x₀) nabla2Alpha ?_
  intro i k j
  have hRmCoord := rm13_eval_eq_christoffelCurvCoord
    (I := I) cov Rm13 x₀ alpha hRm hcurv i k j
  have hcoord' := hcoord i k j
  simp only [coordinateFrameAt_toBasis_apply]
  rw [hRmCoord]
  exact hcoord'

end CoordinateChristoffelCurvature

end Realized
end RicciFlower
