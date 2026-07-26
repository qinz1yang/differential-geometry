import DifferentialGeometry.Geometry.Curvature.Basic
import DifferentialGeometry.Geometry.Coordinates.Tensor
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.Multilinear.Tensor
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Tensor.Product.Basis
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.Tensor.Product.Pretrivialization
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Alternating.Flip
import DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import DifferentialGeometry.Tensor.Alternating.Congr
import Mathlib.LinearAlgebra.Alternating.Basic
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Mathlib.Topology.FiberBundle.Basic
import DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.Auxiliary.PredualBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Trace
import DifferentialGeometry.Tensor.RSTensor.Field

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Static curvature tensor sections

This file bundles static curvature objects as tensor sections over one
manifold.  It deliberately avoids parameterized metric data and flow
hypotheses.

The connection-to-section producer lives in `DifferentialGeometry.Integral.Connection.Basic` as the
intrinsic `rm13Section`, `rm04Section`, and `ricciSection` constructors.  Their
remaining proof fields are the honest smoothness/tensoriality frontier for
`connectionRiemannCurvatureField`; coordinate files should consume those
sections or their component theorems, not define curvature primitively.

This file contains only tensor aliases, pointwise trace operations, and
component evaluation helpers.  Realization predicates for supplied curvature
sections live in `DifferentialGeometry.Integral.Connection.CurvatureTensor`.
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Static smooth `(1,3)` tensor section. -/
abbrev Tensor13Section :=
  TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 1 3

/-- Static smooth `(0,4)` tensor section. -/
abbrev Tensor04Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 4

/-- Preferred name for a static smooth covariant four-tensor field. -/
abbrev FourTensorField := Tensor04Section (I := I) (M := M)

/-- Static smooth `(0,2)` tensor section. -/
abbrev Tensor02Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 2

/-- Preferred name for a static smooth covariant two-tensor field. -/
abbrev TwoTensorField := Tensor02Section (I := I) (M := M)

/-- Pointwise `(0,2)` tensor fiber. -/
abbrev Tensor02At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x

/-- Pointwise `(0,4)` tensor fiber. -/
abbrev Tensor04At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

/-- Pointwise `(1,3)` tensor fiber. -/
abbrev Tensor13At (x : M) :=
  TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3 x

/-- The unit `(0,0)` tensor used to read a `TensorRSSpace 0 s` as a
covariant `(0,s)` tensor. -/
def scalarOne0S (x : M) : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 0 x :=
  ContinuousMultilinearMap.constOfIsEmpty Real
    (fun _ : Fin 0 => TangentSpace I x) 1

/-- Ricci curvature as the trace of the endomorphism
`X ↦ Rm13(X,Y)Z`, expressed in the realized Hom tensor model by tracing the
leading upper/lower pair of a `(1,3)` tensor. -/
def ricciFromRm13At {x : M} (Rm13 : Tensor13At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
    (scalarOne0S (I := I) x)

/-- Feed two explicit tangent vectors into a `Fin 2` tensor. -/
def vec2 {x : M} (X Y : TangentSpace I x) : Fin 2 -> TangentSpace I x :=
  fun i => if i = 0 then X else Y

/-- Feed three explicit tangent vectors into a `Fin 3` tensor. -/
def vec3 {x : M} (X Y Z : TangentSpace I x) : Fin 3 -> TangentSpace I x :=
  fun i => if i = 0 then X else if i = 1 then Y else Z

/-- Feed four explicit tangent vectors into a `Fin 4` tensor. -/
def vec4 {x : M} (W X Y Z : TangentSpace I x) : Fin 4 -> TangentSpace I x :=
  fun i => if i = 0 then W else if i = 1 then X else if i = 2 then Y else Z

/-- Interpret a bundled Ricci section as a pointwise two-tensor field. -/
def tensor02ToField (Ric : Tensor02Section (I := I) (M := M)) :
    RawTwoTensorField (I := I) (M := M) :=
  fun x X Y => Ric x (vec2 X Y)

/-- Interpret a bundled lowered Riemann section as a pointwise four-tensor field. -/
def tensor04ToField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
  fun x X Y Z W => Rm04 x (vec4 X Y Z W)

/-- Standard slot evaluation of a lowered Riemann four-tensor:
`Rm04(X,Y,Z,W) = <R(X,Y)Z,W>`.

This is now direct evaluation of the canonical bundled tensor. -/
def tensor04StdAt {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) : Real :=
  Rm04 (vec4 X Y Z W)

/-- **⚠ SOFT-DEPRECATED — do not add new uses (eventual cleanup target).**

Output-first compatibility evaluation for a lowered Riemann four-tensor:
`Rm04Out(W,X,Y,Z) = Rm04(X,Y,Z,W)`.  This is the OLD slot order, kept explicit only for its remaining
legacy consumers during the convention migration.  Prefer the canonical standard-slot `tensor04StdAt`
(`Rm04(X,Y,Z,W)`) in new code; this output-first eval is slated for removal once the consumers migrate.
(The converter `tensor04StdOfOutAt`/`tensor04StdToOutPerm` are NOT deprecated — they are load-bearing in
the canonical lowering `riemannCurvature04At`.)  See `CurvatureCanonicalization.md`. -/
def tensor04OutAt {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) : Real :=
  Rm04 (vec4 X Y Z W)

/-- Slot permutation sending standard arguments `(X,Y,Z,W)` to the historical
output-first order `(W,X,Y,Z)`. -/
def tensor04StdToOutPerm : Equiv.Perm (Fin 4) where
  toFun i := if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else 2
  invFun i := if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 0
  left_inv i := by
    fin_cases i <;> simp
  right_inv i := by
    fin_cases i <;> simp

/-- Convert a historical output-first lowered Riemann tensor into the canonical
standard-slot tensor. -/
def tensor04StdOfOutAt {x : M} (Rm04Out : Tensor04At (I := I) (M := M) x) :
    Tensor04At (I := I) (M := M) x :=
  Rm04Out.domDomCongr tensor04StdToOutPerm

@[simp]
theorem tensor04StdAt_apply
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) Rm04 X Y Z W =
      Rm04 (vec4 X Y Z W) := rfl

@[simp]
theorem tensor04OutAt_apply
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) :
    tensor04OutAt (I := I) (M := M) Rm04 W X Y Z =
      Rm04 (vec4 X Y Z W) := rfl

@[simp]
theorem tensor04StdOfOutAt_apply
    {x : M} (Rm04Out : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StdOfOutAt (I := I) (M := M) Rm04Out (vec4 X Y Z W) =
      Rm04Out (vec4 W X Y Z) := by
  change Rm04Out (fun i => (vec4 X Y Z W) (tensor04StdToOutPerm i)) =
    Rm04Out (vec4 W X Y Z)
  congr 1
  funext i
  fin_cases i <;> simp [tensor04StdToOutPerm, vec4]

/-- Interpret a bundled lowered Riemann section as a raw four-tensor field in
standard slot order. -/
def tensor04ToStdField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
  fun x X Y Z W => tensor04StdAt (I := I) (Rm04 x) X Y Z W

/-- Interpret a bundled lowered Riemann section as a raw four-tensor field in
the old output-first slot order. -/
def tensor04ToOutField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
  fun x W X Y Z => tensor04OutAt (I := I) (Rm04 x) W X Y Z

/-- Ricci component in a static frame. -/
def ricciComp
    {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  Ric x (vec2 (frame i x) (frame j x))

/-- Lowered Riemann component in a static frame. -/
def rm04Comp
    {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) : Real :=
  Rm04 x (vec4 (frame i x) (frame j x) (frame k x) (frame l x))

/-- `(1,3)` Riemann component in a local frame, pairing the output with the
coframe covector. -/
def rm13Comp
    {Idx : Type*} {u : Set M}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (x : M) (a b c d : Idx) : Real :=
  Rm13 x (dualToCotangent_gen (hframe.coeff a x)) (vec3 (frame b x) (frame c x) (frame d x))

/-- Static bundled curvature data.  Smoothness of the scalar field is stored
explicitly; constructing the tensor sections from a connection is a separate
producer theorem frontier. -/
structure CurvatureTensorData where
  rm13 : Tensor13Section (I := I) (M := M)
  rm04 : Tensor04Section (I := I) (M := M)
  ricci : Tensor02Section (I := I) (M := M)
  scalar : M -> Real
  scalar_smooth : ContMDiff I 𝓘(Real) ∞ scalar

@[simp]
theorem rm04_comp_eq_eval
    {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) :
    rm04Comp (I := I) Rm04 frame x i j k l =
      Rm04 x (vec4 (frame i x) (frame j x) (frame k x) (frame l x)) :=
  rfl

end DifferentialGeometry.Integral.Connection
