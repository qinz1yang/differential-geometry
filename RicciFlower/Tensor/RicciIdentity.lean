import RicciFlower.RoughLaplacian
import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Tensor.RicciIdentity.MixedComponents
import RicciFlower.Tensor.Auxiliary.SlotAlgebra
import RicciFlower.Tensor.RSTensor.CurvatureAction
import RicciFlower.Tensor.RSTensor.NablaOnTensors
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Tensor Ricci Identity Interfaces

This file gives short, reusable names for Ricci-identity statements without
depending on scalar Bochner.  The scalar Bochner file can specialize the
one-form interface by taking `alpha = du`, `dLapAlpha = d(Delta u)`, and
`curvatureVector = grad u`.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open RicciFlower.Tensor.SlotAlgebra
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Smooth covariant tensor sections used by the section-level
covariant-derivative API. -/
abbrev Tensor0SSection (s : ℕ) :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) s

/-- Smooth one-form sections used by the section-level covariant-derivative API. -/
abbrev OneFormSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 1

/-- Smooth covariant two-tensor sections used by the section-level derivative API. -/
abbrev TwoTensorSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 2

/-- A supplied `(0,2)` tensor field realizes the covariant derivative of a
bundled one-form at one point. -/
def NablaOneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    nablaAlpha x (vec2 (X x) Y) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov X alpha x (fun _ : Fin 1 => Y)

/-- Section-level realization of `nablaAlpha = ∇ alpha`.

This is stronger than a single pointwise realization and is the information
needed to interpret a second derivative tensor as the true iterated derivative
of the original one-form. -/
def NablaOneFormSectionRealizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ x : M, NablaOneFormRealizesAt (I := I) cov alpha (fun y => nablaAlpha y) x

/-- A supplied `(0,3)` tensor realizes the true second covariant derivative of a
bundled one-form at `x`: the bundled two-tensor section realizes `∇ alpha`,
and the supplied three-tensor is `∇(∇ alpha)` at `x`. -/
def Nabla2OneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha ∧
    ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (Y Z : TangentSpace I x),
      nabla2Alpha (vec3 (X x) Y Z) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X nablaAlpha x (vec2 Y Z)

theorem nabla2OneFormRealizesAt_first
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha) :
    NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha :=
  h.1

theorem nabla2OneFormRealizesAt_apply
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 (X x) Y Z) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X nablaAlpha x (vec2 Y Z) :=
  h.2 X Y Z

/-- Build the existing pointwise second-one-form realization predicate from
two total covariant derivative realization steps. -/
theorem nabla2OneFormRealizesAt_of_totalNabla
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2AlphaSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov nablaAlpha nabla2AlphaSec)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x
      (nabla2AlphaSec x) := by
  constructor
  · intro y X Y
    have h := h1 X y (fun _ : Fin 1 => Y)
    have hslots :
        Fin.cons (X y) (fun _ : Fin 1 => Y) = vec2 (I := I) (X y) Y := by
      funext i
      fin_cases i <;> simp [vec2, RicciFlower.Curvature.vec2]
    rw [hslots] at h
    exact h
  · intro X Y Z
    have h := h2 X x (vec2 (I := I) Y Z)
    have hslots :
        Fin.cons (X x) (vec2 (I := I) Y Z) = vec3 (I := I) (X x) Y Z := by
      funext i
      fin_cases i
      · simp [Fin.cons_zero, vec3, RicciFlower.Curvature.vec3]
      · change (vec2 (I := I) Y Z) 0 = Y
        simp [vec2, RicciFlower.Curvature.vec2]
      · change (vec2 (I := I) Y Z) 1 = Z
        simp [vec2, RicciFlower.Curvature.vec2]
    rw [hslots] at h
    exact h

/-- Component-level trailing-slot symmetry for a third covariant derivative
candidate `U`. -/
def Nabla2DuTrailingSymmCoord {Idx : Type*}
    (U : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i j k : Idx, U i j k = U i k j

/-- Component-level one-form Ricci identity, with the sign convention already
absorbed into `curvatureAction`. -/
def OneFormRicciIdentityCoord {Idx : Type*}
    (U curvatureAction : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i k j : Idx, U i k j - U k i j = curvatureAction i k j

/-- Component-level trace of the one-form curvature action gives the
Ricci-gradient component. -/
def CurvatureActionTraceEqualsRicGradCoord {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real) : Prop :=
  ∀ k : Idx,
    (∑ i : Idx, ∑ j : Idx, gInv i j * curvatureAction i k j) = ricGrad k

/-- Pure finite-sum form of the Bochner one-form trace commutator.  The only
inputs are trailing symmetry, the one-form Ricci identity, and the traced
curvature-action identification. -/
theorem oneFormRicciTraceCommCoord_of_identities {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (U curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real)
    (h_symm : Nabla2DuTrailingSymmCoord U)
    (h_comm : OneFormRicciIdentityCoord U curvatureAction)
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv curvatureAction ricGrad) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx, gInv i j * U i j k) =
        (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) + ricGrad k := by
  intro k
  calc
    (∑ i : Idx, ∑ j : Idx, gInv i j * U i j k)
        = ∑ i : Idx, ∑ j : Idx, gInv i j * U i k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_symm i j k]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * (U k i j + curvatureAction i k j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          have h : U i k j = U k i j + curvatureAction i k j := by
            calc
              U i k j = (U i k j - U k i j) + U k i j := by ring
              _ = curvatureAction i k j + U k i j := by rw [h_comm i k j]
              _ = U k i j + curvatureAction i k j := by ring
          rw [h]
    _ = (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) +
        (∑ i : Idx, ∑ j : Idx, gInv i j * curvatureAction i k j) := by
          simp_rw [mul_add]
          simp_rw [Finset.sum_add_distrib]
    _ = (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) + ricGrad k := by
          rw [h_trace k]


/-- Pointwise Ricci identity for the third covariant derivative of a one-form.

With the realized convention `Rm13 alpha X Y Z = alpha (R(X,Y)Z)`, the
covector commutator carries the negative sign:
`∇² alpha(X,Y,Z) - ∇² alpha(Y,X,Z) = -Rm13(alpha,X,Y,Z)`. -/
def OneFormThirdCovDerivCommAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z)

theorem one_form_third_covDeriv_comm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  h X Y Z

/-- Swap the first two slots of a `(0,3)` tensor. -/
def swapFirstTwo0S {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  A.domDomCongr (Equiv.swap (0 : Fin 3) 1)

@[simp] theorem swapFirstTwo0S_apply_vec3 {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X Y Z : TangentSpace I x) :
    swapFirstTwo0S (I := I) A (vec3 X Y Z) = A (vec3 Y X Z) := by
  change A (fun i => (vec3 X Y Z) ((Equiv.swap (0 : Fin 3) 1) i)) =
    A (vec3 Y X Z)
  congr 1
  funext q
  fin_cases q <;> simp [Equiv.swap_apply_def, vec3, RicciFlower.Curvature.vec3]

/-- Promote the coordinate form of the one-form Ricci identity to the tensor
identity at a point. -/
theorem one_form_third_comm_of_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ slots : Fin 3 -> Idx,
      nabla2Alpha (fun a => basis (slots a)) -
        nabla2Alpha (fun a => basis (slots ((Equiv.swap (0 : Fin 3) 1) a))) =
          -Rm13 x alpha (fun a => basis (slots a))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  have htensor :
      nabla2Alpha - swapFirstTwo0S (I := I) nabla2Alpha = -Rm13 x alpha := by
    apply ext0S_basis (I := I) basis
    intro slots
    simpa [component0S, swapFirstTwo0S] using hcoord slots
  intro X Y Z
  have h_eval := congrArg
    (fun A :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x =>
        A (vec3 X Y Z)) htensor
  simpa using h_eval

/-- A component-indexed version of `one_form_third_comm_of_coord`. -/
theorem one_form_third_comm_of_coord_ijk
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ i k j : Idx,
      nabla2Alpha (vec3 (basis i) (basis k) (basis j)) -
        nabla2Alpha (vec3 (basis k) (basis i) (basis j)) =
          -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  one_form_third_comm_of_coord (I := I) Rm13 alpha basis nabla2Alpha fun slots => by
    have h := hcoord (slots 0) (slots 1) (slots 2)
    have hslots :
        (fun a => basis (slots a)) =
          vec3 (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) := by
      funext q
      fin_cases q <;> simp [vec3, RicciFlower.Curvature.vec3]
    have hswap :
        (fun a => basis (slots ((Equiv.swap (0 : Fin 3) 1) a))) =
          vec3 (basis (slots 1)) (basis (slots 0)) (basis (slots 2)) := by
      funext q
      fin_cases q <;> simp [Equiv.swap_apply_def, vec3, RicciFlower.Curvature.vec3]
    simpa [hslots, hswap] using h

/-- Pointwise trailing-slot symmetry of the second covariant derivative of a
one-form. For `alpha = du`, this is the Hessian symmetry input preserved in the
last two slots of `∇² alpha`. -/
def OneFormLastTwoSymmAt {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y)

theorem one_form_last_two_symm {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y) :=
  h X Y Z

/-- The traced Hessian-derivative term for a one-form candidate.  In the
scalar specialization `alpha = du`, this is the term that realizes
`d (Delta u)`. -/
def traceNablaOneFormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))

/-- Pointwise one-form trace commutator with an explicit curvature vector:
`tr_g ∇²α(.,.,Y) = tr_g ∇²α(Y,.,.) + Ric(Y,V)`. -/
def OneFormRicciTraceCommWithVectorAt
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    roughLap1FormAt (I := I) basis gInv nabla2Alpha Y =
      traceNablaOneFormAt (I := I) basis gInv nabla2Alpha Y +
        Ric x (vec2 Y curvatureVector)

/-- Coordinate components of a supplied second covariant derivative of a
one-form in a pointwise tangent basis. -/
def nabla2OneFormCoord
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (i j k : Idx) : Real :=
  nabla2Alpha (vec3 (basis i) (basis j) (basis k))

/-- Signed curvature-action components for a one-form.  The minus sign is the
covector curvature-action sign for the convention
`Rm13 alpha X Y Z = alpha (R(X,Y)Z)`. -/
def curvatureActionOnOneFormCoord
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i k j : Idx) : Real :=
  -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))

/-- Ricci-vector components in a pointwise tangent basis. -/
def ricciVectorCoord
    {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (curvatureVector : TangentSpace I x)
    (k : Idx) : Real :=
  Ric x (vec2 (basis k) curvatureVector)

theorem nabla2OneFormTrailingSymmCoord_of_tensor
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha) :
    Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha) := by
  intro i j k
  exact hsymm (basis i) (basis j) (basis k)

theorem oneFormRicciIdentityCoord_of_tensor
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis) := by
  intro i k j
  exact hcomm (basis i) (basis k) (basis j)

/-- Coordinate-basis form of the trace commutator, obtained from the three
component identities. -/
theorem oneFormRicciTraceComm_basisCoord_of_identities
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h_symm : Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha))
    (h_comm : OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis))
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)
      (ricciVectorCoord (I := I) Ric basis curvatureVector)) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx,
        gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha i j k) =
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha k i j) +
          ricciVectorCoord (I := I) Ric basis curvatureVector k :=
  oneFormRicciTraceCommCoord_of_identities gInv
    (nabla2OneFormCoord (I := I) basis nabla2Alpha)
    (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)
    (ricciVectorCoord (I := I) Ric basis curvatureVector)
    h_symm h_comm h_trace

theorem metricTraceInput_one_eq_vec3 {x : M}
    (X Y Z : TangentSpace I x) :
    metricTraceInput (I := I) X Y (fun _ : Fin 1 => Z) = vec3 X Y Z := by
  funext q
  fin_cases q
  · simp [metricTraceInput, vec3, RicciFlower.Curvature.vec3]
  · change
      Fin.cases X (fun i : Fin 2 => Fin.cases Y (fun _ : Fin 1 => Z) i)
          (Fin.succ 0) = Y
    rw [Fin.cases_succ, Fin.cases_zero]
  · change
      Fin.cases X (fun i : Fin 2 => Fin.cases Y (fun _ : Fin 1 => Z) i)
          (Fin.succ (Fin.succ 0)) = Z
    rw [Fin.cases_succ, Fin.cases_succ]

/-- Trace-level Bochner commutator consumer from the untraced one-form Ricci
identity. This is only finite-sum algebra: the actual geometric proof of the
untraced commutator, trailing-slot symmetry, and curvature trace is supplied by
the three pointwise hypotheses. -/
theorem oneForm_ricci_trace_comm_of_third_comm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (hcurv : ∀ Y : TangentSpace I x,
      -∑ i : Idx, ∑ j : Idx,
        gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j)) =
          Ric x (vec2 Y curvatureVector)) :
    OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv curvatureVector
      nabla2Alpha := by
  intro Y
  unfold roughLap1FormAt roughLap0SAt metricTrace0S2InBasis
    traceNablaOneFormAt
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          nabla2Alpha (metricTraceInput (I := I) (basis i) (basis j)
            (fun _ : Fin 1 => Y)))
        = ∑ i : Idx, ∑ j : Idx,
            gInv i j * nabla2Alpha (vec3 (basis i) (basis j) Y) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [metricTraceInput_one_eq_vec3]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 (basis i) Y (basis j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsymm (basis i) (basis j) Y]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (nabla2Alpha (vec3 Y (basis i) (basis j)) -
              Rm13 x alpha (vec3 (basis i) Y (basis j))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          have h := hcomm (basis i) Y (basis j)
          calc
            nabla2Alpha (vec3 (basis i) Y (basis j))
                = (nabla2Alpha (vec3 (basis i) Y (basis j)) -
                    nabla2Alpha (vec3 Y (basis i) (basis j))) +
                    nabla2Alpha (vec3 Y (basis i) (basis j)) := by ring
            _ = -Rm13 x alpha (vec3 (basis i) Y (basis j)) +
                  nabla2Alpha (vec3 Y (basis i) (basis j)) := by rw [h]
            _ = nabla2Alpha (vec3 Y (basis i) (basis j)) -
                  Rm13 x alpha (vec3 (basis i) Y (basis j)) := by ring_nf
    _ = (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))) +
        (-∑ i : Idx, ∑ j : Idx,
          gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j))) := by
          simp_rw [mul_sub]
          simp_rw [Finset.sum_sub_distrib]
          ring
    _ = (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))) +
        Ric x (vec2 Y curvatureVector) := by
          rw [hcurv Y]

/-- One-form Ricci identity interface at a point:
`roughAlpha = dLapAlpha + Ric(., curvatureVector)`. -/
def RicciIdentityOneFormAt
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x) : Prop :=
  ∀ Y : TangentSpace I x,
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector)

theorem ricci_identity_one_form
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x)
    (h : RicciIdentityOneFormAt (I := I) Ric roughAlpha dLapAlpha curvatureVector)
    (Y : TangentSpace I x) :
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector) :=
  h Y

theorem tensor0S_ricciIdentity_one_of_oneForm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext q
    fin_cases q
    rfl
  have hcomm := h X Y (slots 0)
  rw [hslots]
  rw [metricTraceInput_one_eq_vec3, metricTraceInput_one_eq_vec3]
  simp [curvatureAction0SAt, hcomm]

theorem oneFormThirdCovDerivCommAt_of_tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y Z
  have h0 := h X Y (fun _ : Fin 1 => Z)
  simpa [Tensor0SRicciIdentityAt, curvatureAction0SAt,
    metricTraceInput_one_eq_vec3] using h0

theorem tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha ↔
      OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  ⟨oneFormThirdCovDerivCommAt_of_tensor0S_ricciIdentity_one (I := I)
      Rm13 alpha nabla2Alpha,
    tensor0S_ricciIdentity_one_of_oneForm (I := I) Rm13 alpha nabla2Alpha⟩

/-- A supplied `(0,s+1)` tensor field realizes the covariant derivative of a
bundled `(0,s)` tensor at one point. -/
def Nabla0SRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
      (slots : Fin s → TangentSpace I x),
    nablaAlpha x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X alpha x slots

/-- Section-level realization of `nablaAlpha = ∇ alpha` for `(0,s)` tensors. -/
def Nabla0SSectionRealizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)) : Prop :=
  ∀ x : M, Nabla0SRealizesAt (I := I) s cov alpha (fun y => nablaAlpha y) x

/-- A supplied `(0,s+2)` tensor realizes the true second covariant derivative of
a bundled `(0,s)` tensor at one point. -/
def Nabla20SRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha ∧
    ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
        (slots : Fin (s + 1) → TangentSpace I x),
      nabla2Alpha (Fin.cons (X x) slots) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + 1) cov X nablaAlpha x slots

/-- Definition 14.5 for a realized first covariant derivative of a `(0,s)`
tensor section. -/
theorem Nabla0SSectionRealizes.eval_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x)) =
      extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
        x (X x) -
        ∑ a : Fin s,
          alpha x
            (Function.update (fun b : Fin s => V b x) a
              ((cov (fun p : M => V a p) x) (X x))) := by
  calc
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X alpha x (fun a : Fin s => V a x) := by
          exact h x X (fun a : Fin s => V a x)
    _ = extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
          x (X x) -
          ∑ a : Fin s,
            alpha x
              (Function.update (fun b : Fin s => V b x) a
                ((cov (fun p : M => V a p) x) (X x))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V alpha x

/-- Definition 14.5 for a realized first covariant derivative, evaluated on an
arbitrary tangent vector in the derivative slot and smooth moving tensor slots.
The proof extends the tangent vector to a smooth section and reuses
`eval_smooth_slots`. -/
theorem Nabla0SSectionRealizes.eval_point_vector_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    {x : M}
    (W : TangentSpace I x)
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    nablaAlpha x (Fin.cons W (fun q : Fin s => V q x)) =
      extDerivFun (I := I)
        (fun y : M => alpha y (fun q : Fin s => V q y)) x W -
      ∑ q : Fin s,
        alpha x
          (Function.update (fun r : Fin s => V r x) q
            ((cov (fun y : M => V q y) x) W)) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have h0 := Nabla0SSectionRealizes.eval_smooth_slots
    (I := I) h Wsec V x
  simpa [hWsec] using h0

/-- Definition 14.5 for a realized first covariant derivative with only `C¹`
moving slots. -/
theorem Nabla0SSectionRealizes.eval_C1_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → (x : M) → TangentSpace I x)
    (x : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x) :
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x)) =
      extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
        x (X x) -
        ∑ a : Fin s,
          alpha x
            (Function.update (fun b : Fin s => V b x) a
              ((cov (V a) x) (X x))) := by
  calc
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X alpha x (fun a : Fin s => V a x) := by
          exact h x X (fun a : Fin s => V a x)
    _ = extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
          x (X x) -
          ∑ a : Fin s,
            alpha x
              (Function.update (fun b : Fin s => V b x) a
                ((cov (V a) x) (X x))) := by
          exact nabla0SFun_eval_C1_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V alpha x hV_at

/-- Definition 14.5 for a realized second covariant derivative of a `(0,s)`
tensor section, applied to the outer derivative slot and smooth moving
remaining slots. -/
theorem Nabla20SRealizesAt.eval_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    {x : M}
    {nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x}
    (h : Nabla20SRealizesAt (I := I) s cov alpha nablaAlpha x nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    nabla2Alpha (Fin.cons (X x) (fun a : Fin (s + 1) => V a x)) =
      extDerivFun (I := I) (fun p : M => nablaAlpha p
          (fun a : Fin (s + 1) => V a p)) x (X x) -
        ∑ a : Fin (s + 1),
          nablaAlpha x
            (Function.update (fun b : Fin (s + 1) => V b x) a
              ((cov (fun p : M => V a p) x) (X x))) := by
  calc
    nabla2Alpha (Fin.cons (X x) (fun a : Fin (s + 1) => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (s + 1) cov X nablaAlpha x
            (fun a : Fin (s + 1) => V a x) := by
          exact h.2 X (fun a : Fin (s + 1) => V a x)
    _ = extDerivFun (I := I) (fun p : M => nablaAlpha p
            (fun a : Fin (s + 1) => V a p)) x (X x) -
          ∑ a : Fin (s + 1),
            nablaAlpha x
              (Function.update (fun b : Fin (s + 1) => V b x) a
                ((cov (fun p : M => V a p) x) (X x))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V nablaAlpha x

private theorem mdiffAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι → M → Real)
    {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using
        (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real))
          (c := (0 : Real)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

private theorem extDerivFun_finset_sum_at
    {ι : Type*} (t : Finset ι) (f : ι → M → Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x :=
        mdiffAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I) (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

private theorem extDerivFun_neg_at
    {f : M → Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    extDerivFun (I := I) (fun y : M => -f y) x v =
      -extDerivFun (I := I) f x v := by
  have hfun : (fun y : M => -f y) = ((fun _ : M => (-1 : Real)) • f) := by
    ext y
    simp
  rw [hfun]
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => (-1 : Real)) (g := f)
    (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := (-1 : Real)) (x := x))
    hf v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul] using hprod

private theorem extDerivFun_sub_at
    {f g : M → Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y - g y) x v =
      extDerivFun (I := I) f x v - extDerivFun (I := I) g x v := by
  have hneg := extDerivFun_neg_at (I := I) (f := g) (x := x) v hg
  have hadd := congr($(extDerivFun_add
    (I := I) (g := f) (g' := fun y : M => -g y)
    (x := x) hf hg.neg) v)
  simpa [Pi.add_apply, sub_eq_add_neg, hneg] using hadd

private lemma tensor0S_update_curvature_diag
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s)
    (DXY DYX DB : TangentSpace I x) :
    -alpha (Function.update slots q DXY) +
        alpha (Function.update slots q DYX) +
        alpha (Function.update slots q DB) =
      -alpha (Function.update slots q (DXY - DYX - DB)) := by
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun T => alpha (Function.update slots q T)
      map_add' := by
        intro U V
        exact alpha.map_update_add slots q U V
      map_smul' := by
        intro c U
        rw [alpha.map_update_smul]
        simp [smul_eq_mul] }
  change -L DXY + L DYX + L DB = -L (DXY - DYX - DB)
  rw [map_sub, map_sub]
  abel

private lemma metricTraceInput_eq_finCons {s : ℕ} {x : M}
    (X Y : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    metricTraceInput (I := I) X Y tail =
      Fin.cons X (Fin.cons Y tail) := by
  rfl

private lemma first_slot_torsionCorrection_eq
    {s : ℕ} {x : M}
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (A B C : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    nablaAlpha (Fin.cons C slots) - nablaAlpha (Fin.cons A slots) +
        nablaAlpha (Fin.cons B slots) =
      -torsionCorrection0SAt (I := I) nablaAlpha (A - B - C) slots := by
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun T => nablaAlpha (Fin.cons T slots)
      map_add' := by
        intro U V
        let base : Fin (s + 1) → TangentSpace I x := Fin.cons 0 slots
        simpa [base] using nablaAlpha.map_update_add base 0 U V
      map_smul' := by
        intro c U
        let base : Fin (s + 1) → TangentSpace I x := Fin.cons 0 slots
        simpa [base, smul_eq_mul] using nablaAlpha.map_update_smul base 0 c U }
  change L C - L A + L B = -L (A - B - C)
  rw [map_sub, map_sub]
  abel

/-- Section-level expansion frontier for the invariant `(0,s)` Ricci identity.

All pointwise extension choices have already been made here.  The remaining
content is the finite-sum moving-slot calculation: expand both second
covariant derivatives by Definition 14.5, apply the scalar Lie-bracket
commutator, cancel off-diagonal slot updates, and identify the diagonal terms
with connection curvature. -/
private theorem tensor0S_commutator_expansion_from_realizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    let X : TangentSpace I x := Xsec x
    let Y : TangentSpace I x := Ysec x
    let slots : Fin s → TangentSpace I x := fun q => Vsec q x
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots -
        torsionCorrection0SAt (I := I) nablaAlpha (cov.torsion x X Y) slots := by
  classical
  dsimp only
  let Xf : (p : M) → TangentSpace I p := fun p => Xsec p
  let Yf : (p : M) → TangentSpace I p := fun p => Ysec p
  let Vfield : Fin s → (p : M) → TangentSpace I p := fun q p => Vsec q p
  let slots : Fin s → TangentSpace I x := fun q => Vsec q x
  let WY :
      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    Fin.cons Ysec Vsec
  let WX :
      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    Fin.cons Xsec Vsec
  have hXY :
      nabla2Alpha (Fin.cons (Xsec x) (fun a : Fin (s + 1) => WY a x)) =
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p))
            x (Xsec x) -
          ∑ a : Fin (s + 1),
            nablaAlphaSec x
              (Function.update
                (fun b : Fin (s + 1) => WY b x) a
                ((cov (fun p : M => WY a p) x) (Xsec x))) := by
    have h := Nabla20SRealizesAt.eval_smooth_slots
      (I := I) hnabla2 Xsec WY
    simpa using h
  have hYX :
      nabla2Alpha (Fin.cons (Ysec x) (fun a : Fin (s + 1) => WX a x)) =
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p))
            x (Ysec x) -
          ∑ a : Fin (s + 1),
            nablaAlphaSec x
              (Function.update
                (fun b : Fin (s + 1) => WX b x) a
                ((cov (fun p : M => WX a p) x) (Ysec x))) := by
    have h := Nabla20SRealizesAt.eval_smooth_slots
      (I := I) hnabla2 Ysec WX
    simpa using h
  have hFY (p : M) :
      nablaAlphaSec p
          (Fin.cons (Ysec p) (fun q : Fin s => Vsec q p)) =
        extDerivFun (I := I)
            (fun y : M => alphaSec y (fun q : Fin s => Vsec q y))
            p (Ysec p) -
          ∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Ysec p))) := by
    have h := Nabla0SSectionRealizes.eval_smooth_slots
      (I := I) hnabla2.1 Ysec Vsec p
    simpa using h
  have hFX (p : M) :
      nablaAlphaSec p
          (Fin.cons (Xsec p) (fun q : Fin s => Vsec q p)) =
        extDerivFun (I := I)
            (fun y : M => alphaSec y (fun q : Fin s => Vsec q y))
            p (Xsec p) -
          ∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Xsec p))) := by
    have h := Nabla0SSectionRealizes.eval_smooth_slots
      (I := I) hnabla2.1 Xsec Vsec p
    simpa using h
  let YV : Fin s → (p : M) → TangentSpace I p :=
    fun q p => (cov (fun y : M => Vsec q y) p) (Ysec p)
  let XV : Fin s → (p : M) → TangentSpace I p :=
    fun q p => (cov (fun y : M => Vsec q y) p) (Xsec p)
  have hYV_C1 (q : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, YV q p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    simpa [YV] using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := ℝ) cov hcov Ysec (Vsec q) x
  have hXV_C1 (q : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, XV q p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    simpa [XV] using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := ℝ) cov hcov Xsec (Vsec q) x
  let VYq : Fin s → Fin s → (p : M) → TangentSpace I p :=
    fun q => Function.update Vfield q (YV q)
  let VXq : Fin s → Fin s → (p : M) → TangentSpace I p :=
    fun q => Function.update Vfield q (XV q)
  have hVYq_C1 (q a : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, VYq q a p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    by_cases ha : a = q
    · subst a
      simpa [VYq, Vfield] using hYV_C1 q
    · simpa [VYq, Vfield, ha] using
        ((Vsec a).contMDiff.contMDiffAt.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
  have hVXq_C1 (q a : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, VXq q a p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    by_cases ha : a = q
    · subst a
      simpa [VXq, Vfield] using hXV_C1 q
    · simpa [VXq, Vfield, ha] using
        ((Vsec a).contMDiff.contMDiffAt.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
  have hDX_corrY (q : Fin s) :
      extDerivFun (I := I)
          (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
          x (Xsec x) =
        nablaAlphaSec x
            (Fin.cons (Xsec x) (fun a : Fin s => VYq q a x)) +
          ∑ a : Fin s,
            alphaSec x
              (Function.update (fun b : Fin s => VYq q b x) a
                ((cov (fun p : M => VYq q a p) x) (Xsec x))) := by
    have h := Nabla0SSectionRealizes.eval_C1_slots
      (I := I) hnabla2.1 Xsec (VYq q) x (hVYq_C1 q)
    rw [h]
    abel
  have hDY_corrX (q : Fin s) :
      extDerivFun (I := I)
          (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
          x (Ysec x) =
        nablaAlphaSec x
            (Fin.cons (Ysec x) (fun a : Fin s => VXq q a x)) +
          ∑ a : Fin s,
            alphaSec x
              (Function.update (fun b : Fin s => VXq q b x) a
                ((cov (fun p : M => VXq q a p) x) (Ysec x))) := by
    have h := Nabla0SSectionRealizes.eval_C1_slots
      (I := I) hnabla2.1 Ysec (VXq q) x (hVXq_C1 q)
    rw [h]
    abel
  have hcurvAction :
      curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x) =
        curvatureAction0SAtSlots (I := I) alpha
          (fun q : Fin s => Vsec q x)
          (fun q : Fin s =>
            (connectionRiemannCurvatureField (I := I) cov Xf Yf
              (fun p : M => Vsec q p)) x) := by
    simpa [Xf, Yf] using
      curvatureAction0SAt_eq_slots_connectionRiemannCurvature
        (I := I) (cov := cov) (Rm13 := Rm13)
        alpha Xsec Ysec Vsec hRm13
  have hcurvActionSlots :
      curvatureAction0SAtSlots (I := I) alpha
          (fun q : Fin s => Vsec q x)
          (fun q : Fin s =>
            (connectionRiemannCurvatureField (I := I) cov Xf Yf
              (fun p : M => Vsec q p)) x) =
        -∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)) := by
    rfl
  have hX_mdiff : MDiffAt (T% Xf) x := by
    simpa [Xf] using
      (Xsec.contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
  have hY_mdiff : MDiffAt (T% Yf) x := by
    simpa [Yf] using
      (Ysec.contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
  have htorsion_apply :
      cov.torsion x (Xsec x) (Ysec x) =
        (cov Yf x) (Xsec x) - (cov Xf x) (Ysec x) -
          VectorField.mlieBracket I Xf Yf x := by
    simpa [Xf, Yf] using
      cov.torsion_apply hX_mdiff hY_mdiff
  have htorsionFirstSlot :
      nablaAlpha
          (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots) =
        -torsionCorrection0SAt (I := I) nablaAlpha
          (cov.torsion x (Xsec x) (Ysec x)) slots := by
    have h := first_slot_torsionCorrection_eq
      (I := I) nablaAlpha ((cov Yf x) (Xsec x))
      ((cov Xf x) (Ysec x)) (VectorField.mlieBracket I Xf Yf x) slots
    simpa [htorsion_apply] using h
  have hExpanded :
      nabla2Alpha
          (metricTraceInput (I := I) (Xsec x) (Ysec x)
            (fun q : Fin s => Vsec q x)) -
        nabla2Alpha
          (metricTraceInput (I := I) (Ysec x) (Xsec x)
            (fun q : Fin s => Vsec q x))
        =
        (-∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)))
        +
        (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots)) := by
    -- This is the remaining expansion/cancellation core:
    -- use `hXY`/`hYX`, `hFY`/`hFX`, `hDX_corrY`/`hDY_corrX`,
    -- `Nabla0SSectionRealizes.eval_point_vector_smooth_slots`, and
    -- `double_update_sum_cancel_diag`.
    rw [metricTraceInput_eq_finCons (I := I) (Xsec x) (Ysec x)
      (fun q : Fin s => Vsec q x)]
    rw [metricTraceInput_eq_finCons (I := I) (Ysec x) (Xsec x)
      (fun q : Fin s => Vsec q x)]
    have hWYx :
        (fun a : Fin (s + 1) => WY a x) =
          Fin.cons (Ysec x) (fun q : Fin s => Vsec q x) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · simp [WY]
      · intro q
        simp [WY]
    have hWXx :
        (fun a : Fin (s + 1) => WX a x) =
          Fin.cons (Xsec x) (fun q : Fin s => Vsec q x) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · simp [WX]
      · intro q
        simp [WX]
    have hcorrWY :
        (∑ a : Fin (s + 1),
          nablaAlphaSec x
            (Function.update (fun b : Fin (s + 1) => WY b x) a
              ((cov (fun p : M => WY a p) x) (Xsec x)))) =
          nablaAlphaSec x
            (Fin.cons ((cov Yf x) (Xsec x))
              (fun q : Fin s => Vsec q x)) +
            ∑ q : Fin s,
              nablaAlphaSec x
                (Fin.cons (Ysec x)
                  (Function.update (fun r : Fin s => Vsec r x) q
                    (XV q x))) := by
      rw [hWYx]
      simpa [WY, Xf, Yf, XV] using
        sum_update_finCons_raw
          (F := fun slots' : Fin (s + 1) → TangentSpace I x =>
            nablaAlphaSec x slots')
          (head := Ysec x)
          (tail := fun q : Fin s => Vsec q x)
          (d := fun a : Fin (s + 1) =>
            (cov (fun p : M =>
              ((Fin.cons Ysec Vsec :
                Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M → Type _)) a) p) x) (Xsec x))
    have hcorrWX :
        (∑ a : Fin (s + 1),
          nablaAlphaSec x
            (Function.update (fun b : Fin (s + 1) => WX b x) a
              ((cov (fun p : M => WX a p) x) (Ysec x)))) =
          nablaAlphaSec x
            (Fin.cons ((cov Xf x) (Ysec x))
              (fun q : Fin s => Vsec q x)) +
            ∑ q : Fin s,
              nablaAlphaSec x
                (Fin.cons (Xsec x)
                  (Function.update (fun r : Fin s => Vsec r x) q
                    (YV q x))) := by
      rw [hWXx]
      simpa [WX, Xf, Yf, YV] using
        sum_update_finCons_raw
          (F := fun slots' : Fin (s + 1) → TangentSpace I x =>
            nablaAlphaSec x slots')
          (head := Xsec x)
          (tail := fun q : Fin s => Vsec q x)
          (d := fun a : Fin (s + 1) =>
            (cov (fun p : M =>
              ((Fin.cons Xsec Vsec :
                Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M → Type _)) a) p) x) (Ysec x))
    let baseScalar : M → Real :=
      fun p : M => alphaSec p (fun q : Fin s => Vsec q p)
    have hbaseSmooth :
        ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) baseScalar x := by
      simpa [baseScalar] using
        Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec Vsec x
    have hbase2 :
        ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) baseScalar x :=
      hbaseSmooth.of_le
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hX2 :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
          (T% Xf) x := by
      simpa [Xf] using
        (Xsec.contMDiff.contMDiffAt.of_le
          (by
            exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
    have hY2 :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
          (T% Yf) x := by
      simpa [Yf] using
        (Ysec.contMDiff.contMDiffAt.of_le
          (by
            exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
    have hYbase_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p)) x := by
      exact
        (RicciFlower.extDerivFun_apply_contMDiffAt
          (I := I) hbaseSmooth Ysec).mdifferentiableAt (by simp)
    have hXbase_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p)) x := by
      exact
        (RicciFlower.extDerivFun_apply_contMDiffAt
          (I := I) hbaseSmooth Xsec).mdifferentiableAt (by simp)
    have hCY_mdiff (q : Fin s) :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => alphaSec p (fun a : Fin s => VYq q a p)) x := by
      exact
        Tensor0SBundle.tensor0SField_eval_C1_slots_mdiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec (VYq q) x (hVYq_C1 q)
    have hCX_mdiff (q : Fin s) :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => alphaSec p (fun a : Fin s => VXq q a p)) x := by
      exact
        Tensor0SBundle.tensor0SField_eval_C1_slots_mdiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec (VXq q) x (hVXq_C1 q)
    have hCY_sum_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M =>
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) x :=
      by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VYq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          mdiffAt_finset_sum (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VYq q a p))
            (by intro q hq; exact hCY_mdiff q)
    have hCX_sum_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M =>
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) x :=
      by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VXq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          mdiffAt_finset_sum (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VXq q a p))
            (by intro q hq; exact hCX_mdiff q)
    have hFY_fun :
        (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p)) =
          fun p : M =>
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
      funext p
      have hWYp :
          (fun a : Fin (s + 1) => WY a p) =
            Fin.cons (Ysec p) (fun q : Fin s => Vsec q p) := by
        funext a
        refine Fin.cases ?_ ?_ a
        · simp [WY]
        · intro q
          simp [WY]
      have hsum :
          (∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Ysec p)))) =
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        congr 1
        funext a
        by_cases ha : a = q
        · subst a
          simp [VYq, Vfield, YV]
        · simp [VYq, Vfield, YV, ha]
      calc
        nablaAlphaSec p (fun a : Fin (s + 1) => WY a p)
            = nablaAlphaSec p
                (Fin.cons (Ysec p) (fun q : Fin s => Vsec q p)) := by
              rw [hWYp]
        _ =
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s,
                alphaSec p
                  (Function.update (fun r : Fin s => Vsec r p) q
                    ((cov (fun y : M => Vsec q y) p) (Ysec p))) := by
              simpa [baseScalar] using hFY p
        _ =
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
              rw [hsum]
    have hFX_fun :
        (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p)) =
          fun p : M =>
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
      funext p
      have hWXp :
          (fun a : Fin (s + 1) => WX a p) =
            Fin.cons (Xsec p) (fun q : Fin s => Vsec q p) := by
        funext a
        refine Fin.cases ?_ ?_ a
        · simp [WX]
        · intro q
          simp [WX]
      have hsum :
          (∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Xsec p)))) =
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        congr 1
        funext a
        by_cases ha : a = q
        · subst a
          simp [VXq, Vfield, XV]
        · simp [VXq, Vfield, XV, ha]
      calc
        nablaAlphaSec p (fun a : Fin (s + 1) => WX a p)
            = nablaAlphaSec p
                (Fin.cons (Xsec p) (fun q : Fin s => Vsec q p)) := by
              rw [hWXp]
        _ =
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s,
                alphaSec p
                  (Function.update (fun r : Fin s => Vsec r p) q
                    ((cov (fun y : M => Vsec q y) p) (Xsec p))) := by
              simpa [baseScalar] using hFX p
        _ =
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
              rw [hsum]
    have hFY_deriv :
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p))
            x (Xsec x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
              x (Xsec x) -
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
                x (Xsec x) := by
      rw [hFY_fun]
      rw [extDerivFun_sub_at (I := I) (x := x) (v := Xsec x)
        hYbase_mdiff hCY_sum_mdiff]
      have hsum :
          extDerivFun (I := I)
              (fun p : M =>
                ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p))
              x (Xsec x) =
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
                x (Xsec x) := by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VYq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          extDerivFun_finset_sum_at (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VYq q a p))
            (x := x) (v := Xsec x)
            (by intro q hq; exact hCY_mdiff q)
      rw [hsum]
    have hFX_deriv :
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p))
            x (Ysec x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) -
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
                x (Ysec x) := by
      rw [hFX_fun]
      rw [extDerivFun_sub_at (I := I) (x := x) (v := Ysec x)
        hXbase_mdiff hCX_sum_mdiff]
      have hsum :
          extDerivFun (I := I)
              (fun p : M =>
                ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p))
              x (Ysec x) =
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
                x (Ysec x) := by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VXq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          extDerivFun_finset_sum_at (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VXq q a p))
            (x := x) (v := Ysec x)
            (by intro q hq; exact hCX_mdiff q)
      rw [hsum]
    haveI : CompleteSpace E := FiniteDimensional.complete Real E
    haveI : IsManifold I 3 M := by
      exact IsManifold.of_le (I := I) (M := M)
        (by exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hbracket :
        extDerivFun (I := I) baseScalar x
            (VectorField.mlieBracket I Xf Yf x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
              x (Xsec x) -
            extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) := by
      simpa [Xf, Yf] using
        RicciFlower.extDerivFun_apply_mlieBracket
          (I := I) Xf Yf baseScalar x hX2 hY2 hbase2
    have hbracket_eval :
        extDerivFun (I := I) baseScalar x
            (VectorField.mlieBracket I Xf Yf x) =
          nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))) := by
      have h0 := Nabla0SSectionRealizes.eval_point_vector_smooth_slots
        (I := I) hnabla2.1
        (VectorField.mlieBracket I Xf Yf x) Vsec
      rw [hnablaAlpha, halpha] at h0
      linarith
    have hbaseComm :
        extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
            x (Xsec x) -
          extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
            x (Ysec x) =
          nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))) := by
      rw [← hbracket]
      exact hbracket_eval
    have hbaseComm_left :
        extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
            x (Xsec x) =
          (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x)))) +
            extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) := by
      linarith
    rw [← hWYx, ← hWXx]
    rw [hXY, hYX]
    rw [hcorrWY, hcorrWX]
    rw [hFY_deriv, hFX_deriv]
    rw [hbaseComm_left]
    simp_rw [hDX_corrY, hDY_corrX]
    rw [hnablaAlpha, halpha]
    have hVYq_at (q : Fin s) :
        (fun a : Fin s => VYq q a x) =
          Function.update slots q (YV q x) := by
      funext a
      by_cases ha : a = q
      · subst a
        simp [VYq, Vfield, slots]
      · simp [VYq, Vfield, slots, ha]
    have hVXq_at (q : Fin s) :
        (fun a : Fin s => VXq q a x) =
          Function.update slots q (XV q x) := by
      funext a
      by_cases ha : a = q
      · subst a
        simp [VXq, Vfield, slots]
      · simp [VXq, Vfield, slots, ha]
    have hFinConsVY (q : Fin s) :
        (Fin.cons (Xsec x) (fun a : Fin s => VYq q a x) :
            Fin (s + 1) → TangentSpace I x) =
          Function.update
            (Fin.cons (Xsec x) slots : Fin (s + 1) → TangentSpace I x)
            q.succ (YV q x) := by
      rw [hVYq_at q]
      exact finCons_update_tail_eq_update_finCons_succ
        (Xsec x) slots q (YV q x)
    have hFinConsVX (q : Fin s) :
        (Fin.cons (Ysec x) (fun a : Fin s => VXq q a x) :
            Fin (s + 1) → TangentSpace I x) =
          Function.update
            (Fin.cons (Ysec x) slots : Fin (s + 1) → TangentSpace I x)
            q.succ (XV q x) := by
      rw [hVXq_at q]
      exact finCons_update_tail_eq_update_finCons_succ
        (Ysec x) slots q (XV q x)
    have hDoubleY :
        (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VYq q b x) a
              ((cov (fun p : M => VYq q a p) x) (Xsec x)))) =
        ∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (Function.update slots q (YV q x)) a
              (if a = q then
                (cov (fun p : M => YV q p) x) (Xsec x)
              else
                XV a x)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hderiv :
          ((cov (fun p : M => VYq q a p) x) (Xsec x)) =
            (if a = q then
              (cov (fun p : M => YV q p) x) (Xsec x)
            else
              XV a x) := by
        by_cases haq : a = q
        · subst a
          simp [VYq, Vfield, YV, XV]
        · simp [VYq, Vfield, YV, XV, haq]
      rw [hVYq_at q, hderiv]
    have hDoubleX :
        (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VXq q b x) a
              ((cov (fun p : M => VXq q a p) x) (Ysec x)))) =
        ∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (Function.update slots q (XV q x)) a
              (if a = q then
                (cov (fun p : M => XV q p) x) (Ysec x)
              else
                YV a x)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hderiv :
          ((cov (fun p : M => VXq q a p) x) (Ysec x)) =
            (if a = q then
              (cov (fun p : M => XV q p) x) (Ysec x)
            else
              YV a x) := by
        by_cases haq : a = q
        · subst a
          simp [VXq, Vfield, YV, XV]
        · simp [VXq, Vfield, YV, XV, haq]
      rw [hVXq_at q, hderiv]
    have hDoubleCancel :
        - (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VYq q b x) a
              ((cov (fun p : M => VYq q a p) x) (Xsec x)))) +
          (∑ q : Fin s, ∑ a : Fin s,
            alpha
              (Function.update (fun b : Fin s => VXq q b x) a
                ((cov (fun p : M => VXq q a p) x) (Ysec x)))) =
        - (∑ q : Fin s,
          alpha
            (Function.update slots q
              ((cov (fun p : M => YV q p) x) (Xsec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun p : M => XV q p) x) (Ysec x)))) := by
      rw [hDoubleY, hDoubleX]
      exact double_update_sum_cancel_diag
        (eval := fun slots' : Fin s → TangentSpace I x => alpha slots')
        (slots := slots)
        (X := fun q : Fin s => XV q x)
        (Y := fun q : Fin s => YV q x)
        (XY := fun q : Fin s => (cov (fun p : M => YV q p) x) (Xsec x))
        (YX := fun q : Fin s => (cov (fun p : M => XV q p) x) (Ysec x))
    have hDiagCurv :
        - (∑ q : Fin s,
          alpha
            (Function.update slots q
              ((cov (fun p : M => YV q p) x) (Xsec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun p : M => XV q p) x) (Ysec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun y : M => Vsec q y) x)
                  (VectorField.mlieBracket I Xf Yf x)))) =
        -∑ q : Fin s,
          alpha
            (Function.update slots q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)) := by
      let A : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun p : M => YV q p) x) (Xsec x)))
      let B : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun p : M => XV q p) x) (Ysec x)))
      let C : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun y : M => Vsec q y) x)
            (VectorField.mlieBracket I Xf Yf x)))
      let D : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((connectionRiemannCurvatureField (I := I) cov Xf Yf
            (fun p : M => Vsec q p)) x))
      change - (∑ q : Fin s, A q) + (∑ q : Fin s, B q) +
          (∑ q : Fin s, C q) = -∑ q : Fin s, D q
      calc
        - (∑ q : Fin s, A q) + (∑ q : Fin s, B q) +
            (∑ q : Fin s, C q)
            = ∑ q : Fin s, (-A q + B q + C q) := by
              simp [Finset.sum_neg_distrib, Finset.sum_add_distrib]
        _ = ∑ q : Fin s, -D q := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              have hdiag :=
                tensor0S_update_curvature_diag
                  (I := I) alpha slots q
                  ((cov (fun p : M => YV q p) x) (Xsec x))
                  ((cov (fun p : M => XV q p) x) (Ysec x))
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))
              calc
                -A q + B q + C q =
                    -alpha
                      (Function.update slots q
                        (((cov (fun p : M => YV q p) x) (Xsec x)) -
                          ((cov (fun p : M => XV q p) x) (Ysec x)) -
                          ((cov (fun y : M => Vsec q y) x)
                            (VectorField.mlieBracket I Xf Yf x)))) := by
                  simpa [A, B, C] using hdiag
                _ = -D q := by
                  have hvec :
                      ((cov (fun p : M => YV q p) x) (Xsec x)) -
                          ((cov (fun p : M => XV q p) x) (Ysec x)) -
                          ((cov (fun y : M => Vsec q y) x)
                            (VectorField.mlieBracket I Xf Yf x)) =
                        (connectionRiemannCurvatureField (I := I) cov Xf Yf
                          (fun p : M => Vsec q p)) x := by
                    rfl
                  dsimp [D]
                  rw [hvec]
        _ = -∑ q : Fin s, D q := by
              simp [Finset.sum_neg_distrib]
    simp_rw [hFinConsVY, hFinConsVX]
    simp_rw [finCons_update_tail_eq_update_finCons_succ]
    repeat rw [Finset.sum_add_distrib]
    linarith [hDoubleCancel, hDiagCurv]

  calc
    nabla2Alpha
        (metricTraceInput (I := I) (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x)) -
      nabla2Alpha
        (metricTraceInput (I := I) (Ysec x) (Xsec x)
          (fun q : Fin s => Vsec q x))
        =
        (-∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)))
        +
        (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots)) := hExpanded
    _ =
        curvatureAction0SAtSlots (I := I) alpha
          (fun q : Fin s => Vsec q x)
          (fun q : Fin s =>
            (connectionRiemannCurvatureField (I := I) cov Xf Yf
              (fun p : M => Vsec q p)) x)
        +
        (-torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x)) := by
          rw [← hcurvActionSlots]
          simpa [slots] using congrArg
            (fun z =>
              curvatureAction0SAtSlots (I := I) alpha
                (fun q : Fin s => Vsec q x)
                (fun q : Fin s =>
                  (connectionRiemannCurvatureField (I := I) cov Xf Yf
                    (fun p : M => Vsec q p)) x) + z)
            htorsionFirstSlot
    _ =
        curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x)
        +
        (-torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x)) := by
          rw [← hcurvAction]
    _ =
        curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x) -
        torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x) := by
          ring

/-- General invariant Ricci identity for `(0,s)` tensors, with the torsion
correction retained.  This is the single remaining producer frontier for
Theorem 14.12 beyond the checked one-form case. -/
theorem tensor0S_ricciIdentity_with_torsion
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    Tensor0SRicciIdentityWithTorsionAt (I := I) Rm13 alpha nablaAlpha
      nabla2Alpha (fun X Y => cov.torsion x X Y) := by
  classical
  intro X Y slots
  obtain ⟨Xsec, hXx⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYx⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  let Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun q =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
        (slots q)).choose
  have hVx (q : Fin s) : Vsec q x = slots q :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (slots q)).choose_spec
  have hslots : (fun q : Fin s => Vsec q x) = slots := by
    funext q
    exact hVx q
  have hmain :=
    tensor0S_commutator_expansion_from_realizes
      (I := I) cov hcov Rm13 alphaSec nablaAlphaSec alpha nablaAlpha
      nabla2Alpha Xsec Ysec Vsec hRm13 halpha hnablaAlpha hnabla2
  simpa [Tensor0SRicciIdentityWithTorsionAt, hXx, hYx, hslots] using hmain

theorem tensor0S_ricciIdentity_of_torsionFree
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha)
    (htor : cov.torsion x = 0) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y slots
  have h := tensor0S_ricciIdentity_with_torsion
    (I := I) cov hcov Rm13 alphaSec nablaAlphaSec alpha nablaAlpha
    nabla2Alpha hRm13 halpha hnablaAlpha hnabla2 X Y slots
  have hzero : cov.torsion x X Y = 0 := by
    simpa using congrArg (fun T => T X Y) htor
  have ht : nablaAlpha (Fin.cons (0 : TangentSpace I x) slots) = 0 := by
    exact nablaAlpha.map_coord_zero (0 : Fin (s + 1)) rfl
  simp [hzero, torsionCorrection0SAt, ht] at h
  simpa using h

/-- General covariant tensor Ricci-identity interface at one point.  The
left-hand tensor is the realized commutator of two covariant derivatives, and
the right-hand tensor is the slotwise curvature action. -/
def RicciIdentity0SAt {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  comm = curvatureAction

theorem ricci_identity_0s {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (h : RicciIdentity0SAt (I := I) comm curvatureAction) :
    comm = curvatureAction :=
  h

end Realized
end RicciFlower
