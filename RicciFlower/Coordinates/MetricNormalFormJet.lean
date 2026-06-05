import RicciFlower.Coordinates.MetricCompatibility
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# First-jet algebra for metric-normal frames

This file contains the finite-index algebra behind the elementary quadratic
coordinate correction used for first-order metric-normal forms.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open scoped BigOperators
open Bundle
open scoped Manifold ContDiff

variable {Idx : Type*}

/-- The quadratic correction coefficient
`B^p_{ik} = 1/2 * (A_{p i k} + A_{p k i} - A_{i k p})`.

Here `A i j k` should be read as `partial_k g_ij` in an already pointwise
orthonormal frame. -/
def normalJetCoeff (A : Idx -> Idx -> Idx -> Real) (p i k : Idx) : Real :=
  (1 / 2 : Real) * (A p i k + A p k i - A i k p)

/-- If `A` is symmetric in its first two indices, the quadratic correction is
symmetric in the two lower frame indices. This is the algebra behind bracket
vanishing for the corrected coordinate frame. -/
theorem normalJetCoeff_symm
    {A : Idx -> Idx -> Idx -> Real}
    (hA : forall i j k : Idx, A i j k = A j i k)
    (p i j : Idx) :
    normalJetCoeff A p i j = normalJetCoeff A p j i := by
  dsimp [normalJetCoeff]
  rw [hA i j p]
  ring

/-- If `A` is symmetric in its first two indices, the two metric-variation
terms from the quadratic correction add up to the original first derivative
`A_ijd`. This is the algebraic cancellation in the textbook proof. -/
theorem normalJetCoeff_cancel
    {A : Idx -> Idx -> Idx -> Real}
    (hA : forall i j k : Idx, A i j k = A j i k)
    (i j d : Idx) :
    normalJetCoeff A j i d + normalJetCoeff A i j d = A i j d := by
  dsimp [normalJetCoeff]
  rw [hA j i d]
  ring

section TransformedFrame

variable [Fintype Idx]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Change a tangent local frame by a scalar coefficient matrix.  The convention
is that `coeff y p i` is the coefficient of the old frame vector `p` in the
new frame vector `i`. -/
def transformedFrame
    (coeff : M -> Idx -> Idx -> Real)
    (frame : Idx -> (y : M) -> TangentSpace I y) :
    Idx -> (y : M) -> TangentSpace I y :=
  fun i y => ∑ p : Idx, coeff y p i • frame p y

private theorem transformedFrame_eq_toLinearEquiv
    [DecidableEq Idx]
    {u : Set M} {x : M}
    {frame : Idx -> (y : M) -> TangentSpace I y}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hx : x ∈ u)
    (coeff : M -> Idx -> Idx -> Real)
    (hdet : IsUnit (Matrix.det (fun p i : Idx => coeff x p i)))
    (i : Idx) :
    transformedFrame (I := I) coeff frame i x =
      (Matrix.toLinearEquiv (hframe.toBasisAt hx)
        (fun p i : Idx => coeff x p i) hdet)
        ((hframe.toBasisAt hx) i) := by
  classical
  change transformedFrame (I := I) coeff frame i x =
    (Matrix.toLin (hframe.toBasisAt hx) (hframe.toBasisAt hx)
      (fun p i : Idx => coeff x p i)) ((hframe.toBasisAt hx) i)
  rw [Matrix.toLin_self]
  simp [transformedFrame, IsLocalFrameOn.toBasisAt_coe]

/-- If the coefficient matrix is invertible pointwise on `v`, then the
transformed frame values are pointwise linearly independent. -/
theorem transformedFrame_linearIndependent
    [DecidableEq Idx]
    {u v : Set M} {x : M}
    {frame : Idx -> (y : M) -> TangentSpace I y}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hv : v ⊆ u)
    (coeff : M -> Idx -> Idx -> Real)
    (hdet : IsUnit (Matrix.det (fun p i : Idx => coeff x p i)))
    (hx : x ∈ v) :
    LinearIndependent Real
      (fun i : Idx => transformedFrame (I := I) coeff frame i x) := by
  classical
  have hxU : x ∈ u := hv hx
  let A : Matrix Idx Idx Real := fun p i => coeff x p i
  let e : TangentSpace I x ≃ₗ[Real] TangentSpace I x :=
    Matrix.toLinearEquiv (hframe.toBasisAt hxU) A hdet
  have hEq :
      (fun i : Idx => transformedFrame (I := I) coeff frame i x) =
        fun i : Idx => e ((hframe.toBasisAt hxU) i) := by
    funext i
    exact transformedFrame_eq_toLinearEquiv (I := I) hframe hxU coeff hdet i
  rw [hEq]
  exact (hframe.toBasisAt hxU).linearIndependent.map' e.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)

/-- If the coefficient matrix is invertible pointwise on `v`, then the
transformed frame values pointwise span the tangent fiber. -/
theorem transformedFrame_generating
    [DecidableEq Idx]
    {u v : Set M} {x : M}
    {frame : Idx -> (y : M) -> TangentSpace I y}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hv : v ⊆ u)
    (coeff : M -> Idx -> Idx -> Real)
    (hdet : IsUnit (Matrix.det (fun p i : Idx => coeff x p i)))
    (hx : x ∈ v) :
    ⊤ ≤ Submodule.span Real
      (Set.range (fun i : Idx => transformedFrame (I := I) coeff frame i x)) := by
  classical
  have hxU : x ∈ u := hv hx
  let A : Matrix Idx Idx Real := fun p i => coeff x p i
  let e : TangentSpace I x ≃ₗ[Real] TangentSpace I x :=
    Matrix.toLinearEquiv (hframe.toBasisAt hxU) A hdet
  have hEq :
      (fun i : Idx => transformedFrame (I := I) coeff frame i x) =
        fun i : Idx => e ((hframe.toBasisAt hxU) i) := by
    funext i
    exact transformedFrame_eq_toLinearEquiv (I := I) hframe hxU coeff hdet i
  rw [hEq]
  change ⊤ ≤ Submodule.span Real
    (Set.range (((hframe.toBasisAt hxU).map e) : Idx -> TangentSpace I x))
  exact le_of_eq (((hframe.toBasisAt hxU).map e).span_eq).symm

/-- Smoothness of a matrix-transformed local frame, assuming smooth scalar
coefficients. -/
theorem transformedFrame_contMDiffOn
    {u v : Set M}
    {frame : Idx -> (y : M) -> TangentSpace I y}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hv : v ⊆ u)
    (coeff : M -> Idx -> Idx -> Real)
    (hcoeff :
      ∀ p i : Idx,
        CMDiff[v] (∞ : WithTop ℕ∞) (fun y : M => coeff y p i))
    (i : Idx) :
    CMDiff[v] (∞ : WithTop ℕ∞)
      (T% (transformedFrame (I := I) coeff frame i)) := by
  classical
  unfold transformedFrame
  exact ContMDiffOn.sum_section fun p _ =>
    (hcoeff p i).smul_section ((hframe.mono hv).contMDiffOn p)

/-- A matrix-transformed local frame is a local frame on any set where the
coefficient matrix is smooth and pointwise invertible. -/
theorem transformedFrame_isLocalFrameOn
    [DecidableEq Idx]
    {u v : Set M}
    {frame : Idx -> (y : M) -> TangentSpace I y}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hv : v ⊆ u)
    (coeff : M -> Idx -> Idx -> Real)
    (hcoeff :
      ∀ p i : Idx,
        CMDiff[v] (∞ : WithTop ℕ∞) (fun y : M => coeff y p i))
    (hdet : ∀ x ∈ v, IsUnit (Matrix.det (fun p i : Idx => coeff x p i))) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (transformedFrame (I := I) coeff frame) v where
  linearIndependent hx :=
    transformedFrame_linearIndependent (I := I) hframe hv coeff (hdet _ hx) hx
  generating hx :=
    transformedFrame_generating (I := I) hframe hv coeff (hdet _ hx) hx
  contMDiffOn i :=
    transformedFrame_contMDiffOn (I := I) hframe hv coeff hcoeff i

private theorem transformedFrame_det_contMDiffOn
    [DecidableEq Idx]
    {u : Set M}
    (coeff : M -> Idx -> Idx -> Real)
    (hcoeff :
      ∀ p i : Idx,
        CMDiff[u] (∞ : WithTop ℕ∞) (fun y : M => coeff y p i)) :
    CMDiff[u] (∞ : WithTop ℕ∞)
      (fun y : M => Matrix.det (fun p i : Idx => coeff y p i)) := by
  classical
  have hexp :
      (fun y : M => Matrix.det (fun p i : Idx => coeff y p i)) =
        fun y : M =>
          ∑ σ : Equiv.Perm Idx,
            (Equiv.Perm.sign σ : Real) * ∏ i : Idx, coeff y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := (Equiv.Perm.sign σ : Real))) ?_
  refine contMDiffOn_finset_prod (fun i _ => ?_)
  exact hcoeff (σ i) i

/-- Shrink an existing local frame domain to the open set where a smooth
coefficient matrix is invertible, and use that matrix to transform the frame. -/
theorem exists_transformedFrame_isLocalFrameOn
    [DecidableEq Idx]
    {u : Set M} {x : M}
    {frame : Idx -> (y : M) -> TangentSpace I y}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (hx : x ∈ u)
    (coeff : M -> Idx -> Idx -> Real)
    (hcoeff :
      ∀ p i : Idx,
        CMDiff[u] (∞ : WithTop ℕ∞) (fun y : M => coeff y p i))
    (hdetx : IsUnit (Matrix.det (fun p i : Idx => coeff x p i))) :
    ∃ v : Set M,
      IsOpen v ∧ x ∈ v ∧ v ⊆ u ∧
        IsLocalFrameOn I E (∞ : WithTop ℕ∞)
          (transformedFrame (I := I) coeff frame) v := by
  classical
  let detFun : M -> Real := fun y => Matrix.det (fun p i : Idx => coeff y p i)
  let v : Set M := u ∩ detFun ⁻¹' {r : Real | r ≠ 0}
  have hdetCont : ContinuousOn detFun u := by
    simpa [detFun] using
      (transformedFrame_det_contMDiffOn (I := I) (Idx := Idx) coeff hcoeff).continuousOn
  have hopen : IsOpen v := by
    have hne : IsOpen ({r : Real | r ≠ 0}) := isOpen_ne
    simpa [v, detFun] using hdetCont.isOpen_inter_preimage hu hne
  have hxv : x ∈ v := by
    exact ⟨hx, by simpa [detFun, isUnit_iff_ne_zero] using hdetx⟩
  have hvu : v ⊆ u := fun y hy => hy.1
  have hcoeff_v :
      ∀ p i : Idx,
        CMDiff[v] (∞ : WithTop ℕ∞) (fun y : M => coeff y p i) :=
    fun p i => (hcoeff p i).mono hvu
  have hdet_v :
      ∀ y ∈ v, IsUnit (Matrix.det (fun p i : Idx => coeff y p i)) := by
    intro y hy
    exact isUnit_iff_ne_zero.mpr hy.2
  exact ⟨v, hopen, hxv, hvu,
    transformedFrame_isLocalFrameOn (I := I) hframe hvu coeff hcoeff_v hdet_v⟩

/-- Version of `exists_transformedFrame_isLocalFrameOn` for coefficient matrices
whose value at the base point is the identity. -/
theorem exists_transformedFrame_isLocalFrameOn_of_eq_id
    [DecidableEq Idx]
    {u : Set M} {x : M}
    {frame : Idx -> (y : M) -> TangentSpace I y}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (hx : x ∈ u)
    (coeff : M -> Idx -> Idx -> Real)
    (hcoeff :
      ∀ p i : Idx,
        CMDiff[u] (∞ : WithTop ℕ∞) (fun y : M => coeff y p i))
    (hcoeffx : ∀ p i : Idx, coeff x p i = if p = i then 1 else 0) :
    ∃ v : Set M,
      IsOpen v ∧ x ∈ v ∧ v ⊆ u ∧
        IsLocalFrameOn I E (∞ : WithTop ℕ∞)
          (transformedFrame (I := I) coeff frame) v := by
  classical
  have hmat :
      (fun p i : Idx => coeff x p i : Matrix Idx Idx Real) =
        (1 : Matrix Idx Idx Real) := by
    ext p i
    rw [Matrix.one_apply]
    exact hcoeffx p i
  have hdetx : IsUnit (Matrix.det (fun p i : Idx => coeff x p i)) := by
    rw [hmat]
    simp [Matrix.det_one]
  exact exists_transformedFrame_isLocalFrameOn
    (I := I) hframe hu hx coeff hcoeff hdetx

end TransformedFrame

end Coordinates
end RicciFlower
