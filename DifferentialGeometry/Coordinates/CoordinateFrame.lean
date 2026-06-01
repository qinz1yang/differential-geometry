import DifferentialGeometry.Coordinates.Basic
import DifferentialGeometry.Tensor.RSTensor.Components
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate frames at a point

This file packages the tangent local frame induced by the chart/trivialization
at a point.  This is weaker than normal coordinates: it gives a coordinate
local frame and bracket vanishing, but it does not assert Christoffel symbols
vanish.
-/

noncomputable section

namespace DifferentialGeometry
namespace Coordinates

open Set Bundle Tensor0SBundle Filter
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The fixed finite index set used by the chart-induced coordinate frame. -/
abbrev CoordinateIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :=
  Fin (Module.finrank Real E)

/-- The tangent-bundle trivialization used for coordinates at `x₀`. -/
abbrev coordinateTrivializationAt
    (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  trivializationAt E (TangentSpace I : M -> Type _) x₀

/-- The chart-induced coordinate tangent frame at `x₀`.

Outside the base set of the tangent-bundle trivialization this has mathlib's
usual local-frame junk value. -/
def coordinateFrameAt (x₀ : M) :
    CoordinateIdx E -> (x : M) -> TangentSpace I x :=
  (coordinateTrivializationAt (I := I) x₀).localFrame (Module.finBasis Real E)

/-- The open set on which `coordinateFrameAt x₀` is a local frame. -/
def coordinateFrameSet (x₀ : M) : Set M :=
  (coordinateTrivializationAt (I := I) x₀).baseSet

theorem coordinateFrameSet_open (x₀ : M) :
    IsOpen (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).open_baseSet

theorem coordinateFrameAt_mem (x₀ : M) :
    x₀ ∈ coordinateFrameSet (I := I) x₀ :=
  mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀

theorem coordinateFrameAt_isLocalFrame (x₀ : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (∞ : WithTop ℕ∞) (Module.finBasis Real E)

/-- The pointwise basis of `TangentSpace I x` induced by the coordinate frame. -/
def coordinateFrameAt_basis (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    Module.Basis (CoordinateIdx E) Real (TangentSpace I x) :=
  (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx

@[simp]
theorem coordinateFrameAt_basis_apply (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx E) :
    coordinateFrameAt_basis (I := I) x₀ hx i =
      coordinateFrameAt (I := I) x₀ i x := by
  simp [coordinateFrameAt_basis]

/-- The coordinate-frame basis at the base point. -/
def coordinateFrameAt_toBasis (x₀ : M) :
    Module.Basis (CoordinateIdx E) Real (TangentSpace I x₀) :=
  coordinateFrameAt_basis (I := I) x₀ (coordinateFrameAt_mem (I := I) x₀)

@[simp]
theorem coordinateFrameAt_toBasis_apply (x₀ : M) (i : CoordinateIdx E) :
    coordinateFrameAt_toBasis (I := I) x₀ i =
      coordinateFrameAt (I := I) x₀ i x₀ := by
  simp [coordinateFrameAt_toBasis]

/-- On the coordinate chart domain, the coordinate frame is the derivative of
`(extChartAt I x₀).symm` applied to the fixed model-space basis vector. -/
theorem coordinateFrameAt_apply_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx E) :
    coordinateFrameAt (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((Module.finBasis Real E) i) := by
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hx_triv :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  change (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame
      (Module.finBasis Real E) i x =
    (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
      ((Module.finBasis Real E) i)
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := trivializationAt E (TangentSpace I : M -> Type _) x₀)
    (b := Module.finBasis Real E) (i := i) hx_triv]
  simpa [Bundle.Trivialization.basisAt, Trivialization.symmL_apply, extChartAt] using
    congrArg (fun L : E →L[Real] TangentSpace I x => L ((Module.finBasis Real E) i))
      (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_src)

private theorem coordinateFrame_pullback_eq_const (x₀ : M) (i : CoordinateIdx E) :
    VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => (Module.finBasis Real E i : E) := by
  haveI : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((Module.finBasis Real E) i)

private theorem lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin Real (fun _ : E => v) (fun _ : E => w) s x = 0 := by
  simp [VectorField.lieBracketWithin]

/-- Coordinate-frame bracket vanishing at the base point.

This is the chart-coordinate statement `[∂ᵢ, ∂ⱼ](x₀) = 0`. It is intentionally
separate from `IsNormalFrameForConnectionAt`: no Christoffel-vanishing claim is
made here. -/
theorem coordinateFrameAt_bracket_zero (x₀ : M) (i j : CoordinateIdx E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x₀ = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  have hleft :
      VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ i) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis Real E i : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ i
  have hright :
      VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ j) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis Real E j : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ j
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright (by simp)]
  rw [lieBracketWithin_const_const]
  exact ContinuousLinearMap.map_zero _

/-- A packaged chart-induced coordinate frame at one point. -/
structure CoordinateFrameAt (x₀ : M) where
  u : Set M
  frame : CoordinateIdx E -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u
  isOpen_u : IsOpen u
  mem_base : x₀ ∈ u
  bracket_zero : ∀ i j : CoordinateIdx E,
    VectorField.mlieBracket I (frame i) (frame j) x₀ = 0

/-- The canonical coordinate-frame package at `x₀`. -/
def coordinateFramePackageAt (x₀ : M) : CoordinateFrameAt (I := I) x₀ where
  u := coordinateFrameSet (I := I) x₀
  frame := coordinateFrameAt (I := I) x₀
  hframe := coordinateFrameAt_isLocalFrame (I := I) x₀
  isOpen_u := coordinateFrameSet_open (I := I) x₀
  mem_base := coordinateFrameAt_mem (I := I) x₀
  bracket_zero := coordinateFrameAt_bracket_zero (I := I) x₀

/-- Covariant tensor components in the coordinate frame at the base point. -/
def coordComponent0SAt {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx E) : Real :=
  component0S (I := I) (coordinateFrameAt_toBasis (I := I) x₀) A slots

@[simp]
theorem coordComponent0SAt_apply {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx E) :
    coordComponent0SAt (I := I) A slots =
      A (fun a => coordinateFrameAt_toBasis (I := I) x₀ (slots a)) :=
  rfl

/-- Mixed tensor components in the coordinate frame at the base point. -/
def coordComponentRSAt {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx E) (lower : Fin s -> CoordinateIdx E) : Real :=
  componentRS (I := I) (coordinateFrameAt_toBasis (I := I) x₀) T upper lower

@[simp]
theorem coordComponentRSAt_apply {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx E) (lower : Fin s -> CoordinateIdx E) :
    coordComponentRSAt (I := I) T upper lower =
      componentRS (I := I) (coordinateFrameAt_toBasis (I := I) x₀) T upper lower :=
  rfl

end Coordinates
end DifferentialGeometry
