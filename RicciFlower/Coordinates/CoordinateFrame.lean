import RicciFlower.Coordinates.Basic
import RicciFlower.Tensor.RSTensor.Components
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

namespace RicciFlower
namespace Coordinates

open Set Bundle Tensor0SBundle Filter
open scoped Topology Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The fixed finite index set used by the chart-induced coordinate frame. -/
abbrev CoordinateIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] :=
  Fin (Module.finrank 𝕜 E)

/-- The tangent-bundle trivialization used for coordinates at `x₀`. -/
abbrev coordinateTrivializationAt
    (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  trivializationAt E (TangentSpace I : M -> Type _) x₀

/-- The chart-induced coordinate tangent frame at `x₀`.

Outside the base set of the tangent-bundle trivialization this has mathlib's
usual local-frame junk value. -/
def coordinateFrameAt (x₀ : M) :
    CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x :=
  (coordinateTrivializationAt (I := I) x₀).localFrame (Module.finBasis 𝕜 E)

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
    I (∞ : WithTop ℕ∞) (Module.finBasis 𝕜 E)

/-- The coordinate frame as a `C¹` local frame, for Christoffel-component APIs. -/
def coordinateFrameAt_isLocalFrame_one (x₀ : M) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (1 : WithTop ℕ∞) (Module.finBasis 𝕜 E)

/-- Coordinate-frame vector fields are differentiable at the base point. -/
theorem coordinateFrameAt_mdifferentiableAt (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    MDiffAt (T% (coordinateFrameAt (I := I) x₀ i)) x₀ := by
  exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
    (coordinateFrameSet_open (I := I) x₀)
    (coordinateFrameAt_mem (I := I) x₀) i).mdifferentiableAt (by simp)

/-- The pointwise basis of `TangentSpace I x` induced by the coordinate frame. -/
def coordinateFrameAt_basis (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x) :=
  (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx

@[simp]
theorem coordinateFrameAt_basis_apply (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt_basis (I := I) x₀ hx i =
      coordinateFrameAt (I := I) x₀ i x := by
  simp [coordinateFrameAt_basis]

/-- The coordinate-frame basis at the base point. -/
def coordinateFrameAt_toBasis (x₀ : M) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x₀) :=
  coordinateFrameAt_basis (I := I) x₀ (coordinateFrameAt_mem (I := I) x₀)

@[simp]
theorem coordinateFrameAt_toBasis_apply (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt_toBasis (I := I) x₀ i =
      coordinateFrameAt (I := I) x₀ i x₀ := by
  simp [coordinateFrameAt_toBasis]

/-- At the base point, `IsLocalFrameOn.coeff` agrees with the coordinate-frame
basis coordinate functional. -/
theorem coordinateFrameAt_coeff_eq_toBasis_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j x₀ Z =
      (coordinateFrameAt_toBasis (I := I) x₀).coord j Z := by
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt
          (coordinateFrameAt_mem (I := I) x₀) =
        coordinateFrameAt_toBasis (I := I) x₀ := by
    ext k
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [coordinateFrameAt_toBasis_apply]
  unfold IsLocalFrameOn.coeff
  rw [dif_pos (coordinateFrameAt_mem (I := I) x₀)]
  rw [hbasis]

/-- On the coordinate chart domain, the coordinate frame is the derivative of
`(extChartAt I x₀).symm` applied to the fixed model-space basis vector. -/
theorem coordinateFrameAt_apply_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((Module.finBasis 𝕜 E) i) := by
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hx_triv :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  change (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame
      (Module.finBasis 𝕜 E) i x =
    (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
      ((Module.finBasis 𝕜 E) i)
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := trivializationAt E (TangentSpace I : M -> Type _) x₀)
    (b := Module.finBasis 𝕜 E) (i := i) hx_triv]
  simpa [Bundle.Trivialization.basisAt, Trivialization.symmL_apply, extChartAt] using
    congrArg (fun L : E →L[𝕜] TangentSpace I x => L ((Module.finBasis 𝕜 E) i))
      (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src)

/-- At the base point, the chart-induced coordinate basis is the model-space basis. -/
theorem coordinateFrameAt_toBasis_eq_finBasis (x₀ : M) :
    coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis 𝕜 E := by
  ext i
  rw [coordinateFrameAt_toBasis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) (coordinateFrameAt_mem (I := I) x₀) i]
  rw [mfderivWithin_range_extChartAt_symm]
  rfl

private theorem coordinateFrame_pullback_eq_const (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => (Module.finBasis 𝕜 E i : E) := by
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
    ((Module.finBasis 𝕜 E) i)

private theorem coordinateFrame_pullback_eq_const_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x)]
        fun _ : E => (Module.finBasis 𝕜 E i : E) := by
  haveI : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hx_src : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  filter_upwards [extChartAt_target_mem_nhdsWithin' (I := I) hx_src] with y hy
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
    ((Module.finBasis 𝕜 E) i)

private theorem lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin 𝕜 (fun _ : E => v) (fun _ : E => w) s x = 0 := by
  simp [VectorField.lieBracketWithin]

/-- Coordinate-frame bracket vanishing at the base point.

This is the chart-coordinate statement `[∂ᵢ, ∂ⱼ](x₀) = 0`. It is intentionally
separate from `IsNormalFrameForConnectionAt`: no Christoffel-vanishing claim is
made here. -/
theorem coordinateFrameAt_bracket_zero (x₀ : M) (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x₀ = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  have hleft :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ i) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis 𝕜 E i : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ i
  have hright :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ j) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis 𝕜 E j : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ j
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright (by simp)]
  rw [lieBracketWithin_const_const]
  exact ContinuousLinearMap.map_zero _

/-- Fixed coordinate-frame bracket vanishing on the whole coordinate-frame
domain.

This is the chart-coordinate statement `[∂ᵢ, ∂ⱼ](x) = 0` for every point `x`
where the chart-induced frame centered at `x₀` is defined. -/
theorem coordinateFrameAt_bracket_zero_of_mem [IsRCLikeNormedField 𝕜] {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x = 0 := by
  haveI : IsManifold I (minSmoothness 𝕜 2) M :=
    by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact IsManifold.of_le (I := I) (M := M) (n := ∞) (by
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let V : (x : M) → TangentSpace I x := coordinateFrameAt (I := I) x₀ i
  let W : (x : M) → TangentSpace I x := coordinateFrameAt (I := I) x₀ j
  let z : E := extChartAt I x₀ x
  let f : E → M := (extChartAt I x₀).symm
  have hx_src : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  have hz_target : z ∈ (extChartAt I x₀).target := by
    exact (extChartAt I x₀).map_source hx_src
  have hz_range : z ∈ Set.range I :=
    extChartAt_target_subset_range x₀ hz_target
  have hfz : f z = x := by
    exact (extChartAt I x₀).left_inv hx_src
  have hVdiff : MDiffAt[Set.univ] (T% V) (f z) := by
    rw [hfz]
    exact (((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) hx i).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hWdiff : MDiffAt[Set.univ] (T% W) (f z) := by
    rw [hfz]
    exact (((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) hx j).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hf :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞) f (Set.range I) z :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) (x := x₀) hz_target
  have hpb :=
    VectorField.mpullbackWithin_mlieBracketWithin
      (I := 𝓘(𝕜, E)) (I' := I) (n := (∞ : WithTop ℕ∞))
      (f := f) (V := V) (W := W) (x₀ := z)
      (s := Set.range I) (t := Set.univ)
      hVdiff hWdiff I.uniqueMDiffOn hf hz_range
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
      (by simp only [Set.preimage_univ]; exact Filter.univ_mem)
      (by
        simpa [z] using I.range_subset_closure_interior hz_range)
  have hleft :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I f V (Set.range I)
        =ᶠ[𝓝[Set.range I] z]
          fun _ : E => (Module.finBasis 𝕜 E i : E) := by
    simpa [f, V, z] using coordinateFrame_pullback_eq_const_of_mem (I := I) hx i
  have hright :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I f W (Set.range I)
        =ᶠ[𝓝[Set.range I] z]
          fun _ : E => (Module.finBasis 𝕜 E j : E) := by
    simpa [f, W, z] using coordinateFrame_pullback_eq_const_of_mem (I := I) hx j
  have hrhs :
      VectorField.mlieBracketWithin 𝓘(𝕜, E)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I f V (Set.range I))
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I f W (Set.range I))
          (Set.range I) z = 0 := by
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright hz_range]
    exact lieBracketWithin_const_const
  rw [hrhs] at hpb
  rw [VectorField.mlieBracketWithin_univ] at hpb
  simp only [VectorField.mpullbackWithin_apply] at hpb
  have hInv :
      (mfderiv[Set.range I] f z).IsInvertible := by
    simpa [f, z] using isInvertible_mfderivWithin_extChartAt_symm (I := I) hz_target
  have hzero := congrArg (fun v => (mfderiv[Set.range I] f z) v) hpb
  change VectorField.mlieBracket I V W x = 0
  rw [← hfz]
  simpa [ContinuousLinearMap.IsInvertible.self_apply_inverse hInv] using hzero

/-- A packaged chart-induced coordinate frame at one point. -/
structure CoordinateFrameAt (x₀ : M) where
  u : Set M
  frame : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u
  isOpen_u : IsOpen u
  mem_base : x₀ ∈ u
  bracket_zero : ∀ i j : CoordinateIdx (𝕜 := 𝕜) E,
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
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  component0S (I := I) (coordinateFrameAt_toBasis (I := I) x₀) A slots

@[simp]
theorem coordComponent0SAt_apply {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I) A slots =
      A (fun a => coordinateFrameAt_toBasis (I := I) x₀ (slots a)) :=
  rfl

/-- Mixed tensor components in the coordinate frame at the base point. -/
def coordComponentRSAt {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  componentRS (I := I) (coordinateFrameAt_toBasis (I := I) x₀) T upper lower

@[simp]
theorem coordComponentRSAt_apply {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I) T upper lower =
      componentRS (I := I) (coordinateFrameAt_toBasis (I := I) x₀) T upper lower :=
  rfl

end Coordinates
end RicciFlower
