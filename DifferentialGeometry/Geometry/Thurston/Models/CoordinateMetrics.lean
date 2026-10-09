import DifferentialGeometry.Geometry.Thurston.Atlas
import DifferentialGeometry.Geometry.Metric.Construction.Existence
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff

namespace GC.Geometry

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

def coordinateCoframeForm (k : CoordinateModel) (p : ModelCoordinates) :
    Fin 3 → ModelCoordinates →L[ℝ] ℝ :=
  match k with
  | .hyperbolic => ![Real.exp (-p 2) • coord 0, Real.exp (-p 2) • coord 1, coord 2]
  | .hyperbolicProduct => ![Real.exp (-p 1) • coord 0, coord 1, coord 2]
  | .universalSL2 => ![Real.exp (-p 1) • coord 0, coord 1,
      coord 2 + Real.exp (-p 1) • coord 0]
  | .nil => ![coord 0, coord 1, coord 2 - p 0 • coord 1]
  | .sol => ![Real.exp (p 2) • coord 0, Real.exp (-p 2) • coord 1, coord 2]

@[simp] theorem coordinateCoframeForm_apply (k : CoordinateModel)
    (p v : ModelCoordinates) (i : Fin 3) :
    coordinateCoframeForm k p i v = coordinateCoframe k p v i := by
  cases k <;> fin_cases i <;> simp [coordinateCoframeForm, coordinateCoframe, coord]

theorem coordinateCoframeForm_contDiff (k : CoordinateModel) (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : ModelCoordinates => coordinateCoframeForm k p i) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun p : ModelCoordinates => p j) :=
    (coord j).contDiff
  cases k <;> fin_cases i <;> dsimp [coordinateCoframeForm] <;> fun_prop

def coordinateBilinear (k : CoordinateModel) (p : ModelCoordinates) :
    ModelCoordinates →L[ℝ] ModelCoordinates →L[ℝ] ℝ :=
  ∑ i : Fin 3, (coordinateCoframeForm k p i).smulRight (coordinateCoframeForm k p i)

@[simp] theorem coordinateBilinear_apply (k : CoordinateModel)
    (p v w : ModelCoordinates) :
    coordinateBilinear k p v w = coordinateInner k p v w := by
  simp [coordinateBilinear, coordinateInner,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem coordinateBilinear_contDiff (k : CoordinateModel) :
    ContDiff ℝ ∞ (coordinateBilinear k) := by
  apply ContDiff.sum
  intro i _
  exact (((ContinuousLinearMap.smulRightL ℝ ModelCoordinates
    (ModelCoordinates →L[ℝ] ℝ)).contDiff.comp
      (coordinateCoframeForm_contDiff k i)).clm_apply
        (coordinateCoframeForm_contDiff k i))

set_option backward.isDefEq.respectTransparency false in

def coordinateModelMetric (k : CoordinateModel) :
    DifferentialGeometry.SmoothRiemannianMetric (𝓡 3) ModelCoordinates where
  inner := coordinateBilinear k
  symm p v w := by
    change coordinateBilinear k p v w = coordinateBilinear k p w v
    simp only [coordinateBilinear_apply]
    exact coordinateInner_symm k p v w
  pos p v hv := by
    change 0 < coordinateBilinear k p v v
    rw [coordinateBilinear_apply]
    exact coordinateInner_pos k p v hv
  isVonNBounded p := DifferentialGeometry.Geometry.posDef_isVonNBounded
    (coordinateBilinear k p) (fun v hv => by simpa using coordinateInner_pos k p v hv)
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! (coordinateBilinear_contDiff k).contMDiff.contMDiffAt using 1
    ext p v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

@[simp] theorem coordinateModelMetric_inner (k : CoordinateModel)
    (p v w : ModelCoordinates) :
    (coordinateModelMetric k).inner p v w = coordinateInner k p v w :=
  coordinateBilinear_apply k p v w

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in

theorem coordinateModelAtlas_iff_actualModelAtlas
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (k : CoordinateModel) :
    CoordinateModelAtlas g k ↔ ModelAtlas g (coordinateModelMetric k) :=
  coordinateModelAtlas_iff_modelAtlas g k (coordinateModelMetric k)
    (coordinateModelMetric_inner k)

theorem coordinateModelMetric_atlas (k : CoordinateModel) :
    CoordinateModelAtlas (coordinateModelMetric k) k :=
  (coordinateModelAtlas_iff_actualModelAtlas _ _).mpr (ModelAtlas.refl _)

end GC.Geometry
