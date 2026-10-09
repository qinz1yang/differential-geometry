import DifferentialGeometry.Geometry.Thurston.ElementaryModels
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace GC.Geometry

inductive ThurstonModel
  | spherical | euclidean | hyperbolic | sphericalProduct
  | hyperbolicProduct | universalSL2 | nil | sol
  deriving DecidableEq

instance : Fintype ThurstonModel :=
  ⟨{.spherical, .euclidean, .hyperbolic, .sphericalProduct, .hyperbolicProduct,
    .universalSL2, .nil, .sol}, by intro k; cases k <;> simp⟩

theorem ThurstonModel.card : Fintype.card ThurstonModel = 8 := by decide

inductive CoordinateModel
  | hyperbolic | hyperbolicProduct | universalSL2 | nil | sol
  deriving DecidableEq

abbrev ModelCoordinates := EuclideanSpace ℝ (Fin 3)

def coordinateCoframe (k : CoordinateModel) (p v : ModelCoordinates) : Fin 3 → ℝ :=
  match k with
  | .hyperbolic => ![Real.exp (-p 2) * v 0, Real.exp (-p 2) * v 1, v 2]
  | .hyperbolicProduct => ![Real.exp (-p 1) * v 0, v 1, v 2]
  | .universalSL2 => ![Real.exp (-p 1) * v 0, v 1, v 2 + Real.exp (-p 1) * v 0]
  | .nil => ![v 0, v 1, v 2 - p 0 * v 1]
  | .sol => ![Real.exp (p 2) * v 0, Real.exp (-p 2) * v 1, v 2]

theorem coordinateCoframe_add (k : CoordinateModel) (p v w : ModelCoordinates) :
    coordinateCoframe k p (v + w) = coordinateCoframe k p v + coordinateCoframe k p w := by
  cases k <;> ext i <;> fin_cases i <;> simp [coordinateCoframe, mul_add] <;> ring

theorem coordinateCoframe_smul (k : CoordinateModel) (p v : ModelCoordinates) (a : ℝ) :
    coordinateCoframe k p (a • v) = a • coordinateCoframe k p v := by
  cases k <;> ext i <;> fin_cases i <;> simp [coordinateCoframe, mul_sub, mul_add] <;> ring

def coordinateInner (k : CoordinateModel) (p v w : ModelCoordinates) : ℝ :=
  ∑ i : Fin 3, coordinateCoframe k p v i * coordinateCoframe k p w i

theorem coordinateInner_symm (k : CoordinateModel) (p v w : ModelCoordinates) :
    coordinateInner k p v w = coordinateInner k p w v := by
  unfold coordinateInner
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem coordinateCoframe_injective (k : CoordinateModel) (p : ModelCoordinates) :
    Function.Injective (coordinateCoframe k p) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases k <;> simp only [coordinateCoframe, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  all_goals
    have he : Real.exp (-p 1) ≠ 0 := Real.exp_ne_zero _
    have hf : Real.exp (-p 2) ≠ 0 := Real.exp_ne_zero _
    have hg : Real.exp (p 2) ≠ 0 := Real.exp_ne_zero _
    try simp only [mul_right_inj' he, mul_right_inj' hf, mul_right_inj' hg] at h0 h1 h2
    ext i
    fin_cases i <;> simp_all

theorem coordinateCoframe_zero (k : CoordinateModel) (p : ModelCoordinates) :
    coordinateCoframe k p 0 = 0 := by
  cases k <;> ext i <;> fin_cases i <;> simp [coordinateCoframe]

theorem coordinateInner_pos (k : CoordinateModel) (p v : ModelCoordinates)
    (hv : v ≠ 0) : 0 < coordinateInner k p v v := by
  have hco : coordinateCoframe k p v ≠ 0 := by
    intro h
    apply hv
    apply coordinateCoframe_injective k p
    rw [h, coordinateCoframe_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hco
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg _
  · exact ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

end GC.Geometry
