import DifferentialGeometry.Topology.Simplex.Coordinates
import DifferentialGeometry.Topology.Simplex.BoundaryGluing
import Mathlib.Topology.Homotopy.Basic

noncomputable section

open ContinuousMap

open Convexity.StdSimplex

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

def triangleSphereFaces (g : C(coordinateSet ℝ (Fin 3), X)) (x : X) :
    Fin 4 → C(coordinateSet ℝ (Fin 3), X) :=
  Fin.cons g (fun _ => ContinuousMap.const _ x)

theorem triangleSphereFaces_compatible (g : C(coordinateSet ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x)
    (i : Fin 4) (j : Fin 3) (p : coordinateSet ℝ (Fin 2)) :
    triangleSphereFaces g x i (coordinateMap j.succAbove p) =
      triangleSphereFaces g x (i.succAbove j)
        (coordinateMap (j.predAbove i).succAbove p) := by
  have h (k : Fin 3) : g (coordinateMap k.succAbove p) = x :=
    hg _ ⟨k, map_succAbove_apply_pivot k p⟩
  fin_cases i <;> fin_cases j <;> first
    | exact h _
    | exact (h _).symm
    | rfl

def triangleSphereMap (g : C(coordinateSet ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X) :=
  boundarySphereDesc (triangleSphereFaces g x) (triangleSphereFaces_compatible g x hg)

end DifferentialGeometry.Simplex
