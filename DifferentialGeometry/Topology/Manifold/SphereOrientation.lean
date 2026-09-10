import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

open Manifold Metric Module
open scoped Manifold ContDiff

namespace DifferentialGeometry

def sphereOutwardDeterminant (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) : ℝ :=
  Matrix.det (fun i j : Fin (n + 1) ↦
    (Fin.cases (motive := fun _ ↦ EuclideanSpace ℝ (Fin (n + 1)))
      (x : EuclideanSpace ℝ (Fin (n + 1)))
      (fun k ↦ NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin (n + 1)))
        (mfderiv (𝓡 n) (𝓡 (n + 1))
          (fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
            (y : EuclideanSpace ℝ (Fin (n + 1)))) x (b k))) j) i)

theorem exists_unique_sphere_orientation (n : ℕ) (hn : 1 ≤ n) :
    ∃! o : ManifoldOrientation (𝓡 n)
        (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n,
      ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
        b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b := by
  sorry

def sphereOrientation (n : ℕ) (hn : 1 ≤ n) :
    ManifoldOrientation (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n :=
  (exists_unique_sphere_orientation n hn).exists.choose

theorem sphereOrientation_characterization (n : ℕ) (hn : 1 ≤ n)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    b.orientation = (sphereOrientation n hn).orientation x ↔
      0 < sphereOutwardDeterminant n x b :=
  (exists_unique_sphere_orientation n hn).exists.choose_spec x b

theorem sphereOrientation_unique (n : ℕ) (hn : 1 ≤ n)
    (o : ManifoldOrientation (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n)
    (ho : ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
      b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b) :
    o = sphereOrientation n hn :=
  (exists_unique_sphere_orientation n hn).unique ho
    (sphereOrientation_characterization n hn)

end DifferentialGeometry
