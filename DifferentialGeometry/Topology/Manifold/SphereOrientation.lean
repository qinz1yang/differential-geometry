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

theorem sphereOrientation_eq_of_characterization (n : ℕ)
    (o o' : ManifoldOrientation (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n)
    (ho : ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
      b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b)
    (ho' : ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
      b.orientation = o'.orientation x ↔ 0 < sphereOutwardDeterminant n x b) :
    o = o' := by
  apply ManifoldOrientation.ext
  intro x
  have : Module.Finite ℝ (TangentSpace (𝓡 n) x) := by
    change Module.Finite ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  let b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
    Module.finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) x) hdim
  have key : (b.orientation = o.orientation x) ↔ (b.orientation = o'.orientation x) :=
    (ho x b).trans (ho' x b).symm
  rcases b.orientation_eq_or_eq_neg (o.orientation x) with h | h
  · exact h.trans (key.mp h.symm)
  · have hne : o.orientation x ≠ b.orientation := by
      intro hb
      exact Module.Ray.ne_neg_self b.orientation (hb.symm.trans h)
    have hne' : o'.orientation x ≠ b.orientation := fun hb => hne (key.mpr hb.symm).symm
    exact h.trans ((Basis.orientation_ne_iff_eq_neg b (o'.orientation x)).mp hne').symm

theorem exists_sphere_orientation (n : ℕ) (hn : 1 ≤ n) :
    ∃ o : ManifoldOrientation (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n,
      ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
        b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b := by
  sorry

theorem exists_unique_sphere_orientation (n : ℕ) (hn : 1 ≤ n) :
    ∃! o : ManifoldOrientation (𝓡 n)
        (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n,
      ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
        b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b :=
  have h := exists_sphere_orientation n hn
  ⟨h.choose, h.choose_spec, fun o' ho' => sphereOrientation_eq_of_characterization n o' h.choose ho' h.choose_spec⟩

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
