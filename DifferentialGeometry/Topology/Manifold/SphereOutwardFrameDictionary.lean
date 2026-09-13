import DifferentialGeometry.Topology.Manifold.SphereOrientation

set_option autoImplicit false
noncomputable section
open Manifold Metric Module
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry

theorem sphereOutwardDeterminant_eq_basisDet_frame (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    sphereOutwardDeterminant n x b =
      ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases x (fun k => mfderiv (𝓡 n) (𝓡 (n + 1))
          (fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
            (y : EuclideanSpace ℝ (Fin (n + 1)))) x (b k)) j) :=
  rfl

theorem sphereOutwardFrame_pos_iff_sphereOrientation (n : ℕ) (hn : 1 ≤ n)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    0 < ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases x (fun k => mfderiv (𝓡 n) (𝓡 (n + 1))
          (fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
            (y : EuclideanSpace ℝ (Fin (n + 1)))) x (b k)) j) ↔
      b.orientation = (sphereOrientation n hn).orientation x := by
  rw [← sphereOutwardDeterminant_eq_basisDet_frame n x b]
  exact (sphereOrientation_characterization n hn x b).symm

end DifferentialGeometry
