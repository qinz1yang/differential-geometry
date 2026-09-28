import Mathlib.LinearAlgebra.Orientation
import Mathlib.Basic.Real.Basic



namespace DifferentialGeometry.VectorBundle

theorem map_orientation_trans_between {n : ℕ} {A B C : Type*}
    [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C] (f : A ≃ₗ[ℝ] B) (g : B ≃ₗ[ℝ] C)
    (o : Orientation ℝ A (Fin n)) :
    Orientation.map (Fin n) g (Orientation.map (Fin n) f o) =
      Orientation.map (Fin n) (f.trans g) o := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

end DifferentialGeometry.VectorBundle
