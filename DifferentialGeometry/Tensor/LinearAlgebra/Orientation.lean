import Mathlib.LinearAlgebra.Orientation

namespace DifferentialGeometry

theorem orientation_map_trans
    {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {E F G : Type*} [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G]
    {ι : Type*} (A : E ≃ₗ[R] F) (B : F ≃ₗ[R] G) (o : Orientation R E ι) :
    Orientation.map ι (A.trans B) o = Orientation.map ι B (Orientation.map ι A o) := by
  induction o using Module.Ray.ind with
  | h f hf => rfl

end DifferentialGeometry

namespace LinearEquiv

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] [Module.Free R E]

theorem det_neg_eq_neg_one_of_odd (hodd : Odd (Module.finrank R E)) :
    LinearMap.det ((LinearEquiv.neg R : E ≃ₗ[R] E).toLinearMap) = -1 := by
  change LinearMap.det (-LinearMap.id : E →ₗ[R] E) = -1
  rw [← neg_one_smul R (LinearMap.id : E →ₗ[R] E), LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact hodd.neg_one_pow

end LinearEquiv

namespace Orientation

variable {R E ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [Fintype ι]

theorem map_negLinearEquiv_of_odd (o : Orientation R E ι)
    (hcard : Fintype.card ι = Module.finrank R E) (hodd : Odd (Module.finrank R E)) :
    Orientation.map ι (LinearEquiv.neg R) o = -o := by
  apply (Orientation.map_eq_neg_iff_det_neg o _ hcard).mpr
  rw [LinearEquiv.det_neg_eq_neg_one_of_odd hodd]
  exact neg_one_lt_zero

end Orientation
