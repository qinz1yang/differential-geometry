import DifferentialGeometry.External.CanonicalTopology.LinearAlgebra.Orientation

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
