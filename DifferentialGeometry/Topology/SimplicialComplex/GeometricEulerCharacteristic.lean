import DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationHomeomorphism
import DifferentialGeometry.Topology.SimplicialComplex.OrderedRealizationEuler
import Mathlib.SetTheory.Cardinal.Order

set_option autoImplicit false
noncomputable section
namespace Poincare.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
  (k : Type u) [Field k]

theorem finiteHomologyType_geometricSpace :
    Poincare.Homology.finiteHomologyType k (TopCat.of K.space) := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  exact (Poincare.Homology.finiteHomologyType_iff_of_homeomorph k
    (Y := TopCat.of K.space) (geometricRealizationHomeomorphism K)).mp
    (finiteHomologyType_orderedRealization K.toPreAbstractSimplicialComplex k)

theorem eulerChar_geometricSpace_eq_faceEulerChar :
    Poincare.Homology.eulerChar k (TopCat.of K.space) =
      faceEulerChar K.toPreAbstractSimplicialComplex := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  exact (Poincare.Homology.eulerChar_eq_of_homeomorph k
    (Y := TopCat.of K.space) (geometricRealizationHomeomorphism K)).symm.trans
    (eulerChar_orderedRealization_eq_faceEulerChar K.toPreAbstractSimplicialComplex k)

theorem eulerChar_geometricSpace_eq_of_coefficients (l : Type u) [Field l] :
    Poincare.Homology.eulerChar k (TopCat.of K.space) =
      Poincare.Homology.eulerChar l (TopCat.of K.space) := by
  rw [eulerChar_geometricSpace_eq_faceEulerChar, eulerChar_geometricSpace_eq_faceEulerChar]

end Poincare.Topology.SimplicialComplex
