import DifferentialGeometry.Topology.Homology.SmallChains.Union
import DifferentialGeometry.Topology.Homology.EulerCharacteristic
import DifferentialGeometry.Topology.Homology.Algebra.Biproduct

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
noncomputable section
universe u
namespace Poincare.Homology
variable (X : TopCat.{u}) (s t : Set X) (k : Type u) [Field k]

theorem finiteHomologyType_twoSetSmall
    (hs : finiteHomologyType k (TopCat.of s)) (ht : finiteHomologyType k (TopCat.of t))
    (hst : finiteHomologyType k (TopCat.of (s ∩ t : Set X))) :
    Poincare.HomologicalComplex.finiteHomologyType
      ((smallSingularSimplices X (twoSetFamily X s t) : SSet).chainComplex (ModuleCat.of k k)) := by
  let S := subspaceSmallShortComplex X s t (ModuleCat.of k k)
  exact Poincare.HomologicalComplex.finiteHomologyType_last S
    (subspaceSmallShortExact X s t (ModuleCat.of k k)) hst
    (Poincare.HomologicalComplex.finiteHomologyType_biprod _ _ hs ht)

theorem homologyEulerChar_twoSetSmall
    (hs : finiteHomologyType k (TopCat.of s)) (ht : finiteHomologyType k (TopCat.of t))
    (hst : finiteHomologyType k (TopCat.of (s ∩ t : Set X))) :
    ((smallSingularSimplices X (twoSetFamily X s t) : SSet).chainComplex
      (ModuleCat.of k k)).homologyEulerChar =
      eulerChar k (TopCat.of s) + eulerChar k (TopCat.of t) - eulerChar k (TopCat.of (s ∩ t : Set X)) := by
  let S := subspaceSmallShortComplex X s t (ModuleCat.of k k)
  have hm := Poincare.HomologicalComplex.finiteHomologyType_biprod _ _ hs ht
  have hu := finiteHomologyType_twoSetSmall X s t k hs ht hst
  have : ∀ n, FiniteDimensional k (S.X₁.homology n) := hst.1
  have : ∀ n, FiniteDimensional k (S.X₂.homology n) := hm.1
  have : ∀ n, FiniteDimensional k (S.X₃.homology n) := hu.1
  have h := Poincare.HomologicalComplex.homologyEulerChar_additive S
    (subspaceSmallShortExact X s t (ModuleCat.of k k)) hst.2 hm.2 hu.2
  have hb := Poincare.HomologicalComplex.homologyEulerChar_biprod _ _ hs ht
  change S.X₂.homologyEulerChar = eulerChar k (TopCat.of s) + eulerChar k (TopCat.of t) at hb
  rw [hb] at h
  change eulerChar k (TopCat.of s) + eulerChar k (TopCat.of t) =
    eulerChar k (TopCat.of (s ∩ t : Set X)) + _ at h
  change S.X₃.homologyEulerChar = _
  omega

end Poincare.Homology
