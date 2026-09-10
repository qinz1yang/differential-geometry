import DifferentialGeometry.Topology.Homology.Algebra.FiniteType
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k]
  (K L : ChainComplex (ModuleCat.{v} k) ℕ)


def homologyBiprodIso (n : ℕ) :
    (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n := by
  let F := _root_.HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.down ℕ) n
  letI := preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod K L


@[reassoc (attr := simp)]
theorem homologyBiprodIso_fst (n : ℕ) :
    (homologyBiprodIso K L n).hom ≫ biprod.fst =
      _root_.HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) n :=
  by unfold homologyBiprodIso; exact biprod.lift_fst _ _


@[reassoc (attr := simp)]
theorem homologyBiprodIso_snd (n : ℕ) :
    (homologyBiprodIso K L n).hom ≫ biprod.snd =
      _root_.HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) n :=
  by unfold homologyBiprodIso; exact biprod.lift_snd _ _

section Field
variable {k : Type u} [Field k] (K L : ChainComplex (ModuleCat.{v} k) ℕ)


theorem finiteHomologyType_biprod
    (hK : finiteHomologyType K) (hL : finiteHomologyType L) :
    finiteHomologyType (K ⊞ L) := by
  let S := ShortComplex.mk (biprod.inl : K ⟶ K ⊞ L) biprod.snd (by simp)
  exact finiteHomologyType_middle S
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hK hL

theorem homologyEulerChar_biprod
    (hK : finiteHomologyType K) (hL : finiteHomologyType L) :
    (K ⊞ L).homologyEulerChar = K.homologyEulerChar + L.homologyEulerChar := by
  have hKL := finiteHomologyType_biprod K L hK hL
  have := hK.1
  have := hL.1
  have := hKL.1
  let S := ShortComplex.mk (biprod.inl : K ⟶ K ⊞ L) biprod.snd (by simp)
  exact homologyEulerChar_additive S
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hK.2 hKL.2 hL.2

end Field
end DifferentialGeometry.HomologicalComplex
