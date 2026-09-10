import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DifferentialGeometry.HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {A K B L : _root_.HomologicalComplex C c}
  (i : A ⟶ K) (j : B ⟶ L)


abbrev cokernelSequence : ShortComplex (_root_.HomologicalComplex C c) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)


theorem cokernelSequence_shortExact [Mono i] : (cokernelSequence i).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  mono_f := inferInstance
  epi_g := inferInstance

theorem quasiIso_cokernel_map [Mono i] [Mono j]
    (a : A ⟶ B) (b : K ⟶ L) (hab : i ≫ b = a ≫ j)
    (ha : QuasiIso a) (hb : QuasiIso b) : QuasiIso (cokernel.map i j a b hab) := by
  let φ : cokernelSequence i ⟶ cokernelSequence j := {
    τ₁ := a
    τ₂ := b
    τ₃ := cokernel.map i j a b hab
    comm₁₂ := hab.symm
    comm₂₃ := (cokernel.π_desc _ _ _).symm }
  exact _root_.HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (cokernelSequence_shortExact i) (cokernelSequence_shortExact j) ha hb

end DifferentialGeometry.HomologicalComplex
