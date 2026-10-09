/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PushoutHomologyDifference

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGeometry.HomologicalComplex

variable {k : Type*} [Ring k] {ι : Type*} {c : ComplexShape ι}
  {W X Y Z : HomologicalComplex (ModuleCat k) c}
  {f : W ⟶ X} {g : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}

theorem bijective_homologyMap_pair_of_pushout (sq : IsPushout f g r s) [Mono f]
    (i j : ι) (hij : c.Rel i j) (hi : Subsingleton (Z.homology i))
    (hj : Subsingleton (Z.homology j)) :
    Function.Bijective (fun a : W.homology j =>
      (_root_.HomologicalComplex.homologyMap f j a,
        _root_.HomologicalComplex.homologyMap g j a)) := by
  let S := DifferentialGeometry.ShortComplex.pushoutShortComplex sq
  have hS := DifferentialGeometry.ShortComplex.pushoutShortExact sq
  have hδ : hS.δ i j hij = 0 := by
    let _ := hi
    exact (ModuleCat.isZero_of_subsingleton (Z.homology i)).eq_of_src _ _
  have hmono : Mono (_root_.HomologicalComplex.homologyMap S.f j) :=
    (hS.homology_exact₁ i j hij).mono_g hδ
  constructor
  · intro a b hab
    apply (ModuleCat.mono_iff_injective _).mp hmono
    have hfst := congrArg Prod.fst hab
    have hsnd := congrArg Prod.snd hab
    dsimp only at hfst hsnd
    change _root_.HomologicalComplex.homologyMap (biprod.lift f (-g)) j a =
      _root_.HomologicalComplex.homologyMap (biprod.lift f (-g)) j b
    simp only [biprod.lift_eq, _root_.HomologicalComplex.homologyMap_add,
      _root_.HomologicalComplex.homologyMap_comp,
      _root_.HomologicalComplex.homologyMap_neg]
    change _root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) j
        (_root_.HomologicalComplex.homologyMap f j a) +
      _root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) j
        (-(_root_.HomologicalComplex.homologyMap g j a)) =
      _root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) j
        (_root_.HomologicalComplex.homologyMap f j b) +
      _root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) j
        (-(_root_.HomologicalComplex.homologyMap g j b))
    rw [hfst, hsnd]
  · rintro ⟨x, y⟩
    obtain ⟨a, ha, hb⟩ := exists_homology_preimage_of_pushout_eq sq j x y (hj.elim _ _)
    exact ⟨a, Prod.ext ha hb⟩

end DifferentialGeometry.HomologicalComplex
