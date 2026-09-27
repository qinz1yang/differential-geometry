/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PushoutHomology

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGeometry.HomologicalComplex

variable {k : Type*} [Ring k] {ι : Type*} {c : ComplexShape ι}
  {W X Y Z : HomologicalComplex (ModuleCat k) c}
  {f : W ⟶ X} {g : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}

theorem exists_homology_sum_of_pushout (sq : IsPushout f g r s) [Mono f]
    (i j : ι) (hij : c.Rel i j)
    (hinj : Function.Injective (_root_.HomologicalComplex.homologyMap f j))
    (a : Z.homology i) :
    ∃ x : X.homology i, ∃ y : Y.homology i,
      _root_.HomologicalComplex.homologyMap r i x +
        _root_.HomologicalComplex.homologyMap s i y = a := by
  let S := DifferentialGeometry.ShortComplex.pushoutShortComplex sq
  have hS := DifferentialGeometry.ShortComplex.pushoutShortExact sq
  have hmono : Mono (_root_.HomologicalComplex.homologyMap S.f j) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro a b hab
    apply hinj
    have h := congrArg (_root_.HomologicalComplex.homologyMap
      (biprod.fst : X ⊞ Y ⟶ X) j) hab
    change (_root_.HomologicalComplex.homologyMap S.f j ≫
      _root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) j) a =
        (_root_.HomologicalComplex.homologyMap S.f j ≫
          _root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) j) b at h
    simpa only [← _root_.HomologicalComplex.homologyMap_comp, S,
      DifferentialGeometry.ShortComplex.pushoutShortComplex, biprod.lift_fst] using h
  have hδ : hS.δ i j hij = 0 := (hS.homology_exact₁ i j hij).mono_g_iff.mp hmono
  have hepi : Epi (_root_.HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₃ i j hij).epi_f hδ
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective _).mp hepi a
  refine ⟨_root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) i b,
    _root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) i b, ?_⟩
  change (_root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) i ≫
      _root_.HomologicalComplex.homologyMap r i) b +
    (_root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) i ≫
      _root_.HomologicalComplex.homologyMap s i) b = a
  rw [← _root_.HomologicalComplex.homologyMap_comp,
    ← _root_.HomologicalComplex.homologyMap_comp]
  change (_root_.HomologicalComplex.homologyMap (biprod.fst ≫ r) i +
    _root_.HomologicalComplex.homologyMap (biprod.snd ≫ s) i :
      (X ⊞ Y).homology i ⟶ Z.homology i) b = a
  rw [← _root_.HomologicalComplex.homologyMap_add, ← biprod.desc_eq]
  exact hb

end DifferentialGeometry.HomologicalComplex
