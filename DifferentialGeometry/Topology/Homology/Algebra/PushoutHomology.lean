/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PushoutExact
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGeometry.HomologicalComplex

variable {k : Type*} [Ring k] {ι : Type*} {c : ComplexShape ι}
  {W X Y Z : HomologicalComplex (ModuleCat k) c}
  {f : W ⟶ X} {g : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}

theorem exists_homology_preimage_of_pushout (sq : IsPushout f g r s) [Mono f]
    (n : ι) (z : X.homology n) (hz : _root_.HomologicalComplex.homologyMap r n z = 0) :
    ∃ y : W.homology n, _root_.HomologicalComplex.homologyMap f n y = z ∧
      _root_.HomologicalComplex.homologyMap g n y = 0 := by
  let S := DifferentialGeometry.ShortComplex.pushoutShortComplex sq
  let w := _root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n z
  have hw : _root_.HomologicalComplex.homologyMap S.g n w = 0 := by
    change (_root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n ≫
      _root_.HomologicalComplex.homologyMap S.g n) z = 0
    rw [← _root_.HomologicalComplex.homologyMap_comp]
    simpa only [S, DifferentialGeometry.ShortComplex.pushoutShortComplex, biprod.inl_desc] using hz
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((DifferentialGeometry.ShortComplex.pushoutShortExact sq).homology_exact₂ n) w hw
  refine ⟨y, ?_, ?_⟩
  · have h := congrArg (_root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) n) hy
    change (_root_.HomologicalComplex.homologyMap S.f n ≫
      _root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) n) y =
      (_root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n ≫
        _root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) n) z at h
    simpa only [← _root_.HomologicalComplex.homologyMap_comp, S,
      DifferentialGeometry.ShortComplex.pushoutShortComplex, biprod.lift_fst, biprod.inl_fst,
      _root_.HomologicalComplex.homologyMap_id, ModuleCat.id_apply] using h
  · have h := congrArg (_root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) n) hy
    change (_root_.HomologicalComplex.homologyMap S.f n ≫
      _root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) n) y =
      (_root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n ≫
        _root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) n) z at h
    simp only [← _root_.HomologicalComplex.homologyMap_comp, S,
      DifferentialGeometry.ShortComplex.pushoutShortComplex, biprod.lift_snd, biprod.inl_snd,
      _root_.HomologicalComplex.homologyMap_zero, _root_.HomologicalComplex.homologyMap_neg] at h
    change -(_root_.HomologicalComplex.homologyMap g n y) = 0 at h
    exact neg_eq_zero.mp h

end DifferentialGeometry.HomologicalComplex
