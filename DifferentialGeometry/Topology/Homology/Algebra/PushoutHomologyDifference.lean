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

theorem exists_homology_preimage_of_pushout_eq (sq : IsPushout f g r s) [Mono f]
    (n : ι) (x : X.homology n) (y : Y.homology n)
    (hxy : _root_.HomologicalComplex.homologyMap r n x =
      _root_.HomologicalComplex.homologyMap s n y) :
    ∃ a : W.homology n, _root_.HomologicalComplex.homologyMap f n a = x ∧
      _root_.HomologicalComplex.homologyMap g n a = y := by
  let S := DifferentialGeometry.ShortComplex.pushoutShortComplex sq
  let w := _root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n x -
    _root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) n y
  have hw : _root_.HomologicalComplex.homologyMap S.g n w = 0 := by
    simp only [w, map_sub]
    change (_root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n ≫
      _root_.HomologicalComplex.homologyMap S.g n) x -
      (_root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) n ≫
        _root_.HomologicalComplex.homologyMap S.g n) y = 0
    simpa only [← _root_.HomologicalComplex.homologyMap_comp, S,
      DifferentialGeometry.ShortComplex.pushoutShortComplex, biprod.inl_desc,
      biprod.inr_desc, sub_eq_zero] using hxy
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((DifferentialGeometry.ShortComplex.pushoutShortExact sq).homology_exact₂ n) w hw
  refine ⟨a, ?_, ?_⟩
  · have h := congrArg (_root_.HomologicalComplex.homologyMap
      (biprod.fst : X ⊞ Y ⟶ X) n) ha
    simp only [w, map_sub] at h
    change (_root_.HomologicalComplex.homologyMap S.f n ≫
      _root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) n) a =
      (_root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n ≫
        _root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) n) x -
      (_root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) n ≫
        _root_.HomologicalComplex.homologyMap (biprod.fst : X ⊞ Y ⟶ X) n) y at h
    simp only [← _root_.HomologicalComplex.homologyMap_comp, S,
      DifferentialGeometry.ShortComplex.pushoutShortComplex, biprod.lift_fst,
      biprod.inl_fst, biprod.inr_fst, _root_.HomologicalComplex.homologyMap_id,
      _root_.HomologicalComplex.homologyMap_zero, ModuleCat.id_apply] at h
    change _root_.HomologicalComplex.homologyMap f n a = x - 0 at h
    simpa only [sub_zero] using h
  · have h := congrArg (_root_.HomologicalComplex.homologyMap
      (biprod.snd : X ⊞ Y ⟶ Y) n) ha
    simp only [w, map_sub] at h
    change (_root_.HomologicalComplex.homologyMap S.f n ≫
      _root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) n) a =
      (_root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) n ≫
        _root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) n) x -
      (_root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) n ≫
        _root_.HomologicalComplex.homologyMap (biprod.snd : X ⊞ Y ⟶ Y) n) y at h
    simp only [← _root_.HomologicalComplex.homologyMap_comp, S,
      DifferentialGeometry.ShortComplex.pushoutShortComplex, biprod.lift_snd,
      biprod.inl_snd, biprod.inr_snd, _root_.HomologicalComplex.homologyMap_id,
      _root_.HomologicalComplex.homologyMap_zero, _root_.HomologicalComplex.homologyMap_neg,
      ModuleCat.id_apply] at h
    change -(_root_.HomologicalComplex.homologyMap g n a) = 0 - y at h
    exact neg_injective (h.trans (zero_sub y))

end DifferentialGeometry.HomologicalComplex
