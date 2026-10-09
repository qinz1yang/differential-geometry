/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FirstHomologyProduct
import Mathlib.Topology.ContinuousMap.Algebra

open scoped ContinuousMap

namespace DifferentialGeometry.Topology

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem integralFirstHomology_prod_zero_decomposition
    [Zero Y] [PathConnectedSpace Y] (a : integralSingularHomology 1 (Y × Y)) :
    integralSingularHomologyMap 1
        (⟨fun y : Y => (y, 0), continuous_id.prodMk continuous_const⟩ : C(Y, Y × Y))
        (integralSingularHomologyMap 1 ContinuousMap.fst a) +
      integralSingularHomologyMap 1
        (⟨fun y : Y => (0, y), continuous_const.prodMk continuous_id⟩ : C(Y, Y × Y))
        (integralSingularHomologyMap 1 ContinuousMap.snd a) = a := by
  let i₁ : C(Y, Y × Y) := ⟨fun y => (y, 0), continuous_id.prodMk continuous_const⟩
  let i₂ : C(Y, Y × Y) := ⟨fun y => (0, y), continuous_const.prodMk continuous_id⟩
  change integralSingularHomologyMap 1 i₁ (integralSingularHomologyMap 1 ContinuousMap.fst a) +
    integralSingularHomologyMap 1 i₂ (integralSingularHomologyMap 1 ContinuousMap.snd a) = a
  apply integralSingularHomologyOneProdEquiv.injective
  rw [integralSingularHomologyOneProdEquiv_apply,
    integralSingularHomologyOneProdEquiv_apply]
  apply Prod.ext
  · simp only [map_add, ← LinearMap.comp_apply,
      ← integralSingularHomologyMap_comp]
    change integralSingularHomologyMap 1 ContinuousMap.fst a +
      integralSingularHomologyMap 1 (ContinuousMap.const (Y × Y) 0) a = _
    rw [integralSingularHomologyMap_const 1 one_ne_zero, LinearMap.zero_apply, add_zero]
  · simp only [map_add, ← LinearMap.comp_apply,
      ← integralSingularHomologyMap_comp]
    change integralSingularHomologyMap 1 (ContinuousMap.const (Y × Y) 0) a +
      integralSingularHomologyMap 1 ContinuousMap.snd a = _
    rw [integralSingularHomologyMap_const 1 one_ne_zero, LinearMap.zero_apply, zero_add]

theorem integralSingularHomologyMap_one_add
    [AddZeroClass Y] [ContinuousAdd Y] [PathConnectedSpace Y] (f g : C(X, Y)) :
    integralSingularHomologyMap 1 (f + g) =
      integralSingularHomologyMap 1 f + integralSingularHomologyMap 1 g := by
  let s : C(Y × Y, Y) := ⟨fun p => p.1 + p.2, continuous_fst.add continuous_snd⟩
  let i₁ : C(Y, Y × Y) := ⟨fun y => (y, 0), continuous_id.prodMk continuous_const⟩
  let i₂ : C(Y, Y × Y) := ⟨fun y => (0, y), continuous_const.prodMk continuous_id⟩
  have h₁ : s.comp i₁ = ContinuousMap.id Y := by ext y; exact add_zero y
  have h₂ : s.comp i₂ = ContinuousMap.id Y := by ext y; exact zero_add y
  have hs (a : integralSingularHomology 1 (Y × Y)) :
      integralSingularHomologyMap 1 s a =
        integralSingularHomologyMap 1 ContinuousMap.fst a +
          integralSingularHomologyMap 1 ContinuousMap.snd a := by
    have ha := integralFirstHomology_prod_zero_decomposition a
    change integralSingularHomologyMap 1 i₁
        (integralSingularHomologyMap 1 ContinuousMap.fst a) +
      integralSingularHomologyMap 1 i₂
        (integralSingularHomologyMap 1 ContinuousMap.snd a) = a at ha
    conv_lhs => rw [← ha]
    simp only [map_add, ← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
    change integralSingularHomologyMap 1 ((s.comp i₁).comp ContinuousMap.fst) a +
      integralSingularHomologyMap 1 ((s.comp i₂).comp ContinuousMap.snd) a = _
    rw [h₁, h₂]
    rfl
  have hfg : s.comp (f.prodMk g) = f + g := rfl
  ext a
  rw [← hfg, integralSingularHomologyMap_comp, LinearMap.comp_apply, hs,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← integralSingularHomologyMap_comp, ← integralSingularHomologyMap_comp]
  rfl

theorem integralSingularHomologyMap_one_zsmul
    [AddGroup Y] [IsTopologicalAddGroup Y] [PathConnectedSpace Y] (n : ℤ) (f : C(X, Y)) :
    integralSingularHomologyMap 1 (n • f) = n • integralSingularHomologyMap 1 f := by
  let F : C(X, Y) →+
      (integralSingularHomology 1 X →ₗ[ℤ] integralSingularHomology 1 Y) :=
    { toFun := integralSingularHomologyMap 1
      map_zero' := integralSingularHomologyMap_const 1 one_ne_zero 0
      map_add' := integralSingularHomologyMap_one_add }
  exact F.map_zsmul n f

end DifferentialGeometry.Topology
