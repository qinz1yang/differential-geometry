/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem plApproximationManifold_three_of_moise352 (h352 : Moise352.{u} 3) :
    PLApproximationManifold.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ h φ hφ hpos
  have hh : Topology.IsEmbedding (univ.domRestrict (h : M₁ → M₂)) :=
    h.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  obtain ⟨f, hf, himage, hclose⟩ := exists_plh_approx_of_isOpen h352 isOpen_univ hh φ
    hφ.continuousOn (fun x _ => hpos x)
  have hcont : Continuous f := continuousOn_univ.mp hf.continuousOn
  have hinj : Function.Injective f := Set.injOn_univ.mp hf.injOn
  have hsurj : Function.Surjective f := by
    apply range_eq_univ.mp
    rw [← image_univ, himage, image_univ, h.surjective.range_eq]
  let g : M₁ ≃ₜ M₂ := (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont
    (isOpenMap_of_continuous_injective (E := EuclideanSpace ℝ (Fin 3)) hcont hinj)
  refine ⟨g, ?_, fun x => hclose x (mem_univ x)⟩
  change IsPL 3 3 f
  exact StructureGroupoid.liftPropOn_univ.mp hf.isPLOn

end DifferentialGeometry.Topology.PiecewiseLinear
