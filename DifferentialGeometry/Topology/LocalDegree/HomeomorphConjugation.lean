/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.ChartParityTransport
import DifferentialGeometry.Topology.Manifold.EmbeddingLocalHomeomorph

open Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem embeddingOrientationParity_conj_homeomorph
    (c : E ≃ₜ E) {U : Set E} (hU : IsOpen U) {f : E → E}
    (hf : ContinuousOn f U) (hfi : InjOn f U) (x : U) :
    embeddingOrientationParity (hU.preimage c.symm.continuous)
      (c.continuous.comp_continuousOn
        (hf.comp c.symm.continuous.continuousOn (fun _ hx => hx)))
      (fun y hy z hz hyz => c.symm.injective (hfi hy hz (c.injective hyz)))
      ⟨c x, by simpa only [mem_preimage, c.symm_apply_apply] using x.2⟩ =
      embeddingOrientationParity hU hf hfi x := by
  obtain ⟨F, hFs, -, hF⟩ :=
    DifferentialGeometry.Topology.exists_openPartialHomeomorph_of_continuousOn_injOn
      («E» := E) hU hf hfi
  let a := OpenPartialHomeomorph.refl E
  let b := c.toOpenPartialHomeomorph
  have hxF : (x : E) ∈ F.source := hFs ▸ x.2
  have hrel := chartOrientationParity_relative_eq_of_isPreconnected F a b
    isPreconnected_univ (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
    x hxF (mem_univ _) (mem_univ _)
  have hleft : chartOrientationParity a (F ≫ₕ a) x (mem_univ _)
      ⟨hxF, mem_univ _⟩ = embeddingOrientationParity hU hf hfi x := by
    unfold chartOrientationParity
    exact embeddingOrientationParity_congr (a.symm ≫ₕ (F ≫ₕ a)).open_source hU
      (a.symm ≫ₕ (F ≫ₕ a)).continuousOn (a.symm ≫ₕ (F ≫ₕ a)).injOn hf hfi _ x.2
      (Filter.Eventually.of_forall hF)
  have hright : chartOrientationParity b (F ≫ₕ b) x (mem_univ _)
      ⟨hxF, mem_univ _⟩ =
      embeddingOrientationParity (hU.preimage c.symm.continuous)
        (c.continuous.comp_continuousOn
          (hf.comp c.symm.continuous.continuousOn (fun _ hx => hx)))
        (fun y hy z hz hyz => c.symm.injective (hfi hy hz (c.injective hyz)))
        ⟨c x, by simpa only [mem_preimage, c.symm_apply_apply] using x.2⟩ := by
    unfold chartOrientationParity
    apply embeddingOrientationParity_congr
    exact Filter.Eventually.of_forall fun y => congrArg c (hF (c.symm y))
  exact hright.symm.trans (hrel.symm.trans hleft)

end DifferentialGeometry.LocalDegree
