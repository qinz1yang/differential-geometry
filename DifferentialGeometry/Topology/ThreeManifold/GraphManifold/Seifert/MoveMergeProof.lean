import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeSelfSeam

/-!
# The merge move from linear torus mapping classes

`moveMerge'` proves the (S⁺) merge move from the classical input `TorusMappingClassLinear`,
with the case split of `moveMerge` and neither of its two local `sorry` lemmas: a host without
self-seam uses Codex X9's `exists_merge_of_selfSeamFree_of_torusMappingClassLinear`, a host with
a self-seam uses Codex X10's `exists_complexity_one_of_selfSeam_redundant`.
-/

set_option autoImplicit false

universe u

namespace GC.Seifert

theorem moveMerge' (hT : TorusMappingClassLinear) : MoveMerge.{u} := by
  intro Q E j b h
  by_cases hf : E.HostSelfSeamFree j b
  · exact E.exists_merge_of_selfSeamFree_of_torusMappingClassLinear hT j b h hf
  · obtain ⟨k, hl, hr⟩ := ElementaryPresentation.IsMergeSeam.exists_selfSeam hf
    obtain ⟨E', hE'⟩ := E.exists_complexity_one_of_selfSeam_redundant j b h k hl hr
      (h.host_sides hl hr).1 (h.components_count_of_selfSeam hl hr)
      (h.complexity_of_selfSeam hl hr) hT
    exact ⟨E', by rw [hE', h.complexity_of_selfSeam hl hr]⟩

end GC.Seifert
