/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverLocal

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

theorem test_coverPathValue_rawTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H) a) :
    coverPathValue G H (rawTreePathMap G H p) = 1 := by
  induction p with
  | nil =>
      simpa [rawTreePathMap] using
        (coverPathValue_nil G H
          (a := rawBassSerreOrbitRoot G H))
  | @cons b c p e ih =>
      rw [rawTreePathMap_cons_raw]
      cases e using Subtype.rec with
      | mk e he =>
          cases e using Sum.rec with
          | inl f =>
              rw [coverPathValue_pos G H (rawTreePathMap G H p) f]
              rw [ih]
              have hloop := quotientEdgeLoop_tree_pos G H f he
              have hloop' :
                  quotientEdgeLoop G H (coverBaseEdge G H f).2.2 = 𝟙 _ := by
                change quotientEdgeLoop G H f = 𝟙 _
                exact hloop
              simp only [coverEdgeLetter]
              rw [hloop']
              simpa using (treeKuroshFreeInclusion G H).map_one
          | inr f =>
              rw [coverPathValue_neg G H (rawTreePathMap G H p) f]
              rw [ih]
              have hloop := quotientEdgeLoop_tree_neg G H f he
              have hloop' :
                  quotientEdgeLoop G H (coverBaseEdge G H f).2.2 = 𝟙 _ := by
                change quotientEdgeLoop G H f = 𝟙 _
                exact hloop
              simp only [coverEdgeLetter]
              rw [hloop']
              simpa using (treeKuroshFreeInclusion G H).map_one

end GraphCoveringTheory.Kurosh
