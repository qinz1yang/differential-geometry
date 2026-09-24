import Mathlib.Topology.Gluing
import Mathlib.Topology.Compactness.SigmaCompact

open Set

namespace TopCat.GlueData

universe u
variable (D : TopCat.GlueData.{u})

theorem sigmaCompactSpace [Countable D.J] [∀ i, SigmaCompactSpace (D.U i)] :
    SigmaCompactSpace D.toGlueData.glued := by
  apply isSigmaCompact_univ_iff.mp
  have hcover : (⋃ i, Set.range (D.toGlueData.ι i)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective x
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self z⟩
  rw [← hcover]
  exact isSigmaCompact_iUnion _ fun i => isSigmaCompact_range (D.toGlueData.ι i).hom.continuous

end TopCat.GlueData
