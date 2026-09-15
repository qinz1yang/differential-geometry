import Mathlib.Topology.Gluing
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
noncomputable section
namespace TopCat.GlueData

universe u

variable (D : TopCat.GlueData.{u})

def chartMap {Y : Type*} (i : D.J) [Nonempty (D.U i)] (f : D.U i → Y) :
    D.toGlueData.glued → Y :=
  f ∘ ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)).symm

@[simp] theorem chartMap_apply {Y : Type*} (i : D.J) [Nonempty (D.U i)]
    (f : D.U i → Y) (x : D.U i) :
    D.chartMap i f (D.toGlueData.ι i x) = f x := by
  simp only [chartMap, Function.comp_apply]
  rw [(D.ι_isOpenEmbedding i).toOpenPartialHomeomorph_left_inv]

theorem chartMap_apply_overlap {Y : Type*} (i j : D.J)
    [Nonempty (D.U j)] (f : D.U j → Y) (x : D.V (i, j)) :
    D.chartMap j f (D.toGlueData.ι i (D.f i j x)) =
      f (D.f j i (D.t i j x)) := by
  rw [← D.glue_condition_apply i j x]
  exact D.chartMap_apply j f _

theorem continuousOn_chartMap {Y : Type*} [TopologicalSpace Y]
    (i : D.J) [Nonempty (D.U i)] (f : D.U i → Y) (hf : Continuous f) :
    ContinuousOn (D.chartMap i f) (Set.range (D.toGlueData.ι i)) := by
  apply hf.comp_continuousOn
  simpa only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using
    ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)).continuousOn_symm

end TopCat.GlueData
end
