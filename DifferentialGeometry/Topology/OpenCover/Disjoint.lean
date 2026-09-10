import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace Poincare.Topology
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X)
  (hU : ∀ i, IsOpen (U i)) (hd : Pairwise (Disjoint on U))


def disjointOpenUnionHomeomorph : (Σ i, U i) ≃ₜ ⋃ i, U i := by
  let f : (Σ i, U i) → X := fun x => x.2.val
  have hc : Continuous f := continuous_sigma_iff.mpr (fun _ => continuous_subtype_val)
  have hi : Injective f := fun x y h => sigmaToiUnion_injective U hd (Subtype.ext h)
  have ho : IsOpenMap f := isOpenMap_sigma.mpr (fun i => (hU i).isOpenMap_subtype_val)
  have he : IsEmbedding (sigmaToiUnion U) := (IsEmbedding.subtypeVal.of_comp_iff).mp
    (IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi ho).isEmbedding
  exact (Equiv.ofBijective (sigmaToiUnion U) (sigmaToiUnion_bijective U hd)).toHomeomorphOfIsInducing he.isInducing


@[simp]
theorem disjointOpenUnionHomeomorph_apply (x : Σ i, U i) :
    (disjointOpenUnionHomeomorph U hU hd x).val = x.2.val := rfl
end Poincare.Topology
