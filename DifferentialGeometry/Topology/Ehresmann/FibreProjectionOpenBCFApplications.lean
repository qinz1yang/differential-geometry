import DifferentialGeometry.Topology.Ehresmann.FibreProjectionOpenBCF
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

/-!
# Consumer of the open fibre projection kernel (lane S-BCF03)

`isOpenMap_fst_example_BCF`: the kernel applied to the trivial product chart `id : ℝ × S¹ → ℝ × S¹`
over `id : ℝ → ℝ` with `C = Bs = ℝ`: the restriction of `Prod.fst` to `ℝ × S¹` is an open map.
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology

theorem isOpenMap_fst_example_BCF :
    IsOpenMap (fun q : ((univ : Set (ℝ × Circle)) ∩ Prod.fst ⁻¹' (univ : Set ℝ) :
        Set (ℝ × Circle)) => (⟨q.1.1, q.2.2⟩ : (univ : Set ℝ))) := by
  refine isOpenMap_restrict_fibreProj_BCF (X := (univ : Set (ℝ × Circle))) (f := Prod.fst)
    (Bs := (univ : Set ℝ)) (C := (univ : Set ℝ)) (E := ℝ) (Q := Circle) subset_rfl ?_
  intro y _
  refine ⟨id, id, univ, y, rfl, Topology.IsEmbedding.id, isOpen_univ, by simp, continuous_id,
    by simp, fun x z => rfl⟩

end DifferentialGeometry.Topology
