import DifferentialGeometry.Topology.FundamentalGroup.Product
import DifferentialGeometry.Topology.FundamentalGroup.Retraction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

theorem bijective_fundamentalGroup_map_prodMk_const
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (x : X) (y : Y) :
    Function.Bijective
      (FundamentalGroup.map ((ContinuousMap.id X).prodMk (ContinuousMap.const X y)) x) := by
  let f := (ContinuousMap.id X).prodMk (ContinuousMap.const X y)
  have hi := fundamentalGroup_mapOfEq_leftInverse f ContinuousMap.fst (fun _ => rfl) x
  refine ⟨hi.injective, ?_⟩
  intro a
  refine ⟨Path.Homotopic.projLeft a, ?_⟩
  apply (fundamentalGroupProdEquiv x y).injective
  apply Prod.ext
  · change Path.Homotopic.projLeft
      (FundamentalGroup.map f x (Path.Homotopic.projLeft a)) = Path.Homotopic.projLeft a
    generalize Path.Homotopic.projLeft a = b
    induction b using Path.Homotopic.Quotient.ind with
    | mk b => rfl
  · exact Subsingleton.elim _ _

end DifferentialGeometry.Topology
