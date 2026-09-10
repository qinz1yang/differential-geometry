import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected



noncomputable section

namespace Poincare.Topology

theorem simplyConnectedSpace_of_subsingleton_fundamentalGroup
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X)
    [Subsingleton (FundamentalGroup X x₀)] : SimplyConnectedSpace X := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x γ
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀
  have h : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = (1 : FundamentalGroup X x) :=
    e.injective (Subsingleton.elim _ _)
  have hh := congrArg FundamentalGroup.toPath h
  apply Path.Homotopic.Quotient.eq.mp
  exact hh

end Poincare.Topology
