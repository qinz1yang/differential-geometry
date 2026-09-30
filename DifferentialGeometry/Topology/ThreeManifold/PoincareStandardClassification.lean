import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormTrivial
import DifferentialGeometry.Topology.FundamentalGroup.SphericalQuotient
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] (h : isPoincareStandard M) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  classical
  obtain ⟨P⟩ := h
  let x : (i : Fin P.factors.length) → (P.factors.get i).Carrier :=
    fun i => Classical.choice (inferInstance : Nonempty (P.factors.get i).Carrier)
  let y : (finiteConnectedSum P.factors).Carrier := Classical.choice inferInstance
  have hbase : Subsingleton (FundamentalGroup (finiteConnectedSum P.factors).Carrier y) := by
    have he : FundamentalGroup (finiteConnectedSum P.factors).Carrier y ≃*
        FundamentalGroup M (P.diffeomorph.symm y) :=
      fundamentalGroupMulEquivOfHomotopyEquiv P.diffeomorph.symm.toHomeomorph.toHomotopyEquiv
        y (P.diffeomorph.symm y) rfl
    exact he.subsingleton
  have hcoprod : Subsingleton (Monoid.CoprodI (fun i : Fin P.factors.length =>
      FundamentalGroup (P.factors.get i).Carrier (x i))) :=
    @Equiv.subsingleton _ _
      ((fundamentalGroup_finiteConnectedSum_freeProduct P.factors x y).some.symm : _ ≃ _) hbase
  have hsub : ∀ i : Fin P.factors.length,
      Subsingleton (FundamentalGroup (P.factors.get i).Carrier (x i)) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff _).mp hcoprod
  have hL : ∀ F ∈ P.factors, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F.toClosedOrientedManifold standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
    intro F hF
    obtain ⟨i, rfl⟩ := List.get_of_mem hF
    exact exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor
      (P.factors.get i) (x i) (P.standard _ hF) (hsub i)
  obtain ⟨s⟩ := exists_diffeomorph_finiteConnectedSum_standardThreeSphere P.factors hL
  exact ⟨P.diffeomorph.trans s⟩

theorem isPoincareStandard_connectedSum_of_standardFactor
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (hM : isStandardFactor M) (hN : isStandardFactor N) :
    isPoincareStandard (connectedSum M N).Carrier := by
  have h := isPoincareStandard_finite_sum [M, N] (by
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hM
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hN
    exact absurd hF (by simp))
  exact h

end DifferentialGeometry.Topology
