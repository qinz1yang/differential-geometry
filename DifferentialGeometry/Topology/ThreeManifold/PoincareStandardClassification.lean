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
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
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

def poincareStandardConnectedSumClosed : Prop :=
  ∀ M N : ConnectedClosedOrientedManifold.{u} 3,
    isPoincareStandard M.Carrier → isPoincareStandard N.Carrier →
      isPoincareStandard (connectedSum M N).Carrier

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

theorem poincareStandardSumClosed_of_connectedSumClosed
    (h : poincareStandardConnectedSumClosed.{u}) :
    poincareStandardSumClosed.{u} := by
  intro L hL
  induction L with
  | nil => exact isPoincareStandard_sphere
  | cons M L ih =>
    cases L with
    | nil => exact hL M (by simp)
    | cons N L =>
      have hM : isPoincareStandard M.Carrier := hL M (by simp)
      have hT : isPoincareStandard (finiteConnectedSum (N :: L)).Carrier :=
        ih fun F hF => hL F (by simp [hF])
      exact h M (finiteConnectedSum (N :: L)) hM hT

theorem connectedSumClosed_of_poincareStandardSumClosed
    (h : poincareStandardSumClosed.{u}) :
    poincareStandardConnectedSumClosed.{u} := by
  intro M N hM hN
  have h2 := h [M, N] (by
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hM
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hN
    exact absurd hF (by simp))
  exact h2

theorem poincareStandardSumClosed_iff_connectedSumClosed :
    poincareStandardSumClosed.{u} ↔ poincareStandardConnectedSumClosed.{u} :=
  ⟨connectedSumClosed_of_poincareStandardSumClosed,
    poincareStandardSumClosed_of_connectedSumClosed⟩

end DifferentialGeometry.Topology
