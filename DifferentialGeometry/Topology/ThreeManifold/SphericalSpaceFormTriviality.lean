import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormTrivial
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.DeckCovering
import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSum

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem subsingleton_fundamentalGroup_of_standard_factor
    (F : ConnectedClosedOrientedManifold.{u} 3) (p q : F.Carrier)
    (h : Subsingleton (FundamentalGroup F.Carrier p)) :
    Subsingleton (FundamentalGroup F.Carrier q) := by
  let : PathConnectedSpace F.Carrier := instPathConnectedSpaceCarrier F
  exact subsingleton_fundamentalGroup_of_joined
    (Joined.somePath (PathConnectedSpace.joined p q)) h

theorem exists_diffeomorph_standardThreeSphere_of_spherical_factor_presentation
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hstd : isPoincareStandard M) [SimplyConnectedSpace M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  obtain ⟨P⟩ := hstd
  have hMconn : ConnectedSpace M := isPoincareStandard_connectedSpace ⟨P⟩
  let p : M := Classical.choice inferInstance
  let x : (i : Fin P.factors.length) → (P.factors.get i).Carrier :=
    fun i => Classical.choice (inferInstance : Nonempty (P.factors.get i).Carrier)
  let y : (finiteConnectedSum P.factors).Carrier := Classical.choice inferInstance
  have he : FundamentalGroup M p ≃*
      FundamentalGroup (finiteConnectedSum P.factors).Carrier (P.diffeomorph p) :=
    fundamentalGroupMulEquivOfHomotopyEquiv P.diffeomorph.toHomeomorph.toHomotopyEquiv
      p (P.diffeomorph p) rfl
  have hsumAt : Subsingleton
      (FundamentalGroup (finiteConnectedSum P.factors).Carrier (P.diffeomorph p)) :=
    @Equiv.subsingleton (FundamentalGroup (finiteConnectedSum P.factors).Carrier (P.diffeomorph p))
      (FundamentalGroup M p) he.toEquiv.symm
      (inferInstance : Subsingleton (FundamentalGroup M p))
  have hsumSub : Subsingleton (FundamentalGroup (finiteConnectedSum P.factors).Carrier y) :=
    subsingleton_fundamentalGroup_of_joined
      (Joined.somePath (PathConnectedSpace.joined (P.diffeomorph p) y)) hsumAt
  have hcoprod : Subsingleton (Monoid.CoprodI (fun i : Fin P.factors.length =>
      FundamentalGroup (P.factors.get i).Carrier (x i))) :=
    @Equiv.subsingleton
      (Monoid.CoprodI (fun i : Fin P.factors.length =>
        FundamentalGroup (P.factors.get i).Carrier (x i)))
      (FundamentalGroup (finiteConnectedSum P.factors).Carrier y)
      ((fundamentalGroup_finiteConnectedSum_freeProduct P.factors x y).some.toEquiv).symm hsumSub
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

end DifferentialGeometry.Topology
