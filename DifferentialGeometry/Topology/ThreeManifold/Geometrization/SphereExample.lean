import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts
import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSumSimplyConnected
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.ThreeManifold.Poincare

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
namespace GC.Endpoint
universe u

theorem isPrime_of_simplyConnected (P : ConnectedClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace P.Carrier] : IsPrime P := by
  intro A B hd
  obtain ⟨d⟩ := hd
  have : SimplyConnectedSpace (finiteConnectedSum [A, B]).Carrier :=
    d.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  have : SimplyConnectedSpace A.Carrier :=
    simplyConnectedSpace_of_mem_finiteConnectedSum [A, B] A (by simp)
  obtain ⟨f⟩ := DifferentialGeometry.Topology.smooth_poincare_conjecture A.Carrier
  exact Or.inl ⟨f.trans standardThreeSphereLiftDiffeomorph⟩

def sphericalStructure : GC.Geometry.GeometricStructure (𝓡 3)
    standardThreeSphere.Carrier where
  model := .spherical
  metric := GC.Geometry.sphericalModelMetric
  complete := GC.Geometry.sphericalModel_complete
  atlas := by
    change GC.Geometry.ModelAtlas GC.Geometry.sphericalModelMetric GC.Geometry.sphericalModelMetric
    exact GC.Geometry.ModelAtlas.refl _
  hyperbolic_finite_volume := by intro h; cases h

def sphereLiftStructure : GC.Geometry.GeometricStructure (𝓡 3)
    standardThreeSphereLift.{u}.Carrier :=
  sphericalStructure.pullback standardThreeSphereLiftDiffeomorph.symm

def sphereCertificate : GeometrizationCertificate standardThreeSphereLift.{u} := by
  let : SimplyConnectedSpace standardThreeSphere.Carrier :=
    inferInstanceAs (SimplyConnectedSpace SphereThree)
  let : SimplyConnectedSpace standardThreeSphereLift.{u}.Carrier :=
    Homeomorph.ulift.toHomotopyEquiv.simplyConnectedSpace
  refine {
    primeData := {
      factors := [standardThreeSphereLift]
      factors_nonempty := by simp
      prime := ?_
      reconstruction := ClosedOrientedManifold.OrientedDiffeomorph.refl _ }
    geometricFactors := ?_ }
  · intro F hF
    have h : F = standardThreeSphereLift := List.mem_singleton.mp hF
    subst F
    exact isPrime_of_simplyConnected _
  · intro i
    simpa using NoCuts.geometricDecomposition standardThreeSphereLift sphereLiftStructure

theorem standardThreeSphereLift_geometrizes : Geometrizes standardThreeSphereLift.{u} :=
  ⟨sphereCertificate⟩

end GC.Endpoint
