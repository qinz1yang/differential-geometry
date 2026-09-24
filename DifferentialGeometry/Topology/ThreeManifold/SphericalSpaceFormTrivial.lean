import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group
    (G : SphericalSpaceFormGroup) (h : Subsingleton G.group) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      G.manifold.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  classical
  have hbij : Function.Bijective G.projection := by
    refine ⟨fun x y hxy => ?_, G.projection_surjective⟩
    obtain ⟨γ, hγ⟩ := (G.projection_eq_iff x y).mp hxy
    have hsmul : (γ : G.group) • x = y := hγ
    have hγ1 : γ = 1 := h.elim γ 1
    rw [hγ1] at hsmul
    simpa using hsmul
  let d : Diffeomorph (𝓡 3) (𝓡 3)
      (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) G.Orbit ∞ :=
    G.projection_isLocalDiffeomorph.diffeomorphOfBijective hbij
  have hd : d.preservesOrientation (sphereOrientation 3 (by decide)) G.manifold.orientation :=
    fun x => G.projection_positive x
  refine ⟨?_, ?_⟩
  · exact d.symm.trans standardThreeSphereLiftDiffeomorph.{u}
  · exact Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm hd)
      standardThreeSphereLiftDiffeomorph_preservesOrientation

end DifferentialGeometry.Topology
