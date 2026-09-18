import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrderedSides

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology.SphereSeparation (AxialInterval axialZero sliceImage)
open KappaSolutions (SpatialNeckSphere SpatialNeckWitness SpatialNeckSideData)

private local instance neckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps eta t : ℝ} {v p : M}
  {h : SmoothRiemannianMetric I3 M} {yStar : SpatialNeckSphere}
  {W : SpatialNeckWitness h yStar p eta}

namespace StrongNeck

theorem bicollar_zero_sides_eq_of_centralSphere_eq (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (sides : SpatialNeckSideData W)
    (hsphere : nk.map '' (univ ×ˢ ({0} : Set ℝ)) = W.centralSphere) :
    (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide = sides.lower 0 ∧
      (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).endSide = sides.upper 0 := by
  have heta : 0 < eta := W.epsilon_pos
  have hzero : |(0 : ℝ)| < eta⁻¹ + 1 := by
    rw [abs_zero]
    positivity
  have hslice : sliceImage nk.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) =
      W.centralSphere :=
    (nk.bicollar_slice (axialZero (inv_pos.mpr nk.eps_pos))).trans hsphere
  obtain ⟨hlower, hupper, hlowerOpen, hupperOpen, hdisjoint, hunion,
    hcompact, hnoncompact, _⟩ := sides.slice_spec 0 hzero
  change sides.lower 0 ∪ sides.upper 0 = W.centralSphereᶜ at hunion
  have heq :=
    (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).side_sets_unique_of_core_properties
      (sides.lower 0) (sides.upper 0) hlowerOpen hupperOpen hlower hupper hdisjoint
      (hunion.trans (congrArg compl hslice.symm)) hcompact hnoncompact
  exact ⟨heq.1.symm, heq.2.symm⟩

end StrongNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
