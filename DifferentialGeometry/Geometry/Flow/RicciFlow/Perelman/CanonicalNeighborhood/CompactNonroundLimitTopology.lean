import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientTopology
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactGlobalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport

section
set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem nonempty_positiveComponent_of_compact_nonround_pointed_limit
    (X : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappa : ℕ → ℝ} (hX : ∀ i, IsAncientKappaSolution (kappa i) (X i))
    (hnotround : ∀ i, ¬ IsShrinkingSphericalSpaceFormFlow (X i))
    (orient : ∀ i, TangentOrientationSection (X i).M)
    (L : PointedRiemannianManifold.{u, 0, 0} I3) [CompactSpace L.M]
    {phi : ℕ → ℕ} (Phi : PointedRiemannianConvergenceMaps ⟨fun i => (X i).atTime 0⟩ L phi) :
    Nonempty (PositiveComponent (univ : Set L.M)) := by
  obtain ⟨N, hN⟩ := compactLimit_eventually_globalizes Phi (inferInstance : CompactSpace L.M)
    (fun i => (hX (phi i)).connected)
  obtain ⟨_hsrc, _htgt, e, _he, _hei, _hbase, hcompact⟩ := hN N le_rfl
  let _ : CompactSpace (X (phi N)).M := hcompact
  obtain ⟨data⟩ := nonempty_positiveComponent_of_compact_nonround_ancientKappa
    (X (phi N)) (hX (phi N)) (hnotround (phi N)) (orient (phi N))
  obtain ⟨data'⟩ := positiveComponent_transport_of_partialDiffeomorph data e.symm.toPartialDiffeomorph (subset_univ _)
  have himage : e.symm.toPartialDiffeomorph '' (univ : Set ((X (phi N)).atTime 0).M) = univ := by
    change e.symm '' (univ : Set ((X (phi N)).atTime 0).M) = univ
    rw [image_univ]
    exact e.symm.surjective.range_eq
  exact ⟨himage ▸ data'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
