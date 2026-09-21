import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticReducedVolumeCovering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientSphericalCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryCylinderMass

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (b : ℝ) (hb : b < 0) (p : F.M)
    (hmass : (1 / 2 : ℝ≥0∞) < asymptoticReducedVolume F.S b p) :
    Nonempty (DifferentialGeometry.Topology.SphereThree ≃ₘ⟮(𝓡 3), I3⟯ F.M) := by
  let : ConnectedSpace F.M := hF.connected
  obtain ⟨⟨q, hq, hsurj, hd⟩, _⟩ := exists_spherical_cover_of_compact_ancientKappa F hF
  obtain ⟨x, hx⟩ := hsurj p
  have hinj : Function.Injective q :=
    covering_injective_of_one_half_lt_asymptoticReducedVolume F.S F.isSolution q hd hq
      b (fun t ht => by simpa only [ancientTimeInterval_regular, Set.mem_Iio] using ht.trans_lt hb)
      (fun t ht y => ancientKappa_scalar_nonneg F hF (ht.trans hb.le) y) x
      (by simpa only [hx] using hmass)
  exact ⟨hd.diffeomorphOfBijective ⟨hinj, hsurj⟩⟩

theorem nonempty_diffeomorph_sphere_of_compact_ordinary_cylinder
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (b : ℝ) (hb : b < 0) (p : F.M)
    (P : PointedRiemannianManifold (𝓡 3)) (g : SmoothRiemannianMetric (𝓡 3) P.M)
    (f : C^∞⟮(𝓡 3), P.M; ℝ⟯)
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, (𝓡 3)⟯ P.M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = scalarOneShrinkingCylinderMetric 0 (by norm_num))
    (hpotential : ∀ z : SpatialNeckCylinder, f (d z) = 1 + z.2 ^ 2 / 4)
    (hmass : normalizedShrinkerMass g f = asymptoticReducedVolume F.S b p) :
    Nonempty (DifferentialGeometry.Topology.SphereThree ≃ₘ⟮(𝓡 3), I3⟯ F.M) := by
  exact nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume F hF b hb p
    (one_half_lt_asymptoticReducedVolume_of_ordinary_cylinder F.S b p P g f d
      hmetric hpotential hmass)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
