import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckSides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardSubsequence

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.Geometry.Riemannian (IsMetricNorm)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology.SphereSeparation (axialZero)
open KappaSolutions (SpatialNeckSphere SpatialNeckWitness SpatialNeckSideData StrongNeckWitness
  spatialNeckBuffer spatialNeckCentralDomain spatialNeckControlEpsilon)

private local instance neckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun q : M => TangentSpace I3 q)]
  [IsRiemannianManifold I3 M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {h : SmoothRiemannianMetric I3 M}
  {marks : ℕ → SpatialNeckSphere} {centers : ℕ → M} {eps eta t : ℝ}

theorem exists_strongNeck_compactSide_contains_compact_of_disjoint_escaping_family
    (spatial : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) eta)
    (sides : ∀ i : ℕ, SpatialNeckSideData (spatial i))
    (strong : ∀ i : ℕ, StrongNeckWitness S (marks i) (centers i) t eps)
    (hsphere : ∀ i : ℕ,
      (strong i).embedding '' spatialNeckCentralDomain eps = (spatial i).centralSphere)
    (hEnorm : IsMetricNorm (I := I3) h)
    (heta : eta ≤ spatialNeckControlEpsilon) (heps : eps < 1 / 11)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I3) h)
    {c : ℝ≥0 → M} (hc : Isometry c)
    (hcores : Pairwise (fun i j : ℕ => Disjoint (spatial i).core (spatial j).core))
    (hescape : Tendsto centers atTop (cocompact M))
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (K : Set M) (hK : IsCompact K) :
    ∃ (i : ℕ) (nk : StrongNeck S eps (centers i) t),
      K ⊆ (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∧
      nk.map.source = spatialNeckBuffer eps ∧
      nk.map.target = range (strong i).embedding ∧
      nk.center = marks i ∧
      (∀ z : spatialNeckBuffer eps, nk.map z.val = (strong i).embedding z) ∧
      nk.map '' (univ ×ˢ ({0} : Set ℝ)) = (spatial i).centralSphere := by
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun q : M => TangentSpace I3 q) :=
    hEnorm.isContinuousRiemannianBundle
  obtain ⟨phi, _, _, hexhaust⟩ :=
    KappaSolutions.exists_outward_spatialNeck_exhaustion spatial sides
      hEnorm heta hsec hc hcores hescape
  obtain ⟨n, hn⟩ := (hexhaust K hK).exists
  obtain ⟨nk, hsource, htarget, hcenter, hmap, hcentral⟩ :=
    (strong (phi n)).exists_strongNeck heps
  have hsphereNk : nk.map '' (univ ×ˢ ({0} : Set ℝ)) =
      (spatial (phi n)).centralSphere := hcentral.trans (hsphere (phi n))
  have hside :=
    (nk.bicollar_zero_sides_eq_of_centralSphere_eq ψ (sides (phi n)) hsphereNk).1
  refine ⟨phi n, nk, ?_, hsource, htarget, hcenter, hmap, hsphereNk⟩
  rw [hside]
  exact hn

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
