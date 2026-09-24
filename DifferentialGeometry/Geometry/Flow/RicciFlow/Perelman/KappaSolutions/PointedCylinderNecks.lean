import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeckDetection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckDetection

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance pairedSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem pointedCylinderFlowLimit_eventually_neckWitnesses
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    (hD : X.D = ancientTimeInterval)
    (hscalar : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hconvergence : ∀ K : Set L.M, IsCompact K → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ i in atTop, Nonempty (MetricComparisonOn L.S.base.metric
        (X.term (phi i)).S.base.metric (Phi.map i) K (Icc (-1 : ℝ) 0) order delta))
    (C0 : MetricConvergenceData (I := I3) (Phi.atTime (L := L) 0))
    (hC0 : ∀ k, C0.domain k = CanonicalMetricCompactness.canonicalSourceData
      (I := I3) (Phi.atTime (L := L) 0) k)
    (hcomplete : ∀ i, MetricComplete ((X.atZero (I := I3)).obj i))
    (yStar : SpatialNeckSphere)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : ∀ s : ℝ, ∀ hs : s ≤ 0,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
        scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num)))
    (epsilon eta : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (heta : 0 < eta) :
    ∀ᶠ i in atTop,
      ∃ W : StrongNeckWitness (X.term (phi i)).S yStar
          (X.term (phi i)).basepoint 0 epsilon,
        ∃ V : SpatialNeckWitness ((X.term (phi i)).S.base.metric 0) yStar
            (X.term (phi i)).basepoint eta,
          (∀ z : spatialNeckBuffer epsilon,
            W.embedding z = Phi.map i (e (z : SpatialNeckCylinder))) ∧
          (∀ z : spatialNeckBuffer eta,
            V.embedding z = Phi.map i
              (e (cylinderAxialScale (Real.sqrt 2) (by positivity)
                (z : SpatialNeckCylinder)))) ∧
          W.embedding '' spatialNeckCentralDomain epsilon = V.centralSphere := by
  have hstrong := pointedCylinderFlowLimit_eventually_strongNeckWitness Phi hD hscalar
    hconvergence yStar e hmarked hmetric epsilon hepsilon hepsilon_one
  have hzero : DifferentialGeometry.Diffeomorph.pullbackMetricCross
      (L.S.base.metric 0) e = doubleSphereCylinderMetric :=
    (hmetric 0 le_rfl).trans scalarOneShrinkingCylinderMetric_zero
  obtain ⟨i0, hi0⟩ := pointedCylinderLimit_eventually_spatialNeckWitness
    (Phi.atTime (L := L) 0) C0 hC0 (by simp [ThreeSpace]) hcomplete hscalar
    yStar e hmarked hzero eta heta
  filter_upwards [hstrong, eventually_ge_atTop i0] with i hi hindex
  obtain ⟨W, hW⟩ := hi
  have hiV : ∃ V : SpatialNeckWitness ((X.term (phi i)).S.base.metric 0) yStar
      (X.term (phi i)).basepoint eta,
      ∀ z : spatialNeckBuffer eta, V.embedding z = Phi.map i
        (e (cylinderAxialScale (Real.sqrt 2) (by positivity) (z : SpatialNeckCylinder))) :=
    hi0 i hindex
  obtain ⟨V, hV⟩ := hiV
  refine ⟨W, V, hW, hV, ?_⟩
  rw [V.centralSphere_eq_range]
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.val.1, ?_⟩
    change V.embedding (spatialNeckCentralPoint eta V.epsilon_pos z.val.1) = W.embedding z
    rw [hV, hW]
    change Phi.map i (e (cylinderAxialScale (Real.sqrt 2) (by positivity) (z.val.1, 0))) = _
    rw [cylinderAxialScale_central]
    exact congrArg (fun x => Phi.map i (e x)) (Prod.ext rfl hz.symm)
  · rintro ⟨y, rfl⟩
    refine ⟨spatialNeckCentralPoint epsilon hepsilon y, rfl, ?_⟩
    change W.embedding (spatialNeckCentralPoint epsilon hepsilon y) =
      V.embedding (spatialNeckCentralPoint eta V.epsilon_pos y)
    rw [hW, hV]
    change Phi.map i (e (y, 0)) =
      Phi.map i (e (cylinderAxialScale (Real.sqrt 2) (by positivity) (y, 0)))
    rw [cylinderAxialScale_central]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
