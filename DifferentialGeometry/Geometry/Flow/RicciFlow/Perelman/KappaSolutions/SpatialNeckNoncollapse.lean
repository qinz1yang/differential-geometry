import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import DifferentialGeometry.Geometry.Neck.BallVolume

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_tensor_noncollapsed_of_eventually_spatialNeck_at_mapped_centers :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ {X : PointedRiemannianSeq.{u,0,0} (I := ThreeModel)}
        {L : PointedRiemannianManifold.{u,0,0} (I := ThreeModel)} {subseq : ℕ → ℕ}
        (Phi : PointedRiemannianConvergenceMaps (I := ThreeModel) X L subseq)
        (C : MetricConvergenceData Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) →
        MetricComplete (I := ThreeModel) L →
        (∀ z : L.M, ∀ᶠ i in atTop, ∃ eps : ℝ,
          Nonempty (SpatialNeck (X.obj (subseq i)).metric eps (Phi.map i z))) →
        ∀ (z : L.M) (r : ℝ), 0 < r →
          (∀ x ∈ riemannianBallOf L.metric z r,
            r ^ 4 * normSq0S L.metric x 4 (metricRm04At L.metric x) ≤ 1) →
          ENNReal.ofReal kappa * ENNReal.ofReal r ^ 3 ≤
            riemannianVolumeMeasure ThreeModel L.M L.metric (riemannianBallOf L.metric z r) := by
  obtain ⟨kappa,hkappa,hvolume⟩ := exists_pos_mul_cube_le_spatialNeck_ball_volume_of_curvature_bound.{u}
  refine ⟨kappa,hkappa,?_⟩
  intro X L subseq Phi C hcanonical hcomplete hneck
  have hlim := tensor_noncollapsed_of_eventually_pointed_canonical_convergence_at_mapped_centers
    C hcanonical hcomplete kappa ?_
  · simpa only [ThreeSpace, finrank_euclideanSpace_fin] using hlim
  · intro z r hr
    filter_upwards [hneck z] with i hi
    obtain ⟨eps,⟨nk⟩⟩ := hi
    intro hcurv
    have hcenter : Phi.map i z ∈ riemannianBallOf (X.obj (subseq i)).metric (Phi.map i z) r := by
      change riemannianEDistOf (X.obj (subseq i)).metric (Phi.map i z) (Phi.map i z) < ENNReal.ofReal r
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hr
    have hvol := hvolume nk r hr (hcurv _ hcenter)
    simpa only [ThreeSpace, finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow hr.le] using hvol

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
