import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckImageRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedInverseComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {L : PointedRiemannianManifold.{u, 0, 0} I3} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps X L subseq}

theorem eventually_spatialNeck_inverse_transport_on_compact
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧ ∀ x ∈ K,
      2 ≤ metricScalarAt L.metric x →
      ∀ A : Set L.M, A ⊆ interior K →
      ∀ nk : SpatialNeck (X.obj (subseq k)).metric
        (neckModelTolerance alpha) (Phi.map k x),
      (∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ Phi.map k '' A) →
      ∃ nk' : SpatialNeck L.metric (2 * alpha) x,
        nk'.map = partialDiffeomorphTransMixed nk.map (Phi.partialDiffeomorph k).symm := by
  filter_upwards [eventually_scalar_normalized_inverse_comparison C hcanonical K hK
    (⌈(2 * alpha)⁻¹⌉₊) (neckSourceTolerance_pos ha)] with k hk
  refine ⟨hk.1, ?_⟩
  intro x hx hscalar A hA nk houter
  obtain ⟨hq, hcmp⟩ := hk.2 x hx hscalar
  obtain ⟨cmp⟩ := hcmp A hA
  have htarget : Phi.map k '' A ⊆ (Phi.partialDiffeomorph k).symm.source := by
    rintro y ⟨z, hz, rfl⟩
    exact (Phi.partialDiffeomorph k).map_source (hk.1 (interior_subset (hA hz)))
  have hbase : (Phi.partialDiffeomorph k).symm (Phi.map k x) = x :=
    (Phi.partialDiffeomorph k).left_inv (hk.1 hx)
  exact nk.exists_transport_of_local_comparisons
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hscalar)
    (Phi.partialDiffeomorph k).symm cmp ha hsmall
    (neckSourceTolerance_pos ha).le le_rfl le_rfl hbase houter htarget

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {L : PointedRiemannianManifold.{u, 0, 0} I3} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps X L subseq}

theorem eventually_spatialNeck_inverse_transport_of_mem_closedBall
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete L)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    ∀ᶠ k in atTop, ∀ x ∈ Phi.source k,
      Phi.map k x ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho →
      2 ≤ metricScalarAt L.metric x →
      ∀ nk : SpatialNeck (X.obj (subseq k)).metric
        (neckModelTolerance alpha) (Phi.map k x),
      ∃ nk' : SpatialNeck L.metric (2 * alpha) x,
        nk'.map = partialDiffeomorphTransMixed nk.map (Phi.partialDiffeomorph k).symm := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  have hba : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  obtain ⟨R, hR, hneck⟩ := exists_uniform_spatial_neck_image_radius
    (neckModelTolerance_pos ha) hba
  have hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    exact canonicalSourceData_referenceMetric_eq_limitMetric Phi k
  obtain ⟨hAcompact, k0, hk0⟩ := KappaSolutions.exists_pointed_inverse_capture_at
    C hreference hcomplete L.basepoint (s := rho + R) (add_nonneg hrho hR.le)
    (show (0 : ℝ) < 1 by norm_num)
  let A := riemannianClosedBallOf L.metric L.basepoint ((1 + 1) * (rho + R))
  obtain ⟨K, hK, hAK⟩ := exists_compact_superset hAcompact
  have hAK' : A ⊆ interior K := hAK
  obtain ⟨k1, hk1⟩ := KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK 1 zero_lt_one
  filter_upwards [eventually_spatialNeck_inverse_transport_on_compact C hcanonical K hK
    ha (by linarith), eventually_ge_atTop k0, eventually_ge_atTop k1]
    with k htransfer hk hscalarIndex
  intro x hx hxball hscalar nk
  have hcapture : ∀ z ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (rho + R),
      z ∈ (Phi.partialDiffeomorph k).target ∧
        (Phi.partialDiffeomorph k).symm z ∈ A := by
    intro z hz
    have hbase : Phi.map k L.basepoint = (X.obj (subseq k)).basepoint :=
      Phi.basepoint_map k
    exact hk0 k hk z (by simpa only [hbase] using hz)
  have hxA : x ∈ A := by
    have hh := (hcapture (Phi.map k x)
      (riemannianClosedBallOf_mono _ _ (by linarith : rho ≤ rho + R) hxball)).2
    have hleft : (Phi.partialDiffeomorph k).symm (Phi.map k x) = x :=
      (Phi.partialDiffeomorph k).left_inv hx
    rwa [hleft] at hh
  have hq : 1 ≤ metricScalarAt (X.obj (subseq k)).metric (Phi.map k x) := by
    have hdiff := (abs_lt.mp ((hk1 k hscalarIndex).2 x
      (interior_subset (hAK' hxA)))).1
    linarith
  apply htransfer.2 x (interior_subset (hAK' hxA)) hscalar A hAK' nk
  intro y hy
  have hscaled := hneck (X.obj (subseq k)).M (X.obj (subseq k)).metric
    (Phi.map k x) nk y hy
  have hsqrt : 1 ≤ Real.sqrt (metricScalarAt (X.obj (subseq k)).metric (Phi.map k x)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have hnear : nk.map y ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
      (Phi.map k x) R := by
    rw [← riemannianClosedBallOf_scaleMetric
      (metricScalarAt (X.obj (subseq k)).metric (Phi.map k x)) nk.Q_pos]
    exact hscaled.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have houter : nk.map y ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (rho + R) := by
    have hh := (riemannianEDistOf_triangle (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (Phi.map k x) (nk.map y)).trans
      (add_le_add hxball hnear)
    rwa [← ENNReal.ofReal_add hrho hR.le] at hh
  obtain ⟨htarget, hinverse⟩ := hcapture (nk.map y) houter
  exact ⟨(Phi.partialDiffeomorph k).symm (nk.map y), hinverse,
    (Phi.partialDiffeomorph k).right_inv htarget⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
