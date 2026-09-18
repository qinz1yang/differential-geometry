import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.InverseSpatialNeckTransfer

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

theorem exists_eventually_spatialNeck_scalar_upper_bound :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 / 32 ∧
      ∀ (X : PointedRiemannianSeq.{u, 0, 0} I3)
        (L : PointedRiemannianManifold.{u, 0, 0} I3) (subseq : ℕ → ℕ)
        (Phi : PointedRiemannianConvergenceMaps X L subseq)
        (C : MetricConvergenceData Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) →
        MetricComplete L → ConnectedSpace L.M →
        DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature L.metric →
        ∃ B : ℝ, 0 < B ∧ ∀ rho : ℝ, 0 ≤ rho →
          ∀ᶠ k in atTop, ∀ v ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
            (X.obj (subseq k)).basepoint rho,
            SpatialNeck (X.obj (subseq k)).metric (neckModelTolerance alpha) v →
              metricScalarAt (X.obj (subseq k)).metric v ≤ B := by
  obtain ⟨eta₀, heta₀, hbound⟩ := exists_spatialNeck_scalar_upper_bound
  let alpha : ℝ := min (eta₀ / 4) (1 / 64)
  have ha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have hsmall : alpha < 1 / 32 := (min_le_right _ _).trans_lt (by norm_num)
  have htol : 2 * alpha ≤ eta₀ := by
    have hh := min_le_left (eta₀ / 4) (1 / 64)
    change alpha ≤ eta₀ / 4 at hh
    linarith
  refine ⟨alpha, ha, hsmall, ?_⟩
  intro X L subseq Phi C hcanonical hcomplete hconn hsec
  let _ : ConnectedSpace L.M := hconn
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨B₀, hB₀⟩ := hbound L.M L.metric ⟨hcomplete.complete⟩ hsec
  refine ⟨max 3 (B₀ + 1), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro rho hrho
  have hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    exact canonicalSourceData_referenceMetric_eq_limitMetric Phi k
  obtain ⟨hK, k0, hk0⟩ := KappaSolutions.exists_pointed_inverse_capture_at C hreference
    hcomplete L.basepoint hrho (show (0 : ℝ) < 1 by norm_num)
  let K := riemannianClosedBallOf L.metric L.basepoint ((1 + 1) * rho)
  obtain ⟨k1, hk1⟩ := KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK 1 zero_lt_one
  filter_upwards [eventually_spatialNeck_inverse_transport_of_mem_closedBall
    C hcanonical hcomplete ha hsmall rho hrho, eventually_ge_atTop k0,
    eventually_ge_atTop k1] with k htransfer hk hk'
  intro v hv nk
  have hv' : v ∈ riemannianClosedBallOf (X.obj (subseq k)).metric
      (Phi.map k L.basepoint) rho := by
    have hbase : Phi.map k L.basepoint = (X.obj (subseq k)).basepoint :=
      Phi.basepoint_map k
    simpa only [hbase] using hv
  obtain ⟨htarget, hxK⟩ := hk0 k hk v hv'
  let x := (Phi.partialDiffeomorph k).symm v
  have hx : x ∈ Phi.source k := (Phi.partialDiffeomorph k).map_target htarget
  have hmap : Phi.map k x = v := (Phi.partialDiffeomorph k).right_inv htarget
  have herr : |metricScalarAt (X.obj (subseq k)).metric v - metricScalarAt L.metric x| < 1 := by
    simpa only [hmap] using (hk1 k hk').2 x hxK
  by_cases hscalar : 2 ≤ metricScalarAt L.metric x
  · have nkx : SpatialNeck (X.obj (subseq k)).metric (neckModelTolerance alpha)
        (Phi.map k x) := hmap.symm ▸ nk
    obtain ⟨nk', _hmap'⟩ := htransfer x hx (by simpa only [hmap] using hv) hscalar nkx
    have hlimit := hB₀ x (2 * alpha) htol nk'
    have hsource : metricScalarAt (X.obj (subseq k)).metric v ≤ B₀ + 1 := by
      linarith [(abs_lt.mp herr).2]
    exact hsource.trans (le_max_right _ _)
  · have hsource : metricScalarAt (X.obj (subseq k)).metric v ≤ 3 := by
      linarith [(abs_lt.mp herr).2]
    exact hsource.trans (le_max_left _ _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
