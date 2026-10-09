import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.InverseSpatialNeckTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalRadialReserve
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage

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

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem metricScalarAt_le_of_eventually_comparable_spatialNeck
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {L : PointedRiemannianManifold.{u, 0, 0} I3} {subseq : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L subseq)
    (conv : MetricConvergenceData F)
    (hcanonical : ∀ i, conv.domain i =
      CanonicalMetricCompactness.canonicalSourceData F i)
    (hcomplete : MetricComplete L) (hconn : PreconnectedSpace L.M)
    {eps A B C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hbound : ∀ rho : ℝ, 0 ≤ rho → ∀ᶠ i in atTop,
      ∀ v ∈ riemannianClosedBallOf (X.obj (subseq i)).metric
        (X.obj (subseq i)).basepoint rho,
        SpatialNeck (X.obj (subseq i)).metric eps v →
          metricScalarAt (X.obj (subseq i)).metric v ≤ B)
    (hcenters : ∀ x : L.M, A < metricScalarAt L.metric x → ∀ᶠ i in atTop,
      ∃ v : (X.obj (subseq i)).M,
        v ∈ riemannianClosedBallOf (X.obj (subseq i)).metric (F.map i x) r ∧
        Nonempty (SpatialNeck (X.obj (subseq i)).metric eps v) ∧
        metricScalarAt (X.obj (subseq i)).metric (F.map i x) ≤
          C * metricScalarAt (X.obj (subseq i)).metric v) :
    ∀ x : L.M, metricScalarAt L.metric x ≤ max A (C * B) := by
  let _ : PreconnectedSpace L.M := hconn
  have href : ∀ i, (conv.domain i).referenceMetric = (conv.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    exact canonicalSourceData_referenceMetric_eq_limitMetric F i
  intro x
  by_cases hx : metricScalarAt L.metric x ≤ A
  · exact hx.trans (le_max_left _ _)
  have hAx : A < metricScalarAt L.metric x := lt_of_not_ge hx
  obtain ⟨rho, hrho, hcapture⟩ :=
    F.exists_eventually_image_compact_subset_ball conv href hcomplete
      (K := {x}) (isCompact_singleton : IsCompact ({x} : Set L.M))
  have hsource : ∀ᶠ i in atTop,
      metricScalarAt (X.obj (subseq i)).metric (F.map i x) ≤ C * B := by
    filter_upwards [hcenters x hAx, hcapture, hbound (rho + r) (add_nonneg hrho.le hr)]
      with i hi hc hb
    obtain ⟨v, hv, ⟨neck⟩, hcompare⟩ := hi
    have hxball : F.map i x ∈ riemannianClosedBallOf (X.obj (subseq i)).metric
        (X.obj (subseq i)).basepoint rho := hc.2 ⟨x, mem_singleton x, rfl⟩
    have hvball : v ∈ riemannianClosedBallOf (X.obj (subseq i)).metric
        (X.obj (subseq i)).basepoint (rho + r) := by
      have htri := (riemannianEDistOf_triangle (X.obj (subseq i)).metric
        (X.obj (subseq i)).basepoint (F.map i x) v).trans (add_le_add hxball hv)
      rwa [← ENNReal.ofReal_add hrho.le hr] at htri
    exact hcompare.trans (mul_le_mul_of_nonneg_left (hb v hvball neck) hC)
  exact (le_of_tendsto
    (KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      conv hcanonical x) hsource).trans (le_max_right _ _)

theorem NormalizedSequence.metricScalarAt_le_of_eventually_canonicalWitness_neck_center
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (P : MetricCompactLimit (X.toFlowSequence.atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    (hconn : PreconnectedSpace P.limit.M)
    {eta A B C1 C2 : ℝ}
    (hbound : ∀ rho : ℝ, 0 ≤ rho → ∀ᶠ i in atTop,
      ∀ v ∈ riemannianClosedBallOf ((X.term (P.subseq i)).S.base.metric 0)
        (X.term (P.subseq i)).basepoint rho,
        SpatialNeck ((X.term (P.subseq i)).S.base.metric 0) eta v →
          (X.term (P.subseq i)).S.scalar 0 v ≤ B)
    (hcenters : ∀ x : P.limit.M, A < metricScalarAt P.limit.metric x → ∀ᶠ i in atTop,
      ∃ beta : ℝ, ∃ W : CanonicalWitness (X.term (P.subseq i)).S beta C1 C2
          (P.maps.map i x) 0,
        ∃ v ∈ W.domain.carrier, Nonempty (StrongNeck (X.term (P.subseq i)).S eta v 0)) :
    ∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ max (max A 2) (C2 * B) := by
  by_cases hex : ∃ x : P.limit.M, A < metricScalarAt P.limit.metric x
  · obtain ⟨x0, hx0⟩ := hex
    obtain ⟨i0, beta0, W0, v0, hv0, neck0⟩ := (hcenters x0 hx0).exists
    have hsqrtpos : 0 < Real.sqrt ((X.term (P.subseq i0)).S.scalar 0
        (P.maps.map i0 x0)) := Real.sqrt_pos.mpr W0.Q_pos
    have hrpos : 0 < W0.radius :=
      (inv_pos.mpr hsqrtpos).trans_le W0.radius_lower
    have hC1 : 0 ≤ C1 :=
      ((mul_pos hrpos hsqrtpos).trans_le
        ((le_div_iff₀ hsqrtpos).mp W0.radius_upper)).le
    have hC2 : 0 ≤ C2 := zero_le_one.trans W0.one_le_comparison_constant
    apply metricScalarAt_le_of_eventually_comparable_spatialNeck
      P.maps P.convergence.metrics hcanonical P.limit_complete hconn hC2
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC1) hbound
    intro x hx
    have hAx : A < metricScalarAt P.limit.metric x := (le_max_left A 2).trans_lt hx
    have hOne : 1 < metricScalarAt P.limit.metric x :=
      (by norm_num : (1 : ℝ) < 2).trans ((le_max_right A 2).trans_lt hx)
    have hscalar : ∀ᶠ i in atTop,
        1 < (X.term (P.subseq i)).S.scalar 0 (P.maps.map i x) :=
      (KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
        P.convergence.metrics hcanonical x).eventually (Ioi_mem_nhds hOne)
    filter_upwards [hcenters x hAx, hscalar] with i hi hQ
    obtain ⟨beta, W, v, hv, ⟨neck⟩⟩ := hi
    refine ⟨v, W.domain_subset_closedBall_of_one_le_scalar hQ.le hv,
      ⟨neck.toSpatialNeck⟩, ?_⟩
    have hpos : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
    have hh := mul_le_mul_of_nonneg_left (W.scalar_bounds v hv).1 hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hh
  · intro x
    have hx : metricScalarAt P.limit.metric x ≤ A :=
      le_of_not_gt fun hx => hex ⟨x, hx⟩
    exact hx.trans ((le_max_left A 2).trans (le_max_left _ _))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
