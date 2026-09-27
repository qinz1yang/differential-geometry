import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EscapingSpatialNeckCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckWitnessConversion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.OrientedCylinderExclusion
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactScalarBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hbase : PointedFlowScalarAtBase F 1)
    (hnoncompact : NoncompactSpace F.M) {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X (F.atTime 0) subseq)
    (orient : ∀ i, TangentOrientationSection (X.obj i).M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon < 1 / 11) :
    ∃ p : F.M, Nonempty (SpatialNeck (F.S.base.metric 0) epsilon p) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rcases (xor_iff_or_and_not_and _ _).mp
      (ancientKappa_three_dimensional_split_branch F hF hdim) with ⟨hbranch, _⟩
  rcases hbranch with hpositive | ⟨C, hmodel⟩
  · have hsec : HasPositiveSectionalCurvature (F.S.base.metric 0) :=
      (hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (F.S.base.metric 0) hdim).mpr (hpositive 0 le_rfl)
    obtain ⟨mark, centers, necks, _, _⟩ :=
      ancient_kappa_three_exists_escaping_spatial_neck_centers_of_positive_sectional
        F hF hnoncompact hsec F.basepoint hepsilon
    obtain ⟨W⟩ := necks 0
    obtain ⟨nk, _⟩ := W.exists_spatialNeck hepsilon hsmall le_rfl
    exact ⟨centers 0, ⟨nk⟩⟩
  · rcases hmodel with htrivial | hantipodal | hdiagonal
    · obtain ⟨mark, d, hmarked, hmetric, hnecks⟩ :=
        exists_strongNeck_of_shrinkingCylinderCover_trivialModel F C htrivial hbase
      obtain ⟨nk, _, _⟩ := hnecks epsilon hepsilon hsmall
      exact ⟨F.basepoint, ⟨nk.toSpatialNeck⟩⟩
    · obtain ⟨d, hd⟩ := hantipodal.1
      exact (pointedLimit_not_antipodalProduct_diffeomorph Phi orient ⟨d⟩).elim
    · exact exists_spatialNeck_of_shrinkingCylinderCover_diagonalModel
        F C hdiagonal hbase hepsilon hsmall

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hbase : PointedFlowScalarAtBase F 1)
    (hnoncompact : NoncompactSpace F.M)
    {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X (F.atTime 0) subseq)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (orient : ∀ i, TangentOrientationSection (X.obj i).M)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ (p : F.M) (r c B : ℝ), 0 < r ∧ 0 < c ∧ 0 < B ∧
      ∀ᶠ i in atTop,
        Phi.map i p ∈ riemannianClosedBallOf (X.obj (subseq i)).metric
          (X.obj (subseq i)).basepoint r ∧
        c ≤ metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) ∧
        metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) ≤ B ∧
        Nonempty (SpatialNeck (X.obj (subseq i)).metric (2 * alpha) (Phi.map i p)) := by
  have htol : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  obtain ⟨p, ⟨nk⟩⟩ := exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit
    F hF hbase hnoncompact Phi orient (neckModelTolerance_pos ha) htol
  let _ : PreconnectedSpace (F.atTime 0).M := hF.connected.toPreconnectedSpace
  have hcomplete : MetricComplete (F.atTime 0) := hF.complete 0 (by simp)
  have href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    exact canonicalSourceData_referenceMetric_eq_limitMetric Phi i
  obtain ⟨r, hr, hcapture⟩ := Phi.exists_eventually_image_compact_subset_ball
    C href hcomplete (K := {p}) isCompact_singleton
  let q := metricScalarAt (F.S.base.metric 0) p
  have hq : 0 < q := nk.Q_pos
  have hscalar := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical p
  have hlow : ∀ᶠ i in atTop, q / 2 < metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) :=
    hscalar.eventually (Ioi_mem_nhds (by change q / 2 < q; linarith))
  have hhigh : ∀ᶠ i in atTop, metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) < 2 * q :=
    hscalar.eventually (Iio_mem_nhds (by change q < 2 * q; linarith))
  refine ⟨p, r, q / 2, 2 * q, hr, by positivity, by positivity, ?_⟩
  filter_upwards [hcapture, hlow, hhigh,
    nk.eventually_transport_of_metric_convergence C hcanonical ha hsmall]
    with i hc hl hh hn
  exact ⟨hc.2 ⟨p, mem_singleton p, rfl⟩, hl.le, hh.le, ⟨hn.choose⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_uniform_compact_or_spatial_neck_of_oriented_ancient_kappa
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution kappa F → PointedFlowScalarAtBase F 1 →
        TangentOrientationSection F.M →
        (CompactSpace F.M ∧ ∀ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint r ∧
          C⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ C) ∨
        ∃ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint r ∧
          C⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ C ∧
          Nonempty (SpatialNeck (F.S.base.metric 0) (2 * alpha) p) := by
  classical
  by_contra hnone
  have hbad (n : ℕ) : ∃ F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
      ∃ o : TangentOrientationSection F.M,
      IsAncientKappaSolution kappa F ∧ PointedFlowScalarAtBase F 1 ∧
      ¬ ((CompactSpace F.M ∧ ∀ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint ((n : ℝ) + 1) ∧
          ((n : ℝ) + 1)⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ (n : ℝ) + 1) ∨
        ∃ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint ((n : ℝ) + 1) ∧
          ((n : ℝ) + 1)⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ (n : ℝ) + 1 ∧
          Nonempty (SpatialNeck (F.S.base.metric 0) (2 * alpha) p)) := by
    by_contra hno
    push Not at hno
    exact hnone ⟨(n : ℝ) + 1, (n : ℝ) + 1, by positivity, by positivity,
      fun F hF hbase o => hno F o hF hbase⟩
  choose X orient hX hbase hbad using hbad
  obtain ⟨L, phi, hphi, Phi, hL, hLbase, hKL, hconv, hcmp⟩ :=
    exists_ancientKappa_fixed_kappa_compactness X hX hbase
  let F := Phi.atTime (X := ancientPointedFlowSeq X) (L := L) 0
  obtain ⟨C0, hC0⟩ := hconv 0 le_rfl
  have hthreshold : Tendsto (fun i => (phi i : ℝ) + 1) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).comp hphi.tendsto_atTop
  by_cases hcompact : CompactSpace L.M
  · let _ : PreconnectedSpace (L.atTime (I := I3) 0).M := hL.connected.toPreconnectedSpace
    have hcompact0 : CompactSpace (L.atTime (I := I3) 0).M := hcompact
    let _ : CompactSpace (L.atTime (I := I3) 0).M := hcompact0
    obtain ⟨r, c, B, hr, hc, hB, hmodels⟩ :=
      exists_eventually_scalar_bounds_and_bounded_radius_of_compact_positive_limit
        (L := L.atTime (I := I3) 0) F C0 hC0
        (fun i => (hX (phi i)).connected.toPreconnectedSpace)
        (fun p => ancientKappa_scalar_pos L hL le_rfl p)
    have hlarge : ∀ᶠ i in atTop, max r (max B c⁻¹) ≤ (phi i : ℝ) + 1 :=
      hthreshold.eventually (eventually_ge_atTop _)
    obtain ⟨i, hi, hlargei⟩ := (hmodels.and hlarge).exists
    have hinv : ((phi i : ℝ) + 1)⁻¹ ≤ c := by
      have hle : c⁻¹ ≤ (phi i : ℝ) + 1 := (le_max_right B c⁻¹).trans
        ((le_max_right r (max B c⁻¹)).trans hlargei)
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hc) hle
    apply hbad (phi i)
    refine Or.inl ⟨hi.1, ?_⟩
    intro p
    exact ⟨riemannianClosedBallOf_mono _ _ ((le_max_left _ _).trans hlargei) (hi.2 p).1,
      hinv.trans (hi.2 p).2.1, (hi.2 p).2.2.trans ((le_max_left B c⁻¹).trans
        ((le_max_right r (max B c⁻¹)).trans hlargei))⟩
  · have hnoncompact : NoncompactSpace L.M := ⟨fun h => hcompact ⟨h⟩⟩
    obtain ⟨p, r, c, B, hr, hc, hB, hcenters⟩ :=
      exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit
        L hL hLbase hnoncompact F C0 hC0 orient ha hsmall
    have hlarge : ∀ᶠ i in atTop, max r (max B c⁻¹) ≤ (phi i : ℝ) + 1 :=
      hthreshold.eventually (eventually_ge_atTop _)
    obtain ⟨i, hi, hlargei⟩ := (hcenters.and hlarge).exists
    have hinv : ((phi i : ℝ) + 1)⁻¹ ≤ c := by
      have hle : c⁻¹ ≤ (phi i : ℝ) + 1 := (le_max_right B c⁻¹).trans
        ((le_max_right r (max B c⁻¹)).trans hlargei)
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hc) hle
    apply hbad (phi i)
    refine Or.inr ⟨F.map i p, ?_, hinv.trans hi.2.1, ?_, hi.2.2.2⟩
    · exact riemannianClosedBallOf_mono _ _ ((le_max_left _ _).trans hlargei) hi.1
    · exact hi.2.2.1.trans ((le_max_left B c⁻¹).trans
        ((le_max_right r (max B c⁻¹)).trans hlargei))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
