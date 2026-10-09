import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckRays
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EscapingSpatialNeckCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.DiagonalCylinderRayAngle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch

noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_trivial_shrinkingCylinderCover_of_rays_comparisonAngle_lower
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hP : IsAncientKappaSolution kappa P) (hbase : PointedFlowScalarAtBase P 1)
    (o : TangentOrientationSection P.M) (a b : ℝ≥0 → P.M)
    (ha : ∀ s t, metricDistance (P.S.base.metric 0) (a s) (a t) = dist s t)
    (hb : ∀ s t, metricDistance (P.S.base.metric 0) (b s) (b t) = dist s t)
    (ha0 : a 0 = P.basepoint) (hb0 : b 0 = P.basepoint)
    {theta : ℝ} (htheta : 0 < theta)
    (hangle : ∀ᶠ r : ℝ≥0 in atTop, theta ≤ comparisonAngle r r
      (metricDistance (P.S.base.metric 0) (a r) (b r))) :
    ∃ C : ShrinkingCylinderCover P, C.TrivialModel := by
  classical
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : ConnectedSpace P.M := hP.connected
  let g := P.S.base.metric 0
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I3 P.M
  let _ : T3Space P.M := inferInstance
  let _ : RiemannianBundle (fun z : P.M => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : P.M => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  let _ : EMetricSpace P.M := EMetricSpace.ofRiemannianMetric I3 P.M
  let _ : CompleteSpace P.M := hP.complete 0 (by simp)
  have hEnorm : IsMetricNorm (I := I3) g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I3) g z v
  let _ : MetricSpace P.M := riemMetricSpace (I := I3) (M := P.M)
  let _ : IsRiemannianManifold I3 P.M := ⟨fun z w => by
    rw [edist_dist, riemMetric_dist_eq (I := I3)]
    exact ENNReal.ofReal_toReal
      (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
        (I := I3) z w)⟩
  have hdist (z w : P.M) : dist z w = metricDistance g z w := by
    rw [riemMetric_dist_eq (I := I3), metricDistance,
      riemannianEDistOf_eq_riemannianEDist g hEnorm]
  have ha' : Isometry a := Isometry.of_dist_eq fun s t => (hdist _ _).trans (ha s t)
  have hb' : Isometry b := Isometry.of_dist_eq fun s t => (hdist _ _).trans (hb s t)
  have harad (r : ℝ≥0) : metricDistance g P.basepoint (a r) = r := by
    rw [← ha0, ha]
    change |(0 : ℝ) - r| = r
    simp
  have hbrad (r : ℝ≥0) : metricDistance g P.basepoint (b r) = r := by
    rw [← hb0, hb]
    change |(0 : ℝ) - r| = r
    simp
  have hnoncompact : NoncompactSpace P.M := ⟨by
    intro hc
    obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall P.basepoint).mp hc.isBounded
    let r : ℝ≥0 := ⟨|B| + 1, by positivity⟩
    have hh : dist (a r) P.basepoint ≤ B := hB (mem_univ _)
    rw [dist_comm, hdist, harad] at hh
    change |B| + 1 ≤ B at hh
    linarith [le_abs_self B]⟩
  rcases (xor_iff_or_and_not_and _ _).mp
      (ancientKappa_three_dimensional_split_branch P hP (by simp [ThreeSpace])) with ⟨hbranch, _⟩
  rcases hbranch with hpositive | ⟨C, hmodel⟩
  · have hsec : HasPositiveSectionalCurvature g :=
      (hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        g (by simp [ThreeSpace])).mpr (hpositive 0 le_rfl)
    obtain ⟨mark, centers, hnecks, hescape, hscaled⟩ :=
      ancient_kappa_three_exists_escaping_spatial_neck_centers_of_positive_sectional
        P hP hnoncompact hsec P.basepoint spatialNeckControlEpsilon_pos
    let W (i : ℕ) := Classical.choice (hnecks i)
    have hescape' : Tendsto (fun i => dist P.basepoint (centers i)) atTop atTop := by
      simpa only [hdist, metricDistance, g] using hescape
    have hscaled' : Tendsto (fun i => Real.sqrt (metricScalarAt g (centers i)) *
        dist P.basepoint (centers i)) atTop atTop := by
      simpa only [hdist, metricDistance, g, SolutionOn.scalar, SolutionFamily.scalar] using hscaled
    have hzero := tendsto_rays_comparisonAngle_zero_of_spatialNecks W hEnorm le_rfl hsec
      P.basepoint hescape' hscaled' ha' hb' ha0 hb0
    have hradii : Tendsto (fun i => nndist P.basepoint (centers i)) atTop atTop :=
      NNReal.tendsto_coe_atTop.mp hescape'
    have hlower : ∀ᶠ i in atTop, theta ≤ comparisonAngle
        (dist P.basepoint (centers i)) (dist P.basepoint (centers i))
        (dist (a (nndist P.basepoint (centers i))) (b (nndist P.basepoint (centers i)))) := by
      filter_upwards [hradii.eventually hangle] with i hi
      simpa only [coe_nndist, hdist, g] using hi
    exact (not_le_of_gt htheta (ge_of_tendsto hzero hlower)).elim
  · rcases hmodel with htrivial | hantipodal | hdiagonal
    · exact ⟨C, htrivial⟩
    · exact (ShrinkingCylinderCover.not_antipodalProductModel P C o hantipodal).elim
    · apply (C.not_eventually_comparisonAngle_lower_of_diagonalModel hdiagonal hbase
        P.basepoint a b harad hbrad htheta).elim
      exact hangle

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
