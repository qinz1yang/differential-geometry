import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeTerminalExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDirectionCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndAngleMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornIntrinsicRays
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornTwoScale
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

attribute [local instance] FiniteHorn.ambient_metric
attribute [local instance] EndAngles.metric

structure AmbientEndIsometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) : Prop where
  deep : ∃ i, (∀ x ∈ H.subend i, ∀ y ∈ H.subend i,
      dist x y = dist (H.inclusion x) (H.inclusion y)) ∧
    ∀ x ∈ H.subend i, dist (x : UniformSpace.Completion W) H.endpoint =
      dist (H.inclusion x) H.ambient_end

omit [SigmaCompactSpace W] in
theorem finiteHorn_ambientEndIsometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) :
    AmbientEndIsometry H :=
  ⟨H.ambient_end_isometry⟩

omit [SigmaCompactSpace W] in
theorem finiteHorn_frontier_escape_of_ambientEndIsometry {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (hiso : AmbientEndIsometry H) :
    ∀ w : ℕ → W,
      Filter.Tendsto (fun i => (w i : UniformSpace.Completion W)) Filter.atTop
        (nhds H.endpoint) →
      ∀ R : ℝ, 0 < R → ∀ᶠ i in Filter.atTop, ∀ z ∈ H.outer_frontier,
        R * dist (w i : UniformSpace.Completion W) H.endpoint < dist (H.inclusion (w i)) z := by
  obtain ⟨i₀, -, hdist⟩ := hiso.deep
  obtain ⟨δ, hδ, hfar⟩ := H.frontier_far
  intro w hw R hR
  have hmem : ∀ᶠ i in Filter.atTop, w i ∈ H.subend i₀ :=
    finiteHorn_eventually_mem_subend g H hw i₀
  have hsmall : ∀ᶠ i in Filter.atTop,
      dist (w i : UniformSpace.Completion W) H.endpoint < δ / (R + 1) := by
    have hpos : 0 < δ / (R + 1) := div_pos hδ (by linarith)
    exact hw.eventually (Metric.ball_mem_nhds H.endpoint hpos)
  filter_upwards [hmem, hsmall] with i hi hsi
  intro z hz
  have hzδ : δ ≤ dist z H.ambient_end := hfar z hz
  have hri : dist (w i : UniformSpace.Completion W) H.endpoint =
      dist (H.inclusion (w i)) H.ambient_end := hdist (w i) hi
  have hkey : δ - dist (w i : UniformSpace.Completion W) H.endpoint ≤
      dist z (H.inclusion (w i)) := by
    have h := abs_dist_sub_le z (H.inclusion (w i)) H.ambient_end
    rw [← hri] at h
    have := (abs_le.mp h).2
    linarith
  have hexpand : R * dist (w i : UniformSpace.Completion W) H.endpoint <
      δ - dist (w i : UniformSpace.Completion W) H.endpoint := by
    have h := (lt_div_iff₀ (by linarith : (0 : ℝ) < R + 1)).mp hsi
    nlinarith
  rw [dist_comm (H.inclusion (w i)) z]
  linarith

theorem finite_horn_end_rays_of_ambientEndIsometry {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (hiso : AmbientEndIsometry H) : Nonempty (EndGeometry H) :=
  ⟨{ unique_endpoint := finiteHorn_unique_endpoint g H
     intrinsic_ambient := hiso.deep
     rays := finiteHorn_intrinsic_rays g H
     frontier_escape := finiteHorn_frontier_escape_of_ambientEndIsometry H hiso }⟩

theorem finite_horn_end_rays {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) :
    Nonempty (EndGeometry H) :=
  finite_horn_end_rays_of_ambientEndIsometry H (finiteHorn_ambientEndIsometry H)

noncomputable def hornRayApproximationDepth (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] : ℝ :=
  Classical.choose (exists_finiteHorn_ray_approximation_depth (W := W))

noncomputable def hornEndAngleDepth (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] : ℝ :=
  Classical.choose (finite_horn_end_angle_of_depth (W := W))

noncomputable def hornAngleComparisonDepth (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] : ℝ :=
  Classical.choose (finite_horn_endComparisonAngle_le_angle (W := W))

noncomputable def hornDepthThreshold (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] : ℝ :=
  max (max (hornRayApproximationDepth W) (hornEndAngleDepth W))
    (max (hornAngleComparisonDepth W) 1)

theorem hornRayApproximationDepth_pos (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] :
    0 < hornRayApproximationDepth W :=
  (Classical.choose_spec (exists_finiteHorn_ray_approximation_depth (W := W))).1

theorem hornEndAngleDepth_pos (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] :
    0 < hornEndAngleDepth W :=
  (Classical.choose_spec (finite_horn_end_angle_of_depth (W := W))).1

theorem hornAngleComparisonDepth_pos (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] :
    0 < hornAngleComparisonDepth W :=
  (Classical.choose_spec (finite_horn_endComparisonAngle_le_angle (W := W))).1

theorem hornRayApproximationDepth_le_hornDepthThreshold (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] :
    hornRayApproximationDepth W ≤ hornDepthThreshold W := by
  rw [hornDepthThreshold]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

theorem hornEndAngleDepth_le_hornDepthThreshold (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] :
    hornEndAngleDepth W ≤ hornDepthThreshold W := by
  rw [hornDepthThreshold]
  exact le_trans (le_max_right _ _) (le_max_left _ _)

theorem hornAngleComparisonDepth_le_hornDepthThreshold (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] :
    hornAngleComparisonDepth W ≤ hornDepthThreshold W := by
  rw [hornDepthThreshold]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem hornDepthThreshold_pos (W : Type u) [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] :
    0 < hornDepthThreshold W := by
  have h : 0 < hornRayApproximationDepth W := hornRayApproximationDepth_pos W
  exact lt_of_lt_of_le h (hornRayApproximationDepth_le_hornDepthThreshold W)

theorem finite_horn_ray_approximation {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H)
    (hdepth : hornRayApproximationDepth W ≤ H.collar_depth) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H a b lo hi) :=
  (Classical.choose_spec (exists_finiteHorn_ray_approximation_depth (W := W))).2 g H hdepth

theorem finite_horn_end_angle {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H)
    (hdepth : hornEndAngleDepth W ≤ H.collar_depth) : Nonempty (EndAngles H) :=
  (Classical.choose_spec (finite_horn_end_angle_of_depth (W := W))).2 g H hdepth


omit [SigmaCompactSpace W] in
theorem finite_horn_direction_compactness {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (angles : EndAngles H)
    (hnet : ScaleDirectionNet g H) (hsep : ScaleSeparatedEndRays g H) :
    letI := angles.metric
    TotallyBounded (Set.univ : Set angles.quotient) ∧
      CompactSpace (UniformSpace.Completion angles.quotient) ∧
      ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  have htb : TotallyBounded (Set.univ : Set angles.quotient) :=
    totallyBounded_quotient_of_scaleDirectionNet H angles hnet
  exact ⟨htb, compactSpace_completion_of_totallyBounded htb,
    exists_pos_angle_of_separatedEndRays H angles (separatedEndRays_of_scaleSeparated H angles hsep)⟩


theorem finite_horn_cone_convergence {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hreal : ConeDistanceRealization H angles ray d)
    (hdepth : hornAngleComparisonDepth W ≤ H.collar_depth) :
    Nonempty (AnnularConvergence H angles ray d) :=
  nonempty_annularConvergence_of_coneAnnulusRealization H angles ray d hd hzero
    (coneAnnulusRealization_of_coneDistanceRealization
      ((Classical.choose_spec (finite_horn_endComparisonAngle_le_angle (W := W))).2 g H hdepth
        angles)
      hreal)

omit [SigmaCompactSpace W] in
theorem nonempty_hornBarriers_of_neckSectionBarrier {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (barrier : NeckSectionBarrier H ray d) : Nonempty (HornBarriers H ray d) := by
  classical
  have hrange : ∀ i : ℕ, Set.range (fun p : Sphere 2 => (barrier.tube i).map (p, 1 / 2)) =
      (barrier.tube i).sectionSet (1 / 2) :=
    fun i => GlobalNeckTube.range_sectionMap (barrier.tube i) (1 / 2)
  refine ⟨{ sphere := fun i p => (barrier.tube i).map (p, 1 / 2)
            embedding := ?_
            smooth := ?_
            diameter_bound := ?_
            radial_barrier := ?_ }⟩
  · intro i
    have hmem : ∀ p : Sphere 2, (p, (1 / 2 : ℝ)) ∈ (barrier.tube i).map.source := by
      intro p
      rw [(barrier.tube i).source_eq]
      exact ⟨Set.mem_univ _, by norm_num⟩
    have hcont : Continuous (fun p : Sphere 2 => (barrier.tube i).map (p, 1 / 2)) := by
      exact ((barrier.tube i).map.contMDiffOn_toFun.continuousOn).comp_continuous
        (f := fun p : Sphere 2 => (p, (1 / 2 : ℝ))) (by fun_prop) (fun p => hmem p)
    have hinj : Function.Injective (fun p : Sphere 2 => (barrier.tube i).map (p, 1 / 2)) := by
      intro p q hpq
      have hp : (barrier.tube i).map.invFun
          ((barrier.tube i).map.toFun (p, (1 / 2 : ℝ))) = (p, (1 / 2 : ℝ)) :=
        (barrier.tube i).map.left_inv' (hmem p)
      have hq : (barrier.tube i).map.invFun
          ((barrier.tube i).map.toFun (q, (1 / 2 : ℝ))) = (q, (1 / 2 : ℝ)) :=
        (barrier.tube i).map.left_inv' (hmem q)
      have hpq' : (barrier.tube i).map.toFun (p, (1 / 2 : ℝ)) =
          (barrier.tube i).map.toFun (q, (1 / 2 : ℝ)) := hpq
      have h : (p, (1 / 2 : ℝ)) = (q, (1 / 2 : ℝ)) := by rw [← hp, hpq', hq]
      exact congrArg Prod.fst h
    exact (hcont.isClosedEmbedding hinj).isEmbedding
  · intro i
    have hmem : ∀ p : Sphere 2, (p, (1 / 2 : ℝ)) ∈ (barrier.tube i).map.source := by
      intro p
      rw [(barrier.tube i).source_eq]
      exact ⟨Set.mem_univ _, by norm_num⟩
    exact (barrier.tube i).map.contMDiffOn_toFun.comp_contMDiff
      (contMDiff_id.prodMk contMDiff_const) (fun p => hmem p)
  · obtain ⟨L, hL, hbound⟩ := barrier.section_diameter
    refine ⟨L, hL, ?_⟩
    filter_upwards [hbound] with i hi x hx
    exact hi x ((hrange i).symm ▸ hx)
  · intro eta heta heta'
    filter_upwards [barrier.separates eta heta heta'] with i hi c hc hd'
    obtain ⟨t, ht⟩ := hi c hc hd'
    exact ⟨t, (hrange i).symm ▸ ht⟩

theorem finite_horn_barriers {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) : Nonempty (HornBarriers H ray d) := by
  sorry

structure ScaleCurvatureUpperBound {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop where
  upper : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in Filter.atTop,
    metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ C

omit [SigmaCompactSpace W] in
theorem finite_horn_two_scale_comparison {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (_angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hupper : ScaleCurvatureUpperBound H ray d) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 ∧
      metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ C :=
  finite_horn_two_scale_comparison_of_upper_bound H ray d hd hzero hupper.upper

structure ConeFlowLimit (X : FlowSequence.{u}) where
  delta : ℝ
  delta_pos : 0 < delta
  flow : PointedFlowData.{u, 0, 0} I3 (RealTimeInterval.closed (-delta) 0 (by linarith))
  patch : Set flow.M
  open_patch : IsOpen patch
  compact_patch : IsCompact (closure patch)
  connected_patch : IsConnected patch
  base_mem : flow.basepoint ∈ patch
  cone : ConeChart (flow.S.base.metric 0) patch
  nonnegative : ∀ s ∈ Set.Icc (-delta) 0, SecLower (flow.S.base.metric s) 0 patch
  normalized : PointedFlowScalarAtBase flow 1
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale : ℕ → ℝ
  scale_pos : ∀ i, 0 < scale i
  scale_tendsto : Filter.Tendsto scale Filter.atTop Filter.atTop
  map : ∀ i, PartialDiffeomorph I3 I3 flow.M (X.term (subseq i)).M ∞
  contains_patch : ∀ i, patch ⊆ (map i).source
  window : ∀ᶠ i in Filter.atTop,
    Set.Icc (-delta / scale i) 0 ⊆ (X.interval (subseq i)).carrier
  converges : ∀ K : Set flow.M, IsCompact K → K ⊆ patch →
    ∀ m : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in Filter.atTop,
      Nonempty (MetricComparisonOn (fun s => flow.S.base.metric s)
        (rescaledMetric (X.term (subseq i)).S 0 (scale i) (scale_pos i))
        (map i) K (Set.Icc (-delta) 0) m eps)

structure FiniteControlledRadius {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) where
  radius : ℝ
  radius_pos : 0 < radius
  inner_bound : ∀ r : ℝ, 0 < r → r < radius → ∃ C : ℝ, ∀ i y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r →
      (X.term i).S.scalar 0 y ≤ C
  points : ∀ i, (X.term i).M
  distance_limit : Filter.Tendsto (fun i => metricDistance
    ((X.term i).S.base.metric 0) (X.term i).basepoint (points i)) Filter.atTop (nhds radius)
  curvature_limit : Filter.Tendsto (fun i => (X.term i).S.scalar 0 (points i))
    Filter.atTop Filter.atTop

theorem cone_terminal_exclusion {delta : ℝ} (hd : 0 < delta)
    (P : PointedFlowData.{u, 0, 0} I3 (RealTimeInterval.closed (-delta) 0 (by linarith)))
    (U : Set P.M) (_hU : IsOpen U) (cone : ConeChart (P.S.base.metric 0) U)
    (hsec : ∀ s ∈ Set.Icc (-delta) 0, SecLower (P.S.base.metric s) 0 U)
    (hnonflat : ∃ x ∈ U, metricScalarAt (P.S.base.metric 0) x ≠ 0) : False := by
  exact solution_cone_terminal_exclusion P.S P.isSolution (neg_lt_zero.mpr hd)
    (fun _ h => h) (fun _ h => h) U cone hsec hnonflat

structure RealizedFiniteHorn (X : FlowSequence.{u}) where
  space : Type u
  [metric_space : MetricSpace space]
  [charted : ChartedSpace ThreeSpace space]
  [smooth : IsManifold I3 ∞ space]
  [sigmaCompact : SigmaCompactSpace space]
  metric : SmoothRiemannianMetric I3 space
  horn : FiniteHorn metric
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  maps : ∀ i, PartialDiffeomorph I3 I3 space (X.term (subseq i)).M ∞
  exhaustion : ExhaustsByOpen (fun i => (maps i).source)
  convergence : ∀ K : Set space, IsCompact K → ∀ m : ℕ, ∀ eta : ℝ, 0 < eta →
    ∀ᶠ i in Filter.atTop, K ⊆ (maps i).source ∧
      Nonempty (MetricComparisonOn (fun _ => metric)
        (fun _ => (X.term (subseq i)).S.base.metric 0) (maps i) K {0} m eta)
  radii : ℕ → ℝ
  radii_mem : ∀ i, radii i ∈ Set.Ioc 0 horn.axial.length
  radii_zero : Filter.Tendsto radii Filter.atTop (nhds 0)
  directionNet : ScaleDirectionNet metric horn
  separatedRays : ScaleSeparatedEndRays metric horn
  coneRealization : ∀ (angles : EndAngles horn) (ray : EndRay horn.endpoint) (d : ℕ → ℝ),
    (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
    ConeDistanceRealization horn angles ray d
  depth_ok : hornDepthThreshold space ≤ horn.collar_depth
  curvatureUpper : ScaleCurvatureUpperBound horn horn.axial radii

attribute [local instance] RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted
  RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

namespace RealizedFiniteHorn

theorem end_rays {X : FlowSequence.{u}} (H : RealizedFiniteHorn X) :
    Nonempty (EndGeometry H.horn) :=
  finite_horn_end_rays H.horn

theorem ray_approximation {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.horn.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H.horn a b lo hi) :=
  finite_horn_ray_approximation H.horn endData
    (le_trans (hornRayApproximationDepth_le_hornDepthThreshold H.space) H.depth_ok)

theorem end_angle {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) : Nonempty (EndAngles H.horn) :=
  finite_horn_end_angle H.horn endData
    (le_trans (hornEndAngleDepth_le_hornDepthThreshold H.space) H.depth_ok)

theorem direction_compactness {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) (angles : EndAngles H.horn) :
    letI := angles.metric
    TotallyBounded (Set.univ : Set angles.quotient) ∧
      CompactSpace (UniformSpace.Completion angles.quotient) ∧
      ∃ a b : EndRay H.horn.endpoint, 0 < angles.angle a b :=
  finite_horn_direction_compactness H.horn endData angles H.directionNet H.separatedRays

theorem cone_convergence {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) (angles : EndAngles H.horn)
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Nonempty (AnnularConvergence H.horn angles ray d) :=
  finite_horn_cone_convergence H.horn endData angles ray d hd hzero
    (H.coneRealization angles ray d hd hzero)
    (le_trans (hornAngleComparisonDepth_le_hornDepthThreshold H.space) H.depth_ok)

theorem two_scale_comparison {X : FlowSequence.{u}} (H : RealizedFiniteHorn X)
    (endData : EndGeometry H.horn) (angles : EndAngles H.horn) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ∧
      metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ≤ C :=
  finite_horn_two_scale_comparison H.horn endData angles H.horn.axial H.radii
    H.radii_mem H.radii_zero H.curvatureUpper

end RealizedFiniteHorn

theorem finite_horn_construction {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth := by
  sorry

theorem finite_horn_smooth_cone_patch {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hkappa : 0 < kappa)
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (H : RealizedFiniteHorn X.toFlowSequence) (endData : EndGeometry H.horn)
    (angles : EndAngles H.horn)
    (annuli : AnnularConvergence H.horn angles H.horn.axial H.radii)
    (bounds : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ∧
      metricScalarAt H.metric (H.horn.axial.point (H.radii i)) * H.radii i ^ 2 ≤ C) :
    Nonempty (ConeFlowLimit X.toFlowSequence) := by
  sorry

theorem finite_horn_produces_cone {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        FiniteControlledRadius X → Nonempty (ConeFlowLimit X.toFlowSequence) := by
  obtain ⟨alpha, collar, ha, _hasmall, _hc, hparameters⟩ :=
    finite_horn_construction.{u} hkappa hsigma hPhi
  obtain ⟨e, he, hconstruct⟩ := hparameters alpha ha le_rfl collar le_rfl
  refine ⟨e, he, ?_⟩
  intro eps hp hsmall X R
  obtain ⟨H, _hprecision, _hcollar⟩ := hconstruct eps hp hsmall X R
  obtain ⟨endData⟩ := H.end_rays
  obtain ⟨angles⟩ := H.end_angle endData
  obtain ⟨annuli⟩ := H.cone_convergence endData angles
    H.horn.axial H.radii H.radii_mem H.radii_zero
  have bounds := H.two_scale_comparison endData angles
  exact finite_horn_smooth_cone_patch X hkappa hsigma hPhi H endData angles annuli bounds


theorem bounded_curvature_at_distance {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
