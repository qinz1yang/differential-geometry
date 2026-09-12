import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeTerminalExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornIntrinsicRays
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
theorem finite_horn_end_rays {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) :
    Nonempty (EndGeometry H) := by
  sorry

theorem finite_horn_ray_approximation {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H a b lo hi) := by
  sorry

theorem finite_horn_end_angle {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) : Nonempty (EndAngles H) := by
  sorry


theorem finite_horn_direction_compactness {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (angles : EndAngles H) :
    letI := angles.metric
    TotallyBounded (Set.univ : Set angles.quotient) ∧
      CompactSpace (UniformSpace.Completion angles.quotient) ∧
      ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  sorry


theorem finite_horn_cone_convergence {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Nonempty (AnnularConvergence H angles ray d) := by
  sorry

theorem finite_horn_barriers {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) : Nonempty (HornBarriers H ray d) := by
  sorry

theorem finite_horn_two_scale_comparison {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (annuli : AnnularConvergence H angles ray d) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 ∧
      metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ C := by
  sorry

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

attribute [local instance] RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted
  RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

theorem finite_horn_construction {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ H.horn.collar_depth = collar := by
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
  obtain ⟨endData⟩ := finite_horn_end_rays H.horn
  obtain ⟨angles⟩ := finite_horn_end_angle H.horn endData
  obtain ⟨annuli⟩ := finite_horn_cone_convergence H.horn endData angles
    H.horn.axial H.radii H.radii_mem H.radii_zero
  have bounds := finite_horn_two_scale_comparison H.horn endData angles
    H.horn.axial H.radii H.radii_mem H.radii_zero annuli
  exact finite_horn_smooth_cone_patch X hkappa hsigma hPhi H endData angles annuli bounds


theorem bounded_curvature_at_distance {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  sorry


attribute [local instance] FiniteHorn.ambient_metric

structure AmbientEndIsometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) : Prop where
  deep : ∃ i, (∀ x ∈ H.subend i, ∀ y ∈ H.subend i,
      dist x y = dist (H.inclusion x) (H.inclusion y)) ∧
    ∀ x ∈ H.subend i, dist (x : UniformSpace.Completion W) H.endpoint =
      dist (H.inclusion x) H.ambient_end

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


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
