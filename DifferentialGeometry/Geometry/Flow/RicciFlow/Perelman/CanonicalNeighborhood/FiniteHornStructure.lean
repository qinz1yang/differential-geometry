import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactPathAvoidance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeTerminalExclusion
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

structure EndRay (E : UniformSpace.Completion W) where
  length : ℝ
  length_pos : 0 < length
  point : ℝ → W
  radial : ∀ s ∈ Set.Ioc 0 length,
    dist (point s : UniformSpace.Completion W) E = s
  minimizing : ∀ s ∈ Set.Ioc 0 length, ∀ t ∈ Set.Ioc 0 length,
    dist (point s) (point t) = |s - t|

def EndRay.EventuallyEqual {E : UniformSpace.Completion W} (a b : EndRay E) : Prop :=
  ∃ d : ℝ, 0 < d ∧ d ≤ min a.length b.length ∧
    ∀ s ∈ Set.Ioc 0 d, a.point s = b.point s

structure GlobalNeckTube (W : Type u) [MetricSpace W] [ChartedSpace ThreeSpace W] where
  map : PartialDiffeomorph IC I3 Cylinder W ∞
  source_eq : map.source = Set.univ ×ˢ Set.Ioo (0 : ℝ) 1
  target_eq : map.target = Set.univ

namespace GlobalNeckTube


def height (T : GlobalNeckTube W) (x : W) : ℝ := (T.map.symm x).2

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem continuous_height (T : GlobalNeckTube W) : Continuous T.height := by
  have h : Continuous (T.map.symm : W → Cylinder) := by
    rw [← continuousOn_univ]
    change ContinuousOn T.map.invFun Set.univ
    simpa only [T.target_eq] using T.map.contMDiffOn_invFun.continuousOn
  exact continuous_snd.comp h

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem height_mem (T : GlobalNeckTube W) (x : W) : T.height x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hx : x ∈ T.map.target := by rw [T.target_eq]; trivial
  have h := T.map.toPartialEquiv.map_target hx
  rw [T.source_eq] at h
  exact h.2


def sectionSet (T : GlobalNeckTube W) (q : ℝ) : Set W :=
  T.map '' (Set.univ ×ˢ ({q} : Set ℝ))

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem mem_sectionSet_iff (T : GlobalNeckTube W) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (x : W) : x ∈ T.sectionSet q ↔ T.height x = q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyq : y.2 = q := hy.2
    have hys : y ∈ T.map.source := by
      rw [T.source_eq]
      exact ⟨Set.mem_univ _, hyq.symm ▸ hq⟩
    change (T.map.invFun (T.map y)).2 = q
    rw [T.map.left_inv' hys]
    exact hyq
  · intro hx
    refine ⟨T.map.symm x, ⟨Set.mem_univ _, hx⟩, ?_⟩
    exact T.map.right_inv' (by rw [T.target_eq]; trivial)

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem isCompact_slab (T : GlobalNeckTube W) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    IsCompact (T.map '' (Set.univ ×ˢ Set.Icc a b)) := by
  apply ((isCompact_univ : IsCompact (Set.univ : Set (Sphere 2))).prod isCompact_Icc).image_of_continuousOn
  apply T.map.contMDiffOn_toFun.continuousOn.mono
  intro x hx
  rw [T.source_eq]
  exact ⟨Set.mem_univ _, ha.trans_le hx.2.1, hx.2.2.trans_lt hb⟩

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem path_meets_section (T : GlobalNeckTube W) {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (c : ℝ → W)
    (hc : ContinuousOn c (Set.Icc (0 : ℝ) 1))
    (hstart : T.height (c 0) < q) (hend : q < T.height (c 1)) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, c s ∈ T.sectionSet q := by
  have hh : ContinuousOn (T.height ∘ c) (Set.Icc (0 : ℝ) 1) :=
    T.continuous_height.comp_continuousOn hc
  obtain ⟨s, hs, hsq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hh
    ⟨hstart.le, hend.le⟩
  exact ⟨s, hs, (T.mem_sectionSet_iff hq (c s)).2 hsq⟩

end GlobalNeckTube

structure GlobalNeckCrossSection
    (F : PartialDiffeomorph IC I3 Cylinder W ∞) (subend : ℕ → Set W)
    (axis : ℝ → W) (axisLength : ℝ) where
  tube : GlobalNeckTube W
  center_eq : ∀ p : Sphere 2, tube.map (p, 1 / 2) = F (p, 0)
  deep_side : ∃ i, ∀ x ∈ subend i, tube.height x < 1 / 2
  crossing_parameter : ℝ
  crossing_mem : crossing_parameter ∈ Set.Ioc 0 axisLength
  axis_crosses : ∃ p : Sphere 2, F (p, 0) = axis crossing_parameter

omit [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem GlobalNeckCrossSection.path_meets_center
    {F : PartialDiffeomorph IC I3 Cylinder W ∞} {subend : ℕ → Set W}
    {axis : ℝ → W} {axisLength : ℝ}
    (G : GlobalNeckCrossSection F subend axis axisLength) (c : ℝ → W)
    (hc : ContinuousOn c (Set.Icc (0 : ℝ) 1))
    (hstart : G.tube.height (c 0) < 1 / 2) (hend : 1 / 2 < G.tube.height (c 1)) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, c s ∈ Set.range (fun p : Sphere 2 => F (p, 0)) := by
  obtain ⟨s, hs, y, hy, heq⟩ := G.tube.path_meets_section
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) c hc hstart hend
  have hyq : y.2 = 1 / 2 := hy.2
  refine ⟨s, hs, y.1, ?_⟩
  change F (y.1, 0) = c s
  rw [← G.center_eq, ← hyq]
  exact heq

structure _root_.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
    (g : SmoothRiemannianMetric I3 W) where
  intrinsic : ∀ x y : W, dist x y = metricDistance g x y
  endpoint : UniformSpace.Completion W
  endpoint_missing : ∀ x : W, (x : UniformSpace.Completion W) ≠ endpoint
  axial : EndRay endpoint
  tube : GlobalNeckTube W
  subend : ℕ → Set W
  cut_height : ℕ → ℝ
  cut_height_mem : ∀ i, cut_height i ∈ Set.Ioo (0 : ℝ) 1
  cut_height_zero : Filter.Tendsto cut_height Filter.atTop (nhds 0)
  subend_eq : ∀ i, subend i = {x | tube.height x < cut_height i}
  open_subend : ∀ i, IsOpen (subend i)
  connected_subend : ∀ i, IsConnected (subend i)
  nested : ∀ i, subend (i + 1) ⊆ subend i
  cofinal_axial : ∀ i, ∃ d : ℝ, 0 < d ∧ d ≤ axial.length ∧
    ∀ s ∈ Set.Ioc 0 d, axial.point s ∈ subend i
  ambient : Type u
  [ambient_metric : MetricSpace ambient]
  [ambient_complete : CompleteSpace ambient]
  inclusion : W → ambient
  inclusion_continuous : Continuous inclusion
  inclusion_injective : Function.Injective inclusion
  ambient_end : ambient
  ambient_axial : ∀ s ∈ Set.Ioc 0 axial.length, dist (inclusion (axial.point s)) ambient_end = s
  local_distance : ∀ x : W, ∃ U ∈ nhds x, ∀ y ∈ U, ∀ z ∈ U,
    dist (inclusion y) (inclusion z) = dist y z
  outer_frontier : Set ambient
  frontier_eq : outer_frontier = frontier (Set.range inclusion) \ {ambient_end}
  inclusion_isOpenEmbedding : Topology.IsOpenEmbedding inclusion
  frontier_far : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ outer_frontier, δ ≤ dist z ambient_end
  deep_capture : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ambient, z ≠ ambient_end →
    dist z ambient_end < δ → z ∈ Set.range inclusion
  nonnegative : SecLower g 0 Set.univ
  curvature_diverges : ∀ C : ℝ, ∃ i, ∀ x ∈ subend i, C < metricScalarAt g x
  curvature_distance_lower : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ subend 0,
    c ≤ metricScalarAt g x * dist (x : UniformSpace.Completion W) endpoint ^ 2
  neck_precision : ℝ
  neck_precision_pos : 0 < neck_precision
  neck_precision_small : neck_precision < 1 / 11
  collar_depth : ℝ
  collar_depth_pos : 0 < collar_depth
  cylindrical_tail : ∃ i,
    ∀ x ∈ subend i, ∃ (cyl : CylinderReference)
      (F : PartialDiffeomorph IC I3 Cylinder W ∞) (p : Sphere 2),
      F (p, 0) = x ∧
      Nonempty (GlobalNeckCrossSection F subend axial.point axial.length) ∧
      Set.univ ×ˢ Set.Icc (-collar_depth) collar_depth ⊆ F.source ∧
      ∃ hQ : 0 < metricScalarAt g x,
        Nonempty (MetricComparisonOn (fun _ => cyl.metric 0)
          (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
          (Set.univ ×ˢ Set.Icc (-collar_depth) collar_depth)
          {0} (⌈neck_precision⁻¹⌉₊) neck_precision)

attribute [local instance] FiniteHorn.ambient_metric

structure EndGeometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) where
  unique_endpoint : (⋂ i, closure ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend i)) =
    {H.endpoint}
  intrinsic_ambient : ∃ i, (∀ x ∈ H.subend i, ∀ y ∈ H.subend i,
    dist x y = dist (H.inclusion x) (H.inclusion y)) ∧
    ∀ x ∈ H.subend i, dist (x : UniformSpace.Completion W) H.endpoint =
      dist (H.inclusion x) H.ambient_end
  rays : ∃ i, ∀ x ∈ H.subend i, ∃ a : EndRay H.endpoint, a.point a.length = x
  frontier_escape : ∀ w : ℕ → W,
    Filter.Tendsto (fun i => (w i : UniformSpace.Completion W)) Filter.atTop (nhds H.endpoint) →
    ∀ R : ℝ, 0 < R → ∀ᶠ i in Filter.atTop, ∀ z ∈ H.outer_frontier,
      R * dist (w i : UniformSpace.Completion W) H.endpoint < dist (H.inclusion (w i)) z

theorem finite_horn_end_rays {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) :
    Nonempty (EndGeometry H) := by
  sorry

structure RayApproximation {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (a b : EndRay H.endpoint) (lo hi : Fin 2 → ℝ) where
  target_index : ℕ
  arm_index : ℕ
  connector_index : ℕ
  target_buffer : closure (H.subend target_index) ⊆ H.subend arm_index
  arm_buffer : closure (H.subend arm_index) ⊆ H.subend connector_index
  target_mem : (∀ s ∈ Set.Icc (lo 0) (hi 0), a.point s ∈ H.subend target_index) ∧
    (∀ t ∈ Set.Icc (lo 1) (hi 1), b.point t ∈ H.subend target_index)
  base : ℕ → W
  arm : Fin 2 → ℕ → ℝ → W
  length : Fin 2 → ℕ → ℝ
  length_pos : ∀ k i, 0 < length k i
  arm_smooth : ∀ k i, ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ (arm k i) (Set.Icc 0 (length k i))
  arm_mem : ∀ k i s, s ∈ Set.Icc 0 (length k i) → arm k i s ∈ H.subend arm_index
  parameter : Fin 2 → ℕ → ℝ → ℝ
  starts : ∀ k i, arm k i 0 = base i
  minimizing : ∀ k i s, s ∈ Set.Icc 0 (length k i) → ∀ t ∈ Set.Icc 0 (length k i),
    dist (arm k i s) (arm k i t) = |s - t|
  parameter_mono : ∀ k i, MonotoneOn (parameter k i) (Set.Icc (lo k) (hi k))
  parameter_mem : ∀ k i s, s ∈ Set.Icc (lo k) (hi k) → parameter k i s ∈ Set.Icc 0 (length k i)
  connectors : ∀ i, ∀ s ∈ Set.Icc 0 (length 0 i), ∀ t ∈ Set.Icc 0 (length 1 i),
    ∃ c : ℝ → W, c 0 = arm 0 i s ∧
      c 1 = arm 1 i t ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ c (Set.Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, c u ∈ H.subend connector_index) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        dist (c u) (c v) = |u - v| *
          dist (arm 0 i s) (arm 1 i t)
  uniform : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
    dist (base i : UniformSpace.Completion W) H.endpoint < eta ∧
    ∀ s ∈ Set.Icc (lo 0) (hi 0), ∀ t ∈ Set.Icc (lo 1) (hi 1),
      |parameter 0 i s - s| < eta ∧ |parameter 1 i t - t| < eta ∧
      dist (arm 0 i (parameter 0 i s)) (a.point s) < eta ∧
      dist (arm 1 i (parameter 1 i t)) (b.point t) < eta ∧
      |dist (arm 0 i (parameter 0 i s)) (arm 1 i (parameter 1 i t)) -
        dist (a.point s) (b.point t)| < eta

theorem finite_horn_ray_approximation {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H a b lo hi) := by
  sorry

def endComparisonAngle {E : UniformSpace.Completion W} (a b : EndRay E) (s t : ℝ) : ℝ :=
  Real.arccos ((s ^ 2 + t ^ 2 - dist (a.point s) (b.point t) ^ 2) / (2 * s * t))

structure EndAngles {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) where
  angle : EndRay H.endpoint → EndRay H.endpoint → ℝ
  range : ∀ a b, angle a b ∈ Set.Icc 0 Real.pi
  limit : ∀ a b, ∀ eta : ℝ, 0 < eta → ∃ d : ℝ, 0 < d ∧ d ≤ min a.length b.length ∧
    ∀ s ∈ Set.Ioc 0 d, ∀ t ∈ Set.Ioc 0 d, |endComparisonAngle a b s t - angle a b| < eta
  monotone : ∀ a b : EndRay H.endpoint, ∃ d : ℝ, 0 < d ∧ d ≤ min a.length b.length ∧
    ∀ s s' t t', 0 < s → s ≤ s' → s' ≤ d → 0 < t → t ≤ t' → t' ≤ d →
      endComparisonAngle a b s' t' ≤ endComparisonAngle a b s t
  self : ∀ a, angle a a = 0
  symm : ∀ a b, angle a b = angle b a
  triangle : ∀ a b c, angle a c ≤ angle a b + angle b c
  quotient : Type u
  [metric : MetricSpace quotient]
  classOf : EndRay H.endpoint → quotient
  onto : Function.Surjective classOf
  distance : ∀ a b, dist (classOf a) (classOf b) = angle a b
  eventual_eq : ∀ a b, a.EventuallyEqual b → classOf a = classOf b

attribute [local instance] EndAngles.metric


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


def openConeDistance {Y : Type*} [MetricSpace Y] (x y : ℝ × Y) : ℝ :=
  Real.sqrt (x.1 ^ 2 + y.1 ^ 2 - 2 * x.1 * y.1 * Real.cos (min Real.pi (dist x.2 y.2)))

structure AnnularConvergence {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ) where
  relation : ℝ → ℝ → ℕ → Set ((ℝ × UniformSpace.Completion angles.quotient) × W)
  error : ℝ → ℝ → ℕ → ℝ
  error_pos : ∀ a b i, 0 < error a b i
  error_zero : ∀ a b, 0 < a → a < b → Filter.Tendsto (error a b) Filter.atTop (nhds 0)
  annuli : ∀ a b, 0 < a → a < b → ∀ᶠ i in Filter.atTop,
    IsCompact {w : W | a ≤ dist (w : UniformSpace.Completion W) H.endpoint / d i ∧
      dist (w : UniformSpace.Completion W) H.endpoint / d i ≤ b} ∧
    (∀ x w, (x, w) ∈ relation a b i → x.1 ∈ Set.Icc a b ∧
      dist (w : UniformSpace.Completion W) H.endpoint / d i ∈ Set.Icc a b) ∧
    (∀ x : ℝ × UniformSpace.Completion angles.quotient, x.1 ∈ Set.Icc a b →
      ∃ y w, (y, w) ∈ relation a b i ∧ openConeDistance x y < error a b i) ∧
    (∀ w : W, dist (w : UniformSpace.Completion W) H.endpoint / d i ∈ Set.Icc a b →
      ∃ x z, (x, z) ∈ relation a b i ∧ dist w z / d i < error a b i) ∧
    (∀ x w y z, (x, w) ∈ relation a b i → (y, z) ∈ relation a b i →
      |openConeDistance x y - dist w z / d i| < error a b i) ∧
    (∀ x w, (x, w) ∈ relation a b i →
      |x.1 - dist (w : UniformSpace.Completion W) H.endpoint / d i| < error a b i) ∧
    (a < 1 → 1 < b →
      (((1, (angles.classOf ray : UniformSpace.Completion angles.quotient)), ray.point (d i))) ∈
        relation a b i)


theorem finite_horn_cone_convergence {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (angles : EndAngles H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Nonempty (AnnularConvergence H angles ray d) := by
  sorry

structure HornBarriers {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) where
  sphere : ℕ → Sphere 2 → W
  embedding : ∀ i, _root_.Topology.IsEmbedding (sphere i)
  smooth : ∀ i, ContMDiff I2 I3 ∞ (sphere i)
  diameter_bound : ∃ L : ℝ, 0 < L ∧ ∀ᶠ i in Filter.atTop, ∀ x ∈ Set.range (sphere i),
    dist (ray.point (d i)) x ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i)))
  radial_barrier : ∀ eta : ℝ, 0 < eta → eta < 1 / 10 → ∀ᶠ i in Filter.atTop,
    ∀ c : C(Set.Icc (0 : ℝ) 1, W),
      dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint / d i < 1 - eta →
      1 + eta < dist (c ⟨1, by simp⟩ : UniformSpace.Completion W) H.endpoint / d i →
      ∃ t, c t ∈ Set.range (sphere i)

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

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
