import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond

/-!
# The metric space induced by a smooth Riemannian metric

For a smooth Riemannian metric `g` on a manifold `M` (with its given topology) we build the
extended metric space and, on a connected manifold, the metric space whose distance is the
`g`-length distance `riemannianEDistOf g`. The constructions are `@[reducible]` definitions, never
global instances: they are installed with `letI` exactly where a metric-space kernel is applied
to an actual manifold, so they cannot form diamonds with an existing `MetricSpace` instance.

Their topology is definitionally the given topology of `M` (mathlib's
`EMetricSpace.ofRiemannianMetric`), so a `ChartedSpace H M` instance for the original topology is
also one for the metric topology. Together with the bundle `⟨g.toRiemannianMetric⟩` they supply
the full instance block of the Riemannian metric-space kernels (for instance
`exists_finite_scale_cover_of_ricci_bound`): `IsRiemannianManifold`, the compatibility
`IsMetricNorm g`, `IsContinuousRiemannianBundle` and, on compact manifolds, completeness.

## Main declarations

* `inducedEMetricSpace g`, `inducedMetricSpace g`: the structures.
* `inducedEMetricSpace_edist`, `inducedMetricSpace_hmetric`, `inducedMetricSpace_dist`:
  the distance is `riemannianEDistOf g`.
* `inducedMetricSpace_ball`, `inducedMetricSpace_closedBall`: metric balls are the
  `g`-balls `riemannianBallOf` / `riemannianClosedBallOf`.
* `inducedMetricSpace_completeSpace`: completeness on a compact manifold.
* `inducedMetricSpace_riemannian`: `IsRiemannianManifold`, `IsMetricNorm g` and
  `IsContinuousRiemannianBundle` for the bundle `⟨g.toRiemannianMetric⟩`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/- The tangent-space norm instances of `Tensor0SBundle` compete with the fiber norm of the bundle
`⟨g.toRiemannianMetric⟩`; they are disabled in this file, as in
`Geometry/Metric/TensorInner/Tangent/NormDiamond.lean`. -/
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-! ### Tier 1: the extended metric space -/

/-- The extended metric space structure on `M` whose extended distance is the `g`-length
distance. Its topology is definitionally the given topology of `M`. Not an instance. -/
@[reducible] noncomputable def inducedEMetricSpace [T3Space M]
    (g : SmoothRiemannianMetric I M) : EMetricSpace M :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  EMetricSpace.ofRiemannianMetric I M

theorem inducedEMetricSpace_edist [T3Space M] (g : SmoothRiemannianMetric I M) (a b : M) :
    letI := inducedEMetricSpace g
    edist a b = riemannianEDistOf (I := I) g a b :=
  rfl

theorem inducedEMetricSpace_toTopologicalSpace [T3Space M] (g : SmoothRiemannianMetric I M) :
    (inducedEMetricSpace g).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› :=
  rfl

/-! ### Tier 2: the metric space on a connected manifold -/

/-- The metric space structure on a connected manifold whose distance is the real form of the
`g`-length distance. Its topology is definitionally the given topology of `M`, and its extended
distance is definitionally `riemannianEDistOf g`. Not an instance. -/
@[reducible] noncomputable def inducedMetricSpace [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) : MetricSpace M :=
  letI := inducedEMetricSpace g
  EMetricSpace.toMetricSpace fun a b => riemannianEDistOf_ne_top (I := I) g a b

theorem inducedMetricSpace_edist [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (a b : M) :
    letI := inducedMetricSpace g
    edist a b = riemannianEDistOf (I := I) g a b :=
  rfl

theorem inducedMetricSpace_dist [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (a b : M) :
    letI := inducedMetricSpace g
    dist a b = (riemannianEDistOf (I := I) g a b).toReal :=
  rfl

theorem inducedMetricSpace_hmetric [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b) := by
  let := inducedMetricSpace g
  intro a b
  exact edist_dist a b

theorem inducedMetricSpace_toTopologicalSpace [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) :
    (inducedMetricSpace g).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› :=
  rfl

/-- On a connected manifold the induced metric refines the existing pseudometric
`SmoothRiemannianMetric.toPseudoMetricSpace` (`Geometry/Metric/Distance/Topology.lean`). -/
theorem inducedMetricSpace_toPseudoMetricSpace [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) :
    (inducedMetricSpace g).toPseudoMetricSpace = g.toPseudoMetricSpace :=
  rfl

/-! ### Tier 3: balls and Lipschitz functions -/

/-- Metric balls of the induced metric are the `g`-balls, for every radius (both sides are empty
when `r ≤ 0`, so no positivity hypothesis is needed). -/
theorem inducedMetricSpace_ball [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    letI := inducedMetricSpace g
    Metric.ball p r = riemannianBallOf g p r := by
  let := inducedMetricSpace g
  ext y
  rw [Metric.mem_ball, dist_comm, ← edist_lt_ofReal]
  rfl

/-- Closed metric balls of the induced metric are the closed `g`-balls for `r ≥ 0` (for `r < 0`
the metric ball is empty while `riemannianClosedBallOf g p r = {p}`). -/
theorem inducedMetricSpace_closedBall [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 ≤ r) :
    letI := inducedMetricSpace g
    Metric.closedBall p r = riemannianClosedBallOf g p r := by
  let := inducedMetricSpace g
  ext y
  rw [Metric.mem_closedBall, dist_comm, ← edist_le_ofReal hr]
  rfl

/-- Lipschitz functions for the induced metric, in terms of the `g`-distance only. -/
theorem inducedMetricSpace_lipschitzWith_iff [T3Space M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {ρ : M → ℝ} {Λ : ℝ≥0} :
    letI := inducedMetricSpace g
    LipschitzWith Λ ρ ↔
      ∀ p q : M, |ρ p - ρ q| ≤ Λ * (riemannianEDistOf (I := I) g p q).toReal := by
  let := inducedMetricSpace g
  rw [lipschitzWith_iff_dist_le_mul]
  rfl

/-! ### Tier 4: completeness on a compact manifold -/

theorem inducedEMetricSpace_completeSpace [T3Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    letI := inducedEMetricSpace g
    CompleteSpace M := by
  let := inducedEMetricSpace g
  exact complete_of_compact

theorem inducedMetricSpace_completeSpace [T3Space M] [ConnectedSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    CompleteSpace M := by
  let := inducedMetricSpace g
  exact complete_of_compact

theorem inducedMetricSpace_properSpace [T3Space M] [ConnectedSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    ProperSpace M := by
  let := inducedMetricSpace g
  exact proper_of_compact

/-! ### Tier 5: the Riemannian instance package -/

theorem inducedEMetricSpace_isRiemannianManifold [T3Space M] (g : SmoothRiemannianMetric I M) :
    letI := inducedEMetricSpace g
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsRiemannianManifold I M := by
  let := inducedEMetricSpace g
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact ⟨fun _ _ => rfl⟩

theorem inducedMetricSpace_isRiemannianManifold [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsRiemannianManifold I M := by
  let := inducedMetricSpace g
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact ⟨fun _ _ => rfl⟩

/-- The bundle `⟨g.toRiemannianMetric⟩` is continuous (no metric structure involved). -/
theorem isContinuousRiemannianBundle_of_smoothRiemannianMetric (g : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩

/-- The fiber norm of the bundle `⟨g.toRiemannianMetric⟩` is the `g`-norm. -/
theorem isMetricNorm_of_smoothRiemannianMetric (g : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := I) (M := M) g :=
  DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle (I := I) g

/-- The instance package of the Riemannian metric-space kernels, for the metric induced by `g`
and the bundle `⟨g.toRiemannianMetric⟩`. -/
theorem inducedMetricSpace_riemannian [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsRiemannianManifold I M ∧
      DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := I) (M := M) g ∧
      IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
  ⟨inducedMetricSpace_isRiemannianManifold g, isMetricNorm_of_smoothRiemannianMetric g,
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g⟩

end DifferentialGeometry

end
