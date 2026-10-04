import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles

/-!
# Shared vocabulary of the sublevel-and-core family (chapter 13, LC32–LC61)

`inwardMinimizingDirections g hEnorm n q` is the set `𝒰_n(q)` of the frozen blueprint
(master207A, section "Uniform collar margins", before LC49): all `g`-unit tangent vectors
`v` at `q` whose geodesic reaches `n` at time `d(n, q)`. Completeness makes it nonempty
when `q ≠ n` (`inwardMinimizingDirections_nonempty`). It is the direction set quantified
in LC44 ("every inward unit minimizing direction") and in LC49–LC51.

The setting is the PC Riemannian setting of the soul suite: the metric space structure of `M`
is the Riemannian distance (`IsRiemannianManifold`), and `hEnorm` identifies the bundle norm
with the smooth metric `g`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The blueprint's `𝒰_n(q)`: all inward unit minimizing directions at `q` toward `n`. -/
def inwardMinimizingDirections (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (n q : M) : Set (TangentSpace I q) :=
  {v | g.inner q v v = 1 ∧ intrinsicGeodesic (I := I) g hEnorm q v (dist n q) = n}

theorem mem_inwardMinimizingDirections {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g} {n q : M} {v : TangentSpace I q} :
    v ∈ inwardMinimizingDirections (I := I) g hEnorm n q ↔
      g.inner q v v = 1 ∧ intrinsicGeodesic (I := I) g hEnorm q v (dist n q) = n :=
  Iff.rfl

/-- Completeness supplies an inward unit minimizing direction at every `q ≠ n`. -/
theorem inwardMinimizingDirections_nonempty (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {n q : M} (hnq : n ≠ q) :
    (inwardMinimizingDirections (I := I) g hEnorm n q).Nonempty := by
  have hd : 0 < dist q n := dist_pos.mpr hnq.symm
  obtain ⟨u, hu, hun⟩ :=
    DifferentialGeometry.Geometry.Topology.soul_unit_minimizing_initial
      (I := I) g hEnorm q n hd
  refine ⟨u, hu, ?_⟩
  rw [dist_comm n q]
  exact hun

end DifferentialGeometry.Geometry.Collapse
