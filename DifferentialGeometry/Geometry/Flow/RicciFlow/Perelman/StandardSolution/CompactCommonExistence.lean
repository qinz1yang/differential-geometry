import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactUniformExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity

/-!
# Common existence time from an initial curvature bound (LFR50, part B)

On a compact boundaryless 3-manifold, every smooth metric with `|Rm| ≤ B` starts a Ricci flow
(`FlowTo`) that exists strictly beyond the fixed time `compactCurvatureControlTime 3 B` and keeps
`|Rm| ≤ √(2B² + 1)` on `[0, compactCurvatureControlTime 3 B]`. The time depends only on `B`, so a
whole sequence of initial metrics with the same bound has a common existence interval. No bound on
higher derivatives of the initial metric is assumed.

This is `exists_compact_flow_scaled_curvature_bound` (`CompactUniformExistence.lean`) at `Q = 1`.
-/

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

/-- A Ricci flow started at a metric with `|Rm| ≤ B` exists strictly beyond
`compactCurvatureControlTime 3 B` and keeps `|Rm| ≤ √(2B² + 1)` up to that time. -/
theorem exists_flowTo_beyond_compactCurvatureControlTime (g₀ : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) (B : ℝ)
    (hinit : ∀ x : M, Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ B) :
    ∃ τ : ℝ, compactCurvatureControlTime 3 B < τ ∧
      ∃ F : FlowTo g₀ τ,
        ∀ t ∈ Icc 0 (compactCurvatureControlTime 3 B), ∀ x : M,
          Real.sqrt (normSq0S (F.S.base.metric t) x 4 (metricRm04 (F.S.base.metric t) x)) ≤
            Real.sqrt (2 * B ^ 2 + 1) := by
  obtain ⟨τ, hτ, F, hF⟩ := exists_compact_flow_scaled_curvature_bound g₀ hdim B one_pos
    (fun x => by rw [mul_one]; exact hinit x)
  rw [div_one] at hτ hF
  exact ⟨τ, hτ, F, fun t ht x => by simpa only [mul_one] using hF t ht x⟩

/-- Common existence time (LFR50 B): a sequence of metrics with one initial curvature bound `B`
has Ricci flows on a common interval `[0, T]`, `T > 0`, each existing strictly beyond `T`, with
`|Rm| ≤ √(2B² + 1)` on `[0, T]`. Here `T = compactCurvatureControlTime 3 B`. -/
theorem exists_common_compact_flows_of_initial_rm_bound (hdim : Module.finrank ℝ E = 3) (B : ℝ)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hinit : ∀ n x, Real.sqrt (normSq0S (gSeq n) x 4 (metricRm04 (gSeq n) x)) ≤ B) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ,
      ∃ τ : ℝ, T < τ ∧ ∃ F : FlowTo (gSeq n) τ,
        ∀ t ∈ Icc 0 T, ∀ x : M,
          Real.sqrt (normSq0S (F.S.base.metric t) x 4 (metricRm04 (F.S.base.metric t) x)) ≤
            Real.sqrt (2 * B ^ 2 + 1) :=
  ⟨compactCurvatureControlTime 3 B, compactCurvatureControlTime_pos 3 B, fun n =>
    exists_flowTo_beyond_compactCurvatureControlTime (gSeq n) hdim B (hinit n)⟩

omit [CompactSpace M] in
/-- The solution of a `FlowTo` is a smooth Ricci flow solution in the sense of
`IsSmoothSolutionOn`, as the preservation theorems require. -/
theorem FlowTo.isSmoothSolutionOn {g₀ : SmoothRiemannianMetric I M} {τ : ℝ} (F : FlowTo g₀ τ) :
    IsSmoothSolutionOn F.S :=
  smoothOfSolution F.S F.isSolution

omit [I.Boundaryless] [CompactSpace M] in
theorem FlowTo.Icc_subset_carrier {g₀ : SmoothRiemannianMetric I M} {τ T : ℝ} (F : FlowTo g₀ τ)
    (hT : T < τ) : Icc 0 T ⊆ (RealTimeInterval.closedOpen 0 τ F.time_pos).carrier :=
  fun _ ht => ⟨ht.1, ht.2.trans_lt hT⟩

omit [I.Boundaryless] [CompactSpace M] in
theorem FlowTo.Ioc_subset_regular {g₀ : SmoothRiemannianMetric I M} {τ T : ℝ} (F : FlowTo g₀ τ)
    (hT : T < τ) : Ioc 0 T ⊆ (RealTimeInterval.closedOpen 0 τ F.time_pos).regular :=
  fun _ ht => ⟨ht.1, ht.2.trans_lt hT⟩

end DifferentialGeometry.PDE.RicciFlow
