import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChart
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections

/-!
# The LC81 comparison of an LC85 slim chart with `ℝ × Z` (LFR20 item 3)

Blueprint LC85 (`def:collapse-slim-packet`, master207A:30962: "a comparison from LC81 with
`ℝ × Z`") and LFR20 item 3 (A:26358). `SlimProductModel c K` records, for a slim chart `c` (coordinate `η`)
on `M`, a complete finite model `N` (proper, connected, Riemannian for a `C^{(K-2)+1}` metric `G`
with `sec ≥ 0`), an exact splitting `e : N ≃ᵢ ℓ²(ℝ × W)` with `W` compact of diameter `≤ 10³Δ`,
LFR18's vertical field `V` (`dt(V) = 1`), and an actual `C^K` partial diffeomorphism `j : N → M`
defined on the cylinder `{|t| ≤ 19L/20}` (`L = 10⁶Δ`), pointed (`j q = p`, `t(q) = 0`), with the
clauses of LFR20 item 3: on the cylinder `j` lands in `B(p, L)`, `|η ∘ j - t| < Δ/50`,
`∂_t(η ∘ j) > 3/4`, every interpolation `(1 - u) t + u (η ∘ j)` is transverse along `V` with
inverse images of `[-a, a]` in `{|t| < a + Δ/50}`; and EVERY source fibre over `[-a, a]` in
`B(p, L)` lies in `j({|t| < 0.93L})` (`a = 9L/10`).

Producers: `slimChart_model_embedding_threshold` (threshold form, oriented sources).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric WithLp
open scoped Topology ContDiff Manifold
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC81 comparison of a slim chart with `ℝ × Z`** (LFR20 item 3). -/
structure SlimProductModel {g : SmoothRiemannianMetric I M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    (c : SlimChart g hEnorm Δ σ α) (K : ℕ) where
  /-- The finite model. -/
  N : Type
  [instMetricN : MetricSpace N]
  [instChartedN : ChartedSpace H N]
  [instManifoldN : IsManifold I ∞ N]
  [instProperN : ProperSpace N]
  [instConnectedN : ConnectedSpace N]
  [instBundleN : RiemannianBundle (fun x : N => TangentSpace I x)]
  [instRiemannianN : IsRiemannianManifold I N]
  /-- Its finite-order metric. -/
  G : ContMDiffRiemannianMetric I ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 1) E (TangentSpace I : N → Type _)
  enorm : ∀ (x : N) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v))
  sectional_nonneg : ∀ (x : N) (v w : TangentSpace I x), 0 ≤ G.sectionalCurvature x v w
  /-- The compact factor `Z` (as a metric space) and the exact splitting. -/
  W : Type
  [instMetricW : MetricSpace W]
  [instCompactW : CompactSpace W]
  factor_dist : ∀ a b : W, dist a b ≤ 10 ^ 3 * Δ
  e : N ≃ᵢ WithLp 2 (ℝ × W)
  /-- LFR18's vertical field. -/
  V : ∀ x : N, TangentSpace I x
  vertical : ∀ x, G.finiteMinimizingDirectionsTo
    {e.symm (toLp 2 ((e x).fst + 2 * (10 ^ 6 * Δ), (e x).snd))} x = {V x}
  dt_vertical : ∀ x, mvfderiv I (fun y => (e y).fst) x (V x) = 1
  /-- The model embedding. -/
  j : PartialDiffeomorph I I N M K
  q : N
  q_mem : q ∈ j.source
  j_q : j q = p
  t_q : (e q).fst = 0
  cylinder_subset : {x | |(e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ)} ⊆ j.source
  cylinder : ∀ x, |(e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) →
    j x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord (j x) - (e x).fst| < 2 * (Δ / 100) ∧
    3 / 4 < mvfderiv I (fun y => c.coord (j y)) x (V x) ∧
    ∀ u ∈ Icc (0 : ℝ) 1,
      3 / 4 < (1 - u) * 1 + u * mvfderiv I (fun y => c.coord (j y)) x (V x) ∧
      (|(1 - u) * (e x).fst + u * c.coord (j x)| ≤ 9 / 10 * (10 ^ 6 * Δ) →
        |(e x).fst| < 9 / 10 * (10 ^ 6 * Δ) + 2 * (Δ / 100))
  /-- Every source fibre over `[-a, a]` lies in the image. -/
  fibres : ∀ y ∈ ball p (10 ^ 6 * Δ), |c.coord y| ≤ 9 / 10 * (10 ^ 6 * Δ) →
    ∃ x, |(e x).fst| < 93 / 100 * (10 ^ 6 * Δ) ∧ j x = y

end DifferentialGeometry.Geometry.Collapse
