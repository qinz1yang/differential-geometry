import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimPacketClauses

/-!
# The LC85 slim chart (the slim packet without its fibre type)

Blueprint LC85 (`def:collapse-slim-packet`, master207A:30962) and LFR20 (A:26358), at normalized
scale (`sec ≥ -β²` on `B(p, β⁻¹)`, the convention of LFR19/LFR20 and of `CircleChart`). With
`L = 10⁶Δ`, `a' = 905·10³Δ`:

`SlimChart g hEnorm Δ σ α` records, for an ACTUAL normalized `(1, β)`-splitting
`α = (u, v) : M → ℝ × Y` at `p`, an adapted coordinate `η` (LFR19's output clauses: smooth near
`B̄(p, L)`, `η(p) = 0`, `(1 + σ)`-Lipschitz, `|η - u| < Δ/100`, (LFR19.1) with `T = L/σ`) and the
LFR20 clauses that hold for every such `η`: the enclosure (LFR20.2), `dη > 3/4` on `B(p, 0.91L)`,
`η(B(p, L)) ⊇ [-a', a']`, the proper submersion `η : {|η| < a'} → (-a', a')`, trivial over every
`(-R, R)`, `R < a'` (so over LC85's `(-9·10⁵Δ, 9·10⁵Δ)`), and the LC85 cutoff (plateau
`|η| ≤ 8·10⁵Δ`, support in `|η| < 89·10⁴Δ`, smooth, compactly supported, values in `[0, 1]`).

NOT recorded here (they need the limit argument of LFR20 over LFR14/LFR16/LFR17, see
`build-logs/resume/sheet-F7-LFR20b.md`): the fibre TYPE `S²` or `T²`, connectedness of the fibre,
and the LC81 comparison with `ℝ × Z`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC85 slim chart** at normalized scale (fields = the output clauses of LFR19 and of
`slimPacket_clauses_of_coordinate`; `L = 10⁶Δ`, `a' = 905·10³Δ`). -/
structure SlimChart (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (Δ σ : ℝ)
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β) where
  /-- The adapted coordinate `η`. -/
  coord : M → ℝ
  /-- An open neighbourhood of `B̄(p, L)` on which `η` is smooth. -/
  domain : Set M
  isOpen_domain : IsOpen domain
  closedBall_subset_domain : closedBall p (10 ^ 6 * Δ) ⊆ domain
  contMDiffOn_coord : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ coord domain
  coord_center : coord p = 0
  lipschitz : LipschitzWith (Real.toNNReal (1 + σ)) coord
  value : ∀ x ∈ ball p (10 ^ 6 * Δ), |coord x - (α.toFun x).fst| < Δ / 100
  test : ∀ x ∈ ball p (10 ^ 6 * Δ), ∀ x' ∈ ball p (10 ^ 6 * Δ / σ), 10 ^ 6 * Δ < dist x x' →
    ∀ w : TangentSpace I x, g.inner x w w = 1 →
    intrinsicGeodesic g hEnorm x w (dist x x') = x' →
    |mvfderiv (I := I) coord x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ
  /-- (LFR20.2). -/
  enclosure : ∀ x ∈ ball p (10 ^ 6 * Δ), |coord x| ≤ 905 * 10 ^ 3 * Δ →
    dist x p < 91 / 100 * (10 ^ 6 * Δ)
  /-- (LFR20.1) in source form. -/
  derivative : ∀ x ∈ ball p (91 / 100 * (10 ^ 6 * Δ)), ∃ w : TangentSpace I x,
    g.inner x w w = 1 ∧ 3 / 4 < mvfderiv (I := I) coord x w
  surjective : Icc (-(905 * 10 ^ 3 * Δ)) (905 * 10 ^ 3 * Δ) ⊆ coord '' ball p (10 ^ 6 * Δ)
  regular : ∀ x ∈ ball p (10 ^ 6 * Δ), |coord x| < 905 * 10 ^ 3 * Δ →
    ∃ w : E, mfderiv I 𝓘(ℝ, ℝ) coord x w ≠ 0
  /-- The buffered restriction `η : {x ∈ B(p, L) | |η x| < a'} → (-a', a')` is proper. -/
  isProperMap : IsProperMap (realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball coord
    lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ))
  /-- ... and trivial over every `(-R, R)`, `R < a'`, with fibre the zero fibre. -/
  trivial : ∀ R (hR : 0 < R) (hRr : R < 905 * 10 ^ 3 * Δ),
    let f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball coord
      lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
    let y₀ : lineBallOpens (905 * 10 ^ 3 * Δ) := ⟨0, zero_mem_lineBallOpens (hR.trans hRr)⟩
    let _ := regularFiberChartedSpace f y₀
      (contMDiff_realSlabMap isOpen_ball
        (contMDiffOn_coord.mono (ball_subset_closedBall.trans closedBall_subset_domain)) _)
      (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
        (contMDiffOn_coord.mono (ball_subset_closedBall.trans closedBall_subset_domain)) regular x)
    let U : TopologicalSpace.Opens (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball coord
        lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)) :=
      ⟨f ⁻¹' lineBallInner (905 * 10 ^ 3 * Δ) R,
        (lineBallInner (905 * 10 ^ 3 * Δ) R).isOpen.preimage
          (continuous_realSlabMap isOpen_ball _ _)⟩
    ∃ (hy : y₀ ∈ lineBallInner (905 * 10 ^ 3 * Δ) R) (Θ : Diffeomorph
        (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ).prod 𝓘(ℝ, ℝ)) I
        ({x // f x = y₀} × lineBallInner (905 * 10 ^ 3 * Δ) R) U ∞),
      (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)
  /-- The LC85 cutoff. -/
  cutoff : M → ℝ
  contMDiff_cutoff : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  hasCompactSupport_cutoff : HasCompactSupport cutoff
  cutoff_mem_Icc : ∀ x, cutoff x ∈ Icc (0 : ℝ) 1
  cutoff_eq_one : ∀ x ∈ ball p (10 ^ 6 * Δ), |coord x| ≤ 8 * 10 ^ 5 * Δ → cutoff x = 1
  cutoff_ne_zero : ∀ x, cutoff x ≠ 0 → x ∈ ball p (10 ^ 6 * Δ) ∧ |coord x| < 89 * 10 ^ 4 * Δ
  tsupport_cutoff : tsupport cutoff ⊆
    {x | dist x p ≤ 91 / 100 * (10 ^ 6 * Δ) ∧ |coord x| ≤ 89 * 10 ^ 4 * Δ}

end DifferentialGeometry.Geometry.Collapse
