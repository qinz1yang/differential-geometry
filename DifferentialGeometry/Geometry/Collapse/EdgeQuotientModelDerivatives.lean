import DifferentialGeometry.Geometry.Collapse.EdgeSourceDerivatives
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

/-!
# (LFR28.4) for the edge quotient `η_i = F_i / ρ_i`: the LFR27 binding of the kernel

Blueprint 207A, LFR28 step 2 (A:27351–27363): "combine LFR26 with (LFR27.1) … The quotient-rule
error is at most `150ΔΛ`, by LFR27." F7-DOWN's kernel `eventually_abs_mvfderiv_comp_sub_model_le`
takes ANY source functions with a dual-form gradient estimate along `j_i` of LFR26's collar. Here
the source functions are LFR27's quotients `η_i = F_i/ρ_i`, with LFR27's OUTPUT clauses as inputs
(gradient form, on `C_i = B̄(p_i, 20Δ) ∩ {3Δ/4 ≤ d_{A_i} ≤ 21Δ/2}`, nearest directions in the
finite-order vocabulary, which is LFR27's `minimizingDirectionsTo` by
`minimizingDirectionsTo_eq_setOf_expMap`):

* `abs_mvfderiv_quotient_add_inner_le`: `‖∇F + v‖ < ε` and `‖∇η - ∇F‖ ≤ 100ΔΛ` give
  `|dη(w) + g(v, w)| ≤ (ε + 100ΔΛ)|w|` (Cauchy–Schwarz);
* `eventually_mem_edgeSmoothingCore`: eventually `j_i` maps the collar
  `|t| ≤ 10Δ, 2.5Δ ≤ r ≤ 6.5Δ` into `C_i` (metric convergence, LFR25.2
  `coarseBorder_abs_infDist_sub_height_le`, the height comparison (LFR28.2) at slack `1/50`);
* `eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le` (**LFR28.4 with η_i**): for every
  `c > 40√(h+τ)`, `ε' > 0`, eventually on the collar
  `|d(η_i ∘ j_i)(X) - dG_N(X)| ≤ (ε + 100ΔΛ + ε_N + c + ε')|X|`.

Deviation: `τ ≤ 1/4` (instead of the kernel's `τ ≤ 1`) so that the collar lands in LFR27's core
`C_i`; LFR28 has `τ ≤ τ₀ < 10⁻⁸`. The blueprint's `150ΔΛ` is LFR27's proved `100ΔΛ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']

/-- **Quotient gradient in dual form.** If `‖∇F + v‖ < ε` and `‖∇η - ∇F‖ ≤ λ` at `y`, then
`|dη(w) + g(v, w)| ≤ (ε + λ)|w|` for every `w`. -/
theorem abs_mvfderiv_quotient_add_inner_le (g : SmoothRiemannianMetric I M') {F η : M' → ℝ}
    {y : M'} {v : TangentSpace I y} {ε lam : ℝ}
    (hF : Real.sqrt (g.inner y (gradFun g F y + v) (gradFun g F y + v)) < ε)
    (hq : Real.sqrt (g.inner y (gradFun g η y - gradFun g F y) (gradFun g η y - gradFun g F y)) ≤
      lam)
    (w : TangentSpace I y) :
    |mvfderiv I η y w + g.inner y v w| ≤ (ε + lam) * Real.sqrt (g.inner y w w) := by
  have hd : mvfderiv I η y w = g.inner y (gradFun g η y) w :=
    (DifferentialGeometry.Geometry.Connection.gradFun_metricDual g η y w).symm
  have hsplit : mvfderiv I η y w + g.inner y v w =
      g.inner y (gradFun g η y - gradFun g F y) w + g.inner y (gradFun g F y + v) w := by
    rw [hd]
    simp
    ring
  rw [hsplit]
  have h1 := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt g y
    (gradFun g η y - gradFun g F y) w
  have h2 := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt g y
    (gradFun g F y + v) w
  have hw : 0 ≤ Real.sqrt (g.inner y w w) := Real.sqrt_nonneg _
  have h1' : Real.sqrt (g.inner y (gradFun g η y - gradFun g F y)
      (gradFun g η y - gradFun g F y)) * Real.sqrt (g.inner y w w) ≤
      lam * Real.sqrt (g.inner y w w) := mul_le_mul_of_nonneg_right hq hw
  have h2' : Real.sqrt (g.inner y (gradFun g F y + v) (gradFun g F y + v)) *
      Real.sqrt (g.inner y w w) ≤ ε * Real.sqrt (g.inner y w w) :=
    mul_le_mul_of_nonneg_right hF.le hw
  calc |g.inner y (gradFun g η y - gradFun g F y) w + g.inner y (gradFun g F y + v) w|
      ≤ |g.inner y (gradFun g η y - gradFun g F y) w| + |g.inner y (gradFun g F y + v) w| :=
        abs_add_le _ _
    _ ≤ (ε + lam) * Real.sqrt (g.inner y w w) := by linarith

end Pointwise

section Row

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ N]
  [∀ i, IsManifold I ∞ (M i)] in
/-- **The collar lands in LFR27's core.** Under metric convergence on balls about `q`, the
coarse-border chart data and the height comparison (LFR28.2) at slack `1/50`, with `τ ≤ 1/4`:
eventually every collar point `|t| ≤ 10Δ`, `2.5Δ ≤ r ≤ 6.5Δ` is mapped by `j_i` into
`B̄(p_i, 20Δ) ∩ {3Δ/4 ≤ d_{A_i} ≤ 21Δ/2}`. -/
theorem eventually_mem_edgeSmoothingCore {K : ℕ} (q : N)
    (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ h : ℝ} (hΔ : 0 < Δ) (hτ4 : τ ≤ 1 / 4) (hh1 : h < 1 / 100)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i))
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hhgt : ∀ h' : ℝ, h < h' → ∀ᶠ i in atTop, ∀ x ∈ ball q (100 * Δ),
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ) :
    ∀ᶠ i in atTop, ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      j i x ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ} := by
  filter_upwards [hdist (17 * Δ) Δ hΔ, hhgt (1 / 50) (by linarith)] with i hdi hhi
  intro x ht hr1 hr2
  have hxq : dist x q ≤ 33 / 2 * Δ := by
    have := dist_le_abs_fst_add_axisDist Φ hΦq x
    linarith
  have hx17 : x ∈ ball q (17 * Δ) := by
    rw [mem_ball]
    linarith
  have hq17 : q ∈ ball q (17 * Δ) := mem_ball_self (by linarith)
  have hj := abs_lt.mp (hdi x hx17 q hq17)
  have hjx : dist (j i x) (j i q) < 35 / 2 * Δ := by linarith [hj.2]
  have hx100 : x ∈ ball q (100 * Δ) := by
    rw [mem_ball]
    linarith
  have hh := abs_le.mp (hhi x hx100)
  have hτ1 : τ ≤ 1 := by linarith
  have hb := abs_le.mp (coarseBorder_abs_infDist_sub_height_le hΔ hτ1 (hQp i) (hQdist i)
    (hheight i) (hpA i) (hborder i) (hbordercover i)
    (show j i x ∈ ball (j i q) (70 * Δ) by rw [mem_ball]; linarith))
  have hτ0 : 0 ≤ τ * Δ := by
    have hp : j i q ∈ ball (j i q) (200 * Δ) := mem_ball_self (by linarith)
    simpa using hQdist i (j i q) hp (j i q) hp
  have hτΔ : τ * Δ ≤ 1 / 4 * Δ := mul_le_mul_of_nonneg_right hτ4 hΔ.le
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_closedBall]
    linarith
  · nlinarith
  · nlinarith

/-- **(LFR28.4) for the edge quotient `η_i = F_i/ρ_i` (the LFR27 binding).** The hypotheses of
`eventually_abs_mvfderiv_comp_sub_model_le` with `τ ≤ 1/4`, where the source functions are LFR27's
quotients: `ρ_i` `Λ`-Lipschitz, `ρ_i(p_i) = 1`, smooth on `B(p_i, 100Δ)`, `100ΔΛ < 1/100`; `F_i`
smooth on an open `O_i ⊇ C_i` with LFR27's clauses `‖∇F_i + v‖ < ε` (every nearest direction) and
`‖∇(F_i/ρ_i) - ∇F_i‖ ≤ 100ΔΛ` on `C_i`. Then for every `c > 40√(h+τ)` and `ε' > 0`, eventually on
the collar `|d(η_i ∘ j_i)(X) - dG_N(X)| ≤ (ε + 100ΔΛ + ε_N + c + ε')|X|_G`. -/
theorem eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le [∀ i, CompleteSpace (M i)]
    [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    [CompleteSpace N] {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hGsec : ∀ (y : N) (w₁ w₂ : TangentSpace I y), 0 ≤ G.sectionalCurvature y w₁ w₂)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ k h : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτ4 : τ ≤ 1 / 4) (hk : 0 < k)
    (hkΔ : k * Δ ≤ 1 / 100) (hh : 0 < h) (hh1 : h < 1 / 100)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i))
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hQcover : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball (j i q) (200 * Δ), dist (Q i x) z ≤ τ * Δ)
    (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hsec : ∀ i, letI : RiemannianBundle (fun x : M i => TangentSpace I x) :=
        ⟨(g i).toRiemannianMetric⟩
      ∀ z ∈ ball (j i q) (1000 * Δ), DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt
        (g i) z (-k ^ 2))
    (hhgt : ∀ h' : ℝ, h < h' → ∀ᶠ i in atTop, ∀ x ∈ ball q (100 * Δ),
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ)
    (hAc : ∀ i, IsClosed (A i))
    (F ρ : ∀ i, M i → ℝ) {Λ : ℝ≥0} {ε : ℝ} (hε : 0 ≤ ε)
    (hρ : ∀ i, LipschitzWith Λ (ρ i)) (hρp : ∀ i, ρ i (j i q) = 1)
    (hlam : 100 * Δ * Λ < 1 / 100)
    (hρs : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ρ i) (ball (j i q) (100 * Δ)))
    (O : ∀ i, Set (M i)) (hO : ∀ i, IsOpen (O i))
    (hCO : ∀ i, closedBall (j i q) (20 * Δ) ∩
      {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ} ⊆ O i)
    (hFs : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (F i) (O i))
    (hFgrad : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      ∀ v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) y,
        Real.sqrt ((g i).inner y (gradFun (g i) (F i) y + v) (gradFun (g i) (F i) y + v)) < ε)
    (hquot : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      Real.sqrt ((g i).inner y (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)
        (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)) ≤ 100 * Δ * Λ)
    (GN : N → ℝ) {εN : ℝ}
    (hGgrad : ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ G.finiteMinimizingDirectionsTo (Φ ⁻¹' {z | z.snd = z₀}) x, ∀ X : TangentSpace I x,
        |mvfderiv I GN x X + G.inner x v X| ≤ εN * Real.sqrt (G.inner x X X)) :
    ∀ c : ℝ, 40 * Real.sqrt (h + τ) < c → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ i in atTop, ∀ x : N,
      |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ → dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ X : TangentSpace I x,
        |mvfderiv I (fun y => F i (j i y) / ρ i (j i y)) x X - mvfderiv I GN x X| ≤
          (ε + 100 * Δ * Λ + εN + c + ε') * Real.sqrt (G.inner x X X) := by
  have hcore := eventually_mem_edgeSmoothingCore q j hdist Φ hΦq hΔ hτ4 hh1 Q A hQp hQdist
    hheight hpA hborder hbordercover hhgt
  have hρpos : ∀ i, ∀ y ∈ ball (j i q) (100 * Δ), ρ i y ≠ 0 := by
    intro i y hy
    have h1 := (hρ i).dist_le_mul y (j i q)
    rw [Real.dist_eq, hρp i] at h1
    have h2 : (Λ : ℝ) * dist y (j i q) ≤ Λ * (100 * Δ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) Λ.coe_nonneg
    have h3 := (abs_le.mp h1).1
    intro h0
    rw [h0] at h3
    nlinarith
  have hFd : ∀ᶠ i in atTop, ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => F i z / ρ i z) (j i x) := by
    filter_upwards [hcore] with i hci
    intro x ht hr1 hr2
    have hC := hci x ht hr1 hr2
    have h100 : j i x ∈ ball (j i q) (100 * Δ) := by
      have := hC.1
      rw [mem_closedBall] at this
      rw [mem_ball]
      linarith
    have hFx := (hFs i).contMDiffAt ((hO i).mem_nhds (hCO i hC))
    have hρx := (hρs i).contMDiffAt (isOpen_ball.mem_nhds h100)
    exact (hFx.div₀ hρx (hρpos i _ h100)).mdifferentiableAt (by simp)
  have hFgrad' : ∀ᶠ i in atTop, ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) (j i x),
      ∀ w : TangentSpace I (j i x),
        |mvfderiv I (fun z => F i z / ρ i z) (j i x) w + (g i).inner (j i x) v w| ≤
          (ε + 100 * Δ * Λ) * Real.sqrt ((g i).inner (j i x) w w) := by
    filter_upwards [hcore] with i hci
    intro x ht hr1 hr2 v hv w
    have hC := hci x ht hr1 hr2
    exact abs_mvfderiv_quotient_add_inner_le (g i) (hFgrad i _ hC v hv) (hquot i _ hC) w
  have hεS : 0 ≤ ε + 100 * Δ * Λ := by
    have : 0 ≤ 100 * Δ * (Λ : ℝ) := by positivity
    linarith
  exact eventually_abs_mvfderiv_comp_sub_model_le hr G hGnorm hGsec g hmetric hK q j hexh hconv
    hdist hcover Φ hΦq hΔ hτ (by linarith) hk hkΔ hh hh1 Q A hQp hQdist hheight hQcover hpA hborder
    hbordercover hsec hhgt hAc (fun i z => F i z / ρ i z) hεS hFd hFgrad' GN hGgrad

end Row

end DifferentialGeometry.Geometry.Collapse
