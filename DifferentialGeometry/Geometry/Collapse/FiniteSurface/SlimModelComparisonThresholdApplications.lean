import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelComparisonThreshold

/-!
# Consumer of the LFR20 comparison export: SGP01's plateau enclosure

Blueprint SGP01 (master207B:4396–4403), last assertion: "use the SAME slim product map … Choose its
distortion below `Δ/100` and the smooth coordinate value error below `Δ/100`. Pointed product
distance gives `R_i⁻¹ d(p_i, q) ≤ √((8ℓ + Δ/100)² + (1000Δ)²) + Δ/100 < .81L`" for every `q` with
`|η(q)| ≤ 8ℓ`, `ℓ = 10⁵Δ`.

* `SlimProductModel.dist_lt_of_abs_coord_le`: for ANY product model whose embedding has distortion
  `< Δ/100` on the cylinder `{|t| ≤ 19L/20}`, every point of `B(p, L)` with `|η| ≤ 8·10⁵Δ` lies in
  `B(p, 81L/100)` (deterministic; the model's own fibre and value clauses and the factor diameter).
* `slimChart_plateau_dist_lt_threshold`: with the threshold of
  `slimChart_model_comparison_threshold` at `ε = Δ/100`, `R = 0`, this holds for the SAME model.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry
open DifferentialGeometry.Integral.Measure

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_euclidean_three_cmpApp_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

section Deterministic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **SGP01's plateau enclosure through the same product model.** -/
theorem SlimProductModel.dist_lt_of_abs_coord_le {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm g} {Δ σ : ℝ} {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β} {c : SlimChart g hEnorm Δ σ α}
    {K : ℕ} (P : SlimProductModel c K) (hΔ : 0 < Δ)
    (hcmp : ∀ x y : P.N, |(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) →
      |(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) → |dist (P.j x) (P.j y) - dist x y| < Δ / 100)
    {y : M} (hy : y ∈ ball p (10 ^ 6 * Δ)) (hη : |c.coord y| ≤ 8 * 10 ^ 5 * Δ) :
    dist p y < 81 / 100 * (10 ^ 6 * Δ) := by
  obtain ⟨x, hxt, rfl⟩ := P.fibres y hy (by linarith)
  have hxb : |(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) := by linarith
  have hqb : |(P.e P.q).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) := by rw [P.t_q, abs_zero]; positivity
  have hval := (P.cylinder x hxb).2.1
  have hd := hcmp P.q x hqb hxb
  rw [P.j_q] at hd
  have htx : |(P.e x).fst| < 8 * 10 ^ 5 * Δ + 2 * (Δ / 100) := by
    have := abs_sub_abs_le_abs_sub (P.e x).fst (c.coord (P.j x))
    rw [abs_sub_comm] at this
    linarith
  have hsq := WithLp.prod_dist_sq_eq_add_sq (P.e P.q) (P.e x)
  have hW := P.factor_dist (P.e P.q).snd (P.e x).snd
  have hfst : dist (P.e P.q).fst (P.e x).fst = |(P.e x).fst| := by
    rw [Real.dist_eq, P.t_q, zero_sub, abs_neg]
  rw [hfst, P.e.dist_eq] at hsq
  have hqx : dist P.q x ≤ |(P.e x).fst| + 10 ^ 3 * Δ := by
    have h0 := dist_nonneg (x := P.q) (y := x)
    have h1 := abs_nonneg (P.e x).fst
    have h2 := dist_nonneg (x := (P.e P.q).snd) (y := (P.e x).snd)
    nlinarith
  have := (abs_lt.mp hd).2
  linarith

end Deterministic

/-- **SGP01's plateau enclosure for the threshold model.** With LFR20's comparison tolerance
`Δ/100` fixed before `β₀`, the SAME model `P` has distortion `< Δ/100` on its cylinder and every
point of `B(p, L)` with `|η| ≤ 8·10⁵Δ` lies in `B(p, 81L/100)`. -/
theorem slimChart_plateau_dist_lt_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ManifoldOrientation (𝓡 3) M 3 → ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∀ (Y : Type w) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        ∀ c : SlimChart g hEnorm Δ σ α, ∃ P : SlimProductModel c K,
          (∀ x y : P.N, |(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) →
            |(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) → |dist (P.j x) (P.j y) - dist x y| < Δ / 100) ∧
          ∀ y ∈ ball p (10 ^ 6 * Δ), |c.coord y| ≤ 8 * 10 ^ 5 * Δ →
            dist p y < 81 / 100 * (10 ^ 6 * Δ) := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨β₀, hβ₀, h⟩ := slimChart_model_comparison_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A
    (show 0 < Δ / 100 by positivity) 0
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec Y _ y₀ α hD c =>
    ?_⟩
  obtain ⟨P, -, -, hdist, -⟩ := h β hβ hββ₀ M g hEnorm o p hvol hcurv hsec Y y₀ α hD c
  have hcmp : ∀ x y : P.N, |(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) →
      |(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) → |dist (P.j x) (P.j y) - dist x y| < Δ / 100 :=
    fun x y hx hy => hdist x y (Or.inl hx) (Or.inl hy)
  exact ⟨P, hcmp, fun y hy hη => P.dist_lt_of_abs_coord_le hΔ0 hcmp hy hη⟩

end DifferentialGeometry.Geometry.Collapse
