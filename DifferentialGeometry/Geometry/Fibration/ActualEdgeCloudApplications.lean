import DifferentialGeometry.Geometry.Fibration.ActualEdgeCloud
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphApplications

/-!
# EGP07: the all-preimage rank on the final family (Tier 3)

Blueprint `master207B.tex`, EGP07 (`thm:fibration-actual-second-cloud`, B:5141–5225): "At EVERY
`q ∈ M` with `π₂F(q) = x`, projection of `D(π₂F)_q` to `A_x⁰` is onto, its nonzero singular value
lies in `[1/2, 3C†]`, and its normal error is less than `e`." Here `T_x = DΦ_i(a)`, `a = η_i(p)`
for the core witness `i, p`, `A_x⁰ = range T_x`, and `P` is the orthogonal projection onto it.

* `egp07_rank_point_KC5`: at one core witness `p` of `i` and EVERY `q` with `π₂F(q) = π₂F(p)`,
  from EGP06's (EG) for any model `Φ` with `‖DΦ‖ ≤ C`, `|v| ≤ ‖DΦ(a)v‖`: `η_i(q) = η_i(p)`, the
  normal error `‖D w − P D w‖ < e`, the upper bound `‖P D w‖ ≤ 3C` for every `ρ(i)⁻²g`-unit `w`,
  a unit `w₀` with `‖P D w₀‖ ≥ 1/2`, and ontoness of `P D` onto `range T_x`
  (`D w = ρ(i)⁻¹ dπ₂F_q(w)`).
* `egp07_rank` (frozen): the row on every actual `LocalChartPacketsC14`, with EGP06's thresholds
  (`η₀` shrunk to `≤ 1/(1000·10⁶Δ)` for the reference test) and ONE choice of signs and
  translations carrying the model clauses, (EG) and the rank clauses together.
* `egp07_units_KC5`: physical units — for a `g`-unit `v`, `w = ρ(i)v` is `ρ(i)⁻²g`-unit and
  `D w = dπ₂F_q(v)` (the normalization cancels between source and target, as in SGP05).

Deviation (D-KC4-3): FC06's abstract `projected_rank_of_one_dimensional_reference` is replaced by
its rank-one content (`rank_one_projection_KC5`, `rank_one_onto_KC5`); the singular-value interval
is stated as `‖P D w‖ ≤ 3C†` on unit vectors together with a unit `w₀` with `‖P D w₀‖ ≥ 1/2`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- EGP06's early constant is large: `1 ≤ C†`. -/
theorem one_le_egpGraphConst_KC5 : 1 ≤ egpGraphConst := by
  have h1 := egp02ListBound_pos_KC4
  have h2 := one_le_egpProfileConst
  unfold egpGraphConst
  nlinarith

/-- EGP07's coordinate quality: `σ ≤ (e/(20C†))²/10⁸` with `0 < e < 1/100` gives `σ < 1/20`. -/
theorem egp07_sigma_small_KC5 {eg σ : ℝ} (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hσ : σ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8) : σ < 1 / 20 := by
  have hC := one_le_egpGraphConst_KC5
  have hx0 : 0 < eg / (20 * egpGraphConst) := by positivity
  have hx1 : eg / (20 * egpGraphConst) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hx2 : (eg / (20 * egpGraphConst)) ^ 2 < 1 := by nlinarith
  linarith

section Point

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **EGP07's rank at every preimage of a core point** (any model `Φ` with EGP06's (EG), derivative
bound `C ≥ 1` and identity component). With `T = DΦ(η_i(p))`, `P` the orthogonal projection onto
`range T` and `D w = ρ(i)⁻¹ dπ₂F_q(w)`: `η_i(q) = η_i(p)`; for every `ρ(i)⁻²g`-unit `w` the normal
error `‖D w − P D w‖ < e` and `‖P D w‖ ≤ 3C`; some unit `w₀` has `‖P D w₀‖ ≥ 1/2`; and `P ∘ D` is
onto `range T`. -/
theorem egp07_rank_point_KC5
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (hΔ : 1 ≤ Δ) (hσ : σc < 1 / 20) (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) {eg Cd : ℝ}
    (heg1 : eg < 1 / 100) (hCd : 1 ≤ Cd) {i : X} (hi : i ∈ L.edge.centres)
    (Φ : ℝ → BlockSpace (fun _ : CGPTag L Z => ℝ²)) (hΦC : ∀ a, ‖fderiv ℝ Φ a‖ ≤ Cd)
    (hΦlow : ∀ a v : ℝ, ‖v‖ ≤ ‖fderiv ℝ Φ a v‖)
    (hEG : ∀ x ∈ ball i (100 * Δ * ρ i), |L.edge.coord i x| ≤ 8 * Δ →
      cgpHeight L x ≤ 8 * Δ → ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) x w -
          fderiv ℝ Φ (L.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w)‖ < eg)
    {p : X} (hp : p ∈ ball i (100 * Δ * ρ i)) (hηp : |L.edge.coord i p| ≤ 8 * Δ)
    (htp : cgpHeight L p ≤ 8 * Δ) {q : X}
    (hpq : cgpProjMap L Z (cgpQ2Tags L Z) q = cgpProjMap L Z (cgpQ2Tags L Z) p) :
    L.edge.coord i q = L.edge.coord i p ∧
      (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w -
          (LinearMap.range (fderiv ℝ Φ (L.edge.coord i p) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²))).starProjection
            ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w)‖ < eg) ∧
      (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
        ‖(LinearMap.range (fderiv ℝ Φ (L.edge.coord i p) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²))).starProjection
            ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w)‖ ≤ 3 * Cd) ∧
      (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
        1 / 2 ≤ ‖(LinearMap.range (fderiv ℝ Φ (L.edge.coord i p) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²))).starProjection
            ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w₀)‖) ∧
      ∀ k ∈ LinearMap.range (fderiv ℝ Φ (L.edge.coord i p) :
          ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²)),
        ∃ w : TangentSpace 𝓘(ℝ, E3) q,
          (LinearMap.range (fderiv ℝ Φ (L.edge.coord i p) :
            ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²))).starProjection
            ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w) = k := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  let j : L.edge.finite_centres.toFinset := ⟨i, (Set.Finite.mem_toFinset _).mpr hi⟩
  have hcutp : L.edge.cutoff j.1 p = 1 := L.edge.cutoff_eq_one_of_le hΔ0 hi hp hηp htp
  have hex := egp07_exact_coordinate L Z j hcutp hpq
  obtain ⟨hcutq, hηq⟩ := hex
  have hle := L.edge.le_of_cutoff_eq_one_KC5 hΔ0 hcutq
  obtain ⟨-, hq100, hηq8, htq⟩ := hle
  have hEGq := hEG q hq100 hηq8 htq
  change L.edge.coord i q = L.edge.coord i p at hηq
  rw [hηq] at hEGq
  have href := egp07_reference_bounds_wide_KC5 L.edge hΔ hσ hbL hi hq100
  obtain ⟨⟨w₀, hw₀, hw₀η⟩, hup⟩ := href
  set Tq := fderiv ℝ Φ (L.edge.coord i p) with hTq
  have hT : ∀ z : ℝ, |z| ≤ ‖Tq z‖ := fun z => by
    have := hΦlow (L.edge.coord i p) z
    rwa [Real.norm_eq_abs] at this
  have hTC : ‖Tq‖ ≤ Cd := hΦC _
  have hunit : ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
      |mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) q w| ≤ 2 := fun w hw => by
    have h := hup w
    rw [hw, Real.sqrt_one, mul_one] at h
    exact h
  have hrk := fun w (hw : (ρ i)⁻¹ ^ 2 * g.inner q w w = 1) =>
    rank_one_projection_KC5 Tq hT hTC (hEGq w hw)
  refine ⟨hηq, fun w hw => (hrk w hw).1, fun w hw => ?_, ⟨w₀, hw₀, ?_⟩, ?_⟩
  · obtain ⟨-, -, -, h4⟩ := hrk w hw
    have h2 := hunit w hw
    have h5 : Cd * |mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) q w| ≤ Cd * 2 :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  · obtain ⟨-, -, h3, -⟩ := hrk w₀ hw₀
    have h6 := le_abs_self (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) q w₀)
    linarith
  · obtain ⟨-, -, h3, -⟩ := hrk w₀ hw₀
    have h6 := le_abs_self (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) q w₀)
    have hne : (LinearMap.range (Tq : ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²))).starProjection
        ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w₀) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h3
      linarith
    refine rank_one_onto_KC5 Tq
      (fun w : TangentSpace 𝓘(ℝ, E3) q =>
        (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w) ?_ hne
    intro c w
    simp only [map_smul]
    exact smul_comm _ _ _

/-- **Physical units.** For a `g`-unit `v`, `w = ρ(i)v` is a `ρ(i)⁻²g`-unit vector and
`ρ(i)⁻¹ dπ₂F_q(w) = dπ₂F_q(v)`: the rank clauses for `ρ(i)⁻²g`-unit vectors and `D = ρ(i)⁻¹dπ₂F`
are the clauses for `g`-unit vectors and `D(π₂F)_q` itself. -/
theorem egp07_units_KC5
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X) {q : X}
    (v : TangentSpace 𝓘(ℝ, E3) q) (hv : g.inner q v v = 1) :
    (ρ i)⁻¹ ^ 2 * g.inner q (ρ i • v) (ρ i • v) = 1 ∧
      (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q (ρ i • v) =
        mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q v := by
  have hri := (hρ i).ne'
  refine ⟨?_, ?_⟩
  · rw [gInner_smul_self, hv, mul_one, ← mul_pow, inv_mul_cancel₀ hri, one_pow]
  · rw [map_smul, smul_smul, inv_mul_cancel₀ hri, one_smul]

end Point

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_KC5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_KC5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_KC5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **EGP07, the all-preimage rank, on the final family.** For `Δ ≥ 1`, `β₂ ∈ (0, 10⁻⁶)`,
`0 < eg < 1/100` there are `Lc, η₀ > 0` such that on every actual `LocalChartPacketsC14` with
EGP06's hypotheses, at every edge centre `i` there is ONE choice of signs and translations for which
`Φ_i` carries EGP06's model clauses and (EG), and at every core point `p` of `i`
(`p ∈ B(i, 100Δρ(i))`, `|η_i(p)| ≤ 8Δ`, `t(p) ≤ 8Δ`) and EVERY `q` with `π₂F(q) = π₂F(p)`:
`η_i(q) = η_i(p)`, and with `T = DΦ_i(η_i(p))`, `P` the orthogonal projection onto `range T`,
`D w = ρ(i)⁻¹dπ₂F_q(w)`: the normal error `‖D w − P D w‖ < eg` and `‖P D w‖ ≤ 3C†` for every
`ρ(i)⁻²g`-unit `w`, some unit `w₀` has `‖P D w₀‖ ≥ 1/2`, and `P ∘ D` is onto `range T`. -/
theorem egp07_rank {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∀ i ∈ P.edge.centres,
          ∃ sgn c : CGPTag P.toLocalChartFamily P.zero → ℝ, (∀ t, |sgn t| ≤ 1) ∧
            ContDiff ℝ ∞ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) ∧
            (∀ a, ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a‖ ≤
                egpGraphConst ∧
              ‖fderiv ℝ (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)) a‖ ≤
                egpGraphConst) ∧
            (∀ a v : ℝ, ‖v‖ ≤ ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a v‖) ∧
            (∀ a, blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
              (egpModelGraph P.toLocalChartFamily P.zero i sgn c a) =
                egpModelGraph P.toLocalChartFamily P.zero i sgn c a) ∧
            (∀ x ∈ ball i (100 * Δ * ρ i), |P.edge.coord i x| ≤ 8 * Δ →
              cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
              ‖(ρ i)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero) x -
                egpModelGraph P.toLocalChartFamily P.zero i sgn c (P.edge.coord i x)‖ < eg ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
                  fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w)‖ < eg) ∧
            ∀ p ∈ ball i (100 * Δ * ρ i), |P.edge.coord i p| ≤ 8 * Δ →
              cgpHeight P.toLocalChartFamily p ≤ 8 * Δ → ∀ q : X,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q =
                cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p →
              P.edge.coord i q = P.edge.coord i p ∧
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
                  (LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i p) : ℝ →ₗ[ℝ]
                      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
              (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
                ‖(LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i p) : ℝ →ₗ[ℝ]
                      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
              (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
                1 / 2 ≤ ‖(LinearMap.range (fderiv ℝ
                    (egpModelGraph P.toLocalChartFamily P.zero i sgn c) (P.edge.coord i p) :
                    ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
                    ).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                      (cgpProjMap P.toLocalChartFamily P.zero
                        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
              ∀ k ∈ LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                  (P.edge.coord i p) : ℝ →ₗ[ℝ]
                    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                ∃ w : TangentSpace 𝓘(ℝ, E3) q,
                  (LinearMap.range (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i p) : ℝ →ₗ[ℝ]
                      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
                    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                      (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k := by
  obtain ⟨Lc, η₀, hLc, hη₀, h6⟩ := egp06_full_C14 hΔ hβ₂ hβ₂1 heg heg1
  have hC1 := one_le_egpGraphConst_KC5
  have hL0 : (0 : ℝ) < 1 / (1000 * (1000000 * Δ)) := by
    have : (0 : ℝ) < Δ := by linarith
    positivity
  refine ⟨Lc, min η₀ (1 / (1000 * (1000000 * Δ))), hLc, lt_min hη₀ hL0, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  have hσ := egp07_sigma_small_KC5 heg heg1 hσc
  have hbL : b ≤ 1 / (1000 * (1000000 * Δ)) := hb.trans (min_le_right _ _)
  have h6P := h6 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _)) hLmax hΛ hLΛ hμ hτ hσc hμΔ
    hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  have h6i := h6P i hi
  obtain ⟨sgn, c, hsgn, hsm, hbd, hlow, hQ, hEG⟩ := h6i
  refine ⟨sgn, c, hsgn, hsm, hbd, hlow, hQ, hEG, ?_⟩
  intro p hp hηp htp q hpq
  exact egp07_rank_point_KC5 P.toLocalChartFamily P.zero hΔ hσ hbL heg1 hC1 hi _
    (fun a => (hbd a).1) hlow (fun x hx hη ht => (hEG x hx hη ht).2) hp hηp htp hpq

end DifferentialGeometry.Geometry.Collapse
