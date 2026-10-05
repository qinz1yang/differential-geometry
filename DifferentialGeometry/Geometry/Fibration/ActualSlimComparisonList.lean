import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualZeroMeetingClauses

/-!
# SGP01: the actual slim comparison list (the whole row)

Blueprint `master207B.tex`, SGP01 (`lem:fibration-slim-comparison-list`, B:4353–4408), on the final
family with LC62's local comparison `P : LocalChartPacketsR`, `L = 10⁶Δ`, `ℓ = 10⁵Δ`,
`D_i = B(i, .95Lρ(i))`, `J_i = sgpSlimList P.slim i` (C14-SGP's list: slim centres whose CLOSED
cutoff support meets `D_i`):

* `SlimCentre.dist_lt_of_abs_coord_le_ZERO`: LFR20.2 (the slim chart's `enclosure`) in physical
  form: `|η_j| ≤ 905·10³Δ` on `B(j, Lρ(j))` puts the point in `B(j, .91Lρ(j))`.
* `sgpSlimList_ncard_le_ZERO`: `|J_i| ≤ N_*`, `N_* = egp02SlimCount` (LC87's numerical slim
  multiplicity constant, chosen before `Δ` and noncollapse): every listed centre has `i` within
  `2·10⁶Δρ(j)` (meeting point, `.91L`-support, `.99 < s_j`).
* `sgp01_row`: `i ∈ J_i`, `|J_i| ≤ N_*`, (SL), the zero clauses (`sgp01_zero_clauses`, C14-ZERO
  G1) and the plateau `{|η_i| ≤ 8ℓ} ⊂ B(i, .91Lρ(i)) ⊂ D_i` (strictly inside `D_i`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNS_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNS_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCS_ZERO
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LFR20.2 in physical form**: at a slim centre `j`, a point of `B(j, Lρ(j))` with
`|η_j| ≤ 905·10³Δ` lies in `B(j, .91Lρ(j))`. -/
theorem SlimCentre.dist_lt_of_abs_coord_le_ZERO {β₁ : ℝ} {j : X}
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) {x : X} (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j))
    (hη : |c.coord x| ≤ 905 * 10 ^ 3 * Δ) : dist x j < 91 / 100 * (10 ^ 6 * Δ) * ρ j := by
  have hr := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hr hx
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h := P.enclosure x hd hη
  have h' : (ρ j)⁻¹ * @dist X mX.toDist x j < 91 / 100 * (10 ^ 6 * Δ) := h
  rw [inv_mul_lt_iff₀ hr] at h'
  change @dist X mX.toDist x j < 91 / 100 * (10 ^ 6 * Δ) * ρ j
  linarith

/-- **SGP01, the count**: `|J_i| ≤ N_*` with the numerical `N_* = egp02SlimCount` (LC87's slim
multiplicity constant). A listed centre `j` has its closed support within `.91Lρ(j)` of `j` and
`.99 < ρ(j)/ρ(i)`, so `d(i, j) < .95Lρ(i) + .91Lρ(j) < 2Lρ(j)`. -/
theorem sgpSlimList_ncard_le_ZERO
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : X) :
    ((sgpSlimList L.slim i).ncard : ℝ) ≤ egp02SlimCount := by
  have hsub : sgpSlimList L.slim i ⊆
      L.slim.centres ∩ {j | i ∈ ball j (2000000 * (Δ * ρ j))} := by
    intro j hj
    obtain ⟨hjc, hs1, -, -⟩ := sgpSlimList_bounds L hΔ hΛ hLΛ hj
    obtain ⟨-, y, hy1, hy2⟩ := hj
    have hyj := (fc18_slim_row L hΔ hjc).1 hy1
    rw [mem_closedBall] at hyj
    have hyi : dist y i < 95 / 100 * (1000000 * Δ) * ρ i := hy2
    have hri := hρ i
    have hrj := hρ j
    have hij : ρ i < 100 / 99 * ρ j := by
      rw [lt_div_iff₀ hri] at hs1
      linarith
    have hdist : dist i j ≤ dist y i + dist y j := by
      have := dist_triangle i y j
      rw [dist_comm i y] at this
      exact this
    have hΔj : 0 < Δ * ρ j := mul_pos hΔ hrj
    have hstep : 95 / 100 * (1000000 * Δ) * ρ i ≤ 95 / 100 * (1000000 * Δ) * (100 / 99 * ρ j) :=
      mul_le_mul_of_nonneg_left hij.le (by positivity)
    refine ⟨hjc, ?_⟩
    change dist i j < 2000000 * (Δ * ρ j)
    nlinarith
  have hS := Set.ncard_le_ncard hsub (L.slim.finite_centres.inter_of_left _)
  exact (Nat.cast_le.mpr hS).trans (L.slim.multiplicity i)

/-- **SGP01** (`lem:fibration-slim-comparison-list`) on `LocalChartPacketsR`, at a slim centre `i`
(`L = 10⁶Δ`, `ℓ = 10⁵Δ`, `D_i = B(i, .95Lρ(i))`, `LΛ < 10⁻⁵`, `T ≥ 1600L`, `e < 1/40`,
`0 ≤ σs ≤ 1/100`): `i ∈ J_i`; `|J_i| ≤ N_*`; (SL) `.99 < s_j < 1.01`, `d(i, j) < 2Lρ(i)`; at most
one zero support meets `D_i`, and a meeting one has `R₀/R_i ≥ T/20` and the whole `D_i` inside its
buffered shell `3R₀/20 < d(k, ·) < 19R₀/20`; every point of the original set `{|η_i| ≤ 8ℓ}` (in the
coordinate domain `B(i, Lρ(i))`) lies in `B(i, .91Lρ(i))`, strictly inside `D_i`. -/
theorem sgp01_row
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) {i : X}
    (hi : i ∈ P.slim.centres) :
    i ∈ sgpSlimList P.slim i ∧
    ((sgpSlimList P.slim i).ncard : ℝ) ≤ egp02SlimCount ∧
    (∀ j ∈ sgpSlimList P.slim i, 99 / 100 < ρ j / ρ i ∧ ρ j / ρ i < 101 / 100 ∧
      dist i j < 2 * (1000000 * Δ) * ρ i) ∧
    (∀ k₁ (hk₁ : k₁ ∈ P.zero.centres) k₂ (hk₂ : k₂ ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₁ hk₁).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₂ hk₂).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      k₁ = k₂) ∧
    (∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      T / 20 ≤ (P.zero.zero k hk).radius / ρ i ∧
      ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
        3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
          dist k x < 19 / 20 * (P.zero.zero k hk).radius) ∧
    ∀ q ∈ ball i (10 ^ 6 * Δ * ρ i), |(P.slim.centre i hi).coord q| ≤ 8 * (100000 * Δ) →
      q ∈ ball i (91 / 100 * (10 ^ 6 * Δ) * ρ i) := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨huniq, hzero⟩ := sgp01_zero_clauses P hΛ hΔ hLΛ he hT i
  refine ⟨sgpSlimList_mem_self P.toLocalChartFamily hΔ0 hσs hσs1 hi,
    sgpSlimList_ncard_le_ZERO P.toLocalChartFamily hΔ0 hΛ hLΛ i,
    fun j hj => (sgpSlimList_bounds P.toLocalChartFamily hΔ0 hΛ hLΛ hj).2, huniq,
    fun k hk hmeet => ?_, fun q hq hη => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hzero k hk hmeet
    exact ⟨h1, fun x hx => ⟨(h2 x hx).1, (h2 x hx).2.1⟩⟩
  · rw [mem_ball]
    exact SlimCentre.dist_lt_of_abs_coord_le_ZERO (P.slim.centre i hi) hq (by linarith)

end DifferentialGeometry.Geometry.Collapse
