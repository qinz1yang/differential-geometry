import DifferentialGeometry.Geometry.Fibration.ActualSlimDerivativeComparison
import DifferentialGeometry.Geometry.Fibration.ActualReplacementEdgeBall

/-!
# FDC01's zero and slim exclusions: the metric inputs on the original charts

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7177–7199):
"If `p_i` were zero-stratum, LPA05's actual tenth-radius cover would put it in `B(z, R₀/10)` for a
selected zero center. The same shell scale comparison gives `ρ(p_i) ≤ 20R₀/T₀`. Therefore
`d(q, z) < (1/10 + 200Δ/T₀)R₀ < .38R₀`." and "If `p_i` were slim, LPA06's actual slim cover would
put it in `B(p_k, ΔR_k)` for a selected slim center. Slow variation then gives
`d(q, p_k) < 12ΔR_k`. Its original value estimate puts `|η_k(q)| < 13Δ`."

The contradictions themselves ("ZSP02 puts this ball in `int Z`", "GAF07 and (SK) put `q` over
`int K₃`") concern the final map `E` and are NOT here. The family's covers have slightly different
constants: the zero cover is the tenth-radius cover itself (`covers_stratum`); the slim cover puts
`p` in `B(k, 2Δρ(k))` (not `ΔR_k`), whence `d(q, k) < 9Δρ(k)`, `|η_k(q)| < 10Δ` (inside the
blueprint's `12Δ`, `13Δ`). The scale comparison used is the `Λ`-Lipschitz bound of `ρ` with
`Tρ(z) ≤ R_z` (LC80's radius clause), `T ≥ 1000Δ`.

* `SlimCentre.coord_self_FDC1`: the slim coordinate vanishes at its centre.
* `fdc01_zero_exclusion_FDC1`: a zero-stratum point `p` and `d(q, p) < 6Δρ(p)` give a selected
  zero centre `z` with `p ∈ B(z, R_z/10)` and `d(q, z) < .38R_z`.
* `fdc01_slim_exclusion_FDC1`: a slim one-stratum point `p` and `d(q, p) < 6Δρ(p)` give a selected
  slim centre `k` with `d(q, k) < 9Δρ(k)` and `|η_k(q)| < 10Δ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

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

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNPk_FDC1
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNPk_FDC1
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCPk_FDC1
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The slim coordinate of an actual slim packet vanishes at its centre. -/
theorem SlimCentre.coord_self_FDC1 {β₁ : ℝ} {j : X}
    (S : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) : S.coord j = 0 := by
  have hr := hρ j
  unfold SlimCentre.coord
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hr)).mpr hMc
  exact P.coord_center

/-- **FDC01's zero exclusion, metric input**: on the actual packets, a zero-stratum point `p` and
a point `q` with `d(q, p) < 6Δρ(p)` (EDP03's enclosure) give a selected zero centre `z` with
`p ∈ B(z, R_z/10)` (LPA05's tenth-radius cover) and `d(q, z) < .38R_z` (`T ≥ 1000Δ`,
`100ΔΛ ≤ 1/100`). -/
theorem fdc01_zero_exclusion_FDC1
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hT : 1000 * Δ ≤ T) {p q : X}
    (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0) (hqp : dist q p < 6 * Δ * ρ p) :
    ∃ z, ∃ hz : z ∈ P.zero.centres, dist p z < (P.zero.zero z hz).radius / 10 ∧
      dist q z < 38 / 100 * (P.zero.zero z hz).radius := by
  have hcov := P.zero.covers_stratum hp
  simp only [mem_iUnion] at hcov
  obtain ⟨z, hz, hpz⟩ := hcov
  refine ⟨z, hz, hpz, ?_⟩
  set R := (P.zero.zero z hz).radius with hRdef
  have hrz := hρ z
  have hT0 : 0 < T := by nlinarith
  have hTR : T * ρ z ≤ R := (P.zero.radius_mem z hz).1
  have hR : 0 < R := lt_of_lt_of_le (mul_pos hT0 hrz) hTR
  have hpz' : dist p z < R / 10 := hpz
  -- the scale at `p`
  have hρp : ρ p ≤ ρ z + Λ * (R / 10) := by
    have h1 := P.lipschitz_scale.dist_le_mul p z
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist p z ≤ Λ * (R / 10) := mul_le_mul_of_nonneg_left hpz'.le hΛ
    linarith [(abs_le.mp h1).2]
  have h6 : 6 * Δ * ρ p ≤ 6 * Δ * ρ z + 6 * Δ * Λ * (R / 10) := by
    have := mul_le_mul_of_nonneg_left hρp (by positivity : (0 : ℝ) ≤ 6 * Δ)
    linarith
  have hz1 : 6 * Δ * ρ z ≤ 6 / 1000 * R := by
    have h1 : 1000 * Δ * ρ z ≤ T * ρ z := mul_le_mul_of_nonneg_right hT hrz.le
    linarith
  have hz2 : 6 * Δ * Λ * (R / 10) ≤ 6 / 100000 * R := by
    have h1 : Δ * Λ ≤ 1 / 10000 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hR.le
    nlinarith
  have h3 := dist_triangle q p z
  linarith

/-- **FDC01's slim exclusion, metric input**: a slim point `p` of the one-stratum (the ORIGINAL
slim predicate) and a point `q` with `d(q, p) < 6Δρ(p)` give a selected slim centre `k` with
`d(q, k) < 9Δρ(k)` and `|η_k(q)| < 10Δ` (`0 ≤ σs ≤ 1/100`, `100ΔΛ ≤ 1/100`). -/
theorem fdc01_slim_exclusion_FDC1
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) {p q : X} (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hsl : ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))
    (hqp : dist q p < 6 * Δ * ρ p) :
    ∃ k, ∃ hk : k ∈ L.slim.centres, dist q k < 9 * Δ * ρ k ∧
      |(L.slim.centre k hk).coord q| < 10 * Δ := by
  obtain ⟨k, hk, hsub⟩ := L.slim.covers p hp hsl
  refine ⟨k, hk, ?_⟩
  have hrp := hρ p
  have hrk := hρ k
  have hpk : dist p k < 2 * (Δ * ρ k) := hsub (mem_ball_self (by positivity))
  have hρp : ρ p ≤ 10002 / 10000 * ρ k := by
    have h1 := L.lipschitz_scale.dist_le_mul p k
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist p k ≤ Λ * (2 * (Δ * ρ k)) := mul_le_mul_of_nonneg_left hpk.le hΛ
    have h3 : Δ * Λ * ρ k ≤ 1 / 10000 * ρ k := by
      have h4 : Δ * Λ ≤ 1 / 10000 := by linarith
      exact mul_le_mul_of_nonneg_right h4 hrk.le
    linarith [(abs_le.mp h1).2]
  have hqk : dist q k < 9 * Δ * ρ k := by
    have h1 := dist_triangle q p k
    have h2 : 6 * Δ * ρ p ≤ 6 * Δ * (10002 / 10000 * ρ k) :=
      mul_le_mul_of_nonneg_left hρp (by positivity)
    have := mul_pos hΔ hrk
    linarith
  refine ⟨hqk, ?_⟩
  have hlip := (L.slim.centre k hk).abs_coord_sub_le_SGP2 hσs q k
  rw [(L.slim.centre k hk).coord_self_FDC1, sub_zero] at hlip
  have h1 : (1 + σs) * (ρ k)⁻¹ * dist q k ≤ 101 / 100 * (ρ k)⁻¹ * dist q k := by
    have := inv_pos.mpr hrk
    gcongr
    linarith
  have h2 : 101 / 100 * (ρ k)⁻¹ * dist q k < 101 / 100 * (ρ k)⁻¹ * (9 * Δ * ρ k) :=
    mul_lt_mul_of_pos_left hqk (by positivity)
  have h3 : 101 / 100 * (ρ k)⁻¹ * (9 * Δ * ρ k) = 909 / 100 * Δ := by
    have hc : (ρ k)⁻¹ * ρ k = 1 := inv_mul_cancel₀ hrk.ne'
    linear_combination (909 / 100 * Δ) * hc
  linarith

end DifferentialGeometry.Geometry.Collapse
