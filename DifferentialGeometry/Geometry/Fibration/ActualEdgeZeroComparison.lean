import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison
import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignmentEdge
import DifferentialGeometry.Geometry.Fibration.ActualEdgeAffineComparisonRV

/-!
# EGP04's zero block: (EC) for a zero support meeting `D_i`

Blueprint `master207B.tex`, EGP04 (B:4958–4959, proof B:5029–5039): "For a meeting zero block use
`U₀ = s₀η₀` and `λ₀(a) = a₀a + U₀(p_i)`; (EC) holds for it too." "For the zero block use the
reference axis lift of length `400Δ` with sign `a₀`. LC73 at EVERY `x ∈ D_i` has the same raw
distance function up to translation and units. Its own radius is `ρ(x)/(R_iζ₀) > 990L` in reference
units, while its separation threshold is `ρ(x)/R_i < 1.01`. The lift fits these original tests and
(ER0), proving the derivative estimate. LC67 bounds the centered value error by
`ε₀ d(p_i, x) < 20Δε₀`. Together with (ER0) and the reference value error this is less than `θ`."

* `EdgeFamily.test_phys_KC3`: the original edge test of chart `j` in physical form along a
  minimizing velocity of `exists_rescaled_minimizing_SGP2` (the convention of LC73's physical test
  `LocalChartPacketsZ.zero_adapted_phys_SGP3`, C14-SGP3).
* `egp04_zero_saturation_KC3` (step A): the lift `y` of `(u_i(x) + 400Δa₀, v_i(x))`, ONE minimizing
  segment from `x` to `y`, the edge test of chart `i` and LC73's test at `x` along it, and (ER0) at
  `x, y`: both `s₀dη₀` and `a₀dη_i` saturate on one unit vector of `ρ(i)⁻²g`.
* `egp04_zero_derivative_KC3` (step B): FC15's Riesz step, `|s₀dη₀(w) − a₀dη_i(w)| < θ`.
* `egp04_zero_value_KC3`: `|U₀ − λ₀(η_i)| < εr·ρ(i)⁻¹d(x, i) + E + μΔ` (LC67's GLOBAL
  difference-Lipschitz clause of the radial function, (ER0), the edge value error).
* `egp04_zero_row`: the zero block of (EC) on ALL of `D_i` on every actual `LocalChartPacketsZ`.
  The radial difference-Lipschitz constant enters as the ROW parameter bound `εr < θ/(100L)` on the
  family (the final producer `LocalChartPacketsC14` supplies `εr < cap` for any requested cap).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_KC3
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_KC3
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_KC3
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The original edge test in physical form.** For `x ∈ B(j, 100Δρ(j))`, `y ∈ B(j, 1000Δρ(j))`
with `d(x, y) > 100Δρ(j)` and a minimizing initial velocity `v` from `x` to `y` (as produced by
`exists_rescaled_minimizing_SGP2`): `|dη_j(v) − (u_j(y) − u_j(x))| < σ ρ(j)⁻¹ d(x, y)`. -/
theorem EdgeFamily.test_phys_KC3 (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    {j : X} (hj : j ∈ F.centres) {x y : X} (hx : x ∈ ball j (100 * Δ * ρ j))
    (hy : y ∈ ball j (1000 * Δ * ρ j)) (hxy : 100 * Δ * ρ j < dist x y)
    {v : TangentSpace 𝓘(ℝ, E3) x} (hvv : g.inner x v v = dist x y ^ 2)
    (hgeo : let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      ∀ c t : ℝ, c * t = 1 → intrinsicGeodesic gR hnR x (c • v) t = y) :
    |mvfderiv 𝓘(ℝ, E3) (F.coord j) x v - (egpRaw F j y - egpRaw F j x)| <
      σc * ((ρ j)⁻¹ * dist x y) := by
  have hc := F.chart_center j hj
  have hr := hρ j
  have hL : 0 < 100 * Δ * ρ j := pos_of_mem_ball hx
  have hx' : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hr hx
  have hy' : (ρ j)⁻¹ * dist y j < 1000 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hr hy
  have hxy' : 100 * Δ < (ρ j)⁻¹ * dist x y := by
    rw [lt_inv_mul_iff₀ hr]
    linarith
  have hd : 0 < dist x y := hL.trans hxy
  set d := dist x y with hddef
  set r := (ρ j)⁻¹ * d with hrdef
  have hrpos : 0 < r := by positivity
  have hct : ρ j / d * r = 1 := by rw [hrdef]; field_simp
  have hcr : ρ j / d = r⁻¹ := by rw [hrdef]; field_simp
  have hw1 : (ρ j)⁻¹ ^ 2 * g.inner x ((ρ j / d) • v) ((ρ j / d) • v) = 1 := by
    rw [gInner_smul_self, hvv]
    field_simp
  have hsm : mvfderiv 𝓘(ℝ, E3) (F.coord j) x ((ρ j / d) • v) =
      r⁻¹ * mvfderiv 𝓘(ℝ, E3) (F.coord j) x v := by
    rw [map_smul, smul_eq_mul, hcr]
  suffices hT' : |mvfderiv 𝓘(ℝ, E3) (F.coord j) x ((ρ j / d) • v) -
      (egpRaw F j y - egpRaw F j x) / r| < σc by
    rw [hsm] at hT'
    exact abs_sub_lt_of_normalized_SGP2 hrpos hT'
  have hrawx : egpRaw F j x = egpChartRaw F hj x := egpRaw_of_mem F hj x
  have hrawy : egpRaw F j y = egpChartRaw F hj y := egpRaw_of_mem F hj y
  have hcoord : F.coord j = (let C := F.chart j hj
      let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      C.coord) := by
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
  rw [hrawx, hrawy, hcoord]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hc' : C.center = j := hc
  let _ := C.instY
  have hxC : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hx'
  have hyC : y ∈ ball C.center (1000 * Δ) := by
    rw [hc']
    exact hy'
  have hw : gR.inner x ((ρ j / d) • v) ((ρ j / d) • v) = 1 := by
    rw [scaleMetric_inner]
    exact hw1
  have hg : intrinsicGeodesic gR hnR x ((ρ j / d) • v) (dist x y) = y := hgeo _ _ hct
  exact C.test x hxC y hyC hxy' _ hw hg

/-- EGP04's zero lift arithmetic: with `D = 400Δ − 4b`, `δ = 7b/4`, the lift data
`400Δ − 3b < r < 400Δ + 3b` and `a₀(u_i(y) − u_i(x)) > 400Δ − 2b` give `D < r < D + 4δ` and
`D + δ < a₀(u_i(y) − u_i(x))`. -/
theorem egp04_zero_lift_arith_KC3 {Δ b r A : ℝ} (hb : 0 < b) (h5b : 5 * b ≤ Δ)
    (hr1 : 400 * Δ - 3 * b < r) (hr2 : r < 400 * Δ + 3 * b) (hA : 400 * Δ - 2 * b < A) :
    0 < 400 * Δ - 4 * b ∧ 400 * Δ - 4 * b < r ∧ r < 400 * Δ - 4 * b + 4 * (7 * b / 4) ∧
      400 * Δ - 4 * b + 7 * b / 4 < A := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Step A of EGP04's zero block** (one point `x ∈ D_i` in LC73's closed shell of the zero ball
at `k`, with (ER0) of sign `a₀`): there is ONE unit vector of `ρ(i)⁻² g` at `x` on which
`s₀ dη₀ ≥ 1 − (ζ + F)` and `a₀ dη_i ≥ 1 − (σc + F)`, `F = (21b/4 + 2E)/(400Δ − 4b)`
(`s₀ = R₀/ρ(i)`). -/
theorem egp04_zero_saturation_KC3
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    {E a₀ : ℝ} (hΔ : 1 ≤ Δ) (hζ0 : 0 < ζ) (hζL : ζ ≤ 1 / (1000 * (1000000 * Δ)))
    (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ P.edge.centres)
    {k : X} (hk : k ∈ P.zero.centres) (ha₀ : a₀ = 1 ∨ a₀ = -1)
    (hal : ∀ x ∈ ball i (600 * Δ * ρ i),
      |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| < E)
    {x : X} (hx : x ∈ ball i (20 * Δ * ρ i))
    (h1 : (P.zero.zero k hk).radius / 10 ≤ dist k x)
    (h2 : dist k x ≤ 10 * (P.zero.zero k hk).radius)
    (hΛz : Λz ≤ (P.zero.zero k hk).radius / ρ x)
    (hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.zero.zero k hk).radial x)
    (hρx1 : 99 / 100 * ρ i < ρ x) (hρx2 : ρ x < 101 / 100 * ρ i) :
    0 < b ∧ 0 ≤ E ∧ 0 < σc ∧ ∃ v : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x v v = 1 ∧
      1 - (ζ + (3 * (7 * b / 4) + 2 * E) / (400 * Δ - 4 * b)) ≤
        (P.zero.zero k hk).radius / ρ i * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v ∧
      1 - (σc + (3 * (7 * b / 4) + 2 * E) / (400 * Δ - 4 * b)) ≤
        a₀ * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x v := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrx := hρ x
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hal i (mem_ball_self (by positivity))).le
  obtain ⟨hZlip, hZtest⟩ := P.zero_adapted_phys_SGP3 hk h1 h2 hΛz hdiff
  clear hZlip
  obtain ⟨Bi, mBi, qi, ψ, hψx⟩ := exists_edge_split_KC2 P.edge hi
  have hb0 : 0 < b := @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Bi))
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ b ψ
  have hbinv : 1000 * (1000000 * Δ) ≤ b⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hb0]
    simpa only [one_div] using hbL
  have hbΔ : b * (1000 * (1000000 * Δ)) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hbL
    linarith
  have hbb : b ≤ b * Δ := le_mul_of_one_le_right hb0.le hΔ
  have hb1 : 5 * b ≤ Δ := by linarith
  have hxiR : (ρ i)⁻¹ * dist x i < 20 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hri hx
  have habs : |a₀| = 1 := by rcases ha₀ with rfl | rfl <;> simp
  have h400 : |400 * Δ * a₀| = 400 * Δ := by
    rw [abs_mul, habs, mul_one, abs_of_pos (by positivity)]
  obtain ⟨y, hyR, hyu, hyd⟩ := @exists_raw_offset_lift_KC2 X Bi
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) mBi i qi b ψ x (400 * Δ * a₀) (by
      change |400 * Δ * a₀| + 2 * ((ρ i)⁻¹ * dist x i) + 5 * b < b⁻¹
      rw [h400]
      linarith)
  change (ρ i)⁻¹ * dist y i < |400 * Δ * a₀| + 2 * ((ρ i)⁻¹ * dist x i) + 5 * b at hyR
  change abs ((ρ i)⁻¹ * dist x y - |400 * Δ * a₀|) < 3 * b at hyd
  rw [hψx, hψx] at hyu
  rw [h400] at hyR hyd
  -- the lift data in reference units
  obtain ⟨d, hd⟩ : ∃ d, d = dist x y := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = (ρ i)⁻¹ * d := ⟨_, rfl⟩
  have hr1 : 400 * Δ - 3 * b < r := by rw [hr, hd]; linarith [(abs_lt.mp hyd).1]
  have hr2 : r < 400 * Δ + 3 * b := by rw [hr, hd]; linarith [(abs_lt.mp hyd).2]
  have hdeq : d = ρ i * r := by rw [hr]; field_simp
  have hA : 400 * Δ - 2 * b < a₀ * (egpRaw P.edge i y - egpRaw P.edge i x) := by
    have h := abs_lt.mp hyu
    rcases ha₀ with rfl | rfl
    · linarith [h.1]
    · linarith [h.2]
  obtain ⟨hD, hD1, hD2, hV⟩ := egp04_zero_lift_arith_KC3 hb0 hb1 hr1 hr2 hA
  -- the domains of the two original tests and of (ER0)
  have hyiR : (ρ i)⁻¹ * dist y i < 441 * Δ := by linarith
  have hyi : dist y i < 441 * Δ * ρ i := by
    rw [inv_mul_lt_iff₀ hri] at hyiR
    linarith
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hxi : dist x i < 20 * Δ * ρ i := hx
  have hx100 : x ∈ ball i (100 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hx600 : x ∈ ball i (600 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hy1000 : y ∈ ball i (1000 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hy600 : y ∈ ball i (600 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hrd : 399 * Δ < r := by linarith
  have hρΔ : ρ i ≤ Δ * ρ i := le_mul_of_one_le_left hri.le hΔ
  have hd399 : 399 * Δ * ρ i < d := by
    rw [hdeq]
    have h := mul_lt_mul_of_pos_left hrd hri
    linarith only [h]
  have hsep : 100 * Δ * ρ i < dist x y := by rw [← hd]; linarith
  -- one minimizing segment and the two original tests along it
  obtain ⟨v, hvv, hgeo⟩ := exists_rescaled_minimizing_SGP2 g hmetric x y
  have Ti := P.edge.test_phys_KC3 hi hx100 hy1000 hsep hvv (hgeo (ρ i) hri)
  rw [← hd, ← hr] at Ti
  have hσc0 : 0 < σc := by
    have h0 := (abs_nonneg _).trans_lt Ti
    have hr0 : 0 < r := by linarith
    exact pos_of_mul_pos_left h0 hr0.le
  have hρd : ρ x < dist x y := by
    rw [← hd]
    linarith only [hρx2, hd399, hρΔ, hri]
  have hζinv : 1000 * (1000000 * Δ) ≤ ζ⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hζ0]
    simpa only [one_div] using hζL
  have hdζ : dist x y < ζ⁻¹ * ρ x := by
    rw [← hd, hdeq]
    have h1' : ρ i * r < ρ i * (401 * Δ) := mul_lt_mul_of_pos_left (by linarith) hri
    have h2' : (1000 * (1000000 * Δ)) * (99 / 100 * ρ i) ≤ ζ⁻¹ * ρ x :=
      mul_le_mul hζinv hρx1.le (by positivity) (by positivity)
    linarith only [h1', h2', hΔρi]
  have Tz := hZtest y hρd hdζ v hvv hgeo
  rw [← hd] at Tz
  clear hZtest hgeo
  -- (ER0) at `x` and `y`
  have hinc : |(ρ i)⁻¹ * (dist k y - dist k x) -
      a₀ * (egpRaw P.edge i y - egpRaw P.edge i x)| < 2 * E := by
    have he : (ρ i)⁻¹ * (dist k y - dist k x) - a₀ * (egpRaw P.edge i y - egpRaw P.edge i x) =
        ((ρ i)⁻¹ * (dist k y - dist k i) - a₀ * egpRaw P.edge i y) -
          ((ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x) := by ring
    rw [he]
    calc _ ≤ |(ρ i)⁻¹ * (dist k y - dist k i) - a₀ * egpRaw P.edge i y| +
          |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| := abs_sub _ _
      _ < E + E := add_lt_add (hal y hy600) (hal x hx600)
      _ = 2 * E := by ring
  -- the saturation on the unit vector `(ρ(i)/d) v`
  have hl0 := sgp03_lower_zero_SGP3 hri hD hD1 hD2 hdeq Tz hinc hV
  have hli := sgp03_lower_i_SGP2 ha₀ hD hD1 hD2 hE0 Ti hV
  have hd0 : 0 < d := by linarith only [hd399, hΔρi]
  refine ⟨hb0, hE0, hσc0, (ρ i / d) • v, ?_, ?_, ?_⟩
  · rw [gInner_smul_self, hvv, ← hd]
    field_simp
  · rw [map_smul, smul_eq_mul]
    have he : (P.zero.zero k hk).radius / ρ i *
        (ρ i / d * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v) =
        (P.zero.zero k hk).radius / d * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v := by
      field_simp
    rw [he]
    exact hl0
  · rw [map_smul, smul_eq_mul]
    have hcr : ρ i / d = r⁻¹ := by rw [hr]; field_simp
    rw [hcr]
    exact hli

/-- EGP04's zero fraction budget: `(21b/4 + 2E)/(400Δ − 4b) ≤ 9θ²/10⁸` for `b, E ≤ θ²/10⁸`,
`Δ ≥ 1`, `5b ≤ Δ`. -/
theorem zero_frac_budget_KC3 {b E Δ θ : ℝ} (hΔ : 1 ≤ Δ) (hb5 : 5 * b ≤ Δ)
    (hb0 : 0 ≤ b) (hbθ : b ≤ θ ^ 2 / 10 ^ 8) (hE : E ≤ θ ^ 2 / 10 ^ 8) :
    (3 * (7 * b / 4) + 2 * E) / (400 * Δ - 4 * b) ≤ 9 * (θ ^ 2 / 10 ^ 8) := by
  have hD : 1 ≤ 400 * Δ - 4 * b := by linarith
  rw [div_le_iff₀ (by linarith)]
  have h2 := mul_le_mul_of_nonneg_left hD
    (mul_nonneg (by norm_num) (div_nonneg (sq_nonneg θ) (by norm_num)) :
      0 ≤ 9 * (θ ^ 2 / 10 ^ 8))
  linarith

/-- **EGP04's zero block, derivative clause, at one point** (step B): with the edge and radial
adapted qualities and `b, E` at most `θ²/10⁸`, `ζ, b ≤ 1/(1000L)`, at `x ∈ D_i` in LC73's closed
shell: `|s₀ dη₀(w) − a₀ dη_i(w)| < θ` for every unit vector `w` of `ρ(i)⁻² g`. -/
theorem egp04_zero_derivative_KC3
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    {θ E a₀ : ℝ} (hΔ : 1 ≤ Δ) (hθ : 0 < θ) (hθ1 : θ < 1) (hE : E ≤ θ ^ 2 / 10 ^ 8)
    (hσc : σc ≤ θ ^ 2 / 10 ^ 8) (hζ0 : 0 < ζ) (hζθ : ζ ≤ θ ^ 2 / 10 ^ 8)
    (hζL : ζ ≤ 1 / (1000 * (1000000 * Δ))) (hbθ : b ≤ θ ^ 2 / 10 ^ 8)
    (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ P.edge.centres)
    {k : X} (hk : k ∈ P.zero.centres) (ha₀ : a₀ = 1 ∨ a₀ = -1)
    (hal : ∀ x ∈ ball i (600 * Δ * ρ i),
      |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| < E)
    {x : X} (hx : x ∈ ball i (20 * Δ * ρ i))
    (h1 : (P.zero.zero k hk).radius / 10 ≤ dist k x)
    (h2 : dist k x ≤ 10 * (P.zero.zero k hk).radius)
    (hΛz : Λz ≤ (P.zero.zero k hk).radius / ρ x)
    (hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.zero.zero k hk).radial x)
    (hρx1 : 99 / 100 * ρ i < ρ x) (hρx2 : ρ x < 101 / 100 * ρ i) :
    ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
      |(P.zero.zero k hk).radius / ρ i * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
        a₀ * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ := by
  intro w hw
  obtain ⟨hb0, hE0, hσc0, v, hv, hf, hh⟩ :=
    egp04_zero_saturation_KC3 P hΔ hζ0 hζL hbL hi hk ha₀ hal hx h1 h2 hΛz hdiff hρx1 hρx2
  have hri := hρ i
  have hrx := hρ x
  have hΔ0 : 0 < Δ := by linarith
  have hbΔ : b * (1000 * (1000000 * Δ)) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hbL
    linarith
  have hb5 : 5 * b ≤ Δ := by
    have hbb : b ≤ b * Δ := le_mul_of_one_le_right hb0.le hΔ
    linarith
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = (3 * (7 * b / 4) + 2 * E) / (400 * Δ - 4 * b) := ⟨_, rfl⟩
  rw [← hFdef] at hf hh
  have hF0 : 0 ≤ F := by
    rw [hFdef]
    exact div_nonneg (by linarith) (by linarith)
  have hFθ : F ≤ 9 * (θ ^ 2 / 10 ^ 8) := by
    rw [hFdef]
    exact zero_frac_budget_KC3 hΔ hb5 hb0.le hbθ hE
  obtain ⟨εs, hεs⟩ : ∃ e : ℝ, e = σc + ζ + F := ⟨_, rfl⟩
  have hεs0 : 0 ≤ εs := by rw [hεs]; linarith only [hσc0, hζ0, hF0]
  have hεθ : εs < θ ^ 2 / 10 ^ 6 := by
    rw [hεs]
    exact slim_eps_budget_KC3 hθ hσc hζθ hFθ
  -- the covector bounds
  have hxi : dist x i < 20 * Δ * ρ i := hx
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hx100 : x ∈ ball i (100 * Δ * ρ i) := mem_ball.mpr (by linarith only [hxi, hΔρi])
  obtain ⟨hZlip, -⟩ := P.zero_adapted_phys_SGP3 hk h1 h2 hΛz hdiff
  have hR0 : 0 < (P.zero.zero k hk).radius := (P.zero.zero k hk).radius_pos
  have hs0 : 0 < (P.zero.zero k hk).radius / ρ i := div_pos hR0 hri
  have hD0 : ∀ z : TangentSpace 𝓘(ℝ, E3) x,
      |(((P.zero.zero k hk).radius / ρ i) • mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x) z| ≤
        (1 + εs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x z z) := by
    intro z
    have hlip' : ∀ a ∈ ball x (ρ x), ∀ b ∈ ball x (ρ x),
        |(P.zero.zero k hk).radial a - (P.zero.zero k hk).radial b| ≤
          (1 + ζ) * (P.zero.zero k hk).radius⁻¹ * dist a b := hZlip
    have hb := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball (mem_ball_self hrx)
      hdiff hlip' z
    have hg0 := Real.sqrt_nonneg (g.inner x z z)
    rw [smul_apply, smul_eq_mul, abs_mul, abs_of_pos hs0, sqrt_inv_sq_mul_KC2 hri]
    have hk' : (P.zero.zero k hk).radius / ρ i *
        ((1 + ζ) * (P.zero.zero k hk).radius⁻¹ * Real.sqrt (g.inner x z z)) =
        (1 + ζ) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := by field_simp
    calc (P.zero.zero k hk).radius / ρ i *
          |mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x z|
        ≤ (P.zero.zero k hk).radius / ρ i *
          ((1 + ζ) * (P.zero.zero k hk).radius⁻¹ * Real.sqrt (g.inner x z z)) :=
          mul_le_mul_of_nonneg_left hb hs0.le
      _ = (1 + ζ) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := hk'
      _ ≤ (1 + εs) * ((ρ i)⁻¹ * Real.sqrt (g.inner x z z)) := by
          gcongr
          linarith only [hεs, hσc0, hF0]
  have hDi : ∀ z : TangentSpace 𝓘(ℝ, E3) x,
      |(a₀ • mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x) z| ≤
        (1 + εs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x z z) := by
    intro z
    have habs : |a₀| = 1 := by rcases ha₀ with rfl | rfl <;> simp
    rw [smul_apply, smul_eq_mul, abs_mul, habs, one_mul]
    have h := P.edge.abs_deriv_le_KC2 (i := i) (by linarith only [hσc0]) hi hx100 z
    rw [div_self hri.ne', one_mul] at h
    refine h.trans ?_
    gcongr
    linarith only [hεs, hζ0, hF0]
  have hsat := abs_sub_le_of_common_unit_KC2 g x (c := (ρ i)⁻¹ ^ 2)
    (pow_pos (inv_pos.mpr hri) 2)
    (((P.zero.zero k hk).radius / ρ i) • mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x)
    (a₀ • mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x) hεs0 hD0 hDi v hv
    (by rw [smul_apply, smul_eq_mul]; linarith only [hf, hεs, hσc0])
    (by rw [smul_apply, smul_eq_mul]; linarith only [hh, hεs, hζ0]) w hw
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul] at hsat
  exact hsat.trans_lt (egp04_riesz_budget_KC2 hεs0 hθ hθ1 hεθ)

/-- **EGP04's zero block, value clause, at one point** (LC67's GLOBAL difference-Lipschitz clause
of the radial function, (ER0) and the edge value error): at `x ∈ D_i`,
`|U₀(x) − λ₀(η_i(x))| < εr ρ(i)⁻¹ d(x, i) + E + μΔ` (`U₀ = s₀η₀`, `λ₀(a) = a₀a + U₀(p_i)`). -/
theorem egp04_zero_value_KC3
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    {i : X} (hi : i ∈ P.edge.centres) {k : X} (hk : k ∈ P.zero.centres) {a₀ E : ℝ}
    (ha₀ : a₀ = 1 ∨ a₀ = -1)
    (hal : ∀ x ∈ ball i (600 * Δ * ρ i),
      |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| < E)
    (hΔ : 0 < Δ) {x : X} (hx : x ∈ ball i (20 * Δ * ρ i)) :
    |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
        (a₀ * P.edge.coord i x +
          (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| <
      εr * ((ρ i)⁻¹ * dist x i) + E + μ * Δ := by
  have hri := hρ i
  have hR := (P.zero.zero k hk).radius_pos
  obtain ⟨-, -, -, -, hdl, -⟩ := (P.zero.zero k hk).radial_spec
  have hd1 := hdl x i
  rw [@Metric.infDist_singleton X (mX.rescale (P.zero.zero k hk).radius⁻¹
      (inv_pos.mpr (P.zero.zero k hk).radius_pos)).toPseudoMetricSpace x,
    @Metric.infDist_singleton X (mX.rescale (P.zero.zero k hk).radius⁻¹
      (inv_pos.mpr (P.zero.zero k hk).radius_pos)).toPseudoMetricSpace i] at hd1
  have hd2 : |((P.zero.zero k hk).radial x -
      (P.zero.zero k hk).radius⁻¹ * dist x (P.zero.zero k hk).center) -
      ((P.zero.zero k hk).radial i -
      (P.zero.zero k hk).radius⁻¹ * dist i (P.zero.zero k hk).center)| ≤
      εr * ((P.zero.zero k hk).radius⁻¹ * dist x i) := hd1
  rw [P.zero.zero_center k hk, dist_comm x k, dist_comm i k] at hd2
  have hxi : dist x i < 20 * Δ * ρ i := hx
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ hri
  have hx600 : x ∈ ball i (600 * Δ * ρ i) := mem_ball.mpr (by linarith only [hxi, hΔρi])
  have hx100 : x ∈ ball i (100 * Δ * ρ i) := mem_ball.mpr (by linarith only [hxi, hΔρi])
  have h2 := hal x hx600
  have h3 := P.edge.value_KC2 hi hx100
  have haabs : |a₀| = 1 := by rcases ha₀ with rfl | rfl <;> norm_num
  obtain ⟨R, hRe⟩ : ∃ R, (P.zero.zero k hk).radius = R := ⟨_, rfl⟩
  obtain ⟨η, hηe⟩ : ∃ η, (P.zero.zero k hk).radial = η := ⟨_, rfl⟩
  rw [hRe, hηe] at hd2 ⊢
  rw [hRe] at hR
  have hA : |R / ρ i * (η x - η i) - (ρ i)⁻¹ * (dist k x - dist k i)| ≤
      εr * ((ρ i)⁻¹ * dist x i) := by
    have he : R / ρ i * (η x - η i) - (ρ i)⁻¹ * (dist k x - dist k i) =
        R / ρ i * ((η x - R⁻¹ * dist k x) - (η i - R⁻¹ * dist k i)) := by
      field_simp
      ring
    have he2 : εr * ((ρ i)⁻¹ * dist x i) = R / ρ i * (εr * (R⁻¹ * dist x i)) := by field_simp
    rw [he, he2, abs_mul, abs_of_pos (div_pos hR hri)]
    exact mul_le_mul_of_nonneg_left hd2 (div_pos hR hri).le
  have hC : |a₀ * egpRaw P.edge i x - a₀ * P.edge.coord i x| < μ * Δ := by
    rw [← mul_sub, abs_mul, haabs, one_mul, abs_sub_comm]
    exact h3
  have he : R / ρ i * η x - (a₀ * P.edge.coord i x + R / ρ i * η i) =
      (R / ρ i * (η x - η i) - (ρ i)⁻¹ * (dist k x - dist k i)) +
        ((ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x) +
        (a₀ * egpRaw P.edge i x - a₀ * P.edge.coord i x) := by ring
  rw [he]
  calc _ ≤ |R / ρ i * (η x - η i) - (ρ i)⁻¹ * (dist k x - dist k i)| +
        |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| +
        |a₀ * egpRaw P.edge i x - a₀ * P.edge.coord i x| := abs_add_three _ _ _
    _ < εr * ((ρ i)⁻¹ * dist x i) + E + μ * Δ := by
        have := add_lt_add_of_le_of_lt hA h2
        linarith

section Row

/-- **EGP04's zero block on the actual family.** For `0 < θ < 1` there are a curvature radius
`Lc` and a raw quality `η₀` (EGP03 (ER0) at `E = θ²/10⁸`, and `η₀ ≤ θ²/10⁸, 1/(1000L)`) such that
for every actual `P : LocalChartPacketsZ` with (ER0)'s hypotheses, `20Λz ≤ T`, the edge tangential
quality `σc ≤ θ²/10⁸`, the edge value error `μΔ < θ/100`, the radial adapted quality
`0 < ζ ≤ θ²/10⁸, 1/(1000L)` and the radial difference-Lipschitz constant `εr < θ/(100L)`
(`L = 10⁶Δ`), at every edge centre `i` and every zero support (centre `k`, radius `R₀`, radial
function `η₀`) meeting `D_i = B(i, 20Δρ(i))` there is ONE sign `a₀` with, on ALL of `D_i`,
`|s₀η₀ − (a₀η_i + s₀η₀(p_i))| < θ` and `|s₀dη₀(w) − a₀dη_i(w)| < θ` for every unit vector `w`
of `ρ(i)⁻² g` (`s₀ = R₀/ρ(i)`). -/
theorem egp04_zero_row {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
        (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        σc ≤ θ ^ 2 / 10 ^ 8 → μ * Δ < θ / 100 → 0 < ζ → ζ ≤ θ ^ 2 / 10 ^ 8 →
        ζ ≤ 1 / (1000 * (1000000 * Δ)) → εr < θ / (100 * (1000000 * Δ)) →
        ∀ i ∈ P.edge.centres, ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
            |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
                (a₀ * P.edge.coord i x +
                  (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                |(P.zero.zero k hk).radius / ρ i *
                    mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
                  a₀ * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ := by
  have hE : (0 : ℝ) < θ ^ 2 / 10 ^ 8 := by positivity
  obtain ⟨Lc, η₃, hLc, hη₃, h3⟩ := egp03_zero_supplier_egpRaw_ZERO hΔ hβ₂ hβ₂1 hE
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Lc, min η₃ (min (θ ^ 2 / 10 ^ 8) (1 / (1000 * (1000000 * Δ)))), hLc,
    lt_min hη₃ (lt_min hE (by positivity)), ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hb hs
    hβ1 hLmax hΛ hLΛ he hT hTz hσc hμΔ hζ0 hζθ hζL hεr i hi k hk hmeet
  obtain ⟨a₀, ha₀, hal⟩ := h3 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    ζ Λz P (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _)) hLmax hΛ hLΛ he hT i hi
    k hk hmeet
  have hbθ : b ≤ θ ^ 2 / 10 ^ 8 := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbL : b ≤ 1 / (1000 * (1000000 * Δ)) :=
    hb.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hri := hρ i
  have hT0 : 0 < T := by
    have : (0 : ℝ) < 1600 * (1000000 * Δ) := by positivity
    linarith
  have hsmall : 2 * (20 * Δ / T) + 2 * (20 * Δ * Λ) ≤ 1 / 40 := by
    have h1 : 20 * Δ / T ≤ 1 / 80000 := by
      rw [div_le_iff₀ hT0]
      linarith
    have h2 : 20 * Δ * Λ ≤ 1 / 5000000 := by nlinarith
    linarith
  obtain ⟨-, hcl⟩ := zero_meeting_clauses_ZERO P.toLocalChartPacketsR hΛ he hT0 i
    (by positivity : (0 : ℝ) < 20 * Δ) hsmall
  obtain ⟨hball, O, hO, hDO, hsmooth⟩ := hcl k hk hmeet
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := P.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  refine ⟨a₀, ha₀, fun x hx => ⟨?_, ?_⟩⟩
  · -- the value clause
    have hv := egp04_zero_value_KC3 P hi hk ha₀ hal hΔ0 hx
    have hxi : dist x i < 20 * Δ * ρ i := hx
    have ht0 : 0 ≤ (ρ i)⁻¹ * dist x i := by positivity
    have ht : (ρ i)⁻¹ * dist x i < 1000000 * Δ := by
      have h := inv_mul_dist_lt_of_mem_ball_LC87 hri hx
      linarith
    have hEθ : θ ^ 2 / 10 ^ 8 < θ / 100 := by
      have : θ ^ 2 < θ := by nlinarith
      linarith
    exact hv.trans (sgp03_zero_budget_SGP3 hθ (by positivity) ht0 ht hεr hEθ hμΔ)
  · -- the derivative clause
    obtain ⟨h31, h32, h33, h34, h35⟩ := hball x hx
    have hΛz : Λz ≤ (P.zero.zero k hk).radius / ρ x := by linarith
    have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.zero.zero k hk).radial x :=
      ((hsmooth.contMDiffAt (hO.mem_nhds (hDO hx))).mdifferentiableAt (by simp))
    have hlip : |ρ x - ρ i| ≤ Λ * dist x i := by
      have h := hρL.dist_le_mul x i
      rw [Real.dist_eq, hc] at h
      exact h
    have hxi : dist x i < 95 / 100 * (1000000 * Δ) * ρ i := by
      have : dist x i < 20 * Δ * ρ i := hx
      have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
      linarith
    obtain ⟨hρx1, hρx2⟩ := sgp03_rho_ratio_SGP3 hri hΛ hlip hxi hLΛ
    exact egp04_zero_derivative_KC3 P hΔ hθ hθ1 le_rfl hσc hζ0 hζθ hζL hbθ hbL hi hk ha₀ hal hx
      h33 h34 hΛz hdiff hρx1 hρx2

end Row

end DifferentialGeometry.Geometry.Collapse
