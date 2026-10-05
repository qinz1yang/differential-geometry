import DifferentialGeometry.Geometry.Fibration.ActualEdgeAffineComparison

/-!
# EGP04: the derivative clause of (EC) for the listed SLIM charts `J_s`

Blueprint `master207B.tex`, EGP04 (`lem:fibration-edge-actual-comparison`, B:4943–5040), the
paragraph "For `j ∈ J_s`": a common long endpoint would fail the original edge test. Instead, in
`j` units, lift `(u_j(x) + 10L, v_j(x))` to `y`; on a minimizing segment of `R_i⁻² g` from `x` to
`y` let `z` be the point at reference distance `200Δ`. The slim LONG test (to `y`) and the edge
SHORT test of chart `i` (to `z`) with the SAME initial vector saturate both covectors with error
`ς_slim + ς_edge + (7β₁ + 2E)/(200Δ)` (FC22's calculation, slim raw distortion at `y, z`, (ER) at
`x, z` only), and FC15's Riesz step proves `|s_j dη_j(w) − a_j dη_i(w)| < θ` on `D_i`.

* `egp04_slim_saturation_KC3` (step A): the common unit vector and both saturation inequalities.
* `egp04_slim_derivative_pair_KC3` (step B): the Riesz assembly at one pair `i`, `j ∈ J_s`, given
  EGP03's (ER) for the sign `a`.
* `egp04_slim_derivative` (row tier): the derivative clause for every `j ∈ J_s` on the actual
  family (`LocalChartFamilyE`), EGP03 (`egp03_row`) at `E = θ²/10⁸` supplying the sign.

The value clause for `J_s` needs LFR19's separate slim value tolerance (`LocalChartPacketsRV`);
it is proved with the full row in `ActualEdgeAffineComparisonRV`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Pair

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ : ℝ}

/-- The derivative of a slim coordinate in reference units: `|s_j dη_j(w)| ≤ (1 + σ)√(R_i⁻² g)` on
the slim chart ball. -/
theorem SlimCentre.abs_deriv_le_KC3 {β₁ : ℝ} {i j : X}
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hσ : 0 ≤ 1 + σs) {x : X}
    (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (w : TangentSpace 𝓘(ℝ, E3) x) :
    |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) c.coord x w| ≤
      (1 + σs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hrj := hρ j
  have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord x :=
    (c.contMDiffOn_coord.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hud
    (fun y _ z _ => slimCentre_coord_lipschitz_KA2 c hσ y z) w
  rw [sqrt_inv_sq_mul_KC2 hri, abs_mul, abs_of_pos (div_pos hrj hri)]
  calc ρ j / ρ i * |mvfderiv 𝓘(ℝ, E3) c.coord x w|
      ≤ ρ j / ρ i * ((1 + σs) / ρ j * Real.sqrt (g.inner x w w)) :=
        mul_le_mul_of_nonneg_left h (div_pos hrj hri).le
    _ = (1 + σs) * ((ρ i)⁻¹ * Real.sqrt (g.inner x w w)) := by
        field_simp

/-- EGP04's slim gains (FC22's arithmetic): the long slim gain and the short edge gain. -/
theorem slim_gains_KC3 {s β E Δ Lw ℓ dj dyz uy ux uz vx vz a c : ℝ} (hs : 0 < s)
    (hs2 : s < 101 / 100) (hb : 0 < β) (hyu : |uy - ux - 10 * Lw| < 2 * β)
    (hdj : dj < 10 * Lw + 3 * β) (hℓ : ℓ = s * dj) (hyz : uy - uz ≤ dyz + β)
    (hyzi : s * dyz = ℓ - 200 * Δ) (hx : |s * ux - a * vx - c| < E)
    (hz : |s * uz - a * vz - c| < E) (ha : a = 1 ∨ a = -1) :
    ℓ - (7 * β + 2 * E) ≤ s * (uy - ux) ∧ 200 * Δ - (7 * β + 2 * E) ≤ a * (vz - vx) := by
  have h1 : 10 * Lw - 2 * β ≤ uy - ux := by linarith [(abs_lt.mp hyu).1]
  have h2 := mul_le_mul_of_nonneg_left h1 hs.le
  have h3 : ℓ ≤ s * (10 * Lw + 3 * β) := by
    rw [hℓ]
    exact mul_le_mul_of_nonneg_left hdj.le hs.le
  have h4 : s * (5 * β) ≤ 101 / 100 * (5 * β) := mul_le_mul_of_nonneg_right hs2.le (by positivity)
  have e1 : s * (10 * Lw - 2 * β) = s * (10 * Lw + 3 * β) - s * (5 * β) := by ring
  have hE0 : 0 < E := lt_of_le_of_lt (abs_nonneg _) hx
  have hGj : ℓ - 7 * β ≤ s * (uy - ux) := by linarith
  have h5 := mul_le_mul_of_nonneg_left hyz hs.le
  rw [mul_add, hyzi] at h5
  have h6 : s * β ≤ 2 * β := mul_le_mul_of_nonneg_right (by linarith) hb.le
  have hzx : 200 * Δ - 7 * β ≤ s * (uz - ux) := by
    have e2 : s * (uz - ux) = s * (uy - ux) - s * (uy - uz) := by ring
    rw [e2]
    linarith
  have hinc : |s * (uz - ux) - a * (vz - vx)| < 2 * E := by
    have hsplit : s * (uz - ux) - a * (vz - vx) =
        (s * uz - a * vz - c) - (s * ux - a * vx - c) := by
      ring
    rw [hsplit]
    calc _ ≤ _ := abs_sub _ _
      _ < E + E := add_lt_add hz hx
      _ = 2 * E := by ring
  have hc := ha
  exact ⟨by linarith, by linarith [(abs_lt.mp hinc).2]⟩

/-- EGP04's slim error budget: `σc + σs + F < θ²/10⁶` for `σc, σs ≤ θ²/10⁸`, `F ≤ 9θ²/10⁸`. -/
theorem slim_eps_budget_KC3 {σc σs F θ : ℝ} (hθ : 0 < θ) (hσc : σc ≤ θ ^ 2 / 10 ^ 8)
    (hσs : σs ≤ θ ^ 2 / 10 ^ 8) (hF : F ≤ 9 * (θ ^ 2 / 10 ^ 8)) : σc + σs + F < θ ^ 2 / 10 ^ 6 := by
  have : 0 < θ ^ 2 := pow_pos hθ 2
  linarith

/-- EGP04's slim fraction budget: `(7β₁ + 2E)/(200Δ) ≤ 9θ²/10⁸` for `β₁, E ≤ θ²/10⁸`, `Δ ≥ 1`. -/
theorem slim_frac_budget_KC3 {β₁ E Δ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ : β₁ ≤ θ ^ 2 / 10 ^ 8)
    (hE : E ≤ θ ^ 2 / 10 ^ 8) : (7 * β₁ + 2 * E) / (200 * Δ) ≤ 9 * (θ ^ 2 / 10 ^ 8) := by
  have h200 : 0 < 200 * Δ := by linarith
  rw [div_le_iff₀ h200]
  have h2 := mul_le_mul_of_nonneg_left (show 1 ≤ 200 * Δ by linarith)
    (mul_nonneg (by norm_num) (div_nonneg (sq_nonneg θ) (by norm_num)) :
      0 ≤ 9 * (θ ^ 2 / 10 ^ 8))
  linarith

/-- **Step A of EGP04's slim derivative clause** (`j ∈ J_s`, EGP03's (ER) with the sign `a`): at
every `x ∈ D_i` there is one unit vector `v` of `ρ(i)⁻² g` on which the slim long test and the
edge short test saturate `s_j dη_j` and `a dη_i` up to `ς + (7β₁ + 2E)/(200Δ)`; also `x` lies in
the slim chart ball and the edge tangential quality is positive. -/
theorem egp04_slim_saturation_KC3
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    {E a : ℝ} (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hβL : β 1 ≤ 1 / (1000 * (1000000 * Δ))) (hσs0 : 0 < σs) (hσs12 : σs ≤ 1 / 12)
    {i j : X} (hi : i ∈ L.edge.centres) (hjc : j ∈ L.slim.centres)
    (hj : (tsupport (L.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty)
    (ha : a = 1 ∨ a = -1)
    (hER : ∀ x ∈ ball i (600 * Δ * ρ i), |ρ j / ρ i * sgpRaw L.slim j x - a * egpRaw L.edge i x -
      ρ j / ρ i * sgpRaw L.slim j i| < E) :
    ∀ x ∈ ball i (20 * Δ * ρ i), x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ 0 < σc ∧
      0 ≤ (7 * β 1 + 2 * E) / (200 * Δ) ∧ ∃ v : TangentSpace 𝓘(ℝ, E3) x,
        (ρ i)⁻¹ ^ 2 * g.inner x v v = 1 ∧
        1 - (σs + (7 * β 1 + 2 * E) / (200 * Δ)) ≤
          ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hjc).coord x v ∧
        1 - (σc + (7 * β 1 + 2 * E) / (200 * Δ)) ≤
          a * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x v := by
  intro x hx
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := L.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  obtain ⟨y₀, hy1, hy2⟩ := hj
  have hsl := fc18_slim_row L.toLocalChartFamily hΔ0 hjc
  have hm : (closedBall j ((910000 * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
    ⟨y₀, hsl.1 hy1, hy2⟩
  have hΛ1 : 250 * (Λ * (20 * Δ)) ≤ 1 := by
    have e : Λ * (20 * Δ) = 1 / 50000 * (1000000 * Δ * Λ) := by ring
    linarith
  have hΛ2 : 250 * (Λ * (910000 * Δ)) ≤ 1 := by
    have e : Λ * (910000 * Δ) = 91 / 100 * (1000000 * Δ * Λ) := by ring
    linarith
  obtain ⟨hs1, hs2, -, h4⟩ := support_meeting_sharp_bounds hρL hri hrj (a := 20 * Δ)
    (c := 910000 * Δ) (by positivity) (by positivity) (by rw [hc]; exact hΛ1)
    (by rw [hc]; exact hΛ2) hm
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hΔρj : 0 < Δ * ρ j := mul_pos hΔ0 hrj
  have hsub : ball i (20 * Δ * ρ i) ⊆ ball j (92 / 100 * (1000000 * Δ) * ρ j) :=
    (h4 (20 * Δ) (by positivity)).trans (ball_subset_ball
      (mul_le_mul_of_nonneg_right (by linarith) hrj.le))
  have hxj : dist x j < 92 / 100 * (1000000 * Δ) * ρ j := hsub hx
  have hxjR : (ρ j)⁻¹ * dist x j < 92 / 100 * (1000000 * Δ) :=
    inv_mul_dist_lt_of_mem_ball_LC87 hrj (hsub hx)
  have hxi : dist x i < 20 * Δ * ρ i := hx
  have hx6 : x ∈ ball j (10 ^ 6 * Δ * ρ j) := mem_ball.mpr (by linarith)
  have hx100i : x ∈ ball i (100 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hx600 : x ∈ ball i (600 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hE0 : 0 < E := lt_of_le_of_lt (abs_nonneg _) (hER i (mem_ball_self (by positivity)))
  have habs : |a| = 1 := by rcases ha with rfl | rfl <;> simp
  have hsj : 0 < ρ j / ρ i := div_pos hrj hri
  have hρij : 99 / 100 * ρ i < ρ j := by
    have := (lt_div_iff₀ hri).mp hs1
    linarith
  have hraw : ∀ p, sgpRaw L.slim j p = (sgpSplitMap (L.slim.centre j hjc) p).fst :=
    sgpRaw_of_mem L.slim hjc
  let Sj := L.slim.centre j hjc
  let _ := Sj.instZ
  have hb0 : 0 < β 1 := @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Sj.Z))
    (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ j _ (β 1) Sj.split
  have hbinv : 1000 * (1000000 * Δ) ≤ (β 1)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hb0]
    simpa only [one_div] using hβL
  have hbΔ : β 1 * (1000 * (1000000 * Δ)) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hβL
    linarith
  have hbb : β 1 ≤ β 1 * Δ := le_mul_of_one_le_right hb0.le hΔ
  have hb1 : 5 * β 1 ≤ Δ := by linarith
  set Lw : ℝ := 1000000 * Δ with hLw
  have hL10 : |10 * Lw| = 10 * Lw := abs_of_pos (by positivity)
  -- the long lift in `j` units
  obtain ⟨y, hyR, hyu, hyd⟩ := @exists_raw_offset_lift_KC2 X Sj.Z
    (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) Sj.instZ j Sj.z (β 1) Sj.split x (10 * Lw) (by
      change |10 * Lw| + 2 * ((ρ j)⁻¹ * dist x j) + 5 * β 1 < (β 1)⁻¹
      rw [hL10]
      linarith)
  change (ρ j)⁻¹ * dist y j < |10 * Lw| + 2 * ((ρ j)⁻¹ * dist x j) + 5 * β 1 at hyR
  change abs ((ρ j)⁻¹ * dist x y - |10 * Lw|) < 3 * β 1 at hyd
  rw [hL10] at hyR hyd
  change |(sgpSplitMap Sj y).fst - (sgpSplitMap Sj x).fst - 10 * Lw| < 2 * β 1 at hyu
  rw [← hraw, ← hraw] at hyu
  have hyjR : (ρ j)⁻¹ * dist y j < 12 * Lw := by linarith
  have hdj1 : 10 * Lw - 3 * β 1 < (ρ j)⁻¹ * dist x y := by linarith [(abs_lt.mp hyd).1]
  have hdj2 : (ρ j)⁻¹ * dist x y < 10 * Lw + 3 * β 1 := by linarith [(abs_lt.mp hyd).2]
  have hdxy : (9 * Lw) * ρ j < dist x y := by
    have h := hdj1
    rw [lt_inv_mul_iff₀ hrj] at h
    have h' := mul_le_mul_of_nonneg_right (show 9 * Lw ≤ 10 * Lw - 3 * β 1 by linarith) hrj.le
    linarith
  have hxy : x ≠ y := by
    intro h
    rw [h, dist_self] at hdxy
    have : 0 < 9 * Lw * ρ j := by positivity
    linarith
  -- the common direction
  obtain ⟨v, hv, hgeo⟩ := exists_minimizing_direction_KC2 g hmetric hri hxy
  set ℓ := (ρ i)⁻¹ * dist x y with hℓ
  have hℓs : ℓ = ρ j / ρ i * ((ρ j)⁻¹ * dist x y) := by
    rw [hℓ]
    field_simp
  -- the slim long test
  have hyS : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) := by
    rw [mem_ball]
    have h := hyjR
    rw [inv_mul_lt_iff₀ hrj] at h
    have h12 : 12 * Lw ≤ 10 ^ 6 * Δ / σs := by
      rw [le_div_iff₀ hσs0, hLw]
      have := mul_le_mul_of_nonneg_left hσs12 (show 0 ≤ 12 * (1000000 * Δ) by positivity)
      linarith
    have := mul_le_mul_of_nonneg_right h12 hrj.le
    linarith
  have hsepS : 10 ^ 6 * Δ * ρ j < dist x y := by
    have : 10 ^ 6 * Δ * ρ j ≤ 9 * Lw * ρ j := by
      rw [hLw]
      have := hΔρj.le
      linarith
    linarith
  have htS := SlimCentre.test_at_scale_KC2 Sj hri hx6 hyS hsepS v hv hgeo
  -- the point `z` at reference distance `200Δ`
  have hℓ200 : 200 * Δ ≤ ℓ := by
    rw [hℓs]
    have h1 : 0 < (ρ j)⁻¹ * dist x y := by linarith
    have h2 : 99 / 100 ≤ ρ j / ρ i := hs1.le
    have h3 := mul_le_mul h2 (show 9 * Lw ≤ (ρ j)⁻¹ * dist x y by linarith) (by positivity)
      hsj.le
    rw [hLw] at h3
    linarith
  obtain ⟨z, hzdef⟩ : ∃ z : X, z = (let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)
      letI := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr hri)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ i)⁻¹ (inv_pos.mpr hri)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ i)⁻¹ (inv_pos.mpr hri)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr hri)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x v (200 * Δ)) := ⟨_, rfl⟩
  have hz : (ρ i)⁻¹ * dist x z = 200 * Δ ∧ (ρ i)⁻¹ * dist z y = ℓ - 200 * Δ := by
    rw [hzdef]
    exact geodesic_point_dist_KC2 g hmetric hri v hv hgeo (by positivity) hℓ200
  obtain ⟨hz1, hz2⟩ := hz
  have hgz : (let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)
      letI := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr hri)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ i)⁻¹ (inv_pos.mpr hri)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ i)⁻¹ (inv_pos.mpr hri)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr hri)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x v (dist x z) = z) := by
    let hMc : CompleteSpace X := complete_of_compact
    let mR : MetricSpace X := mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)
    let bR := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr hri)
    let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ i)⁻¹ (inv_pos.mpr hri)
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ i)⁻¹ (inv_pos.mpr hri)
    let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr hri)).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    have hd : dist x z = 200 * Δ := hz1
    change intrinsicGeodesic gR hnR x v (dist x z) = z
    rw [hd, hzdef]
  have hdxz : dist x z = 200 * Δ * ρ i := by
    rw [inv_mul_eq_iff_eq_mul₀ hri.ne'] at hz1
    linarith
  have hz1000 : z ∈ ball i (1000 * Δ * ρ i) := by
    rw [mem_ball]
    have ht := dist_triangle z x i
    rw [dist_comm z x] at ht
    linarith
  have hz600 : z ∈ ball i (600 * Δ * ρ i) := by
    rw [mem_ball]
    have ht := dist_triangle z x i
    rw [dist_comm z x] at ht
    linarith
  have hsepz : 100 * Δ * ρ i < dist x z := by linarith
  -- the edge short test of chart `i`
  have htE := L.edge.test_at_scale_KC2 hi hri hx100i hz1000 hsepz v hv hgz
  rw [div_self hri.ne', one_mul, one_mul, hz1] at htE
  have hσc0 : 0 < σc := lt_of_le_of_lt (abs_nonneg _) htE
  -- the slim raw distortion at `y, z`
  have hzjR : (ρ j)⁻¹ * dist z j < (β 1)⁻¹ := by
    have ht := dist_triangle z x j
    rw [dist_comm z x] at ht
    have h' : dist z j < 2 * Lw * ρ j := by
      have := mul_lt_mul_of_pos_left hρij hΔ0
      rw [hLw]
      linarith
    rw [inv_mul_lt_iff₀ hrj]
    have := mul_le_mul_of_nonneg_right (show 2 * Lw ≤ (β 1)⁻¹ by linarith) hrj.le
    linarith
  have hyjB : (ρ j)⁻¹ * dist y j < (β 1)⁻¹ := by linarith
  have hdist := @KleinerLottApprox.distortion X (WithLp 2 (ℝ × Sj.Z))
    (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ j _ (β 1) Sj.split y hyjB z hzjR
  change |dist (sgpSplitMap Sj y) (sgpSplitMap Sj z) - (ρ j)⁻¹ * dist y z| ≤ β 1 at hdist
  have hfst := WithLp.dist_fst_le (sgpSplitMap Sj y) (sgpSplitMap Sj z)
  rw [Real.dist_eq] at hfst
  have hyz : sgpRaw L.slim j y - sgpRaw L.slim j z ≤ (ρ j)⁻¹ * dist y z + β 1 := by
    rw [hraw, hraw]
    linarith [le_abs_self ((sgpSplitMap Sj y).fst - (sgpSplitMap Sj z).fst), (abs_le.mp hdist).2]
  have hyzi : ρ j / ρ i * ((ρ j)⁻¹ * dist y z) = ℓ - 200 * Δ := by
    rw [← hz2, dist_comm y z]
    field_simp
  -- the gains
  set Gj := ρ j / ρ i * (sgpRaw L.slim j y - sgpRaw L.slim j x) with hGj
  set Gi := a * (egpRaw L.edge i z - egpRaw L.edge i x) with hGi
  obtain ⟨hGj2, hGi1⟩ := slim_gains_KC3 hsj hs2 hb0 hyu hdj2 hℓs hyz hyzi (hER x hx600)
    (hER z hz600) ha
  have h200 : 0 < 200 * Δ := by positivity
  have he0 : 0 ≤ 7 * β 1 + 2 * E := by positivity
  have htesti : |a * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x v - Gi / (200 * Δ)| ≤ σc := by
    have he : a * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x v - Gi / (200 * Δ) =
        a * (mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x v -
          (egpRaw L.edge i z - egpRaw L.edge i x) / (200 * Δ)) := by
      rw [hGi]; ring
    rw [he, abs_mul, habs, one_mul]
    exact htE.le
  have htestj : |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) Sj.coord x v - Gj / ℓ| ≤ σs := by
    have he : Gj / ℓ = ρ j / ρ i * ((sgpSplitMap Sj y).fst - (sgpSplitMap Sj x).fst) / ℓ := by
      rw [hGj, hraw, hraw]
    rw [he]
    exact htS.le
  have hsi := ContinuousLinearMap.saturation_of_test_gain h200 le_rfl he0 htesti hGi1
  have hsj' := ContinuousLinearMap.saturation_of_test_gain h200 hℓ200 he0 htestj hGj2
  exact ⟨hx6, hσc0, div_nonneg he0 h200.le, v, hv, hsj', hsi⟩

/-- **EGP04's derivative clause for one listed slim chart** (`j ∈ J_s`), given EGP03's (ER) with
the sign `a`: step A's common unit vector and FC15's Riesz step give
`|s_j dη_j(w) − a dη_i(w)| < θ` for every unit vector `w` of `ρ(i)⁻² g` at every `x ∈ D_i`. -/
theorem egp04_slim_derivative_pair_KC3
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    {θ E a : ℝ} (hΔ : 1 ≤ Δ) (hθ : 0 < θ) (hθ1 : θ < 1) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hβθ : β 1 ≤ θ ^ 2 / 10 ^ 8)
    (hβL : β 1 ≤ 1 / (1000 * (1000000 * Δ))) (hE : E ≤ θ ^ 2 / 10 ^ 8)
    (hσc : σc ≤ θ ^ 2 / 10 ^ 8) (hσs0 : 0 < σs) (hσs : σs ≤ θ ^ 2 / 10 ^ 8)
    {i j : X} (hi : i ∈ L.edge.centres) (hjc : j ∈ L.slim.centres)
    (hj : (tsupport (L.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty)
    (ha : a = 1 ∨ a = -1)
    (hER : ∀ x ∈ ball i (600 * Δ * ρ i), |ρ j / ρ i * sgpRaw L.slim j x - a * egpRaw L.edge i x -
      ρ j / ρ i * sgpRaw L.slim j i| < E) :
    ∀ x ∈ ball i (20 * Δ * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
        |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hjc).coord x w -
          a * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| < θ := by
  intro x hx w hw
  have hσs12 : σs ≤ 1 / 12 := by
    have : θ ^ 2 ≤ 1 := by nlinarith
    linarith
  obtain ⟨hx6, hσc0, hfrac0, v, hv, hsj', hsi⟩ :=
    egp04_slim_saturation_KC3 L hΔ hΛ hLΛ hβL hσs0 hσs12 hi hjc hj ha hER x hx
  have hx100i : x ∈ ball i (100 * Δ * ρ i) := by
    have hri := hρ i
    have hΔ0 : 0 < Δ := by linarith
    have hxi : dist x i < 20 * Δ * ρ i := hx
    exact mem_ball.mpr (by nlinarith)
  obtain ⟨εs, hεs⟩ : ∃ e : ℝ, e = σc + σs + (7 * β 1 + 2 * E) / (200 * Δ) := ⟨_, rfl⟩
  have hεs0 : 0 ≤ εs := by rw [hεs]; exact add_nonneg (add_nonneg hσc0.le hσs0.le) hfrac0
  have hεθ : εs < θ ^ 2 / 10 ^ 6 := by
    rw [hεs]
    exact slim_eps_budget_KC3 hθ hσc hσs (slim_frac_budget_KC3 hΔ hβθ hE)
  have hDj : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      |((ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hjc).coord x) w| ≤
        (1 + εs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
    intro w
    rw [smul_apply, smul_eq_mul]
    refine ((L.slim.centre j hjc).abs_deriv_le_KC3 (by linarith only [hσs0]) hx6 w).trans ?_
    gcongr
    linarith only [hεs, hσc0, hfrac0]
  have hDi : ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      |(a • mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x) w| ≤
        (1 + εs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
    intro w
    have habs : |a| = 1 := by rcases ha with rfl | rfl <;> simp
    rw [smul_apply, smul_eq_mul, abs_mul, habs, one_mul]
    have h := L.edge.abs_deriv_le_KC2 (i := i) (by linarith only [hσc0]) hi hx100i w
    rw [div_self (hρ i).ne', one_mul] at h
    refine h.trans ?_
    gcongr
    linarith only [hεs, hσs0, hfrac0]
  have hsat := abs_sub_le_of_common_unit_KC2 g x (c := (ρ i)⁻¹ ^ 2)
    (pow_pos (inv_pos.mpr (hρ i)) 2) ((ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hjc).coord x)
    (a • mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x) hεs0 hDj hDi v hv
    (by rw [smul_apply, smul_eq_mul]; linarith only [hsj', hεs, hσc0])
    (by rw [smul_apply, smul_eq_mul]; linarith only [hsi, hεs, hσs0]) w hw
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul] at hsat
  exact hsat.trans_lt (egp04_riesz_budget_KC2 hεs0 hθ hθ1 hεθ)

end Pair

section Row

/-- **EGP04's derivative clause for the listed slim charts on the actual family.** For
`0 < θ < 1` there are a curvature radius `Lc` and a raw quality `η₀` (EGP03 at `E = θ²/10⁸`, and
`η₀ ≤ θ²/10⁸, 1/(1000L)`) such that for every actual family `L` with EGP03's hypotheses, the
tangential qualities `σc, σs ≤ θ²/10⁸` (`σs > 0`), every edge centre `i` and every slim centre
`j` whose cutoff support meets `D_i` have one sign `a` with `|s_j dη_j(w) − a dη_i(w)| < θ` for
every unit vector `w` of `ρ(i)⁻² g` at every `x ∈ D_i = B(i, 20Δρ(i))`. -/
theorem egp04_slim_derivative {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ : ℝ)
        (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        0 < σs → σs ≤ θ ^ 2 / 10 ^ 8 → ∀ i ∈ L.edge.centres, ∀ j (hj : j ∈ L.slim.centres),
          (tsupport (L.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
            ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
              |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hj).coord x w -
                a * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) x w| < θ := by
  have hE : (0 : ℝ) < θ ^ 2 / 10 ^ 8 := by positivity
  obtain ⟨Lc, η₃, hLc, hη₃, h3⟩ := egp03_row hΔ hβ₂ hβ₂1 hE
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Lc, min η₃ (min (θ ^ 2 / 10 ^ 8) (1 / (1000 * (1000000 * Δ)))), hLc,
    lt_min hη₃ (lt_min hE (by positivity)), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1 hLmax hΛ
    hLΛ hμ hτ hσc hσs0 hσs i hi j hj hmeet
  obtain ⟨-, hsl⟩ := h3 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L
    (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _)) hLmax hΛ hLΛ hμ hτ i hi
  obtain ⟨a, ha, hER⟩ := hsl j ⟨hj, hmeet⟩
  exact ⟨a, ha, egp04_slim_derivative_pair_KC3 L hΔ hθ hθ1 hΛ hLΛ
    (hβ1.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hβ1.trans ((min_le_right _ _).trans (min_le_right _ _))) le_rfl hσc hσs0 hσs hi hj hmeet ha
    hER⟩

end Row

end DifferentialGeometry.Geometry.Collapse
