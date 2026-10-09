import DifferentialGeometry.Geometry.Fibration.ActualOverlapBindingPacket
import DifferentialGeometry.Geometry.Fibration.ActualEdgeAffineComparison
import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison
import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonList
import DifferentialGeometry.Geometry.Fibration.ActualSlimComparisonList

/-!
# FC23 items 1–2 for the projected analogues (edge base EGP04, slim base SGP03)

Blueprint `master207B.tex`, FC23 (B:1505–1508): "For each local model used in FC07 OR ITS
PROJECTED ANALOGUES, produce a FINITE collection of constant affine comparisons on the same
buffered source domain." The projected analogues are the edge base (EGP, `D_i = B(i, 20ΔR_i)`,
EGP04 B:4943–5040) and the slim base (SGP, `D_i = B(i, .95LR_i)`, `L = 10⁶Δ`, SGP03 B:4483–4560).

Item 1 at these bases is the accepted comparison-list rows: `egp02_row` (EGP02: count of the edge
and slim lists, ratios, `d(i, j)`, `D_i ⊆` chart balls with smooth coordinates, zero clauses) and
`sgp01_row` (SGP01: the slim list, ratios, `d(i, j) < 2LR_i`, zero clauses). Items 3–4 are EGP03 /
EGP04 and SGP02 / SGP03 (accepted). This module restates item 2 — the test configurations used in
the accepted EGP04 / SGP03 proofs (same lifts, same lengths, same original domains), with the
common direction in the form `ScaledGeodesicReaches_RFC`:

* `fc23_edgebase_lift_RFC`: at the edge base `i`, `x ∈ D_i`, sign `a`: the reference raw-offset lift
  of length `400ΔR_i` (gain `400Δa` up to `2b`), its original edge test domains (near
  `B(i, 100ΔR_i)`, far `B(i, 1000ΔR_i)`, separation `100ΔR_i`) and the (ER) ball `B(i, 600ΔR_i)`.
* `fc23_edgebase_edge_tests_RFC` (`j ∈ J_e`, FC19 route): the same endpoint also in `j`'s original
  edge test domains.
* `fc23_edgebase_slim_tests_RFC` (`j ∈ J_s`, FC22 route, B:5019–5033): the slim chart's own lift of
  length `10LR_j`, its original slim test domains, the short point `z` at `t = 200ΔR_i` on the SAME
  segment in `B(i, 220ΔR_i)` (edge far ball and (ER) ball), `100ΔR_i < t < ℓ₀ = (10L − 3β₁)R_j`.
* `fc23_edgebase_zero_tests_RFC` (zero block): the reference lift of length `400ΔR_i` with sign
  `a₀` and LC73's test domain at scale `ρ(x)`: `ρ(x) < d(x, y) < ζ⁻¹ρ(x)`.
* `fc23_slimbase_lift_RFC`: at the slim base `i`, `x ∈ D_i`, sign `a`: the reference lift of length
  `10LR_i` (SGP03's `sgp03_reference_lift_SGP2`), the original slim test domains at `i` and the
  (RA) ball `B(i, 30LR_i)`.
* `fc23_slimbase_slim_tests_RFC` (`j ∈ J_i`, FC19 route): the same endpoint in `j`'s original slim
  test domains.
* `fc23_slimbase_zero_tests_RFC`: LC73's test domain at scale `ρ(x)` for the same lift.
* ROWS `fc23_items12_edgebase_RFC` (on `LocalChartPackets`: every listed edge chart of EGP02's list
  and every slim chart meeting `D_i`, list bounds from `egp02_row`) and `fc23_items12_slimbase_RFC`
  (on `LocalChartPacketsR`: every chart of SGP01's list, list bounds from `sgp01_row`).
* Consumer `fc23_edgebase_slim_short_long_RFC` (FC22's `0 < t < ℓ₀ ≤ ℓ` at the edge base).
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
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

section EdgeBase

variable {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- **FC23 item 2 at the edge base: the reference lift** (EGP04 B:4975–4985). At `x ∈ D_i =
B(i, 20Δρ(i))` and a sign `a`, the lift `y` of `(u_i(x) + 400Δa, v_i(x))` through the reference
edge splitting, a `g`-unit `w₀` reaching it, the gain, the length, and the original edge test
domains of `i` and the (ER) ball. -/
theorem fc23_edgebase_lift_RFC (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    (hΔ : 1 ≤ Δ) (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ F.centres) {x : X}
    (hx : x ∈ ball i (20 * Δ * ρ i)) {a : ℝ} (ha : a = 1 ∨ a = -1) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      |egpRaw F i y - egpRaw F i x - 400 * Δ * a| < 2 * b ∧
      (400 * Δ - 3 * b) * ρ i < dist x y ∧ dist x y < (400 * Δ + 3 * b) * ρ i ∧
      y ∈ ball i (441 * Δ * ρ i) ∧ x ∈ ball i (100 * Δ * ρ i) ∧ y ∈ ball i (1000 * Δ * ρ i) ∧
      100 * Δ * ρ i < dist x y ∧ x ∈ ball i (600 * Δ * ρ i) ∧ y ∈ ball i (600 * Δ * ρ i) := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  obtain ⟨Bi, mBi, qi, ψ, hψx⟩ := exists_edge_split_KC2 F hi
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
  have habs : |a| = 1 := by rcases ha with rfl | rfl <;> simp
  have h400 : |400 * Δ * a| = 400 * Δ := by
    rw [abs_mul, habs, mul_one, abs_of_pos (by positivity)]
  obtain ⟨y, hyR, hyu, hyd⟩ := @exists_raw_offset_lift_KC2 X Bi
    (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) mBi i qi b ψ x (400 * Δ * a) (by
      change |400 * Δ * a| + 2 * ((ρ i)⁻¹ * dist x i) + 5 * b < b⁻¹
      rw [h400]
      linarith)
  change (ρ i)⁻¹ * dist y i < |400 * Δ * a| + 2 * ((ρ i)⁻¹ * dist x i) + 5 * b at hyR
  change abs ((ρ i)⁻¹ * dist x y - |400 * Δ * a|) < 3 * b at hyd
  rw [hψx, hψx] at hyu
  rw [h400] at hyR hyd
  have hyiR : (ρ i)⁻¹ * dist y i < 441 * Δ := by linarith
  have hyi : dist y i < 441 * Δ * ρ i := by
    rw [inv_mul_lt_iff₀ hri] at hyiR
    linarith
  have hd1 : (400 * Δ - 3 * b) * ρ i < dist x y := by
    have h : 400 * Δ - 3 * b < (ρ i)⁻¹ * dist x y := by linarith [(abs_lt.mp hyd).1]
    rw [lt_inv_mul_iff₀ hri] at h
    linarith
  have hd2 : dist x y < (400 * Δ + 3 * b) * ρ i := by
    have h : (ρ i)⁻¹ * dist x y < 400 * Δ + 3 * b := by linarith [(abs_lt.mp hyd).2]
    rw [inv_mul_lt_iff₀ hri] at h
    linarith
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hsep : 100 * Δ * ρ i < dist x y := by nlinarith
  have hdpos : 0 < dist x y := lt_of_le_of_lt (by positivity) hsep
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hdpos; exact lt_irrefl _ hdpos
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hxi : dist x i < 20 * Δ * ρ i := hx
  exact ⟨y, w₀, hw₀, hgy, hyu, hd1, hd2, hyi, mem_ball.mpr (by linarith),
    mem_ball.mpr (by linarith), hsep, mem_ball.mpr (by linarith), mem_ball.mpr (by linarith)⟩

/-- **FC23 item 2 at the edge base, edge chart `j ∈ J_e`** (FC19 route, EGP04 B:4975–4993): with
EGP02's list bounds (`.99 < ρ(j)/ρ(i) < 1.01`, `d(i, j) < 36Δρ(i)`, `D_i ⊆ B(j, 57Δρ(j))`), the
reference lift is a COMMON endpoint of both original edge tests. -/
theorem fc23_edgebase_edge_tests_RFC
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    (hΔ : 1 ≤ Δ) (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) {i j : X} (hi : i ∈ F.centres)
    (hs1 : 99 / 100 < ρ j / ρ i) (hs2 : ρ j / ρ i < 101 / 100) (hdij : dist i j < 36 * Δ * ρ i)
    {x : X} (hx : x ∈ ball i (20 * Δ * ρ i)) (hxj : x ∈ ball j (57 * Δ * ρ j)) {a : ℝ}
    (ha : a = 1 ∨ a = -1) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      |egpRaw F i y - egpRaw F i x - 400 * Δ * a| < 2 * b ∧
      (400 * Δ - 3 * b) * ρ i < dist x y ∧ dist x y < (400 * Δ + 3 * b) * ρ i ∧
      x ∈ ball i (100 * Δ * ρ i) ∧ y ∈ ball i (1000 * Δ * ρ i) ∧ 100 * Δ * ρ i < dist x y ∧
      x ∈ ball j (100 * Δ * ρ j) ∧ y ∈ ball j (1000 * Δ * ρ j) ∧ 100 * Δ * ρ j < dist x y ∧
      x ∈ ball i (600 * Δ * ρ i) ∧ y ∈ ball i (600 * Δ * ρ i) := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  obtain ⟨y, w₀, hw₀, hgy, hyu, hd1, hd2, hyi, hx100, hy1000, hsep, hx600, hy600⟩ :=
    fc23_edgebase_lift_RFC F hΔ hbL hi hx ha
  have hρij : 99 / 100 * ρ i < ρ j := by
    have := (lt_div_iff₀ hri).mp hs1
    linarith
  have hρji : ρ j < 101 / 100 * ρ i := by
    have := (div_lt_iff₀ hri).mp hs2
    linarith
  have hb0 : 0 < b := by
    obtain ⟨Bi, mBi, qi, ψ, -⟩ := exists_edge_split_KC2 F hi
    exact @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Bi))
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ b ψ
  have hbL' : 3 * b ≤ Δ := by
    have h : b ≤ 1 / 1000 := hbL.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    linarith
  have hyi' : dist y i < 441 * Δ * ρ i := hyi
  have hxj' : dist x j < 57 * Δ * ρ j := hxj
  refine ⟨y, w₀, hw₀, hgy, hyu, hd1, hd2, hx100, hy1000, hsep, ?_, ?_, ?_, hx600, hy600⟩
  · exact mem_ball.mpr (by nlinarith)
  · rw [mem_ball]
    have ht := dist_triangle y i j
    have h' := mul_lt_mul_of_pos_left hρij hΔ0
    nlinarith
  · have h' := mul_lt_mul_of_pos_left hρji hΔ0
    nlinarith

/-- **FC23 item 2 at the edge base, slim chart `j ∈ J_s`** (FC22 route, EGP04 B:5019–5033): the
slim chart's OWN lift of length `10Lρ(j)` (`L = 10⁶Δ`; gain `10L` up to `2β₁`), its original slim
test domains (near `B(j, Lρ(j))`, far `B(j, (L/σ_s)ρ(j))`, separation `Lρ(j)`), and on the SAME
minimizing segment the short point `z` at `t = 200Δρ(i)` with `z ∈ B(i, 220Δρ(i))` (the reference
edge test's far ball and the (ER) ball), `100Δρ(i) < t < ℓ₀ = (10L − 3β₁)ρ(j) ≤ d(x, y)`. -/
theorem fc23_edgebase_slim_tests_RFC {Λ : ℝ} {σs : ℝ} {K : ℕ}
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 1 ≤ Δ)
    (hβL : β 1 ≤ 1 / (1000 * (10 ^ 6 * Δ))) (hσs0 : 0 < σs) (hσs12 : σs ≤ 1 / 12) {i j : X}
    (hj : j ∈ L.slim.centres) (hs1 : 99 / 100 < ρ j / ρ i) {x : X}
    (hx : x ∈ ball i (20 * Δ * ρ i)) (hxj : x ∈ ball j (92 / 100 * (10 ^ 6 * Δ) * ρ j)) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      |slimRaw_KA3 L j y - slimRaw_KA3 L j x - 10 * (10 ^ 6 * Δ)| < 2 * β 1 ∧
      (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y ∧
      dist x y ≤ (10 * (10 ^ 6 * Δ) + 3 * β 1) * ρ j ∧
      x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) ∧
      10 ^ 6 * Δ * ρ j < dist x y ∧
      x ∈ ball i (100 * Δ * ρ i) ∧ 100 * Δ * ρ i < 200 * Δ * ρ i ∧
      200 * Δ * ρ i < (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ∧
      ∃ z : X, dist x z = 200 * Δ * ρ i ∧ dist z y = dist x y - 200 * Δ * ρ i ∧
        z ∈ ball i (220 * Δ * ρ i) ∧ ScaledGeodesicReaches_RFC g hmetric x w₀ z := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hρij : 99 / 100 * ρ i < ρ j := by
    have := (lt_div_iff₀ hri).mp hs1
    linarith
  have hbpos : 0 < β 1 := by
    let Sj := L.slim.centre j hj
    let _ := Sj.instZ
    exact @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ Sj.split
  have hL : (1000000 : ℝ) ≤ 10 ^ 6 * Δ := by linarith
  have hbinv : 1000 * (10 ^ 6 * Δ) ≤ (β 1)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hbpos]
    rwa [one_div] at hβL
  have hb1 : β 1 ≤ 1 / 1000 := hβL.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hxjd : dist x j < 92 / 100 * (10 ^ 6 * Δ) * ρ j := mem_ball.mp hxj
  obtain ⟨y, hdxy, hlift, hyj⟩ := slim_lift_KA5 L hj (t := 10 * (10 ^ 6 * Δ)) hxjd
    (by positivity) (by linarith)
  have hD1 : (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y := by
    have h' : 10 * (10 ^ 6 * Δ) - 3 * β 1 ≤ (ρ j)⁻¹ * dist x y := by
      linarith [(abs_le.mp hdxy).1]
    have := (le_inv_mul_iff₀ hrj).mp h'
    linarith
  have hD2 : dist x y ≤ (10 * (10 ^ 6 * Δ) + 3 * β 1) * ρ j := by
    have h' : (ρ j)⁻¹ * dist x y ≤ 10 * (10 ^ 6 * Δ) + 3 * β 1 := by
      linarith [(abs_le.mp hdxy).2]
    have := (inv_mul_le_iff₀ hrj).mp h'
    linarith
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have ht : 200 * Δ * ρ i < (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j := by nlinarith
  have hDpos : 0 < dist x y := lt_of_lt_of_le (by positivity) (ht.le.trans hD1)
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hDpos; exact lt_irrefl _ hDpos
  have h200 : 200 * Δ * ρ i ≤ dist x y := by linarith
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨z, hxz, hzy, hgz⟩ := hseg (200 * Δ * ρ i) (by positivity) h200
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hxL : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by rw [mem_ball]; nlinarith
  have hyL : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) := by
    rw [mem_ball]
    have h12 : 12 * (10 ^ 6 * Δ) ≤ 10 ^ 6 * Δ / σs := by
      rw [le_div_iff₀ hσs0]
      nlinarith
    have h' : (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ / σs := by linarith
    have := (inv_mul_lt_iff₀ hrj).mp h'
    linarith
  have hxi : dist x i < 20 * Δ * ρ i := mem_ball.mp hx
  have hzi : z ∈ ball i (220 * Δ * ρ i) := by
    rw [mem_ball]
    have := dist_triangle z x i
    rw [dist_comm z x] at this
    linarith
  refine ⟨y, w₀, hw₀, hgy, hlift, hD1, hD2, hxL, hyL, by nlinarith,
    mem_ball.mpr (by linarith), by linarith, ht, z, hxz, hzy, hzi, hgz⟩

/-- **FC23 item 2 at the edge base, zero block** (EGP04's zero block): the reference lift of
length `400Δρ(i)` with sign `a₀` (`fc23_edgebase_lift_RFC`) also lies in LC73's original radial
test domain at the scale `ρ(x)` of the point: `ρ(x) < d(x, y) < ζ⁻¹ρ(x)` (for `.99ρ(i) < ρ(x) <
1.01ρ(i)` and `0 < ζ ≤ 1/(1000·10⁶Δ)`). -/
theorem fc23_edgebase_zero_tests_RFC
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {ζ : ℝ}
    (hΔ : 1 ≤ Δ) (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) (hζ0 : 0 < ζ)
    (hζL : ζ ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ F.centres) {x : X}
    (hx : x ∈ ball i (20 * Δ * ρ i)) (hρx1 : 99 / 100 * ρ i < ρ x) (hρx2 : ρ x < 101 / 100 * ρ i)
    {a₀ : ℝ} (ha₀ : a₀ = 1 ∨ a₀ = -1) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      |egpRaw F i y - egpRaw F i x - 400 * Δ * a₀| < 2 * b ∧
      (400 * Δ - 3 * b) * ρ i < dist x y ∧ dist x y < (400 * Δ + 3 * b) * ρ i ∧
      x ∈ ball i (100 * Δ * ρ i) ∧ y ∈ ball i (1000 * Δ * ρ i) ∧ 100 * Δ * ρ i < dist x y ∧
      x ∈ ball i (600 * Δ * ρ i) ∧ y ∈ ball i (600 * Δ * ρ i) ∧
      ρ x < dist x y ∧ dist x y < ζ⁻¹ * ρ x := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  obtain ⟨y, w₀, hw₀, hgy, hyu, hd1, hd2, -, hx100, hy1000, hsep, hx600, hy600⟩ :=
    fc23_edgebase_lift_RFC F hΔ hbL hi hx ha₀
  have hb0 : 0 < b := by
    obtain ⟨Bi, mBi, qi, ψ, -⟩ := exists_edge_split_KC2 F hi
    exact @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Bi))
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ b ψ
  have hb3 : 3 * b ≤ Δ := by
    have h : b ≤ 1 / 1000 := hbL.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    linarith
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hζinv : 1000 * (1000000 * Δ) ≤ ζ⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hζ0]
    simpa only [one_div] using hζL
  refine ⟨y, w₀, hw₀, hgy, hyu, hd1, hd2, hx100, hy1000, hsep, hx600, hy600, ?_, ?_⟩
  · have hρΔ : ρ i ≤ Δ * ρ i := le_mul_of_one_le_left hri.le hΔ
    nlinarith
  · have h2' : (1000 * (1000000 * Δ)) * (99 / 100 * ρ i) ≤ ζ⁻¹ * ρ x :=
      mul_le_mul hζinv hρx1.le (by positivity) (by positivity)
    nlinarith

/-- **Consumer: FC22's length data at the edge base** (slim charts): `0 < t < ℓ₀ ≤ ℓ` with
`t = 200Δρ(i)`, `ℓ₀ = (10L − 3β₁)ρ(j)`, `ℓ = d(x, y)` (B:1527 "Require `ℓ₀ > t`"). -/
theorem fc23_edgebase_slim_short_long_RFC {Λ : ℝ} {σs : ℝ} {K : ℕ}
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 1 ≤ Δ)
    (hβL : β 1 ≤ 1 / (1000 * (10 ^ 6 * Δ))) (hσs0 : 0 < σs) (hσs12 : σs ≤ 1 / 12) {i j : X}
    (hj : j ∈ L.slim.centres) (hs1 : 99 / 100 < ρ j / ρ i) {x : X}
    (hx : x ∈ ball i (20 * Δ * ρ i)) (hxj : x ∈ ball j (92 / 100 * (10 ^ 6 * Δ) * ρ j)) :
    ∃ y : X, 0 < 200 * Δ * ρ i ∧ 200 * Δ * ρ i < (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ∧
      (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y := by
  obtain ⟨y, -, -, -, -, hD1, -, -, -, -, -, -, ht, -⟩ :=
    fc23_edgebase_slim_tests_RFC L hΔ hβL hσs0 hσs12 hj hs1 hx hxj
  have hΔ0 : 0 < Δ := by linarith
  exact ⟨y, mul_pos (mul_pos (by norm_num) hΔ0) (hρ i), ht, hD1⟩

end EdgeBase

section SlimBase

variable {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}

/-- **FC23 item 2 at the slim base: the reference lift** (SGP03 B:4523–4531, `L = 10⁶Δ`). At
`x ∈ D_i = B(i, .95Lρ(i))` and a sign `a`, SGP03's reference lift `y` of `(u_i(x) + 10La, v_i(x))`
(`sgp03_reference_lift_SGP2`), a `g`-unit `w₀` reaching it, the original slim test domains of `i`
(near `B(i, Lρ(i))`, far `B(i, (L/σ_s)ρ(i))`, separation `Lρ(i)`) and the (RA) ball
`B(i, 30Lρ(i))`. -/
theorem fc23_slimbase_lift_RFC (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {δ : ℝ}
    (hΔ : 1 ≤ Δ) (hδ1 : δ < 1) (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100))
    (hσs : 0 < σs) (hσs24 : σs * 24 ≤ 1) {i : X} (hi : i ∈ S.centres) {x : X}
    (hxi : x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i)) {a : ℝ} (ha : a = 1 ∨ a = -1) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      y ∈ ball i (21 * (1000000 * Δ) * ρ i) ∧
      |(ρ i)⁻¹ * dist x y - 10 * (1000000 * Δ)| < 2 * δ ∧
      10 * (1000000 * Δ) - δ < a * (sgpRaw S i y - sgpRaw S i x) ∧
      x ∈ ball i (10 ^ 6 * Δ * ρ i) ∧ y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) ∧
      10 ^ 6 * Δ * ρ i < dist x y ∧
      x ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧ y ∈ ball i (30 * (1000000 * Δ) * ρ i) := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have h106 : (10 : ℝ) ^ 6 * Δ = 1000000 * Δ := by norm_num
  have hLpos : 0 < 1000000 * Δ := by positivity
  have hL6 : (1000000 : ℝ) ≤ 1000000 * Δ := by linarith
  obtain ⟨y, hy21, hdxy, hay⟩ := sgp03_reference_lift_SGP2 S hΔ hδ1 hβ hi hxi ha
  have hr1 : 10 * (1000000 * Δ) - 2 * δ < (ρ i)⁻¹ * dist x y := by
    linarith [(abs_lt.mp hdxy).1]
  have hD : 0 < 10 * (1000000 * Δ) - 2 * δ := by nlinarith
  have hdeq : dist x y = ρ i * ((ρ i)⁻¹ * dist x y) := by field_simp
  have hxyi : 10 ^ 6 * Δ * ρ i < dist x y := by
    rw [h106, hdeq]
    exact sgp03_num_far_SGP2 hL6 hδ1 hri (by linarith) hr1
  have hdpos : 0 < dist x y := lt_of_le_of_lt (by positivity) hxyi
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hdpos; exact lt_irrefl _ hdpos
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hxLi : x ∈ ball i (10 ^ 6 * Δ * ρ i) := by
    rw [h106]
    refine ball_subset_ball ?_ hxi
    have := mul_mul_le_mul_mul_SGP2 (k := 95 / 100) (k' := 1) (by norm_num) hLpos.le hri.le
    linarith
  have hyLi : y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) := by
    rw [h106]
    refine ball_subset_ball ?_ hy21
    exact mul_le_mul_of_nonneg_right
      (sgp03_num_outer_SGP2 hLpos.le hσs (by linarith)) hri.le
  exact ⟨y, w₀, hw₀, hgy, hy21, hdxy, hay, hxLi, hyLi, hxyi,
    ball_subset_ball (mul_mul_le_mul_mul_SGP2 (by norm_num) hLpos.le hri.le) hxi,
    ball_subset_ball (mul_mul_le_mul_mul_SGP2 (by norm_num) hLpos.le hri.le) hy21⟩

/-- **FC23 item 2 at the slim base, slim chart `j ∈ J_i`** (FC19 route, SGP03 B:4525–4535): with
SGP01's list bounds (`.99 < ρ(j)/ρ(i) < 1.01`, `d(i, j) < 2Lρ(i)`) and `x ∈ B(j, Lρ(j))`, the
reference lift is a COMMON endpoint of both original slim tests. -/
theorem fc23_slimbase_slim_tests_RFC (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {δ : ℝ}
    (hΔ : 1 ≤ Δ) (hδ1 : δ < 1) (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100))
    (hσs : 0 < σs) (hσs24 : σs * 24 ≤ 1) {i j : X} (hi : i ∈ S.centres)
    (hs1 : 99 / 100 < ρ j / ρ i) (hs2 : ρ j / ρ i < 101 / 100)
    (hdij : dist i j < 2 * (1000000 * Δ) * ρ i) {a : ℝ} (ha : a = 1 ∨ a = -1) {x : X}
    (hxi : x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i)) (hxj : x ∈ ball j (1000000 * Δ * ρ j)) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      |(ρ i)⁻¹ * dist x y - 10 * (1000000 * Δ)| < 2 * δ ∧
      10 * (1000000 * Δ) - δ < a * (sgpRaw S i y - sgpRaw S i x) ∧
      x ∈ ball i (10 ^ 6 * Δ * ρ i) ∧ y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) ∧
      10 ^ 6 * Δ * ρ i < dist x y ∧
      x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) ∧
      10 ^ 6 * Δ * ρ j < dist x y ∧
      x ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧ y ∈ ball i (30 * (1000000 * Δ) * ρ i) := by
  have hri := hρ i
  have hrj := hρ j
  have hΔ0 : 0 < Δ := by linarith
  have h106 : (10 : ℝ) ^ 6 * Δ = 1000000 * Δ := by norm_num
  have hLpos : 0 < 1000000 * Δ := by positivity
  have hL6 : (1000000 : ℝ) ≤ 1000000 * Δ := by linarith
  have hij : ρ i < 100 / 99 * ρ j := by
    rw [lt_div_iff₀ hri] at hs1
    linarith
  have hji : ρ j < 101 / 100 * ρ i := by
    rw [div_lt_iff₀ hri] at hs2
    linarith
  obtain ⟨y, w₀, hw₀, hgy, hy21, hdxy, hay, hxLi, hyLi, hxyi, hx30, hy30⟩ :=
    fc23_slimbase_lift_RFC S hΔ hδ1 hβ hσs hσs24 hi hxi ha
  have hr1 : 10 * (1000000 * Δ) - 2 * δ < (ρ i)⁻¹ * dist x y := by
    linarith [(abs_lt.mp hdxy).1]
  have hdeq : dist x y = ρ i * ((ρ i)⁻¹ * dist x y) := by field_simp
  have hxLj : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by rw [h106]; exact hxj
  have hyLj : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) := by
    rw [h106, mem_ball]
    have hyi : dist y i < 21 * (1000000 * Δ) * ρ i := hy21
    have htri := dist_triangle y i j
    have h24 := mul_le_mul_of_nonneg_right (sgp03_num_outer_SGP2 hLpos.le hσs hσs24) hrj.le
    have hl := sgp03_num_lift_SGP2 hLpos hri hij hyi hdij
    linarith
  have hxyj : 10 ^ 6 * Δ * ρ j < dist x y := by
    rw [h106, hdeq]
    exact sgp03_num_far_SGP2 hL6 hδ1 hri hji.le hr1
  exact ⟨y, w₀, hw₀, hgy, hdxy, hay, hxLi, hyLi, hxyi, hxLj, hyLj, hxyj, hx30, hy30⟩

/-- **FC23 item 2 at the slim base, zero block** (SGP03 B:4549–4556): the reference lift with sign
`a₀` lies in LC73's original radial test domain at the scale `ρ(x)`:
`ρ(x) < d(x, y) < ζ⁻¹ρ(x)` (for `.99ρ(i) < ρ(x) < 1.01ρ(i)`, `0 < ζ < 1/(100L)`). -/
theorem fc23_slimbase_zero_tests_RFC (S : SlimFamily X g hmetric ρ hρ β Δ σs K) {δ ζ : ℝ}
    (hΔ : 1 ≤ Δ) (hδ1 : δ < 1) (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δ / 100))
    (hσs : 0 < σs) (hσs24 : σs * 24 ≤ 1) (hζ : 0 < ζ) (hζL : ζ < 1 / (100 * (1000000 * Δ)))
    {i : X} (hi : i ∈ S.centres) {x : X} (hxi : x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i))
    (hρx1 : 99 / 100 * ρ i < ρ x) (hρx2 : ρ x < 101 / 100 * ρ i) {a₀ : ℝ}
    (ha₀ : a₀ = 1 ∨ a₀ = -1) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      |(ρ i)⁻¹ * dist x y - 10 * (1000000 * Δ)| < 2 * δ ∧
      10 * (1000000 * Δ) - δ < a₀ * (sgpRaw S i y - sgpRaw S i x) ∧
      x ∈ ball i (10 ^ 6 * Δ * ρ i) ∧ y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) ∧
      10 ^ 6 * Δ * ρ i < dist x y ∧
      x ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧ y ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧
      ρ x < dist x y ∧ dist x y < ζ⁻¹ * ρ x := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hL6 : (1000000 : ℝ) ≤ 1000000 * Δ := by linarith
  obtain ⟨y, w₀, hw₀, hgy, -, hdxy, hay, hxLi, hyLi, hxyi, hx30, hy30⟩ :=
    fc23_slimbase_lift_RFC S hΔ hδ1 hβ hσs hσs24 hi hxi ha₀
  have hr1 : 10 * (1000000 * Δ) - 2 * δ < (ρ i)⁻¹ * dist x y := by
    linarith [(abs_lt.mp hdxy).1]
  have hr2 : (ρ i)⁻¹ * dist x y < 10 * (1000000 * Δ) - 2 * δ + 4 * δ := by
    linarith [(abs_lt.mp hdxy).2]
  have hdeq : dist x y = ρ i * ((ρ i)⁻¹ * dist x y) := by field_simp
  obtain ⟨hz1, hz2⟩ := sgp03_zero_range_SGP3 hL6 hδ1 hζ hζL hri hρx1 hρx2 hr1 hr2 hdeq
  exact ⟨y, w₀, hw₀, hgy, hdxy, hay, hxLi, hyLi, hxyi, hx30, hy30, hz1, hz2⟩

end SlimBase

section Rows

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_RFC23P
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_RFC23P
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_RFC23P
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNR_RFC23P
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCR_RFC23P
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC23 item 2 at the edge base** (projected analogue, EGP04's base `D_i = B(i, 20Δρ(i))`) on
`LocalChartPackets`: for every listed edge chart `j` of EGP02's list, every `x ∈ D_i` and sign `a`,
the FC19-route configuration; for every slim chart whose support meets `D_i` and every `x ∈ D_i`,
the FC22-route configuration (item 1 = `egp02_row`). -/
theorem fc23_items12_edgebase_RFC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T)
    (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) (hβL : β 1 ≤ 1 / (1000 * (10 ^ 6 * Δ)))
    (hσs0 : 0 < σs) (hσs12 : σs ≤ 1 / 12) {i : X} (hi : i ∈ P.edge.centres) :
    (∀ j ∈ egpEdgeList P.toLocalChartFamily i, ∀ x ∈ ball i (20 * Δ * ρ i), ∀ a : ℝ,
      (a = 1 ∨ a = -1) →
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        |egpRaw P.edge i y - egpRaw P.edge i x - 400 * Δ * a| < 2 * b ∧
        (400 * Δ - 3 * b) * ρ i < dist x y ∧ dist x y < (400 * Δ + 3 * b) * ρ i ∧
        x ∈ ball i (100 * Δ * ρ i) ∧ y ∈ ball i (1000 * Δ * ρ i) ∧ 100 * Δ * ρ i < dist x y ∧
        x ∈ ball j (100 * Δ * ρ j) ∧ y ∈ ball j (1000 * Δ * ρ j) ∧ 100 * Δ * ρ j < dist x y ∧
        x ∈ ball i (600 * Δ * ρ i) ∧ y ∈ ball i (600 * Δ * ρ i)) ∧
    (∀ j ∈ P.slim.centres, (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      ∀ x ∈ ball i (20 * Δ * ρ i),
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        |slimRaw_KA3 P.toLocalChartFamily j y - slimRaw_KA3 P.toLocalChartFamily j x -
          10 * (10 ^ 6 * Δ)| < 2 * β 1 ∧
        (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y ∧
        dist x y ≤ (10 * (10 ^ 6 * Δ) + 3 * β 1) * ρ j ∧
        x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) ∧
        10 ^ 6 * Δ * ρ j < dist x y ∧
        x ∈ ball i (100 * Δ * ρ i) ∧ 100 * Δ * ρ i < 200 * Δ * ρ i ∧
        200 * Δ * ρ i < (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ∧
        ∃ z : X, dist x z = 200 * Δ * ρ i ∧ dist z y = dist x y - 200 * Δ * ρ i ∧
          z ∈ ball i (220 * Δ * ρ i) ∧ ScaledGeodesicReaches_RFC g hmetric x w₀ z) := by
  obtain ⟨-, -, hE, hS, -⟩ := egp02_row P.toLocalChartFamilyE P.zero hΛ hΔ hμ hτ hLΛ he hT hi
  have h106 : (10 : ℝ) ^ 6 * Δ = 1000000 * Δ := by norm_num
  refine ⟨fun j hj x hx a ha => ?_, fun j hj hmeet x hx => ?_⟩
  · obtain ⟨hs1, hs2, hdij, hsub, -⟩ := hE j hj
    exact fc23_edgebase_edge_tests_RFC P.edge hΔ hbL hi hs1 hs2 hdij hx (hsub hx) ha
  · obtain ⟨hs1, -, -, hsub, -⟩ := hS j hj hmeet
    have hxj : x ∈ ball j (92 / 100 * (10 ^ 6 * Δ) * ρ j) := by rw [h106]; exact hsub hx
    exact fc23_edgebase_slim_tests_RFC P.toLocalChartFamily hΔ hβL hσs0 hσs12 hj hs1 hx hxj

/-- **FC23 item 2 at the slim base** (projected analogue, SGP03's base `D_i = B(i, .95Lρ(i))`) on
`LocalChartPacketsR`: for every chart `j` of SGP01's list, every `x ∈ D_i ∩ B(j, Lρ(j))` and sign
`a`, the FC19-route configuration (item 1 = `sgp01_row`). -/
theorem fc23_items12_slimbase_RFC
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) {δr : ℝ}
    (hδ1 : δr < 1) (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δr / 100)) {i : X}
    (hi : i ∈ P.slim.centres) :
    ∀ j ∈ sgpSlimList P.slim i, ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
      x ∈ ball j (1000000 * Δ * ρ j) → ∀ a : ℝ, (a = 1 ∨ a = -1) →
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        |(ρ i)⁻¹ * dist x y - 10 * (1000000 * Δ)| < 2 * δr ∧
        10 * (1000000 * Δ) - δr < a * (sgpRaw P.slim i y - sgpRaw P.slim i x) ∧
        x ∈ ball i (10 ^ 6 * Δ * ρ i) ∧ y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) ∧
        10 ^ 6 * Δ * ρ i < dist x y ∧
        x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) ∧
        10 ^ 6 * Δ * ρ j < dist x y ∧
        x ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧ y ∈ ball i (30 * (1000000 * Δ) * ρ i) := by
  obtain ⟨-, -, hL, -⟩ := sgp01_row P hΛ hΔ hLΛ he hT hσs.le hσs1 hi
  intro j hj x hxi hxj a ha
  obtain ⟨hs1, hs2, hdij⟩ := hL j hj
  exact fc23_slimbase_slim_tests_RFC P.slim hΔ hδ1 hβ hσs (by linarith) hi hs1 hs2 hdij ha hxi hxj

end Rows

end DifferentialGeometry.Geometry.Collapse
