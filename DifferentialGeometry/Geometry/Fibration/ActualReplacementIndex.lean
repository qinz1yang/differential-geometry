import DifferentialGeometry.Geometry.Fibration.ActualEdgeAffineComparison
import DifferentialGeometry.Geometry.Fibration.ActualReplacementEdgeBall

/-!
# FDC01's replacement edge index on the original charts (given a selected centre near `q'`)

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7217–7240):
"… a center `p_j` with `d(q', p_j) < .72ΔR_j`. Its original coordinate estimate gives
`|η_j(q')| < .8Δ`. Moreover `q' ∈ E'`, so the SAME distance smoothing gives tiny `t(q')`; both
original `j` cutoffs are full. Consequently `j ∈ J_e(i)`, since `q' ∈ D_i`. EGP02–EGP04 apply to
this actual selected index and to both `q, q' ∈ D_i`. With their permitted `θ < 1/100`, they give
`|η_j(q) − η_j(q')| ≤ (|η_i(q) − η_i(q')| + 2θ)/.99 < .04Δ`. Thus `|η_j(q)| < 2Δ`. The distance
estimate just obtained also puts `q` in its original smooth `j` domain. The common height is below
`4.01Δ`, so `ζ_j(q) = 1`."

The centre `p_j` near the weak-border witness `q'` comes from LFR44 item 2 (on
`LocalChartPacketsC14D`, lane C14-FAM3: `d(q', j) < (Δ + 2)ρ(j)` and `< 2Δρ(j)`); the lemmas below
take ANY selected centre `j` with `d(q', j) < Rρ(j)`, `R ≤ 2Δ`, universally quantified, and give
`|η_j(q)| < 1.001R + .031Δ` (so `< 2Δ` for `R = Δ + 2`, `Δ ≥ 100`; `< 2.1Δ` for `R = 2Δ`).

* `fdc01_replacement_of_comparison_FDC1` (kernel): with EGP04's (EC) for `j` on `D_i` as data.
* `fdc01_replacement_row_FDC1` (row tier): (EC) supplied by `egp04_edge` at `θ = 1/100`.
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

section Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}

/-- **FDC01's replacement index, kernel**: for an edge index `i`, points `q, q'` with
`d(q', i) < 4.1Δρ(i)`, `d(q, q') < 4.2Δρ(i)`, `|η_i(q') − η_i(q)| < Δ/100`, `t(q') < Δ/100`,
`t(q) ≤ 4.01Δ`, and a selected edge centre `j` with `d(q', j) < Rρ(j)` (`R ≤ 2Δ`): `j ∈ J_e(i)`,
and if `η_j` satisfies an affine comparison `|s_j η_j − (aη_i + c)| < θ` on `D_i` (`a = ±1`,
`θ ≤ 1/100`, EGP04's (EC)), then `d(q, j) < 7Δρ(j)`, `|η_j(q)| < 1.001R + .031Δ` and
`ζ_j(q) = 1`. -/
theorem fdc01_replacement_of_comparison_FDC1
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hσc : σc ≤ 1 / 1000)
    {i : X} {q q' : X} (hq'i : dist q' i < 41 / 10 * Δ * ρ i)
    (hqq' : dist q q' < 42 / 10 * Δ * ρ i) (hη' : |L.edge.coord i q' - L.edge.coord i q| < Δ / 100)
    (ht' : L.edge.smoothing q' / ρ q' < Δ / 100) (htq : L.edge.smoothing q / ρ q ≤ 401 / 100 * Δ)
    {R : ℝ} (hR : R ≤ 2 * Δ) {j : X} (hj : j ∈ L.edge.centres) (hq'j : dist q' j < R * ρ j) :
    j ∈ egpEdgeList L i ∧
      ∀ a θ c : ℝ, (a = 1 ∨ a = -1) → θ ≤ 1 / 100 →
        (∀ x ∈ ball i (20 * Δ * ρ i),
          |ρ j / ρ i * L.edge.coord j x - (a * L.edge.coord i x + c)| < θ) →
        dist q j < 7 * Δ * ρ j ∧ |L.edge.coord j q| < 1001 / 1000 * R + 31 / 1000 * Δ ∧
          L.edge.cutoff j q = 1 := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hκ : Δ * Λ ≤ 1 / 10 ^ 11 := by nlinarith
  -- the scale ratio `s_j = ρ(j)/ρ(i)`
  have hq'j2 : dist q' j < 2 * Δ * ρ j := by
    have := mul_le_mul_of_nonneg_right hR hrj.le
    linarith
  have hij : dist i j < 41 / 10 * Δ * ρ i + 2 * Δ * ρ j := by
    have h := dist_triangle i q' j
    rw [dist_comm i q'] at h
    linarith
  have hρij : |ρ j - ρ i| ≤ 41 / 10 * (Δ * Λ) * ρ i + 2 * (Δ * Λ) * ρ j := by
    have h1 := L.lipschitz_scale.dist_le_mul j i
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq, dist_comm] at h1
    have h2 : Λ * dist i j ≤ Λ * (41 / 10 * Δ * ρ i + 2 * Δ * ρ j) :=
      mul_le_mul_of_nonneg_left hij.le hΛ
    linarith
  have hκi : (Δ * Λ) * ρ i ≤ 1 / 10 ^ 11 * ρ i := mul_le_mul_of_nonneg_right hκ hri.le
  have hκj : (Δ * Λ) * ρ j ≤ 1 / 10 ^ 11 * ρ j := mul_le_mul_of_nonneg_right hκ hrj.le
  have hr1 : 99 / 100 * ρ i ≤ ρ j := by linarith [(abs_le.mp hρij).1]
  have hr2 : 99 / 100 * ρ j ≤ ρ i := by linarith [(abs_le.mp hρij).2]
  -- the coordinate and the cutoff of `j` at `q'`
  have hlip' := L.edge.coord_lipschitz_max_KC4 hj q' j
  rw [L.edge.coord_self_FDC1 hj, sub_zero] at hlip'
  have hmax : max (1 + σc) 0 ≤ 1001 / 1000 := max_le (by linarith) (by norm_num)
  have hcq' : |L.edge.coord j q'| < 1001 / 1000 * R := by
    have h1 : max (1 + σc) 0 / ρ j * dist q' j ≤ 1001 / 1000 / ρ j * dist q' j :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmax hrj.le) dist_nonneg
    have h2 : 1001 / 1000 / ρ j * dist q' j < 1001 / 1000 / ρ j * (R * ρ j) :=
      mul_lt_mul_of_pos_left hq'j (by positivity)
    have h3 : 1001 / 1000 / ρ j * (R * ρ j) = 1001 / 1000 * R := by
      field_simp
    linarith
  have hDj : 0 < Δ * ρ j := mul_pos hΔ0 hrj
  have hDi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hq'jB : q' ∈ ball j (100 * Δ * ρ j) := by
    rw [mem_ball]
    linarith
  have hζq' : L.edge.cutoff j q' = 1 :=
    L.edge.cutoff_eq_one_of_le hΔ0 hj hq'jB (by linarith) (by linarith)
  have hq'D : q' ∈ ball i (20 * Δ * ρ i) := by
    rw [mem_ball]
    linarith
  have hlist : j ∈ egpEdgeList L i :=
    ⟨hj, q', subset_tsupport _ (by rw [Function.mem_support, hζq']; norm_num), hq'D⟩
  refine ⟨hlist, fun a θ c ha hθ hEC => ?_⟩
  -- (EC) at `q` and `q'`
  have hqD : q ∈ ball i (20 * Δ * ρ i) := by
    rw [mem_ball]
    have h := dist_triangle q q' i
    linarith
  have h1 := hEC q hqD
  have h2 := hEC q' hq'D
  set sj := ρ j / ρ i with hsj
  have hsj99 : 99 / 100 ≤ sj := by
    rw [hsj, le_div_iff₀ hri]
    exact hr1
  have hdiff : sj * |L.edge.coord j q - L.edge.coord j q'| < 3 / 100 * Δ := by
    have hai : |a * L.edge.coord i q - a * L.edge.coord i q'| < Δ / 100 := by
      rcases ha with rfl | rfl
      · rw [one_mul, one_mul, abs_sub_comm]
        exact hη'
      · have he : -1 * L.edge.coord i q - -1 * L.edge.coord i q' =
            L.edge.coord i q' - L.edge.coord i q := by ring
        rw [he]
        exact hη'
    have hs0 : 0 ≤ sj := by linarith
    rw [← abs_of_nonneg hs0, ← abs_mul, mul_sub]
    have h3 := abs_sub_le (sj * L.edge.coord j q) (a * L.edge.coord i q + c)
      (sj * L.edge.coord j q')
    have h4 := abs_sub_le (a * L.edge.coord i q + c) (a * L.edge.coord i q' + c)
      (sj * L.edge.coord j q')
    have h5 : (a * L.edge.coord i q + c) - (a * L.edge.coord i q' + c) =
        a * L.edge.coord i q - a * L.edge.coord i q' := by ring
    rw [h5] at h4
    rw [abs_sub_comm (a * L.edge.coord i q' + c)] at h4
    linarith
  have hdiff' : |L.edge.coord j q - L.edge.coord j q'| < 31 / 1000 * Δ := by
    have h3 : 99 / 100 * |L.edge.coord j q - L.edge.coord j q'| ≤
        sj * |L.edge.coord j q - L.edge.coord j q'| :=
      mul_le_mul_of_nonneg_right hsj99 (abs_nonneg _)
    linarith
  have hcq : |L.edge.coord j q| < 1001 / 1000 * R + 31 / 1000 * Δ := by
    have h3 := abs_sub_abs_le_abs_sub (L.edge.coord j q) (L.edge.coord j q')
    linarith
  -- the distance from `q` to `j` and the cutoff of `j` at `q`
  have hqj : dist q j < 7 * Δ * ρ j := by
    have h3 := dist_triangle q q' j
    have h4 : 99 / 100 * (Δ * ρ i) ≤ Δ * ρ j := by
      have := mul_le_mul_of_nonneg_left hr1 hΔ0.le
      linarith
    linarith
  have hqjB : q ∈ ball j (100 * Δ * ρ j) := by
    rw [mem_ball]
    linarith
  exact ⟨hqj, hcq, L.edge.cutoff_eq_one_of_le hΔ0 hj hqjB (by linarith) (by linarith)⟩

end Kernel

/-- **FDC01's replacement index, row tier**: (EC) from `egp04_edge` at `θ = 1/100`. For the
original-chart data of FDC01 (`q, q'` as in `fdc01_replacement_of_comparison_FDC1`), every
selected edge centre `j` with `d(q', j) < Rρ(j)` (`R ≤ 2Δ`) lies in `J_e(i)` and has
`d(q, j) < 7Δρ(j)`, `|η_j(q)| < 1.001R + .031Δ` and `ζ_j(q) = 1`. -/
theorem fdc01_replacement_row_FDC1 {Δ β₂ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ : ℝ)
        (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ 1 / 10 ^ 12 →
        μ * Δ < 1 / 10 ^ 4 → ∀ i ∈ L.edge.centres, ∀ q q' : X,
          dist q' i < 41 / 10 * Δ * ρ i → dist q q' < 42 / 10 * Δ * ρ i →
          |L.edge.coord i q' - L.edge.coord i q| < Δ / 100 →
          L.edge.smoothing q' / ρ q' < Δ / 100 → L.edge.smoothing q / ρ q ≤ 401 / 100 * Δ →
          ∀ R : ℝ, R ≤ 2 * Δ → ∀ j ∈ L.edge.centres, dist q' j < R * ρ j →
            j ∈ egpEdgeList L.toLocalChartFamily i ∧ dist q j < 7 * Δ * ρ j ∧
              |L.edge.coord j q| < 1001 / 1000 * R + 31 / 1000 * Δ ∧ L.edge.cutoff j q = 1 := by
  obtain ⟨Lc, η₀, hLc, hη₀, h4⟩ := egp04_edge hΔ hβ₂ hβ₂1 (by norm_num : (0 : ℝ) < 1 / 100)
    (by norm_num)
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1 hLmax hΛ
    hLΛ hμ hτ hσc hμΔ i hi q q' hq'i hqq' hη' ht' htq R hR j hj hq'j
  obtain ⟨hlist, hrep⟩ := fdc01_replacement_of_comparison_FDC1 L.toLocalChartFamily hΔ hΛ hLΛ
    (hσc.trans (by norm_num)) hq'i hqq' hη' ht' htq hR hj hq'j
  have hσc' : σc ≤ (1 / 100 : ℝ) ^ 2 / 10 ^ 8 := hσc.trans (by norm_num)
  have hμΔ' : μ * Δ < (1 / 100 : ℝ) / 100 := hμΔ.trans_le (by norm_num)
  obtain ⟨a, ha, hEC⟩ := h4 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1
    hLmax hΛ hLΛ hμ hτ hσc' hμΔ' i hi j hlist
  exact ⟨hlist, hrep a (1 / 100) _ ha le_rfl (fun x hx => (hEC x hx).1)⟩

end DifferentialGeometry.Geometry.Collapse
