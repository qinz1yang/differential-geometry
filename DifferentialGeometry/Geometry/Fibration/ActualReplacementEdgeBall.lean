import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphBlocks
import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink

/-!
# FDC03's edge-ball coverage on the original charts (the part free of the final map)

Blueprint `master207B.tex`, FDC03 (`thm:fibration-actual-circle-remainder`, B:7327–7330): "Any
nonslim one-stratum point lies, by LFR44.2 and LPA06, in a selected edge ball with `|η_i| < 3.1Δ`
and `t < 3.1Δ`." (LFR44.2's display, `master207A.tex` A:28739–28742.) The consequence "EDP02 puts
a full ambient neighborhood of that point in `X₂`" concerns the final map `E` and is NOT here.

On the actual edge charts of `L : LocalChartFamily` (tangential coordinate `η_j`, the ONE shared
smoothing `F`, `t = F/ρ`), with `σ ≤ 1/2`, `μ ≤ 1/100`, `100ΔΛ ≤ 1/100`:

* `EdgeFamily.coord_self_FDC1`: `η_j(j) = 0`.
* `edge_ball_bounds_FDC1`: `d(x, j) < 2Δρ(j)` gives `|η_j(x)| < 3.1Δ`, `t(x) < 3.1Δ` and
  `ζ_j(x) = 1`.
* `fdc03_nonslim_edge_ball_FDC1`: every nonslim point of the LC16 one-stratum (the family's
  `covers_nonslim`, LFR44 item 1) lies in such a ball.
* `fdc03_edge_alternative_FDC1`: the family's exhaustion with the edge alternative sharpened to
  these bounds.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
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
  {σc μ b s b' s' ε γc βc : ℝ}

/-- The tangential coordinate of an actual edge chart vanishes at its centre. -/
theorem EdgeFamily.coord_self_FDC1 (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    {j : X} (hj : j ∈ F.centres) : F.coord j j = 0 := by
  have hc := F.chart_center j hj
  unfold EdgeFamily.coord
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have h0 := C.coord_center
  rw [hc'] at h0
  exact h0

/-- **LFR44.2's bounds on an actual edge ball**: `d(x, j) < 2Δρ(j)` gives `|η_j(x)| < 3.1Δ`,
`t(x) < 3.1Δ` and `ζ_j(x) = 1` (`σ ≤ 1/2`, `μ ≤ 1/100`, `100ΔΛ ≤ 1/100`). -/
theorem edge_ball_bounds_FDC1
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (hσc : σc ≤ 1 / 2) (hμ : μ ≤ 1 / 100) (hΛ : 0 ≤ Λ)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {j : X} (hj : j ∈ L.edge.centres) {x : X}
    (hx : dist x j < 2 * Δ * ρ j) :
    |L.edge.coord j x| < 31 / 10 * Δ ∧ cgpHeight L x < 31 / 10 * Δ ∧ L.edge.cutoff j x = 1 := by
  have hrj := hρ j
  have hrx := hρ x
  have hD : 0 < Δ * ρ j := mul_pos hΔ hrj
  -- the tangential coordinate
  have hlip := L.edge.coord_lipschitz_max_KC4 hj x j
  rw [L.edge.coord_self_FDC1 hj, sub_zero] at hlip
  have hmax : max (1 + σc) 0 ≤ 3 / 2 := max_le (by linarith) (by norm_num)
  have hcoord : |L.edge.coord j x| < 31 / 10 * Δ := by
    have h1 : max (1 + σc) 0 / ρ j * dist x j ≤ 3 / 2 / ρ j * dist x j :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmax hrj.le) dist_nonneg
    have h2 : 3 / 2 / ρ j * dist x j < 3 / 2 / ρ j * (2 * Δ * ρ j) :=
      mul_lt_mul_of_pos_left hx (by positivity)
    have h3 : 3 / 2 / ρ j * (2 * Δ * ρ j) = 3 * Δ := by
      field_simp
    linarith
  -- the scale on the ball
  have hρx : 99 / 100 * ρ j ≤ ρ x := by
    have h1 := L.lipschitz_scale.dist_le_mul x j
    rw [Real.dist_eq, Real.coe_toNNReal _ hΛ] at h1
    have h2 : Λ * dist x j ≤ Λ * (2 * Δ * ρ j) := mul_le_mul_of_nonneg_left hx.le hΛ
    have h3 : Λ * (2 * Δ * ρ j) ≤ 1 / 5000 * ρ j := by
      have h4 : Δ * Λ ≤ 1 / 10000 := by linarith
      have h5 := mul_le_mul_of_nonneg_right h4 hrj.le
      nlinarith
    linarith [(abs_le.mp h1).1]
  -- the height
  have hA := L.edge.centre_mem_closure_weak hj
  have hsm : L.edge.smoothing x < dist x j + μ * (Δ * ρ j) := by
    have h1 := (abs_lt.mp (L.edge.smoothing_value j hj x)).2
    have h2 := infDist_le_dist_of_mem hA (x := x)
    linarith
  have hheight : cgpHeight L x < 31 / 10 * Δ := by
    unfold cgpHeight
    rw [div_lt_iff₀ hrx]
    have h1 : μ * (Δ * ρ j) ≤ 1 / 100 * (Δ * ρ j) := mul_le_mul_of_nonneg_right hμ hD.le
    have h2 : 31 / 10 * Δ * (99 / 100 * ρ j) ≤ 31 / 10 * Δ * ρ x :=
      mul_le_mul_of_nonneg_left hρx (by positivity)
    nlinarith
  refine ⟨hcoord, hheight, ?_⟩
  have hx100 : x ∈ ball j (100 * Δ * ρ j) := by
    rw [mem_ball]
    nlinarith
  exact L.edge.cutoff_eq_one_of_le hΔ hj hx100 (by linarith)
    (by unfold cgpHeight at hheight; linarith)

/-- **FDC03's nonslim coverage, original part**: every nonslim point of the LC16 one-stratum lies
in an actual edge ball `B(j, 2Δρ(j))` with `|η_j| < 3.1Δ`, `t < 3.1Δ` and `ζ_j = 1` there. -/
theorem fdc03_nonslim_edge_ball_FDC1
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (hσc : σc ≤ 1 / 2) (hμ : μ ≤ 1 / 100) (hΛ : 0 ≤ Λ)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {x : X} (hx : x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hns : ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) _ x (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))) :
    ∃ j ∈ L.edge.centres, dist x j < 2 * Δ * ρ j ∧ |L.edge.coord j x| < 31 / 10 * Δ ∧
      cgpHeight L x < 31 / 10 * Δ ∧ L.edge.cutoff j x = 1 := by
  obtain ⟨j, hj, hd⟩ := L.edge.covers_nonslim x hx hns
  exact ⟨j, hj, hd, edge_ball_bounds_FDC1 L hΔ hσc hμ hΛ hΔΛ hj hd⟩

/-- **The family's exhaustion with the sharpened edge alternative**: every point is in the zero
stratum, a circle ball `B(j, 2ρ(j))`, a slim ball `B(j, 2Δρ(j))`, or an actual edge ball
`B(j, 2Δρ(j))` on which `|η_j| < 3.1Δ`, `t < 3.1Δ` and `ζ_j = 1`. -/
theorem fdc03_edge_alternative_FDC1
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (hσc : σc ≤ 1 / 2) (hμ : μ ≤ 1 / 100) (hΛ : 0 ≤ Λ)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (x : X) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0 ∨
      (∃ j ∈ L.circle.centres, x ∈ ball j (2 * ρ j)) ∨
      (∃ j ∈ L.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
      ∃ j ∈ L.edge.centres, dist x j < 2 * Δ * ρ j ∧ |L.edge.coord j x| < 31 / 10 * Δ ∧
        cgpHeight L x < 31 / 10 * Δ ∧ L.edge.cutoff j x = 1 := by
  rcases L.exhaustion x with h | h | h | ⟨j, hj, hd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, hd, edge_ball_bounds_FDC1 L hΔ hσc hμ hΛ hΔΛ hj hd⟩))

end DifferentialGeometry.Geometry.Collapse
