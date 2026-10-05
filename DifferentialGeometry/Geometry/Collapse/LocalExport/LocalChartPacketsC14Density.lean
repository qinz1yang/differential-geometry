import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# LFR44 item 2 on the final chapter-13 family (`LocalChartPacketsC14D`)

Lane C14-FAM3 (producer-side fix of lane C14-FDC1's obstruction: chapter 14's FDC01, blueprint
207B B:7217, needs LFR44 item 2 at the SAME family). `LocalChartPacketsC14D … vs ζ Λz` extends the
final family `LocalChartPacketsC14` (no delivered structure is edited; every row stated on
`LocalChartPacketsC14` applies through the projection `toLocalChartPacketsC14`) by ONE field:

* `weak_edge_density`: LFR44 item 2 verbatim (blueprint 207A, `thm:collapse-strong-edge-density-cover`,
  A:28632–28634): for every nonslim point `p` of the LC16 one-stratum (the nonslim condition of
  `EdgeFamily.covers_nonslim`, verbatim) and every weak edge `q` (own scale, qualities `b', s'`)
  with `d(q, p) < 10Δρ(p)`, there is a strong edge `a` (own scale, qualities `b, s`) with
  `d(q, a) < ρ(a)`.

The finite (centre) forms follow with `covers_strong` and the `Λ`-Lipschitz scale:

* `LocalChartPacketsC14D.weak_edge_centre_FAM3`: a strong edge `a` with `d(q, a) < ρ(a)` and an
  edge centre `j` with `d(a, j) < Δρ(j)` and `d(q, j) < (Δ + 2)ρ(j)`;
* `LocalChartPacketsC14D.weak_edge_centre_two_FAM3`: an edge centre `j` with `d(q, j) < 2Δρ(j)`
  (the finite cover's radius, `exists_strong_edge_cover_tail`).

Producer: `eventually_nonempty_localChartPacketsC14D` (`LocalChartPacketsC14DensityProducer`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The final chapter-13 family with LFR44 item 2**: `LocalChartPacketsC14` whose weak edges
near the nonslim one-stratum have nearby strong edges (blueprint 207A, A:28632–28634). -/
structure LocalChartPacketsC14D (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
    extends
      LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs ζ Λz
    where
  /-- LFR44 item 2: every weak edge within `10Δρ(p)` of a nonslim one-stratum point `p` has a
  strong edge `a` with `d(q, a) < ρ(a)`. -/
  weak_edge_density : ∀ p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1,
    ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
    ∀ q : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q Δ b' s' →
      dist q p < 10 * Δ * ρ p →
      ∃ a : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
        dist q a < ρ a

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **LFR44 item 2, centre form with the strong edge** (FDC01, B:7217–7222): a weak edge `q`
within `10Δρ(p)` of a nonslim one-stratum point `p` has a strong edge `a` with `d(q, a) < ρ(a)`,
and `covers_strong` gives an edge centre `j` with `d(a, j) < Δρ(j)`, hence
`d(q, j) < (Δ + 2)ρ(j)` (the scale is `Λ`-Lipschitz with `ΛΔ ≤ 10⁻⁴`). -/
theorem LocalChartPacketsC14D.weak_edge_centre_FAM3
    (P : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100)
    {p : X} (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hns : ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))))
    {q : X} (hq : @isEdgePoint.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q Δ b' s')
    (hqp : dist q p < 10 * Δ * ρ p) :
    ∃ a : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
      dist q a < ρ a ∧ ∃ j ∈ P.edge.centres, dist a j < Δ * ρ j ∧ dist q j < (Δ + 2) * ρ j := by
  obtain ⟨a, ha, hqa⟩ := P.weak_edge_density p hp hns q hq hqp
  obtain ⟨j, hj, haj⟩ := P.edge.covers_strong a ha
  refine ⟨a, ha, hqa, j, hj, haj, ?_⟩
  have hlip := P.lipschitz_scale.dist_le_mul a j
  rw [Real.dist_eq, Real.coe_toNNReal _ hΛ] at hlip
  have hρj := hρ j
  have hΛΔ : Λ * Δ ≤ 1 := by nlinarith
  have hρa : ρ a ≤ 2 * ρ j := by
    have h1 := (abs_le.mp hlip).2
    have h2 : Λ * dist a j ≤ Λ * (Δ * ρ j) := mul_le_mul_of_nonneg_left haj.le hΛ
    have h3 : (Λ * Δ) * ρ j ≤ 1 * ρ j := mul_le_mul_of_nonneg_right hΛΔ hρj.le
    nlinarith
  calc dist q j ≤ dist q a + dist a j := dist_triangle _ _ _
    _ < ρ a + Δ * ρ j := add_lt_add hqa haj
    _ ≤ (Δ + 2) * ρ j := by nlinarith

/-- **LFR44 item 2, finite form** (the radius `2Δρ(j)` of the finite cover
`exists_strong_edge_cover_tail`): a weak edge `q` within `10Δρ(p)` of a nonslim one-stratum
point `p` lies within `2Δρ(j)` of an edge centre `j` of the SAME family (`Δ ≥ 2`). -/
theorem LocalChartPacketsC14D.weak_edge_centre_two_FAM3
    (P : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hΔ : 2 ≤ Δ)
    {p : X} (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hns : ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))))
    {q : X} (hq : @isEdgePoint.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q Δ b' s')
    (hqp : dist q p < 10 * Δ * ρ p) :
    ∃ j ∈ P.edge.centres, dist q j < 2 * Δ * ρ j := by
  obtain ⟨-, -, -, j, hj, -, hqj⟩ := P.weak_edge_centre_FAM3 hΛ hΔΛ hp hns hq hqp
  refine ⟨j, hj, hqj.trans_le ?_⟩
  have hρj := hρ j
  nlinarith

end DifferentialGeometry.Geometry.Collapse
