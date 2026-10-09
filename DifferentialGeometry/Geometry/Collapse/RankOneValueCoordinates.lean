import DifferentialGeometry.Geometry.Collapse.RankOneAdaptedCoordinates
import DifferentialGeometry.Geometry.Comparison.Toponogov.ScaledRiemannianProductAnchors

/-!
# LFR19: rank-one coordinates with a separate value tolerance

Blueprint 207A, LFR19 (`lem:collapse-buffered-scalar-coordinate`, A:26310–26357). For fixed
`L > 0`, `T > 2L`, `e > 0` and `0 < σ < 1`, every normalized `(1, β)`-splitting `α = (u, v)` of
a complete smooth pointed manifold with `sec ≥ -β²` on `B(p, β⁻¹)`, `β` small, has a scalar
coordinate `η`, smooth on a neighbourhood of `B̄(p, L)`, with `η(p) = 0`, `Lip η ≤ 1 + σ`,
`|η - u| < e` on `B(p, L)`, image within Hausdorff distance `σ L` of `(-L, L)`, and the
all-direction estimate (LFR19.1) for every minimizing initial unit direction of every tested
segment from `B(p, L)` to `B(p, T)` of length greater than `L`.

The proof is the LC79 construction at scale `L` (no rescaling of the Riemannian structure): the
scale-`L` anchor `exists_scaled_product_anchor_directions` (LC78 at scale `L`), the smooth
localized distance smoothing LC28 on `B̄(p, L) ⊆ B(p, 2L)`, and the first-order control of the
smoothing along minimizing directions. The source is smooth, so LC28 (not its finite-order
form LFR02) supplies the smoothing, exactly as in LC79. The threshold depends only on
`L, T, e, σ` (not even on the dimension).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The LC79 smoothing step at scale `L`, with the value clause retained. -/
private theorem scaled_smoothed_anchor_coordinate
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {Y : Type*} [MetricSpace Y] {q a : M} {y₀ : Y} {β L R ε τ : ℝ}
    (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) β)
    (hL : 0 < L) (hε : 0 < ε) (hτ : τ < ε / 4)
    (ha : a ∉ Metric.ball q (2 * L))
    (hvalue : ∀ x ∈ Metric.ball q (R * L),
      |(dist q a - dist x a) - (α.toFun x).fst| < τ * L)
    (hangle : ∃ θ : ℝ, 0 ≤ θ ∧ θ < τ ∧
      ∀ x ∈ Metric.ball q (2 * L), ∀ u u' : TangentSpace I x,
      g.inner x u u = 1 → g.inner x u' u' = 1 →
      intrinsicGeodesic g hEnorm x u (dist x a) = a →
      intrinsicGeodesic g hEnorm x u' (dist x a) = a →
      Real.arccos (g.inner x u u') ≤ θ)
    (htest : ∀ x ∈ Metric.ball q (2 * L), ∀ z ∈ Metric.ball q (R * L), L < dist x z →
      ∀ u w : TangentSpace I x,
      g.inner x u u = 1 → g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x u (dist x a) = a →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      |g.inner x u w - ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < τ) :
    ∃ φ : M → ℝ, ∃ O : Set M, IsOpen O ∧ Metric.closedBall q L ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ O ∧ φ q = 0 ∧
      LipschitzWith (Real.toNNReal (1 + ε)) φ ∧
      (∀ x ∈ Metric.ball q (R * L),
        |φ x - (α.toFun x).fst| < ε * dist x q + τ * L) ∧
      ∀ x ∈ Metric.ball q L, ∀ z ∈ Metric.ball q (R * L), L < dist x z →
        ∀ w : TangentSpace I x, g.inner x w w = 1 →
        intrinsicGeodesic g hEnorm x w (dist x z) = z →
        |mvfderiv (I := I) φ x w -
          ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < ε + τ := by
  let : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  obtain ⟨θ, hθ, hθτ, hangle⟩ := hangle
  have hdir : ∀ x ∈ Metric.ball q (2 * L),
      ∀ u ∈ minimizingDirectionsTo g hEnorm {a} x,
      ∀ u' ∈ minimizingDirectionsTo g hEnorm {a} x,
      Real.arccos (g.inner x u u') < ε / 4 := by
    intro x hx u hu u' hu'
    exact (hangle x hx u u' hu.1 hu'.1
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu.2)
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu'.2)).trans_lt
        (hθτ.trans hτ)
  have hUY : Metric.ball q (2 * L) ⊆ ({a} : Set M)ᶜ := by
    intro x hx hxa
    have heq : x = a := mem_singleton_iff.mp hxa
    exact ha (heq ▸ hx)
  have hCU : Metric.closedBall q L ⊆ Metric.ball q (2 * L) := fun x hx =>
    Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
  obtain ⟨F, O, hO, hCO, hFO, -, -, hdiff, hFl⟩ :=
    exists_localized_distance_smoothing_of_arccos g hEnorm hε isClosed_singleton
      (singleton_nonempty a) Metric.isOpen_ball hUY hdir
      (isCompact_closedBall q L) hCU (e := 1) zero_lt_one
  let φ : M → ℝ := fun x => F q - F x
  have hφ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ O := contMDiffOn_const.sub hFO
  have hφl : LipschitzWith (Real.toNNReal (1 + ε)) φ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa only [φ, Real.dist_eq, sub_sub_sub_cancel_left, abs_neg, dist_comm y x] using
      hFl.dist_le_mul y x
  have hφanchor (x : M) : |φ x - (dist q a - dist x a)| ≤ ε * dist x q := by
    have hd := hdiff q x
    simp only [Metric.infDist_singleton] at hd
    rw [dist_comm q x] at hd
    convert hd using 1
    congr 1
    dsimp only [φ]
    ring
  refine ⟨φ, O, hO, hCO, hφ, by simp [φ], hφl, ?_, ?_⟩
  · intro x hx
    calc |φ x - (α.toFun x).fst|
        ≤ |φ x - (dist q a - dist x a)| +
          |(dist q a - dist x a) - (α.toFun x).fst| := abs_sub_le _ _ _
      _ < ε * dist x q + τ * L := add_lt_add_of_le_of_lt (hφanchor x) (hvalue x hx)
  · intro x hx z hz hxz w hw hwz
    have hx2 : x ∈ Metric.ball q (2 * L) :=
      Metric.ball_subset_ball (by linarith) hx
    have hxO : x ∈ O := hCO (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le)
    have hFx := (hFO x hxO).contMDiffAt (hO.mem_nhds hxO)
    have hxY : 0 < Metric.infDist x ({a} : Set M) :=
      (isClosed_singleton.notMem_iff_infDist_pos (singleton_nonempty a)).mp (hUY hx2)
    obtain ⟨u, hu, hFu⟩ := exists_minimizingDirection_smoothing_derivative_bound
      g hEnorm hε.le isClosed_singleton (singleton_nonempty a) hxY
      (hFx.mdifferentiableAt (by simp)) hdiff
    have hφder : mvfderiv (I := I) φ x w = -mvfderiv (I := I) F x w := by
      change mvfderiv (I := I) ((fun y : M => F q) - F) x w = _
      rw [_root_.mvfderiv_sub mdifferentiableAt_const
        (hFx.mdifferentiableAt (by simp)), _root_.mvfderiv_const]
      simp
    have hcontrol := hFu w hw
    have hcompare := htest x hx2 z hz hxz u w hu.1 hw
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu.2) hwz
    rw [hφder]
    have hsum := abs_add_le (-mvfderiv (I := I) F x w - g.inner x u w)
      (g.inner x u w - ((α.toFun z).fst - (α.toFun x).fst) / dist x z)
    have heq : (-mvfderiv (I := I) F x w - g.inner x u w) +
        (g.inner x u w - ((α.toFun z).fst - (α.toFun x).fst) / dist x z) =
        -mvfderiv (I := I) F x w -
          ((α.toFun z).fst - (α.toFun x).fst) / dist x z := by ring
    rw [heq] at hsum
    have hc : |-mvfderiv (I := I) F x w - g.inner x u w| ≤ ε := by
      have he : -mvfderiv (I := I) F x w - g.inner x u w =
          -(mvfderiv (I := I) F x w + g.inner x u w) := by ring
      rw [he, abs_neg]
      exact hcontrol
    exact hsum.trans_lt (add_lt_add_of_le_of_lt hc hcompare)

/-- A real number of absolute value below `(1 + ε) L` lies within `ε L` of `(-L, L)`. -/
private theorem image_Ioo_scaled_distance_bound {a ε L : ℝ} (hε : 0 < ε)
    (ha : |a| < (1 + ε) * L) : Metric.infDist a (Ioo (-L) L) ≤ ε * L := by
  have hden : 0 < 1 + ε := by linarith
  have habs : |a| / (1 + ε) < L := by rw [div_lt_iff₀ hden]; linarith
  have ht : a / (1 + ε) ∈ Ioo (-L) L := by
    have h := abs_lt.mp (show |a / (1 + ε)| < L by rwa [abs_div, abs_of_pos hden])
    exact ⟨h.1, h.2⟩
  have hv : |a - a / (1 + ε)| ≤ ε * L := by
    have he : a - a / (1 + ε) = a * ε / (1 + ε) := by field_simp; ring
    rw [he, abs_div, abs_mul, abs_of_pos hε, abs_of_pos hden, div_le_iff₀ hden]
    nlinarith [abs_nonneg a]
  exact (Metric.infDist_le_dist_of_mem ht).trans (by simpa only [Real.dist_eq] using hv)

universe uE uH u v

/-- **LFR19: rank-one coordinates with a separate value tolerance.** For `L > 0`, `T > 2L`,
`e > 0`, `0 < σ < 1` there is `β₀ > 0` such that for every `0 < β < β₀`, every actual normalized
`(1, β)`-splitting `α` of a complete smooth pointed manifold with `sec ≥ -β²` on `B(p, β⁻¹)` has
a coordinate `η`: smooth on an open neighbourhood of `B̄(p, L)`, `η p = 0`, globally
`(1 + σ)`-Lipschitz, `|η - u| < e` on `B(p, L)`, with image within Hausdorff distance `σ L` of
`(-L, L)` (both inclusions), and (LFR19.1) for every minimizing initial unit direction. -/
theorem exists_rankOne_coordinate_value_tolerance {L T e σ : ℝ} (hL : 0 < L)
    (hT : 2 * L < T) (he : 0 < e) (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (p : M) (y₀ : Y)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y ∈ Metric.ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∃ η : M → ℝ, ∃ O : Set M, IsOpen O ∧ Metric.closedBall p L ⊆ O ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O ∧ η p = 0 ∧
          LipschitzWith (Real.toNNReal (1 + σ)) η ∧
          (∀ x ∈ Metric.ball p L, |η x - (α.toFun x).fst| < e) ∧
          (∀ x ∈ Metric.ball p L, Metric.infDist (η x) (Ioo (-L) L) ≤ σ * L) ∧
          (∀ t ∈ Ioo (-L) L, Metric.infDist t (η '' Metric.ball p L) ≤ σ * L) ∧
          ∀ x ∈ Metric.ball p L, ∀ x' ∈ Metric.ball p T, L < dist x x' →
            ∀ w : TangentSpace I x, g.inner x w w = 1 →
            intrinsicGeodesic g hEnorm x w (dist x x') = x' →
            |mvfderiv (I := I) η x w -
              ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ := by
  let R : ℝ := T / L + 3
  let ε : ℝ := min (σ / 8) (e / (4 * L))
  let τ : ℝ := ε / 8
  have hR : 2 < R := by
    have : 0 < T / L := div_pos (by linarith) hL
    dsimp [R]; linarith
  have hRL : R * L = T + 3 * L := by
    dsimp [R]; field_simp
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεσ : ε ≤ σ / 8 := min_le_left _ _
  have hεe : ε * L ≤ e / 4 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (σ / 8) (e / (4 * L))) hL.le
    have h' : e / (4 * L) * L = e / 4 := by field_simp
    dsimp [ε]; linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ < ε / 4 := by dsimp [τ]; linarith
  obtain ⟨β₁, hβ₁, hanchors⟩ := exists_scaled_product_anchor_directions hL hR hτ
  refine ⟨min β₁ (min (σ * L / 12) (1 / (2 * L + 2))), lt_min hβ₁ (lt_min (by positivity)
    (by positivity)), ?_⟩
  intro β hβ hβsmall E instNorm instSpace instFinite instNe H instTop I instBoundary
    M instMetric instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y instY p y₀ α hsec
  have hββ₁ : β < β₁ := hβsmall.trans_le (min_le_left _ _)
  have hβσ : β < σ * L / 12 :=
    hβsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβL : β < 1 / (2 * L + 2) :=
    hβsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨a, haway, hvalue, hangle, htest⟩ :=
    hanchors β hβ hββ₁ E H I M g hEnorm Y p y₀ α hsec
  obtain ⟨φ, O, hO, hCO, hφ, hφp, hφl, hφvalue, hφtest⟩ :=
    scaled_smoothed_anchor_coordinate g hEnorm α hL hε hτε haway hvalue hangle htest
  have hballR : Metric.ball p L ⊆ Metric.ball p (R * L) :=
    Metric.ball_subset_ball (by rw [hRL]; linarith)
  have hballT : Metric.ball p T ⊆ Metric.ball p (R * L) :=
    Metric.ball_subset_ball (by rw [hRL]; linarith)
  have hτL : τ * L ≤ ε * L / 8 := by dsimp [τ]; nlinarith
  have hφrad (x : M) : |φ x| ≤ (1 + ε) * dist x p := by
    have hl := hφl.dist_le_mul x p
    rw [hφp, Real.dist_eq, sub_zero, Real.coe_toNNReal _ (by linarith)] at hl
    exact hl
  refine ⟨φ, O, hO, hCO, hφ, hφp, hφl.weaken (Real.toNNReal_le_toNNReal (by linarith)),
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hv := hφvalue x (hballR hx)
    have hxp : dist x p < L := hx
    have hεd : ε * dist x p ≤ ε * L := mul_le_mul_of_nonneg_left hxp.le hε.le
    linarith
  · intro x hx
    have hxp : dist x p < L := hx
    have hb : |φ x| < (1 + ε) * L :=
      (hφrad x).trans_lt (mul_lt_mul_of_pos_left hxp (by linarith))
    exact (image_Ioo_scaled_distance_bound hε hb).trans
      (mul_le_mul_of_nonneg_right (by linarith) hL.le)
  · intro t ht
    have hνone : β < 1 := α.error_lt_one
    let t' : ℝ := (1 - σ / 4) * t
    have hσ4 : 0 < 1 - σ / 4 := by linarith
    have htabs : |t| < L := abs_lt.mpr ht
    have ht' : |t'| < (1 - σ / 4) * L := by
      dsimp [t']
      rw [abs_mul, abs_of_pos hσ4]
      exact mul_lt_mul_of_pos_left htabs hσ4
    have hβinv : 2 * L + 2 ≤ β⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hβ]
      exact hβL.le.trans (by rw [one_div])
    have ht0 : |t'| < β⁻¹ - β := by nlinarith
    have hdt : dist (WithLp.toLp 2 (t', y₀)) (WithLp.toLp 2 ((0 : ℝ), y₀)) = |t'| := by
      rw [(WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq]
      simp only [Real.dist_eq, sub_zero]
    obtain ⟨x, hx, hxim⟩ :=
      α.coverage_witness (WithLp.toLp 2 (t', y₀)) (by rw [hdt]; exact ht0)
    have hr := (abs_le.mp (α.radial_error x hx)).1
    have htri := dist_triangle (α.toFun x) (WithLp.toLp 2 (t', y₀))
      (WithLp.toLp 2 ((0 : ℝ), y₀))
    rw [hdt, dist_comm (α.toFun x) (WithLp.toLp 2 (t', y₀))] at htri
    have hxL : dist x p < L := by nlinarith
    have hx1 : x ∈ Metric.ball p L := hxL
    have hfst := (WithLp.dist_fst_le (WithLp.toLp 2 (t', y₀)) (α.toFun x)).trans_lt hxim
    simp only [WithLp.toLp_fst, Real.dist_eq] at hfst
    have hscale : |t' - t| ≤ σ / 4 * L := by
      have he' : t' - t = -(σ / 4 * t) := by dsimp [t']; ring
      rw [he', abs_neg, abs_mul, abs_of_pos (by positivity : 0 < σ / 4)]
      exact mul_le_mul_of_nonneg_left htabs.le (by positivity)
    have hv := hφvalue x (hballR hx1)
    have hεd : ε * dist x p ≤ ε * L := mul_le_mul_of_nonneg_left hxL.le hε.le
    have hεσL : ε * L ≤ σ / 8 * L := mul_le_mul_of_nonneg_right hεσ hL.le
    have hsump := abs_sub_le t t' (α.toFun x).fst
    have hsum := abs_sub_le t (α.toFun x).fst (φ x)
    have htotal : |t - φ x| < σ * L := by
      rw [abs_sub_comm t t'] at hsump
      rw [abs_sub_comm (α.toFun x).fst (φ x)] at hsum
      nlinarith
    exact (Metric.infDist_le_dist_of_mem (mem_image_of_mem φ hx1)).trans
      (by simpa only [Real.dist_eq] using htotal.le)
  · intro x hx x' hx' hxx' w hw hwx'
    exact (hφtest x hx x' (hballT hx') hxx' w hw hwx').trans (by linarith)

end DifferentialGeometry.Geometry.Collapse
