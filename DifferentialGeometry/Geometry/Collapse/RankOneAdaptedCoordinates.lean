import DifferentialGeometry.Geometry.Collapse.RankOneSmoothingDerivative
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianProductAnchors

/-!
# Same-splitting smooth rank-one coordinates

Long product anchors supply the actual minimizing-direction control used by
localized distance smoothing. Centering the resulting function preserves the
original splitting map in every value and differential estimate.
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

private theorem smoothed_anchor_coordinate
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {Y : Type*} [MetricSpace Y] {q a : M} {y₀ : Y} {ν R ε τ : ℝ}
    (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (hε : 0 < ε) (hτ : τ < ε / 4)
    (ha : a ∉ Metric.ball q 2)
    (hvalue : ∀ x ∈ Metric.ball q R,
      |(dist q a - dist x a) - (α.toFun x).fst| < τ)
    (hangle : ∃ θ : ℝ, 0 ≤ θ ∧ θ < τ ∧
      ∀ x ∈ Metric.ball q 2, ∀ u u' : TangentSpace I x,
      g.inner x u u = 1 → g.inner x u' u' = 1 →
      intrinsicGeodesic g hEnorm x u (dist x a) = a →
      intrinsicGeodesic g hEnorm x u' (dist x a) = a →
      Real.arccos (g.inner x u u') ≤ θ)
    (htest : ∀ x ∈ Metric.ball q 2, ∀ z ∈ Metric.ball q R, 1 < dist x z →
      ∀ u w : TangentSpace I x,
      g.inner x u u = 1 → g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x u (dist x a) = a →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      |g.inner x u w - ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < τ) :
    ∃ φ : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1) ∧ φ q = 0 ∧
      LipschitzWith (Real.toNNReal (1 + ε)) φ ∧
      (∀ x ∈ Metric.ball q R,
        |φ x - (α.toFun x).fst| < ε * dist x q + τ) ∧
      ∀ x ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q R, 1 < dist x z →
        ∀ w : TangentSpace I x, g.inner x w w = 1 →
        intrinsicGeodesic g hEnorm x w (dist x z) = z →
        |mvfderiv (I := I) φ x w -
          ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < ε + τ := by
  let : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  obtain ⟨θ, hθ, hθτ, hangle⟩ := hangle
  have hdir : ∀ x ∈ Metric.ball q 2,
      ∀ u ∈ minimizingDirectionsTo g hEnorm {a} x,
      ∀ u' ∈ minimizingDirectionsTo g hEnorm {a} x,
      Real.arccos (g.inner x u u') < ε / 4 := by
    intro x hx u hu u' hu'
    exact (hangle x hx u u' hu.1 hu'.1
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu.2)
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu'.2)).trans_lt
        (hθτ.trans hτ)
  have hUY : Metric.ball q 2 ⊆ ({a} : Set M)ᶜ := by
    intro x hx hxa
    have heq : x = a := mem_singleton_iff.mp hxa
    exact ha (heq ▸ hx)
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hFl⟩ :=
    exists_localized_distance_smoothing_of_arccos g hEnorm hε isClosed_singleton
      (singleton_nonempty a) Metric.isOpen_ball hUY hdir
      (isCompact_closedBall q 1)
      (fun x hx => Metric.mem_ball.mpr
        (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by norm_num : (1 : ℝ) < 2)))
      (e := 1) zero_lt_one
  let φ : M → ℝ := fun x => F q - F x
  have hφ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1) :=
    (contMDiffOn_const.sub hFO).mono
      (fun x hx => hCO (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le))
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
  refine ⟨φ, hφ, by simp [φ], hφl, ?_, ?_⟩
  · intro x hx
    calc |φ x - (α.toFun x).fst|
        ≤ |φ x - (dist q a - dist x a)| +
          |(dist q a - dist x a) - (α.toFun x).fst| := abs_sub_le _ _ _
      _ < ε * dist x q + τ := add_lt_add_of_le_of_lt (hφanchor x) (hvalue x hx)
  · intro x hx z hz hxz w hw hwz
    have hx2 : x ∈ Metric.ball q 2 := Metric.ball_subset_ball (by norm_num) hx
    have hxO : x ∈ O := hCO (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le)
    have hFx := (hFO x hxO).contMDiffAt (hO.mem_nhds hxO)
    have hxY : 0 < Metric.infDist x ({a} : Set M) := by
      exact (isClosed_singleton.notMem_iff_infDist_pos (singleton_nonempty a)).mp
        (hUY hx2)
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

private theorem image_Ioo_distance_bound {a ε : ℝ} (hε : 0 < ε)
    (ha : |a| < 1 + ε) : Metric.infDist a (Ioo (-1 : ℝ) 1) ≤ ε := by
  have hden : 0 < 1 + ε := by linarith
  have ht : a / (1 + ε) ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · rw [lt_div_iff₀ hden]
      linarith [(abs_lt.mp ha).1]
    · rw [div_lt_iff₀ hden]
      simpa only [one_mul] using (abs_lt.mp ha).2
  have hv : |a - a / (1 + ε)| ≤ ε := by
    have he : a - a / (1 + ε) = a * ε / (1 + ε) := by field_simp; ring
    rw [he, abs_div, abs_mul, abs_of_pos hε, abs_of_pos hden, div_le_iff₀ hden]
    nlinarith
  exact (Metric.infDist_le_dist_of_mem ht).trans (by simpa only [Real.dist_eq] using hv)

universe uE uH u v

theorem exists_rankOne_adapted_coordinate_parameters {γ : ℝ}
    (hγ : 0 < γ) (hγone : γ < 1) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ < min γ (1 / 4) ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (q : M) (y₀ : Y)
        (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν),
        (∀ y ∈ Metric.ball q ν⁻¹, SectionalBoundedBelowAt g y (-ν ^ 2)) →
        ∃ φ : M → ℝ,
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1) ∧ φ q = 0 ∧
          (∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
            |φ x - φ y| ≤ (1 + γ) * dist x y) ∧
          (∀ x ∈ Metric.ball q 1, Metric.infDist (φ x) (Ioo (-1 : ℝ) 1) ≤ γ) ∧
          (∀ t ∈ Ioo (-1 : ℝ) 1,
            Metric.infDist t (φ '' Metric.ball q 1) ≤ γ) ∧
          ∀ x ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q γ⁻¹, 1 < dist x z →
            ∀ w : TangentSpace I x, g.inner x w w = 1 →
            intrinsicGeodesic g hEnorm x w (dist x z) = z →
            |mvfderiv (I := I) φ x w -
              ((α.toFun z).fst - (α.toFun x).fst) / dist x z| < γ := by
  let R : ℝ := γ⁻¹ + 3
  let ε : ℝ := γ / 32
  let τ : ℝ := γ / 256
  have hR : 2 < R := by
    dsimp [R]
    have hi : 0 < γ⁻¹ := inv_pos.mpr hγ
    linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ < ε / 4 := by dsimp [τ, ε]; linarith
  obtain ⟨s, hs, νStar, hνStar, hparameters⟩ :=
    exists_product_anchor_direction_parameters hR hτ
  let ν₀ : ℝ := min νStar (γ / 64) / 2
  have hν₀ : 0 < ν₀ := by dsimp [ν₀]; positivity
  have hν₀Star : ν₀ < νStar := by
    have hm := min_le_left νStar (γ / 64)
    dsimp only [ν₀]
    linarith
  have hν₀γ : ν₀ < γ / 64 := by
    have hm := min_le_right νStar (γ / 64)
    dsimp only [ν₀]
    linarith
  refine ⟨ν₀, hν₀, lt_min (by linarith) (by linarith), ?_⟩
  intro ν hν hνsmall E instNorm instSpace instFinite instNe H instTop I instBoundary
    M instMetric instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y instY q y₀ α hsec
  have hνs : ν < νStar := hνsmall.trans_lt hν₀Star
  have hνγ : ν < γ / 64 := hνsmall.trans_lt hν₀γ
  have hνone : ν < 1 := α.error_lt_one
  obtain ⟨hbuffer, hanchors⟩ := hparameters ν hν hνs
  have hs0 : 0 < s := by linarith
  have hR0 : 0 < R := by linarith
  have hcov : s < ν⁻¹ - ν := by linarith
  have hdp : dist (WithLp.toLp 2 (s, y₀)) (WithLp.toLp 2 ((0 : ℝ), y₀)) = s := by
    rw [(WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq]
    simp only [Real.dist_eq, sub_zero, abs_of_pos hs0]
  have hdm : dist (WithLp.toLp 2 (-s, y₀)) (WithLp.toLp 2 ((0 : ℝ), y₀)) = s := by
    rw [(WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq]
    simp only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hs0]
  obtain ⟨aPlus, haPlus, himagePlus⟩ :=
    α.coverage_witness (WithLp.toLp 2 (s, y₀)) (by rw [hdp]; exact hcov)
  obtain ⟨aMinus, haMinus, himageMinus⟩ :=
    α.coverage_witness (WithLp.toLp 2 (-s, y₀)) (by rw [hdm]; exact hcov)
  rw [dist_comm] at himagePlus himageMinus
  obtain ⟨hradPlus, hradMinus, hvalue, hangle, htest⟩ :=
    hanchors E H I M g hEnorm Y q y₀ α aPlus aMinus hsec
      haPlus haMinus himagePlus himageMinus
  have haAway : aPlus ∉ Metric.ball q 2 := by
    intro ha2
    have hr := α.supplied_anchor_radius_error aPlus haPlus himagePlus
    rw [abs_of_pos hs0] at hr
    have hl := (abs_lt.mp hr).1
    have ha2d := Metric.mem_ball.mp ha2
    rw [dist_comm aPlus q] at ha2d
    linarith
  obtain ⟨φ, hφ, hφq, hφl, hφvalue, hφtest⟩ :=
    smoothed_anchor_coordinate g hEnorm α hε hτε haAway hvalue hangle htest
  have hεγ : ε ≤ γ := by dsimp [ε]; linarith
  have hετγ : ε + τ < γ := by dsimp [ε, τ]; linarith
  have hballR : Metric.ball q 1 ⊆ Metric.ball q R :=
    Metric.ball_subset_ball (by linarith)
  have hφrad (x : M) : |φ x| ≤ (1 + ε) * dist x q := by
    have hl := hφl.dist_le_mul x q
    rw [hφq, Real.dist_eq, sub_zero, Real.coe_toNNReal _ (by linarith)] at hl
    exact hl
  refine ⟨φ, hφ, hφq, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hl := hφl.dist_le_mul x y
    rw [Real.dist_eq, Real.coe_toNNReal _ (by linarith)] at hl
    exact hl.trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  · intro x hx
    have hx1 := Metric.mem_ball.mp hx
    have hrad := hφrad x
    have hb : |φ x| < 1 + ε := by nlinarith
    exact (image_Ioo_distance_bound hε hb).trans hεγ
  · intro t ht
    let t' : ℝ := (1 - 6 * ν) * t
    have hνsix : 0 < 1 - 6 * ν := by linarith
    have htabs : |t| < 1 := abs_lt.mpr ht
    have ht' : |t'| < 1 - 6 * ν := by
      dsimp [t']
      rw [abs_mul, abs_of_pos hνsix]
      nlinarith
    have ht0 : |t'| < ν⁻¹ - ν := by linarith
    have hdt : dist (WithLp.toLp 2 (t', y₀)) (WithLp.toLp 2 ((0 : ℝ), y₀)) = |t'| := by
      rw [(WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq]
      simp only [Real.dist_eq, sub_zero]
    obtain ⟨x, hx, hxim⟩ :=
      α.coverage_witness (WithLp.toLp 2 (t', y₀)) (by rw [hdt]; exact ht0)
    have hr := (abs_le.mp (α.radial_error x hx)).1
    have htri := dist_triangle (α.toFun x) (WithLp.toLp 2 (t', y₀))
      (WithLp.toLp 2 ((0 : ℝ), y₀))
    rw [hdt, dist_comm (α.toFun x) (WithLp.toLp 2 (t', y₀))] at htri
    have hx1 : x ∈ Metric.ball q 1 := Metric.mem_ball.mpr (by linarith)
    have hfst := (WithLp.dist_fst_le (WithLp.toLp 2 (t', y₀)) (α.toFun x)).trans_lt hxim
    simp only [WithLp.toLp_fst, Real.dist_eq] at hfst
    have hscale : |t' - t| ≤ 6 * ν := by
      have he : t' - t = -(6 * ν * t) := by dsimp [t']; ring
      rw [he, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 6 * ν)]
      nlinarith
    have hv := hφvalue x (hballR hx1)
    have hdistx := Metric.mem_ball.mp hx1
    have hsump := abs_sub_le t t' (α.toFun x).fst
    have hsum := abs_sub_le t (α.toFun x).fst (φ x)
    have htotal : |t - φ x| < γ := by
      rw [abs_sub_comm t t'] at hsump
      rw [abs_sub_comm (α.toFun x).fst (φ x)] at hsum
      dsimp [ε, τ] at hv
      nlinarith
    exact (Metric.infDist_le_dist_of_mem (mem_image_of_mem φ hx1)).trans
      (by simpa only [Real.dist_eq] using htotal.le)
  · intro x hx z hz hxz w hw hwz
    have hzR : z ∈ Metric.ball q R :=
      Metric.ball_subset_ball (by dsimp [R]; linarith) hz
    exact (hφtest x hx z hzR hxz w hw hwz).trans hετγ

end DifferentialGeometry.Geometry.Collapse
