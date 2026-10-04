import DifferentialGeometry.Geometry.Collapse.RankOneValueCoordinates
import DifferentialGeometry.Geometry.Collapse.LongTestValuesRiemannian
import DifferentialGeometry.Geometry.Comparison.AdaptedStabilityRiemannian
import DifferentialGeometry.Geometry.Metric.Approximation.EndpointProductLifts

/-!
# LFR36.2, tangential half: the LFR19 coordinate is pinned to every anchor direction

Blueprint 207A, LFR36 (`lem:collapse-edge-prescribed-gradient-pinning`, A:28073–28208), first
inequality of (LFR36.2), in the original metric. Let `f` satisfy the conclusions of LFR19 with
`L = 100Δ`, `T = 1000Δ` and quality `σ` for an actual normalized `(1, b)`-splitting `α = (u, v)`.
At a point `y ∈ B(p, 16Δ)`, let `a` be a point with `Δ/80 ≤ d(y, a) ≤ 40Δ` whose coordinate
slope is almost one: `(1 - θ) d(y, a) ≤ u(a) - u(y)` (for the LFR35 anchor `a₁₊` this is the
chart estimate `D/r → 1` of the blueprint's proof). Then for EVERY minimizing unit direction `v`
from `y` to `a`, `‖∇f(y) - v‖ ≤ ι`, written in the covector form
`|df_y(X) - g(v, X)| ≤ ι |X|_g`.

Route (the blueprint's, with one change): `f` is pinned to the direction `w₊` of a long lift `l₊`
of `(u(y) + 200Δ, v(y))` by the LFR19 test and the Riesz step; `w₊` and `v` are compared through
the scale-`Δ/100` product anchor at `y` (`exists_scaled_product_anchor_directions` for the
splitting recentred at `y`), whose direction pairs with every tested direction like the
coordinate slope. The blueprint compares `l₋` with `a₁₊` directly by a product computation; the
anchor route needs the curvature bound of LFR19 itself (`sec ≥ -b²` on `B(p, b⁻¹)`, which holds
whenever `f` is an LFR19 output) instead of the bound on `B(p, 10000Δ)` only.

The own-scale form in `g_x = q⁻² g` follows from this one by the factor `q`
(`abs_scaled_mvfderiv_sub_inner_le`): the error grows by `|q - 1|`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

/-- Recentring a normalized `(1, b)`-splitting at a nearby point `y`: the real coordinate is
translated by `u(y)`, the factor point becomes `v(y)`. -/
theorem exists_recentered_product_approx {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {p : X} {y₀ : Y} {b δ : ℝ} (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b)
    (y : X) (hbδ : 3 * b ≤ δ) (hδ : δ < 1) (hdom : dist y p + δ⁻¹ + 2 * b ≤ b⁻¹) :
    ∃ α' : KleinerLottApprox y (WithLp.toLp 2 ((0 : ℝ), (α.toFun y).snd)) δ,
      ∀ x, (α'.toFun x).fst = (α.toFun x).fst - (α.toFun y).fst := by
  have hb := α.error_pos
  have hδ0 : 0 < δ := by linarith
  set c : ℝ := (α.toFun y).fst
  let e : WithLp 2 (ℝ × Y) → WithLp 2 (ℝ × Y) := fun w => WithLp.toLp 2 (w.fst - c, w.snd)
  have he (w w' : WithLp 2 (ℝ × Y)) : dist (e w) (e w') = dist w w' := by
    rw [WithLp.prod_dist_eq_sqrt_sq_add_sq, WithLp.prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist (w.fst - c) (w'.fst - c) ^ 2 + dist w.snd w'.snd ^ 2) = _
    rw [dist_sub_right]
  have hyp : y ∈ ball p b⁻¹ := mem_ball.mpr (by have := inv_pos.mpr hδ0; linarith)
  have hin (x : X) (hx : dist x y < δ⁻¹) : x ∈ ball p b⁻¹ := by
    have ht := dist_triangle x y p
    exact mem_ball.mpr (by linarith)
  have hbase : e (α.toFun y) = WithLp.toLp 2 ((0 : ℝ), (α.toFun y).snd) := by
    change WithLp.toLp 2 ((α.toFun y).fst - c, (α.toFun y).snd) = _
    rw [sub_self]
  refine ⟨⟨hδ0, hδ, fun x => e (α.toFun x), hbase, ?_, ?_⟩, fun x => rfl⟩
  · intro x hx x' hx'
    rw [he]
    exact (α.distortion x (hin x hx) x' (hin x' hx')).trans (by linarith)
  · intro w hw
    let w₀ : WithLp 2 (ℝ × Y) := WithLp.toLp 2 (w.fst + c, w.snd)
    have hew : e w₀ = w := by
      change WithLp.toLp 2 (w.fst + c - c, w.snd) = w
      rw [add_sub_cancel_right]
      rfl
    have hw₀y : dist w₀ (α.toFun y) < δ⁻¹ - δ := by
      rw [← he, hew, hbase]
      exact hw
    have hyrad := (abs_le.mp (α.radial_error y hyp)).2
    have hw₀p : dist w₀ (WithLp.toLp 2 ((0 : ℝ), y₀)) < b⁻¹ - b := by
      have ht := dist_triangle w₀ (α.toFun y) (WithLp.toLp 2 ((0 : ℝ), y₀))
      linarith
    obtain ⟨x, hx, hxw⟩ := α.coverage_witness w₀ hw₀p
    have hxy : dist x y < δ⁻¹ := by
      have h1 := abs_le.mp (α.distortion x hx y hyp)
      have h2 := dist_triangle (α.toFun x) w₀ (α.toFun y)
      rw [dist_comm (α.toFun x) w₀] at h2
      linarith
    have hmem : e (α.toFun x) ∈ (fun x => e (α.toFun x)) '' ball y δ⁻¹ := ⟨x, hxy, rfl⟩
    refine (infDist_le_dist_of_mem hmem).trans ?_
    rw [← hew, he]
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
/-- Two `g`-unit vectors with `g(U, W) ≥ 1 - c` pair with every vector alike up to
`√(2c) |X|_g`. -/
theorem abs_inner_sub_inner_le_of_inner_ge (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {y : M} {U W : TangentSpace I y} {c : ℝ}
    (hU : g.inner y U U = 1) (hW : g.inner y W W = 1) (hc : 1 - c ≤ g.inner y U W)
    (X : TangentSpace I y) :
    |g.inner y U X - g.inner y W X| ≤ Real.sqrt (2 * c) * Real.sqrt (g.inner y X X) := by
  have hnorm (Z : TangentSpace I y) : ‖Z‖ = Real.sqrt (g.inner y Z Z) := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq]
  have hsq : ‖U - W‖ ^ 2 ≤ 2 * c := by
    rw [norm_sub_sq_real, hnorm, hnorm, hU, hW, Real.sqrt_one, hEnorm.inner_eq]
    linarith
  have hUW : ‖U - W‖ ≤ Real.sqrt (2 * c) := Real.le_sqrt_of_sq_le hsq
  have hdiff : g.inner y U X - g.inner y W X = inner ℝ (U - W) X := by
    rw [inner_sub_left, hEnorm.inner_eq, hEnorm.inner_eq]
  rw [hdiff, ← hnorm]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hUW (norm_nonneg X))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
/-- A bound on unit vectors gives the covector bound `|df(X)| ≤ h |X|_g`. -/
theorem abs_mvfderiv_le_mul_sqrt_of_unit (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {f : M → ℝ} {y : M} {h : ℝ}
    (hunit : ∀ w : TangentSpace I y, g.inner y w w = 1 → |mvfderiv (I := I) f y w| ≤ h)
    (X : TangentSpace I y) :
    |mvfderiv (I := I) f y X| ≤ h * Real.sqrt (g.inner y X X) := by
  have hnorm (Z : TangentSpace I y) : ‖Z‖ = Real.sqrt (g.inner y Z Z) := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq]
  rw [← hnorm]
  rcases eq_or_ne X 0 with rfl | hX
  · simp
  have hpos : 0 < ‖X‖ := norm_pos_iff.mpr hX
  set w : TangentSpace I y := ‖X‖⁻¹ • X with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
  have hwg : g.inner y w w = 1 := by
    rw [← hEnorm.inner_eq, real_inner_self_eq_norm_sq, hwn, one_pow]
  have hXw : X = ‖X‖ • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have h1 := hunit w hwg
  rw [hXw, map_smul, smul_eq_mul, abs_mul, abs_of_pos hpos, norm_smul, norm_norm, hwn,
    mul_one]
  exact mul_le_mul_of_nonneg_left h1 hpos.le |>.trans (by rw [mul_comm])

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
/-- The own-scale form: multiplying the differential by `q` costs `|q - 1|`. -/
theorem abs_scaled_mvfderiv_sub_inner_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {f : M → ℝ}
    {y : M} {v : TangentSpace I y} {q ι : ℝ} (hq : 0 ≤ q) (hv : g.inner y v v = 1)
    (hpin : ∀ X : TangentSpace I y,
      |mvfderiv (I := I) f y X - g.inner y v X| ≤ ι * Real.sqrt (g.inner y X X))
    (X : TangentSpace I y) :
    |q * mvfderiv (I := I) f y X - g.inner y v X| ≤
      (q * ι + |q - 1|) * Real.sqrt (g.inner y X X) := by
  have hnorm (Z : TangentSpace I y) : ‖Z‖ = Real.sqrt (g.inner y Z Z) := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq]
  have h1 := hpin X
  have h2 : |g.inner y v X| ≤ Real.sqrt (g.inner y X X) := by
    have h := abs_real_inner_le_norm v X
    rwa [hEnorm.inner_eq, hnorm, hnorm, hv, Real.sqrt_one, one_mul] at h
  have he : q * mvfderiv (I := I) f y X - g.inner y v X =
      q * (mvfderiv (I := I) f y X - g.inner y v X) + (q - 1) * g.inner y v X := by ring
  rw [he]
  calc |q * (mvfderiv (I := I) f y X - g.inner y v X) + (q - 1) * g.inner y v X|
      ≤ |q * (mvfderiv (I := I) f y X - g.inner y v X)| + |(q - 1) * g.inner y v X| :=
        abs_add_le _ _
    _ ≤ q * (ι * Real.sqrt (g.inner y X X)) + |q - 1| * Real.sqrt (g.inner y X X) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 hq)
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = (q * ι + |q - 1|) * Real.sqrt (g.inner y X X) := by ring

private theorem sqrt_le_third {A ι : ℝ} (hι : 0 < ι) (hA : A ≤ ι ^ 2 / 9) :
    Real.sqrt A ≤ ι / 3 := by
  have h := Real.sqrt_le_sqrt (show A ≤ (ι / 3) ^ 2 by linarith)
  rwa [Real.sqrt_sq (by positivity)] at h

universe uE uH u v

/-- **LFR36.2, tangential half (original metric).** For every `ι > 0` there is `σ₀ > 0` and, for
every `Δ > 0`, a `b₀ > 0` such that the following holds for `0 ≤ σ ≤ σ₀`, `θ ≤ σ₀`,
`0 < b < b₀`. Let `α = (u, v)` be an actual normalized `(1, b)`-splitting of a complete smooth
pointed manifold with `sec ≥ -b²` on `B(p, b⁻¹)`, and let `f` be `(1 + σ)`-Lipschitz with the
LFR19 test (LFR19.1) for `L = 100Δ`, `T = 1000Δ`, quality `σ`. If `f` is differentiable at
`y ∈ B(p, 16Δ)` and `a` satisfies `Δ/80 ≤ d(y, a) ≤ 40Δ` and
`(1 - θ) d(y, a) ≤ u(a) - u(y)`, then for EVERY minimizing unit direction `v` from `y` to `a`,
`|df_y(X) - g(v, X)| ≤ ι |X|_g` for all `X`, i.e. `‖∇f(y) - v‖ ≤ ι`. -/
theorem exists_edge_tangential_pinning {ι : ℝ} (hι : 0 < ι) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ Δ : ℝ, 0 < Δ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ σ θ b : ℝ, 0 ≤ σ → σ ≤ σ₀ → θ ≤ σ₀ → 0 < b → b < b₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (p : M) (y₀ : Y)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b),
        (∀ z ∈ Metric.ball p b⁻¹, SectionalBoundedBelowAt g z (-b ^ 2)) →
        ∀ f : M → ℝ, LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ Metric.ball p (100 * Δ), ∀ x' ∈ Metric.ball p (1000 * Δ),
          100 * Δ < dist x x' → ∀ w : TangentSpace I x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x x') = x' →
          |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∀ y ∈ Metric.ball p (16 * Δ), MDifferentiableAt I 𝓘(ℝ, ℝ) f y →
        ∀ a : M, Δ / 80 ≤ dist y a → dist y a ≤ 40 * Δ →
        (1 - θ) * dist y a ≤ (α.toFun a).fst - (α.toFun y).fst →
        ∀ v : TangentSpace I y, g.inner y v v = 1 →
        intrinsicGeodesic g hEnorm y v (dist y a) = a →
        ∀ X : TangentSpace I y,
          |mvfderiv (I := I) f y X - g.inner y v X| ≤ ι * Real.sqrt (g.inner y X X) := by
  set η₀ : ℝ := min 1 (ι ^ 2 / 100) with hη₀
  have hη₀pos : 0 < η₀ := lt_min one_pos (by positivity)
  have hη₀one : η₀ ≤ 1 := min_le_left _ _
  have hη₀ι : η₀ ≤ ι ^ 2 / 100 := min_le_right _ _
  set τ : ℝ := η₀ / 4 with hτ
  have hτpos : 0 < τ := by positivity
  refine ⟨η₀ / 4, by positivity, ?_⟩
  intro Δ hΔ
  obtain ⟨β₁, hβ₁, hA⟩ := exists_scaled_product_anchor_directions (L := Δ / 100) (R := 30000)
    (τ := τ) (by positivity) (by norm_num) hτpos
  refine ⟨min (β₁ / 4) (min (1 / (300 * Δ + 10)) (min (10 * Δ * η₀) (Δ / 100))),
    lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))),
    ?_⟩
  intro σ θ b hσ hσ₀ hθ hb hb₀ E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α hsec
    f hflip htest y hy hfy a ha1 ha2 hD v hv hva X
  have hbβ : b < β₁ / 4 := hb₀.trans_le (min_le_left _ _)
  have hb300 : b < 1 / (300 * Δ + 10) :=
    hb₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbη : b < 10 * Δ * η₀ :=
    hb₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbΔ : b < Δ / 100 :=
    hb₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hbinv : 300 * Δ + 10 ≤ b⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hb]
    exact hb300.le.trans (by rw [one_div])
  have hbone : b ≤ 1 / 10 := by
    have h10 : (10 : ℝ) ≤ b⁻¹ := by linarith
    have h := mul_le_mul_of_nonneg_left h10 hb.le
    rw [mul_inv_cancel₀ hb.ne'] at h
    linarith
  have hd (x z : M) : (riemannianEDist I x z).toReal = dist x z := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hyp : dist y p < 16 * Δ := hy
  have hyball : y ∈ ball p b⁻¹ := mem_ball.mpr (by linarith)
  -- the splitting at `y`
  have hrad := (abs_le.mp (α.radial_error y hyball)).2
  have hfy0 := WithLp.dist_fst_le (α.toFun y) (WithLp.toLp 2 ((0 : ℝ), y₀))
  have hsy0 := WithLp.dist_snd_le (α.toFun y) (WithLp.toLp 2 ((0 : ℝ), y₀))
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sub_zero] at hfy0 hsy0
  -- the long lift `l₊` of `(u(y) + 200Δ, v(y))`
  set T₀ : ℝ := 200 * Δ with hT₀
  have hT₀pos : 0 < T₀ := by positivity
  have hbuffer : |(α.toFun y).fst + T₀| + dist (α.toFun y).snd y₀ + 3 * b < b⁻¹ := by
    have := abs_add_le (α.toFun y).fst T₀
    rw [abs_of_pos hT₀pos] at this
    linarith
  obtain ⟨l, hlp, hlimg, -⟩ := α.exists_product_lift_radius _ _ hbuffer
  set tgt : WithLp 2 (ℝ × Y) := WithLp.toLp 2 ((α.toFun y).fst + T₀, (α.toFun y).snd)
  have hlp' : dist l p < 232 * Δ + 5 * b := by
    have := abs_add_le (α.toFun y).fst T₀
    rw [abs_of_pos hT₀pos] at this
    linarith
  have hlball : l ∈ ball p b⁻¹ := mem_ball.mpr (by linarith)
  have htgt : dist (α.toFun y) tgt = T₀ := by
    rw [WithLp.prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist (α.toFun y).fst ((α.toFun y).fst + T₀) ^ 2 +
      dist (α.toFun y).snd (α.toFun y).snd ^ 2) = T₀
    rw [dist_self, Real.dist_eq, show (α.toFun y).fst - ((α.toFun y).fst + T₀) = -T₀ by ring,
      abs_neg, abs_of_pos hT₀pos, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hT₀pos.le]
  have hyl : |dist y l - T₀| < 3 * b := by
    have h1 := abs_le.mp (α.distortion y hyball l hlball)
    have h2 := dist_triangle (α.toFun y) tgt (α.toFun l)
    have h3 := dist_triangle (α.toFun y) (α.toFun l) tgt
    rw [dist_comm tgt (α.toFun l)] at h2
    rw [abs_lt]; constructor <;> linarith
  have hul : T₀ - 2 * b ≤ (α.toFun l).fst - (α.toFun y).fst := by
    have h := (WithLp.dist_fst_le (α.toFun l) tgt).trans_lt hlimg
    simp only [tgt, WithLp.toLp_fst, Real.dist_eq] at h
    linarith [(abs_lt.mp h).1]
  have hdyl : 0 < dist y l := by linarith [(abs_lt.mp hyl).1]
  set eb : ℝ := 5 * b / T₀ with heb
  have heb0 : 0 ≤ eb := by positivity
  have hebT : eb * T₀ = 5 * b := by rw [heb]; field_simp
  have hebη : eb ≤ η₀ / 4 := by
    rw [heb, div_le_iff₀ hT₀pos, hT₀]
    linarith
  have hslope : 1 - eb ≤ ((α.toFun l).fst - (α.toFun y).fst) / dist y l := by
    rw [le_div_iff₀ hdyl]
    have heb1 : 0 ≤ 1 - eb := by linarith
    have hup : dist y l < T₀ + 3 * b := by linarith [(abs_lt.mp hyl).2]
    linarith [mul_le_mul_of_nonneg_left hup.le heb1, mul_nonneg hb.le heb0]
  -- the LFR19 test toward `l₊` and the Riesz step
  obtain ⟨wP, hwP, hwPl⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm y l
    (by rw [hd]; exact hdyl)
  rw [hd] at hwPl
  have htP := abs_lt.mp (htest y (mem_ball.mpr (by linarith)) l (mem_ball.mpr (by linarith))
    (by linarith [(abs_lt.mp hyl).1]) wP hwP hwPl)
  have hsatP : 1 - (σ + eb) ≤ mvfderiv (I := I) f y wP := by linarith [htP.1]
  have hunit : ∀ w : TangentSpace I y, g.inner y w w = 1 →
      |mvfderiv (I := I) f y w| ≤ 1 + σ := fun w hw =>
    DifferentialGeometry.Geometry.Comparison.abs_mvfderiv_le_of_lipschitzOn g hEnorm
      isOpen_univ (mem_univ y) hfy (fun x _ z _ => by
        have h := hflip.dist_le_mul x z
        rwa [Real.dist_eq, Real.coe_toNNReal _ (by linarith)] at h) w hw
  have hR := abs_sub_le_of_direction_saturation g hEnorm (α := σ) (ε := σ + eb)
    (by linarith) (by linarith) (abs_mvfderiv_le_mul_sqrt_of_unit g hEnorm hunit) hwP hsatP X
  -- the scale-`Δ/100` product anchor at `y`
  have h4 : (4 * b)⁻¹ = b⁻¹ / 4 := by rw [mul_inv]; ring
  obtain ⟨α', hα'⟩ := exists_recentered_product_approx α y (δ := 4 * b) (by linarith)
    (by linarith) (by rw [h4]; linarith)
  have hsec' : ∀ z ∈ ball y (4 * b)⁻¹, SectionalBoundedBelowAt g z (-(4 * b) ^ 2) := by
    intro z hz
    refine SectionalBoundedBelowAt.mono (hsec z ?_) ?_
    · have ht := dist_triangle z y p
      have hz' : dist z y < (4 * b)⁻¹ := hz
      rw [h4] at hz'
      exact mem_ball.mpr (by linarith)
    · linarith [sq_nonneg b, show (4 * b) ^ 2 = 16 * b ^ 2 by ring]
  obtain ⟨A, hAaway, -, -, htestA⟩ := hA (4 * b) (by positivity) (by linarith) E H I M g hEnorm
    Y y (α.toFun y).snd α' hsec'
  have hyA : 0 < dist y A := by
    have h := hAaway
    rw [mem_ball, not_lt] at h
    rw [dist_comm]
    linarith [show 0 < 2 * (Δ / 100) by positivity]
  obtain ⟨U, hU, hUA⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm y A
    (by rw [hd]; exact hyA)
  rw [hd] at hUA
  have hyy : y ∈ ball y (2 * (Δ / 100)) := mem_ball_self (by positivity)
  have hcoord (z : M) : (α'.toFun z).fst - (α'.toFun y).fst =
      (α.toFun z).fst - (α.toFun y).fst := by
    rw [hα', hα']; ring
  have htUa := abs_lt.mp (htestA y hyy a (mem_ball.mpr (by rw [dist_comm]; linarith))
    (by linarith) U v hU hv hUA hva)
  have htUl := abs_lt.mp (htestA y hyy l (mem_ball.mpr (by
      rw [dist_comm]; linarith [(abs_lt.mp hyl).2]))
    (by linarith [(abs_lt.mp hyl).1]) U wP hU hwP hUA hwPl)
  rw [hcoord] at htUa htUl
  have hya : 0 < dist y a := by linarith
  have hratio : 1 - θ ≤ ((α.toFun a).fst - (α.toFun y).fst) / dist y a := by
    rw [le_div_iff₀ hya]; exact hD
  have hUv : 1 - (θ + τ) ≤ g.inner y U v := by linarith [htUa.1]
  have hUw : 1 - (eb + τ) ≤ g.inner y wP U := by
    rw [g.symm]
    linarith [htUl.1]
  have h2 := abs_inner_sub_inner_le_of_inner_ge g hEnorm hwP hU hUw X
  have h3 := abs_inner_sub_inner_le_of_inner_ge g hEnorm hU hv hUv X
  -- the numerical choice
  have hε₁ : σ + eb ≤ η₀ / 2 := by linarith
  have hk1 : Real.sqrt (4 * (σ + eb) + (σ + eb) ^ 2) ≤ ι / 3 := by
    apply sqrt_le_third hι
    have h0 : 0 ≤ σ + eb := by linarith
    have hsq : (σ + eb) ^ 2 ≤ (σ + eb) * (1 / 2) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) h0
    linarith
  have hk2 : Real.sqrt (2 * (eb + τ)) ≤ ι / 3 := sqrt_le_third hι (by linarith)
  have hk3 : Real.sqrt (2 * (θ + τ)) ≤ ι / 3 := sqrt_le_third hι (by linarith)
  have hX := Real.sqrt_nonneg (g.inner y X X)
  calc |mvfderiv (I := I) f y X - g.inner y v X|
      ≤ |mvfderiv (I := I) f y X - g.inner y wP X| + |g.inner y wP X - g.inner y U X| +
          |g.inner y U X - g.inner y v X| := by
        have := abs_sub_le (mvfderiv (I := I) f y X) (g.inner y wP X) (g.inner y v X)
        have := abs_sub_le (g.inner y wP X) (g.inner y U X) (g.inner y v X)
        linarith
    _ ≤ (ι / 3) * Real.sqrt (g.inner y X X) + (ι / 3) * Real.sqrt (g.inner y X X) +
          (ι / 3) * Real.sqrt (g.inner y X X) := by
        gcongr
        · exact hR.trans (mul_le_mul_of_nonneg_right hk1 hX)
        · exact h2.trans (mul_le_mul_of_nonneg_right hk2 hX)
        · exact h3.trans (mul_le_mul_of_nonneg_right hk3 hX)
    _ = ι * Real.sqrt (g.inner y X X) := by ring

end DifferentialGeometry.Geometry.Collapse
