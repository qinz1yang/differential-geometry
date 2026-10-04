import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBandEnclosure
import DifferentialGeometry.Geometry.Operator.Scaling
set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem edgeVertical_anchor {A : Set M} {p x a : M} {Q : M → WithLp 2 (ℝ × ℝ)}
    {Δ τ : ℝ} (hΔpos : 0 < Δ) (hτsmall : τ ≤ 1)
    (hQp : Q p = 0)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hheight : ∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd) (hpA : p ∈ A)
    (hborder : ∀ z ∈ A ∩ ball p (190 * Δ), (Q z).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ z ∈ A ∩ ball p (190 * Δ), dist (Q z) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (ha : a ∈ ball p (20 * Δ))
    (hanchor : dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ) :
    |infDist x A - (Q x).snd| ≤ 2 * τ * Δ ∧
      |infDist a A - (Q a).snd| ≤ 2 * τ * Δ ∧
      |(Q a).snd - ((Q x).snd + Δ / 40)| ≤ τ * Δ ∧
      |dist x a - Δ / 40| ≤ 2 * τ * Δ := by
  have hxp : dist x p < 15 * Δ := hx
  have hap : dist a p < 20 * Δ := ha
  have hx70 : x ∈ ball p (70 * Δ) := by change dist x p < _; linarith only [hxp, hΔpos]
  have ha70 : a ∈ ball p (70 * Δ) := by change dist a p < _; linarith only [hap, hΔpos]
  have hbx := coarseBorder_abs_infDist_sub_height_le hΔpos hτsmall hQp hdist hheight hpA
    hborder hbordercover hx70
  have hba := coarseBorder_abs_infDist_sub_height_le hΔpos hτsmall hQp hdist hheight hpA
    hborder hbordercover ha70
  have hanchorH : |(Q a).snd - ((Q x).snd + Δ / 40)| ≤ τ * Δ := by
    have hh := WithLp.dist_snd_le (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40))
    have hh' : |(Q a).snd - ((Q x).snd + Δ / 40)| ≤
        dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) := hh
    exact hh'.trans hanchor
  have hxa : |dist x a - Δ / 40| ≤ 2 * τ * Δ := by
    have hdist' := hdist x (ball_subset_ball (by linarith) hx)
      a (ball_subset_ball (by linarith) ha)
    have hqdist : |dist (Q x) (Q a) - Δ / 40| ≤ τ * Δ := by
      have hh := abs_dist_sub_le (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) (Q x)
      rw [dist_comm (Q a) (Q x), dist_comm (Q x + _) (Q x)] at hh
      have he : dist (Q x) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) = Δ / 40 := by
        rw [dist_eq_norm]
        have he : Q x - (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) =
            -WithLp.toLp 2 ((0 : ℝ), Δ / 40) := by abel
        rw [he, norm_neg, WithLp.prod_norm_eq_of_L2]
        change Real.sqrt (‖(0 : ℝ)‖ ^ 2 + ‖Δ / 40‖ ^ 2) = Δ / 40
        simp only [norm_zero]
        rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Δ / 40)]
        norm_num only [zero_pow, zero_add]
        exact Real.sqrt_sq (by positivity : 0 ≤ Δ / 40)
      rw [he] at hh
      exact hh.trans hanchor
    have he : dist x a - Δ / 40 =
          (dist x a - dist (Q x) (Q a)) + (dist (Q x) (Q a) - Δ / 40) := by ring
    rw [he]
    have hh := abs_add_le (dist x a - dist (Q x) (Q a)) (dist (Q x) (Q a) - Δ / 40)
    rw [abs_sub_comm] at hdist'
    linarith only [hh, hqdist, hdist']
  exact ⟨by simpa only [mul_assoc] using hbx,
    by simpa only [mul_assoc] using hba, hanchorH, hxa⟩

private theorem edgeVertical_hinge (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {A : Set M} {p y a : M} {Δ τ κ : ℝ}
    (hΔ : 1000000 ≤ Δ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 10000)
    (hypdist : dist y p < 16 * Δ) (hyA : Δ / 25 ≤ infDist y A)
    (hyA' : infDist y A ≤ 21 / 2 * Δ) (hℓlo : Δ / 80 ≤ dist y a)
    (hℓhi : dist y a ≤ Δ / 40 + 303 + 2 * τ * Δ)
    (hexcess : infDist y A + dist y a - infDist a A ≤ 1200 + 9 * τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    {v w : TangentSpace I y} (hv : v ∈ minimizingDirectionsTo g hEnorm A y)
    (hw : w ∈ minimizingDirectionsTo g hEnorm {a} y) :
    ‖v + w‖ ≤ Real.sqrt (504000 / Δ + 3780 * τ) := by
  have hΔpos : 0 < Δ := by linarith only [hΔ]
  have hAy : 0 < infDist y A := by linarith only [hyA, hΔpos]
  have hℓ : 0 < dist y a := by linarith only [hℓlo, hΔpos]
  let k : ℝ := 1 / (100 * Δ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hκk : κ ≤ k := by dsimp [k]; rw [le_div_iff₀ (by positivity)]; nlinarith
  have hsec' : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-k ^ 2) :=
    fun z hz => SectionalBoundedBelowAt.mono (hsec z hz) (by nlinarith)
  have hR : dist y p + 2 * infDist y A + dist y a < 1000 * Δ := by
    have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
    linarith only [hypdist, hΔpos, hΔ, hτΔ, hyA', hℓhi]
  have hw' : w ∈ inwardMinimizingDirections g hEnorm a y := by
    refine ⟨hw.1, ?_⟩
    simpa only [Metric.infDist_singleton, Set.mem_singleton_iff, dist_comm] using hw.2
  have hhinge := one_add_inner_le_of_nearest_direction g hEnorm hk hsec' hAy hℓ hR hv hw'
  have hcosh : Real.cosh (k * (infDist y A + dist y a)) ≤ 2 := by
    have hnon : 0 ≤ k * (infDist y A + dist y a) := by positivity
    have hle : k * (infDist y A + dist y a) ≤ 1 := by
      dsimp [k]
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
      linarith
    have hh := Real.cosh_sub_one_le_sq hnon hle
    nlinarith
  have hexcess0 : 0 ≤ infDist y A + dist y a - infDist a A := by
    have hh := infDist_le_infDist_add_dist (x := a) (y := y) (s := A)
    rw [dist_comm a y] at hh
    linarith
  have hratio : (infDist y A + dist y a) / (infDist y A * dist y a) ≤ 105 / Δ := by
    rw [div_le_iff₀ (mul_pos hAy hℓ), div_mul_eq_mul_div, le_div_iff₀ hΔpos]
    have ha1 : Δ ≤ 25 * infDist y A := by linarith only [hyA]
    have hl1 : Δ ≤ 80 * dist y a := by linarith only [hℓlo]
    have h1 := mul_le_mul_of_nonneg_right ha1 (dist_nonneg (x := y) (y := a))
    have h2 := mul_le_mul_of_nonneg_right hl1 (infDist_nonneg (x := y) (s := A))
    nlinarith only [h1, h2]
  have hpair : g.inner y (v + w) (v + w) ≤ 504000 / Δ + 3780 * τ := by
    have he : g.inner y (v + w) (v + w) = 2 * (1 + g.inner y v w) := by
      simp only [map_add, add_apply]
      rw [hv.1, hw.1, g.symm y w v]
      ring
    rw [he]
    have hb : Real.cosh (k * (infDist y A + dist y a)) *
        (infDist y A + dist y a - infDist a A) * (infDist y A + dist y a) /
        (infDist y A * dist y a) ≤ 2 * (1200 + 9 * τ * Δ) * (105 / Δ) := by
      rw [mul_div_assoc]
      exact mul_le_mul (mul_le_mul hcosh hexcess (by positivity) (by positivity)) hratio
        (by positivity) (by positivity)
    have he' : 2 * (2 * (1200 + 9 * τ * Δ) * (105 / Δ)) = 504000 / Δ + 3780 * τ := by
      field_simp
      ring
    nlinarith only [hhinge, hb, he']
  rw [norm_tangent_eq_sqrt_gInner hEnorm]
  exact Real.sqrt_le_sqrt hpair

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompleteSpace M] in
theorem edgeQuotient_gradient_error (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {A : Set M} {p y : M} {F ρ : M → ℝ} {Δ ε μ : ℝ} {Λ : ℝ≥0}
    (hΔ : 0 < Δ) (hε : 0 ≤ ε) (hε1 : ε < 1 / 100) (hμ1 : μ < 1 / 100)
    (hFL : LipschitzWith (Real.toNNReal (1 + ε)) F)
    (hval : |F y - infDist y A| ≤ μ * Δ)
    (hFs : MDifferentiableAt I 𝓘(ℝ, ℝ) F y)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ y) (hlam : 100 * Δ * Λ ≤ 1 / 100)
    (hyp : dist y p ≤ 20 * Δ) (hyA : infDist y A ≤ 21 / 2 * Δ) :
    ‖gradFun g (fun z => F z / ρ z) y - gradFun g F y‖ ≤ 100 * Δ * Λ
 := by
  have hFg := sqrt_gInner_gradFun_le_of_lipschitzWith g hEnorm hFL hFs
  rw [Real.coe_toNNReal _ (by linarith)] at hFg
  have hρg := sqrt_gInner_gradFun_le_of_lipschitzWith g hEnorm hρ hρs
  have hρclose : |ρ y - 1| ≤ 20 * Δ * Λ := by
    have hh := hρ.dist_le_mul y p
    rw [Real.dist_eq, hρp] at hh
    nlinarith [mul_nonneg hΔ.le Λ.coe_nonneg]
  have hFb : |F y| ≤ 1061 / 100 * Δ := by
    have hh := abs_le.mp hval
    rw [abs_le]
    constructor <;> nlinarith [infDist_nonneg (x := y) (s := A)]
  have hquot := sqrt_gInner_gradFun_div_sub_le g hEnorm hFs hρs hFg hρg hρclose
    (by nlinarith) hFb
  rw [norm_tangent_eq_sqrt_gInner hEnorm]
  refine hquot.trans ?_
  have hΔΛ : 0 ≤ Δ * Λ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hε1.le hΔΛ]

theorem edgeBand_vertical_gradient (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {A : Set M} (hA : IsClosed A) {p x a : M} {Q : M → WithLp 2 (ℝ × ℝ)}
    {F ρ : M → ℝ} {Δ τ κ ε μ ι : ℝ} {Λ : ℝ≥0}
    (hΔ : 1000000 ≤ Δ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 10000)
    (hQp : Q p = 0)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hheight : ∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd)
    (hpA : p ∈ A) (hborder : ∀ z ∈ A ∩ ball p (190 * Δ), (Q z).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ z ∈ A ∩ ball p (190 * Δ), dist (Q z) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hxA : 9 / 100 * Δ < infDist x A)
    (hxA' : infDist x A < 101 / 10 * Δ)
    (ha : a ∈ ball p (20 * Δ))
    (hanchor : dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 ≤ ε) (hε1 : ε < 1 / 100) (hμ1 : μ < 1 / 100)
    (hFL : LipschitzWith (Real.toNNReal (1 + ε)) F)
    (hval : ∀ y, |F y - infDist y A| ≤ μ * Δ)
    (hFs : ∀ y ∈ closedBall p (20 * Δ) ∩
      {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
        MDifferentiableAt I 𝓘(ℝ, ℝ) F y)
    (hFgrad : ∀ y ∈ closedBall p (20 * Δ) ∩
      {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
      ∀ v ∈ minimizingDirectionsTo g hEnorm A y,
        Real.sqrt (g.inner y (gradFun g F y + v) (gradFun g F y + v)) < ε)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hlam : 100 * Δ * Λ ≤ 1 / 100)
    (hbudget : 2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < ι) :
    ∀ y ∈ ball x (300 * ρ x), ∀ w ∈ minimizingDirectionsTo g hEnorm {a} y,
      Real.sqrt (g.inner y (ρ x • gradFun g (fun z => F z / ρ z) y - w)
        (ρ x • gradFun g (fun z => F z / ρ z) y - w)) < ι := by
  have hΔpos : 0 < Δ := by linarith
  have hτsmall : τ ≤ 1 := by linarith
  have hxp : dist x p < 15 * Δ := hx
  have hap : dist a p < 20 * Δ := ha
  obtain ⟨hbx, hba, hanchorH, hxa⟩ := edgeVertical_anchor hΔpos hτsmall hQp hdist hheight
    hpA hborder hbordercover hx ha hanchor
  have hq : |ρ x - 1| ≤ 20 * Δ * Λ := by
    have hh := hρ.dist_le_mul x p
    rw [Real.dist_eq, hρp] at hh
    nlinarith only [hh, hxp, mul_nonneg hΔpos.le Λ.coe_nonneg]
  have hqpos : 0 < ρ x := by linarith [(abs_le.mp hq).1]
  have hq1 : ρ x ≤ 101 / 100 := by linarith [(abs_le.mp hq).2]
  intro y hy w hw
  have hxy : dist x y < 303 := by
    have hh : dist y x < 300 * ρ x := hy
    rw [dist_comm] at hh
    linarith
  obtain ⟨hyp, hyA, hyA'⟩ := edgeBand_buffer_subset hΔ hx hxA hxA' hxy
  have hypdist : dist y p < 16 * Δ := hyp
  have hyC : y ∈ closedBall p (20 * Δ) ∩
      {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} := by
    refine ⟨?_, hyA, hyA'⟩
    change dist y p ≤ 20 * Δ
    linarith only [hypdist, hΔpos]
  have hℓlo : Δ / 80 ≤ dist y a := by
    have hh := dist_triangle x y a
    have hh' := (abs_le.mp hxa).1
    linarith only [hh, hh', hxy, hΔ, hτ1, mul_le_mul_of_nonneg_right hτ1 hΔpos.le]
  have hℓhi : dist y a ≤ Δ / 40 + 303 + 2 * τ * Δ := by
    have hh := dist_triangle y x a
    rw [dist_comm y x] at hh
    linarith [(abs_le.mp hxa).2]
  have hexcess : infDist y A + dist y a - infDist a A ≤ 1200 + 9 * τ * Δ := by
    have hh := infDist_le_infDist_add_dist (x := y) (y := x) (s := A)
    rw [dist_comm y x] at hh
    linarith only [hh, hxy, hℓhi, (abs_le.mp hbx).2, (abs_le.mp hba).1,
      (abs_le.mp hanchorH).1, mul_nonneg hτ hΔpos.le]
  have hAy : 0 < infDist y A := by linarith
  have hℓ : 0 < dist y a := by linarith
  let : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  obtain ⟨z, hzA, hzdist⟩ := hA.exists_infDist_eq_dist ⟨p, hpA⟩ y
  obtain ⟨v, hv1, hvend⟩ := soul_unit_minimizing_initial g hEnorm y z (by rw [← hzdist]; exact hAy)
  have hv : v ∈ minimizingDirectionsTo g hEnorm A y := by
    refine ⟨hv1, ?_⟩
    rw [hzdist, hvend]
    exact hzA
  have hpairN := edgeVertical_hinge g hEnorm hΔ hτ hτ1 hypdist hyA hyA' hℓlo hℓhi
    hexcess hκ hκΔ hsec hv hw
  have hFdiff := hFs y hyC
  have hρdiff := (hρs.contMDiffAt (x := y)).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hquot' := edgeQuotient_gradient_error g hEnorm hΔpos hε hε1 hμ1 hFL
    (hval y) hFdiff hρ hρp hρdiff hlam (by linarith only [hypdist, hΔpos]) hyA'
  have hFG : ‖gradFun g F y + v‖ < ε := by
    rw [norm_tangent_eq_sqrt_gInner hEnorm]
    exact hFgrad y hyC v hv
  have hnV : ‖v‖ = 1 := by rw [norm_tangent_eq_sqrt_gInner hEnorm, hv1, Real.sqrt_one]
  have he : ρ x • gradFun g (fun z => F z / ρ z) y - w =
      ρ x • (gradFun g (fun z => F z / ρ z) y - gradFun g F y) +
      ρ x • (gradFun g F y + v) + (1 - ρ x) • v - (v + w) := by module
  rw [← norm_tangent_eq_sqrt_gInner hEnorm, he]
  have hnorm := norm_sub_le
    (ρ x • (gradFun g (fun z => F z / ρ z) y - gradFun g F y) +
      ρ x • (gradFun g F y + v) + (1 - ρ x) • v) (v + w)
  have hnorm' := norm_add_le
    (ρ x • (gradFun g (fun z => F z / ρ z) y - gradFun g F y) +
      ρ x • (gradFun g F y + v)) ((1 - ρ x) • v)
  have hnorm'' := norm_add_le
    (ρ x • (gradFun g (fun z => F z / ρ z) y - gradFun g F y))
    (ρ x • (gradFun g F y + v))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hqpos, hnV, mul_one,
    abs_sub_comm 1 (ρ x)] at hnorm hnorm' hnorm''
  have h1 := mul_le_mul_of_nonneg_left hquot' hqpos.le
  have h2 := mul_lt_mul_of_pos_left hFG hqpos
  have h3 := mul_le_mul_of_nonneg_right hq1 (show 0 ≤ 100 * Δ * Λ by positivity)
  have h4 := mul_le_mul_of_nonneg_right hq1 hε
  have hΔΛ : 0 ≤ Δ * Λ := by positivity
  linarith only [hnorm, hnorm', hnorm'', h1, h2, h3, h4, hq, hpairN, hbudget, hε, hΔΛ]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- Exact conversion to the row's metric g_x=q^-2g and its q-scaled unit direction. -/
theorem edgeRescaled_gradient_norm (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (y : M) (q : ℝ) (hq : 0 < q) (w : TangentSpace I y) :
    let gx := DifferentialGeometry.scaleMetric (q⁻¹ ^ 2) (by positivity) g
    Real.sqrt (gx.inner y (gradFun gx f y - q • w) (gradFun gx f y - q • w)) =
      Real.sqrt (g.inner y (q • gradFun g f y - w) (q • gradFun g f y - w))
 := by
  dsimp only
  change Real.sqrt ((DifferentialGeometry.scaleMetric (q⁻¹ ^ 2) _ g).inner y
    (gradientFun (DifferentialGeometry.scaleMetric (q⁻¹ ^ 2) _ g) f y - q • w)
    (gradientFun (DifferentialGeometry.scaleMetric (q⁻¹ ^ 2) _ g) f y - q • w)) =
    Real.sqrt (g.inner y (q • gradientFun g f y - w) (q • gradientFun g f y - w))
  rw [gradientFun_scale]
  simp only [DifferentialGeometry.scaleMetric_inner, map_sub, sub_apply, map_smul,
    smul_apply, smul_eq_mul]
  congr 1
  field_simp

end DifferentialGeometry.Geometry.Collapse
