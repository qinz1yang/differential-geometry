import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeChart
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

/-!
# The quantitative rank of an edge chart's collar pair (`(η, F/ρ)`, singular margin)

Lane C14-FAM, register R8 of external review 48 (design `build-logs/resume/design-C14-FAM.md` (e)):
TCP04 / EDP03 need a joint singular margin `> .9` of the SAME pair `J = (η_j, P/ρ)` (blueprint 207B,
B:6938–6945: "least singular value greater than .95 in the point's own scale … leaving the asserted
.9"; PBR01 PR26–28, B:10233). It is a LEMMA from the collar clause `EdgeChart.collar` (LFR38: the
pair is adapted of quality `γ` to an actual `β`-Kleiner–Lott plane map, with long derivative tests),
by the mechanism of TCP01's circle lower bound (`circleAdapted_gram_lower_KA2`): a coverage point of
the plane map at distance `1000` in the direction `ξ`, a minimizing geodesic toward it, the test.

* `EdgeChart.collar_lower_FAM`: at a collar point `x` (`|η(x)| ≤ 10Δ`, `Δ/10 ≤ F(x)/ρ(x) ≤ 10Δ`) and
  every `y ∈ B(x, 100ρ(x))`, for every unit `ξ ∈ ℝ²` some `g`-unit `W` at `y` has
  `‖ρ(x) DJ(y) W − ξ‖ < γ + β` (for `0 < γ ≤ 1/100`, `β ≤ 10⁻⁵`).
* `EdgeChart.collar_singular_margin_FAM`: hence `⟨ρ(x) DJ(y) W, ξ⟩ > 1 − (γ + β) > 9/10`, i.e. the
  least singular value of `ρ(x) DJ(y)` exceeds `9/10` (the adjoint has `‖(ρ(x)DJ(y))* ξ‖ > 9/10`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **The collar lower bound** (R8): at a collar point `x` of an edge chart and at every
`y ∈ B(x, 100ρ(x))`, every unit `ξ ∈ ℝ²` is reached within `γ + β` by `ρ(x) DJ(y) W` for a `g`-unit
`W`, `J = (η, F/ρ)`. -/
theorem EdgeChart.collar_lower_FAM {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g}
    {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}
    (c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 100)
    (hβ1 : β ≤ 1 / 100000) {x : M} (hx : x ∈ ball c.center (100 * Δ)) (hη : |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F x / ρ x) (hF2 : F x / ρ x ≤ 10 * Δ) {y : M} (hy : y ∈ ball x (100 * ρ x))
    (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ‖ξ‖ = 1) :
    ∃ W : TangentSpace I y, g.inner y W W = 1 ∧
      ‖ρ x • mvfderiv (I := I) (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W -
        ξ‖ < γ + β := by
  obtain ⟨hq, ⟨Φ, hΦ⟩, -, -, -, -, -, htest⟩ := c.collar x hx hη hF1 hF2
  have hρx : 0 < ρ x := lt_of_lt_of_le (by norm_num) hq.1
  -- the plane map `f = Φ` of the rescaled metric `ρ(x)⁻¹ d`, its facts read off once
  let q₀ : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))
  let f : M → WithLp 2 (ℝ × ℝ) := @KleinerLottApprox.toFun M (WithLp 2 (ℝ × ℝ))
    (mM.rescale (ρ x)⁻¹ (inv_pos.mpr hρx)) _ x q₀ β Φ
  have hβ : 0 < β := @KleinerLottApprox.error_pos M (WithLp 2 (ℝ × ℝ))
    (mM.rescale (ρ x)⁻¹ (inv_pos.mpr hρx)) _ x q₀ β Φ
  have hf0 : f x = q₀ := @KleinerLottApprox.basepoint M (WithLp 2 (ℝ × ℝ))
    (mM.rescale (ρ x)⁻¹ (inv_pos.mpr hρx)) _ x q₀ β Φ
  have hfd : ∀ a, (ρ x)⁻¹ * dist a x < β⁻¹ → ∀ a', (ρ x)⁻¹ * dist a' x < β⁻¹ →
      |dist (f a) (f a') - (ρ x)⁻¹ * dist a a'| ≤ β := fun a ha a' ha' =>
    @KleinerLottApprox.distortion M (WithLp 2 (ℝ × ℝ)) (mM.rescale (ρ x)⁻¹ (inv_pos.mpr hρx)) _ x
      q₀ β Φ a ha a' ha'
  have hfc : ∀ v, dist v q₀ < β⁻¹ - β → ∃ a, (ρ x)⁻¹ * dist a x < β⁻¹ ∧ dist v (f a) < 2 * β := by
    intro v hv
    obtain ⟨a, ha, h⟩ := @KleinerLottApprox.coverage_witness M (WithLp 2 (ℝ × ℝ))
      (mM.rescale (ρ x)⁻¹ (inv_pos.mpr hρx)) _ x q₀ β Φ v hv
    exact ⟨a, ha, h⟩
  have hβinv : 100000 ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hβ]
    linarith
  have hyx' : dist y x < 100 * ρ x := mem_ball.mp hy
  have hyx : (ρ x)⁻¹ * dist y x < 100 := by
    rw [inv_mul_lt_iff₀ hρx]
    linarith
  have hyB : (ρ x)⁻¹ * dist y x < β⁻¹ := by linarith
  have hxB : (ρ x)⁻¹ * dist x x < β⁻¹ := by
    rw [dist_self, mul_zero]
    positivity
  set t : ℝ := 1000 with ht
  set u : WithLp 2 (ℝ × ℝ) := planeReferenceIsometry.symm ξ with hu
  have hun : ‖u‖ = 1 := by rw [hu, LinearIsometryEquiv.norm_map, hξ]
  set ystar : WithLp 2 (ℝ × ℝ) := f y + t • u with hystar
  have hyst : dist ystar (f y) = t := by
    rw [hystar, dist_eq_norm, add_sub_cancel_left, norm_smul, hun, Real.norm_eq_abs,
      abs_of_pos (by norm_num), mul_one]
  have hrad := hfd y hyB x hxB
  rw [hf0] at hrad
  have hy0 : dist ystar q₀ < β⁻¹ - β := by
    have h2 := dist_triangle ystar (f y) q₀
    have h4 := (abs_le.mp hrad).2
    linarith
  obtain ⟨z, hzB, hzd⟩ := hfc ystar hy0
  have hdist := hfd y hyB z hzB
  have hdsx : |dist (f y) (f z) - t| ≤ 2 * β := by
    have e1 := dist_triangle (f y) ystar (f z)
    have e2 := dist_triangle ystar (f z) (f y)
    have e3 := dist_comm ystar (f y)
    have e4 := dist_comm (f z) (f y)
    rw [abs_le]
    constructor <;> linarith
  set D : ℝ := dist y z / ρ x with hD
  have hDeq : (ρ x)⁻¹ * dist y z = D := by rw [hD, div_eq_inv_mul]
  rw [hDeq] at hdist
  have hdD : |D - t| ≤ 3 * β := by
    rw [abs_le] at hdist hdsx ⊢
    constructor <;> linarith [hdist.1, hdist.2, hdsx.1, hdsx.2]
  have hDpos : 5 < D := by
    have := (abs_le.mp hdD).1
    linarith
  have hyz : ρ x < dist y z := by
    have h : 5 * ρ x < dist y z := by
      have := hDpos
      rw [hD, lt_div_iff₀ hρx] at this
      exact this
    linarith
  have hzx : z ∈ ball x (100 * ρ x / γ) := by
    rw [mem_ball]
    have hxz := dist_triangle z y x
    have hDu : D ≤ t + 3 * β := by linarith [(abs_le.mp hdD).2]
    have hzy : dist z y ≤ (t + 3 * β) * ρ x := by
      rw [dist_comm]
      have := hDu
      rw [hD, div_le_iff₀ hρx] at this
      exact this
    have hγinv : 10000 ≤ 100 / γ := by
      rw [le_div_iff₀ hγ]
      linarith
    have hfinal : (t + 3 * β) * ρ x + 100 * ρ x < 100 * ρ x / γ := by
      rw [show 100 * ρ x / γ = (100 / γ) * ρ x by ring]
      nlinarith
    linarith
  have hfin : riemannianEDist I y z ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨v, hv, hlen⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm y z
    hfin
  have hdlen : (riemannianEDist I y z).toReal = dist y z := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rw [hdlen] at hlen
  have hdpos : 0 < dist y z := by linarith
  let W : TangentSpace I y := (dist y z)⁻¹ • v
  have hvpos : 0 < g.inner y v v := Real.sqrt_pos.mp (hlen ▸ hdpos)
  have hvv : g.inner y v v = dist y z ^ 2 := by
    rw [← hlen, Real.sq_sqrt hvpos.le]
  have hW : g.inner y W W = 1 := by
    rw [gInner_smul_self, hvv]
    field_simp
  have hgeo : intrinsicGeodesic g hEnorm y W (dist y z) = z := by
    rw [← intrinsicGeodesic_smul g hEnorm y W (dist y z)]
    have hdw : dist y z • W = v := by
      change dist y z • ((dist y z)⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    rw [hdw]
    exact hv
  have hT : ‖ρ x • mvfderiv (I := I) (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W -
      D⁻¹ • (planeReferenceIsometry (f z) - planeReferenceIsometry (f y))‖ < γ := by
    have h := htest y hy z hzx hyz W hW hgeo
    rwa [← hΦ z, ← hΦ y] at h
  refine ⟨W, hW, ?_⟩
  set e : WithLp 2 (ℝ × ℝ) := f z - ystar with he
  have hen : ‖e‖ < 2 * β := by
    rw [he, ← dist_eq_norm, dist_comm]
    exact hzd
  have hsplit : planeReferenceIsometry (f z) - planeReferenceIsometry (f y) =
      t • ξ + planeReferenceIsometry e := by
    rw [← map_sub, he]
    rw [hystar]
    have hξu : planeReferenceIsometry u = ξ := by
      rw [hu, LinearIsometryEquiv.apply_symm_apply]
    rw [show f z - f y = t • u + (f z - (f y + t • u)) by abel,
      map_add, map_smul, hξu]
  have hDne : D ≠ 0 := by linarith
  have hdec : D⁻¹ • (planeReferenceIsometry (f z) - planeReferenceIsometry (f y)) -
      ξ = (D⁻¹ * (t - D)) • ξ + D⁻¹ • planeReferenceIsometry e := by
    rw [hsplit, smul_add, smul_smul, mul_sub, inv_mul_cancel₀ hDne, sub_smul, one_smul]
    abel
  have hkey : ‖D⁻¹ • (planeReferenceIsometry (f z) - planeReferenceIsometry (f y)) -
      ξ‖ ≤ 5 * β / D := by
    rw [hdec]
    refine (norm_add_le _ _).trans ?_
    have hDp : 0 < D := by linarith
    rw [norm_smul, norm_smul, hξ, mul_one, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hDp]
    have h3 : |t - D| ≤ 3 * β := by
      rw [abs_sub_comm]
      exact hdD
    rw [div_eq_mul_inv]
    have hi : 0 < D⁻¹ := inv_pos.mpr hDp
    nlinarith [norm_nonneg e]
  have hsmall : 5 * β / D ≤ β := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hDpos.le hβ.le
    linarith
  calc ‖ρ x • mvfderiv (I := I) (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W -
        ξ‖
      ≤ ‖ρ x • mvfderiv (I := I) (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W -
          D⁻¹ • (planeReferenceIsometry (f z) - planeReferenceIsometry (f y))‖ +
          ‖D⁻¹ • (planeReferenceIsometry (f z) - planeReferenceIsometry (f y)) -
            ξ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < γ + β := add_lt_add_of_lt_of_le hT (hkey.trans hsmall)

/-- **The joint singular margin of the collar pair** (R8; TCP04, EDP03): at a collar point `x` and
every `y ∈ B(x, 100ρ(x))`, every unit `ξ ∈ ℝ²` has a `g`-unit `W` with
`⟨ρ(x) DJ(y) W, ξ⟩ > 1 − (γ + β) > 9/10`; so the least singular value of `ρ(x) DJ(y)` exceeds
`9/10`. -/
theorem EdgeChart.collar_singular_margin_FAM {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm g} {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}
    (c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 100)
    (hβ1 : β ≤ 1 / 100000) {x : M} (hx : x ∈ ball c.center (100 * Δ)) (hη : |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F x / ρ x) (hF2 : F x / ρ x ≤ 10 * Δ) {y : M} (hy : y ∈ ball x (100 * ρ x))
    (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ‖ξ‖ = 1) :
    ∃ W : TangentSpace I y, g.inner y W W = 1 ∧
      1 - (γ + β) < inner ℝ (ρ x • mvfderiv (I := I)
        (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W) ξ ∧
      9 / 10 < inner ℝ (ρ x • mvfderiv (I := I)
        (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W) ξ := by
  obtain ⟨W, hW, hlt⟩ := c.collar_lower_FAM hγ hγ1 hβ1 hx hη hF1 hF2 hy ξ hξ
  set uJ := ρ x • mvfderiv (I := I) (edgeReferenceCoordinates ![c.coord, fun z => F z / ρ z]) y W
    with huJ
  have h1 : inner ℝ uJ ξ = inner ℝ (uJ - ξ) ξ + inner ℝ ξ ξ := by
    rw [inner_sub_left]
    ring
  have h2 : inner ℝ ξ ξ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hξ]
    norm_num
  have h3 : |inner ℝ (uJ - ξ) ξ| ≤ ‖uJ - ξ‖ := by
    have := abs_real_inner_le_norm (uJ - ξ) ξ
    rwa [hξ, mul_one] at this
  have hlow : 1 - (γ + β) < inner ℝ uJ ξ := by
    rw [h1, h2]
    linarith [(abs_le.mp h3).1]
  refine ⟨W, hW, hlow, ?_⟩
  linarith

end DifferentialGeometry.Geometry.Collapse
