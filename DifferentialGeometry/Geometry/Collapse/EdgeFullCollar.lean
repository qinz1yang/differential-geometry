import DifferentialGeometry.Geometry.Collapse.EdgeReferenceChartUniform
import DifferentialGeometry.Geometry.Collapse.EdgeTangentialPinning

/-!
# LFR38: the original edge pair has the full adapted collar (single strong-edge centre)

Blueprint 207A, LFR38 (`thm:collapse-full-edge-collar-packet`, A:28243–28320), first paragraph and
proof, at a centre normalized by `ρ(p) = 1`. The pieces are the accepted rows:

* LFR35 in the row's order (`exists_edge_reference_chart_parameters_uniform`, this campaign's G1 on
  Codex X90): actual comparison map `Φ_x`, the SAME anchors, smooth reference chart `χ_x`;
* LFR36.3 enclosure (`edgeBand_mem_ball_and_infDist_window`, `edgeBand_buffer_subset`);
* LFR36.2 tangential half (`exists_edge_tangential_pinning`, F7-FOLLOW) and vertical half
  (`edgeBand_vertical_gradient`, Codex X91);
* LFR37 in the point's own scale `d_x = d/q`, `q = ρ(x)`: `rankTwo_adapted_of_scaled_perturbation`
  below (Codex X91's `rankTwo_adapted_of_buffered_perturbation` is the case `q = 1`).

Main theorem `exists_edge_full_collar_parameters`: ordered parameters `γ, β₂ → Δ → (σ) → τ → κ, b`
with the explicit LFR34/LFR36 budget `2ε + 300ΔΛ + √(504000/Δ + 3780τ) < γ/1000`; for any
LFR34-type smoothing `F` (hypotheses = LFR34's output clauses) and ANY LFR19-type coordinate `f`
(Lipschitz, value and test clauses for the actual `(1, b)`-splitting `α` whose first coordinate is the
chart's), at EVERY point `x` of the band (LFR36.1) the ORIGINAL pair `J = (f, F/ρ)` has, on
`B_{d_x}(x, 100) = B(x, 100q)`, rank two and all scale-`100` adapted conditions of quality `γ`
relative to the actual KL `β₂`-map `Φ_x` (the plane comparison map in `d/q`). The derivative test
holds for every tested length `d(y, z) > q` (the row asks `> 100q`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open scoped Manifold ContDiff Topology NNReal RealInnerProductSpace
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison
open GC.MetricGeometry
open ContinuousLinearMap

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-! ### Anchor targets and the tangential anchor slope -/

theorem planeReferenceIsometry_symm_single_zero (c : ℝ) :
    planeReferenceIsometry.symm (EuclideanSpace.single 0 c) = WithLp.toLp 2 (c, (0 : ℝ)) := by
  apply planeReferenceIsometry.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext j
  fin_cases j <;> simp

theorem planeReferenceIsometry_symm_single_one (c : ℝ) :
    planeReferenceIsometry.symm (EuclideanSpace.single 1 c) = WithLp.toLp 2 ((0 : ℝ), c) := by
  apply planeReferenceIsometry.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext j
  fin_cases j <;> simp

/-- The positive tangential anchor `a ≈ Q(x) + (Δ/40, 0)` is seen from every point of the buffer
`B(x, 303)` at distance in `[Δ/80, 40Δ]` with first-coordinate slope at least `1 - θ`. -/
theorem edgeTangentialAnchor_slope {X : Type*} [MetricSpace X] {Q : X → WithLp 2 (ℝ × ℝ)}
    {p x y a : X} {Δ τ θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hΔθ : 40400 ≤ θ * Δ)
    (hτθ : τ ≤ θ / 400)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (ha : a ∈ ball p (20 * Δ)) (hxy : dist x y < 303)
    (hanchor : dist (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) ≤ τ * Δ) :
    Δ / 80 ≤ dist y a ∧ dist y a ≤ 40 * Δ ∧
      (1 - θ) * dist y a ≤ (Q a).fst - (Q y).fst := by
  have hΔpos : 0 < Δ := by
    by_contra h
    have h' : Δ ≤ 0 := le_of_not_gt h
    nlinarith
  have hΔbig : 40400 ≤ Δ := by nlinarith
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hτΔ : τ * Δ ≤ θ * Δ / 400 := by nlinarith
  have hxp : dist x p < 15 * Δ := hx
  have hap : dist a p < 20 * Δ := ha
  have hx200 : x ∈ ball p (200 * Δ) := (show dist x p < 200 * Δ by linarith)
  have ha200 : a ∈ ball p (200 * Δ) := (show dist a p < 200 * Δ by linarith)
  have hy200 : y ∈ ball p (200 * Δ) := by
    have h := dist_triangle y x p
    rw [dist_comm y x] at h
    change dist y p < 200 * Δ
    linarith
  -- the anchor in the chart
  have hfst : |(Q a).fst - ((Q x).fst + Δ / 40)| ≤ τ * Δ := by
    have hh := WithLp.dist_fst_le (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ)))
    have hh' : |(Q a).fst - ((Q x).fst + Δ / 40)| ≤
        dist (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) := hh
    exact hh'.trans hanchor
  have hqdist : |dist (Q x) (Q a) - Δ / 40| ≤ τ * Δ := by
    have hh := abs_dist_sub_le (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) (Q x)
    rw [dist_comm (Q a) (Q x), dist_comm (Q x + _) (Q x)] at hh
    have he : dist (Q x) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) = Δ / 40 := by
      rw [dist_eq_norm]
      have he : Q x - (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) =
          -WithLp.toLp 2 (Δ / 40, (0 : ℝ)) := by abel
      rw [he, norm_neg, WithLp.prod_norm_eq_of_L2]
      change Real.sqrt (‖Δ / 40‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2) = Δ / 40
      rw [norm_zero, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Δ / 40)]
      norm_num only [zero_pow, add_zero]
      exact Real.sqrt_sq (by positivity : 0 ≤ Δ / 40)
    rw [he] at hh
    exact hh.trans hanchor
  have hxa : |dist x a - Δ / 40| ≤ 2 * (τ * Δ) := by
    have h1 := hdist x hx200 a ha200
    rw [abs_le] at h1 hqdist ⊢
    constructor <;> linarith [h1.1, h1.2, hqdist.1, hqdist.2]
  have hQxy : dist (Q x) (Q y) ≤ dist x y + τ * Δ := by
    have h1 := (abs_le.mp (hdist x hx200 y hy200)).2
    linarith
  have hfxy : (Q x).fst - (Q y).fst ≥ -(dist x y + τ * Δ) := by
    have hh := WithLp.dist_fst_le (Q x) (Q y)
    have hh' : |(Q x).fst - (Q y).fst| ≤ dist (Q x) (Q y) := hh
    linarith [(abs_le.mp hh').1]
  have hya_up : dist y a ≤ dist x y + Δ / 40 + 2 * (τ * Δ) := by
    have h := dist_triangle y x a
    rw [dist_comm y x] at h
    linarith [(abs_le.mp hxa).2]
  have hya_lo : Δ / 40 - 2 * (τ * Δ) - dist x y ≤ dist y a := by
    have h := dist_triangle x y a
    linarith [(abs_le.mp hxa).1]
  have hxy0 : 0 ≤ dist x y := dist_nonneg
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hu : Δ / 40 - 2 * (τ * Δ) - dist x y ≤ (Q a).fst - (Q y).fst := by
    linarith [(abs_le.mp hfst).1]
  have hθ' : 0 ≤ 1 - θ := by linarith
  calc (1 - θ) * dist y a ≤ (1 - θ) * (dist x y + Δ / 40 + 2 * (τ * Δ)) :=
        mul_le_mul_of_nonneg_left hya_up hθ'
    _ ≤ Δ / 40 - 2 * (τ * Δ) - dist x y := by nlinarith
    _ ≤ (Q a).fst - (Q y).fst := hu


/-- Every LFR35 anchor `a ≈ Q(x) + v`, `‖v‖ = Δ/40`, is seen from the buffer `B(x, 303)` at
distance in `[Δ/80, 40Δ]`. -/
theorem edgeAnchor_dist_window {X : Type*} [MetricSpace X] {Q : X → WithLp 2 (ℝ × ℝ)}
    {p x y a : X} {Δ τ : ℝ} {v : WithLp 2 (ℝ × ℝ)} (hΔ : 40400 ≤ Δ) (hτ : τ ≤ 1 / 400)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (ha : a ∈ ball p (20 * Δ)) (hxy : dist x y < 303)
    (hv : ‖v‖ = Δ / 40) (hanchor : dist (Q a) (Q x + v) ≤ τ * Δ) :
    Δ / 80 ≤ dist y a ∧ dist y a ≤ 40 * Δ := by
  have hΔpos : 0 < Δ := by linarith
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hτΔ : τ * Δ ≤ Δ / 400 := by nlinarith
  have hxp : dist x p < 15 * Δ := hx
  have hap : dist a p < 20 * Δ := ha
  have hx200 : x ∈ ball p (200 * Δ) := (show dist x p < 200 * Δ by linarith)
  have ha200 : a ∈ ball p (200 * Δ) := (show dist a p < 200 * Δ by linarith)
  have hqdist : |dist (Q x) (Q a) - Δ / 40| ≤ τ * Δ := by
    have hh := abs_dist_sub_le (Q a) (Q x + v) (Q x)
    rw [dist_comm (Q a) (Q x), dist_comm (Q x + v) (Q x)] at hh
    have he : dist (Q x) (Q x + v) = Δ / 40 := by
      rw [dist_eq_norm, show Q x - (Q x + v) = -v by abel, norm_neg, hv]
    rw [he] at hh
    exact hh.trans hanchor
  have h1 := hdist x hx200 a ha200
  have hxa_lo : Δ / 40 - 2 * (τ * Δ) ≤ dist x a := by
    linarith [(abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp hqdist).1]
  have hxa_hi : dist x a ≤ Δ / 40 + 2 * (τ * Δ) := by
    linarith [(abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp hqdist).2]
  have h2 := dist_triangle x y a
  have h3 := dist_triangle y x a
  rw [dist_comm y x] at h3
  constructor <;> nlinarith

/-! ### Riemannian helpers -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- A scaled gradient close to a vector gives the covector estimate. -/
theorem abs_mul_mvfderiv_sub_inner_le_of_gradFun (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {φ : M → ℝ} {y : M} {v : TangentSpace I y} {q c : ℝ}
    (h : Real.sqrt (g.inner y (q • gradFun g φ y - v) (q • gradFun g φ y - v)) ≤ c)
    (X : TangentSpace I y) :
    |q * mvfderiv I φ y X - g.inner y v X| ≤ c * Real.sqrt (g.inner y X X) := by
  have hg := inner_gradFun g φ y X
  change g.inner y (gradFun g φ y) X = mvfderiv I φ y X at hg
  have he : q * mvfderiv I φ y X - g.inner y v X = inner ℝ (q • gradFun g φ y - v) X := by
    rw [inner_sub_left, real_inner_smul_left, hEnorm.inner_eq, hEnorm.inner_eq, hg]
  rw [he]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_tangent_eq_sqrt_gInner hEnorm, norm_tangent_eq_sqrt_gInner hEnorm]
  exact mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- Components of the differential of an `ℝ²`-valued map. -/
theorem mvfderiv_component_apply (χ : M → EuclideanSpace ℝ (Fin 2)) {y : M}
    (hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) χ y)
    (w : TangentSpace I y) (j : Fin 2) :
    mvfderiv I (fun z => χ z j) y w = mvfderiv I χ y w j := by
  let P : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _j : Fin 2 => ℝ) j
  have h := _root_.mvfderiv_comp_apply y P.differentiableAt.mdifferentiableAt hχ w
  rw [mvfderiv_eq_fderiv, P.fderiv] at h
  exact h

/-- Two component bounds give the Euclidean bound `‖v‖ ≤ 2a`. -/
theorem norm_le_two_mul_of_components {v : EuclideanSpace ℝ (Fin 2)} {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ j, |v j| ≤ a) : ‖v‖ ≤ 2 * a := by
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have h0 := (sq_le_sq₀ (abs_nonneg (v 0)) ha).mpr (hv 0)
  have h1 := (sq_le_sq₀ (abs_nonneg (v 1)) ha).mpr (hv 1)
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg v]

/-! ### LFR37 in the point's own scale `d/q` -/

/-- **LFR37, own scale.** In the metric `d_x = d/q` (balls `B(x, rq)`, unit vectors `q W` for
`g`-unit `W`): a smooth `χ` with `χ(x) = 0`, adapted of quality `γ/4` on `B(x, 100q)` to the
target differences of `P`, with scaled Gram `‖(qDχ)(qDχ)* − 1‖ < γ/4` on `B(x, 300q)`, and a
smooth `J` with `‖qDJ − qDχ‖ ≤ γ/100` there: `J` has rank two on `B(x, 100q)` and is adapted of
quality `γ` to the SAME `P`, centred at `J(x)`. -/
theorem rankTwo_adapted_of_scaled_perturbation (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {x : M} {χ J P : M → EuclideanSpace ℝ (Fin 2)} {γ q : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) (hq : 0 < q)
    (hχ : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ χ (ball x (300 * q)))
    (hJ : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * q)))
    (hχx : χ x = 0)
    (hχL : ∀ y ∈ ball x (100 * q), ∀ z ∈ ball x (100 * q),
      ‖χ y - χ z‖ ≤ (1 + γ / 4) * (dist y z / q))
    (hχI : ∀ y ∈ ball x (100 * q),
      infDist (χ y) (ball (0 : EuclideanSpace ℝ (Fin 2)) 100) < 25 * γ)
    (hχI' : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
      ∃ y ∈ ball x (100 * q), ‖χ y - v‖ < 25 * γ)
    (hχtest : ∀ y ∈ ball x (100 * q), ∀ z ∈ ball x (400 * q / γ), q < dist y z →
      ∀ W : TangentSpace I y, g.inner y W W = 1 →
      intrinsicGeodesic g hEnorm y W (dist y z) = z →
      ‖q • mvfderiv I χ y W - (dist y z / q)⁻¹ • (P z - P y)‖ < γ / 4)
    (hgram : ∀ y ∈ ball x (300 * q),
      let L := q • mvfderiv I χ y
      ‖L.comp L.adjoint - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ < γ / 4)
    (hDJ : ∀ y ∈ ball x (300 * q), ∀ w : TangentSpace I y,
      ‖q • mvfderiv I J y w - q • mvfderiv I χ y w‖ ≤ γ / 100 * Real.sqrt (g.inner y w w)) :
    (∀ y ∈ ball x (100 * q), Function.Surjective (mvfderiv I J y)) ∧
      (∀ y ∈ ball x (100 * q), ∀ z ∈ ball x (100 * q),
        ‖J y - J z‖ ≤ (1 + γ) * (dist y z / q)) ∧
      (∀ y ∈ ball x (100 * q), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
      (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * q), ‖J y - v‖ < 100 * γ) ∧
      (∀ y ∈ ball x (100 * q), ∀ z ∈ ball x (100 * q / γ), q < dist y z →
        ∀ W : TangentSpace I y, g.inner y W W = 1 →
        intrinsicGeodesic g hEnorm y W (dist y z) = z →
        ‖q • mvfderiv I J y W - (dist y z / q)⁻¹ • (P z - P y)‖ < γ) := by
  have hqinv : 0 < q⁻¹ := inv_pos.mpr hq
  have hder (y : M) (hy : y ∈ ball x (300 * q)) :
      ‖mvfderiv I J y - mvfderiv I χ y‖ ≤ γ / (100 * q) := by
    refine opNorm_le_bound _ (by positivity) fun w => ?_
    have h := hDJ y hy w
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hq,
      ← norm_tangent_eq_sqrt_gInner hEnorm] at h
    rw [sub_apply]
    have h' : ‖mvfderiv I J y w - mvfderiv I χ y w‖ ≤ γ / 100 * ‖w‖ / q := by
      rw [le_div_iff₀ hq, mul_comm]; exact h
    calc ‖mvfderiv I J y w - mvfderiv I χ y w‖ ≤ γ / 100 * ‖w‖ / q := h'
      _ = γ / (100 * q) * ‖w‖ := by field_simp
  have hd (y : M) (hy : y ∈ ball x (300 * q)) :
      MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun z => J z - χ z) y :=
    ((hJ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp)).sub
      ((hχ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp))
  have hc (y : M) (hy : y ∈ ball x (300 * q)) :
      mvfderiv I (fun z => J z - χ z) y = mvfderiv I J y - mvfderiv I χ y :=
    _root_.mvfderiv_sub
      ((hJ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp))
      ((hχ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp))
  have hscalar (a : EuclideanSpace ℝ (Fin 2)) (y : M) (hy : y ∈ ball x (300 * q))
      (w : TangentSpace I y) :
      mvfderiv I (fun z => inner ℝ a (J z - χ z)) y w =
        inner ℝ a ((mvfderiv I J y - mvfderiv I χ y) w) := by
    let L := innerSL ℝ a
    have hh := _root_.mvfderiv_comp_apply y L.differentiableAt.mdifferentiableAt (hd y hy) w
    have heq : L ∘ (fun z => J z - χ z) = (fun z => inner ℝ a (J z - χ z)) := by
      funext z
      exact innerSL_apply_apply ℝ a (J z - χ z)
    rw [heq, mvfderiv_eq_fderiv, L.fderiv] at hh
    have hh' : mvfderiv I (fun z => inner ℝ a (J z - χ z)) y w =
        inner ℝ a (mvfderiv I (fun z => J z - χ z) y w) := by
      simpa only [mvfderiv, comp_apply, L, innerSL_apply_apply] using hh
    rw [hc y hy] at hh'
    exact hh'
  have h3 : 3 * (100 * q) = 300 * q := by ring
  have hD : ∀ a : EuclideanSpace ℝ (Fin 2), ‖a‖ = 1 → ∀ y ∈ ball x (3 * (100 * q)),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => inner ℝ a (J z - χ z)) y := by
    intro a _ha y hy
    rw [h3] at hy
    exact (innerSL ℝ a).differentiableAt.mdifferentiableAt.comp y (hd y hy)
  have hgrad : ∀ a : EuclideanSpace ℝ (Fin 2), ‖a‖ = 1 → ∀ y ∈ ball x (3 * (100 * q)),
      Real.sqrt (g.inner y (gradFun g (fun z => inner ℝ a (J z - χ z)) y)
        (gradFun g (fun z => inner ℝ a (J z - χ z)) y)) ≤ γ / (100 * q) := by
    intro a ha y hy
    rw [h3] at hy
    let V := gradFun g (fun z => inner ℝ a (J z - χ z)) y
    have hh := abs_real_inner_le_norm a ((mvfderiv I J y - mvfderiv I χ y) V)
    rw [ha, one_mul, ← hscalar a y hy, ← inner_gradientFun] at hh
    change |g.inner y V V| ≤ ‖(mvfderiv I J y - mvfderiv I χ y) V‖ at hh
    rw [← hEnorm.inner_eq, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
    have hb : ‖(mvfderiv I J y - mvfderiv I χ y) V‖ ≤ γ / (100 * q) * ‖V‖ :=
      (le_opNorm _ V).trans (mul_le_mul_of_nonneg_right (hder y hy) (norm_nonneg V))
    have hn := norm_nonneg V
    have hpos : 0 < γ / (100 * q) := by positivity
    have hg : ‖V‖ ≤ γ / (100 * q) := by nlinarith
    simpa only [← norm_tangent_eq_sqrt_gInner hEnorm] using hg
  have hdiff (y : M) (hy : y ∈ ball x (100 * q)) (z : M) (hz : z ∈ ball x (100 * q)) :
      ‖(J y - χ y) - (J z - χ z)‖ ≤ γ / 100 * (dist y z / q) := by
    have h := norm_sub_le_of_gradFun_inner_le_on_ball g hEnorm (D := fun w => J w - χ w)
      (R := 100 * q) hD hgrad hy hz
    calc ‖(J y - χ y) - (J z - χ z)‖ ≤ γ / (100 * q) * dist y z := h
      _ = γ / 100 * (dist y z / q) := by field_simp
  have hx100 : x ∈ ball x (100 * q) := mem_ball_self (by positivity)
  have hsmall (y : M) (hy : y ∈ ball x (100 * q)) : ‖J y - (J x + χ y)‖ < γ := by
    have h := hdiff y hy x hx100
    rw [hχx, sub_zero] at h
    have hyx : dist y x < 100 * q := hy
    have e : J y - (J x + χ y) = (J y - χ y) - J x := by abel
    rw [e]
    calc ‖(J y - χ y) - J x‖ ≤ γ / 100 * (dist y x / q) := h
      _ < γ / 100 * (100 * q / q) := by
          apply mul_lt_mul_of_pos_left _ (by positivity)
          exact div_lt_div_of_pos_right hyx hq
      _ = γ := by field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hy300 : y ∈ ball x (300 * q) := ball_subset_ball (by linarith) hy
    have hB : ‖q • mvfderiv I J y - q • mvfderiv I χ y‖ < ((γ + 1 / 100) / 2) / 100 := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
      have h := mul_le_mul_of_nonneg_left (hder y hy300) hq.le
      have he : q * (γ / (100 * q)) = γ / 100 := by field_simp
      rw [he] at h
      linarith
    have hs := surjective_of_gram_perturbation (γ := (γ + 1 / 100) / 2) (by linarith)
      ((hgram y hy300).trans (by linarith)) hB
    intro v
    obtain ⟨w, hw⟩ := hs (q • v)
    refine ⟨w, ?_⟩
    have he' : q • mvfderiv I J y w = q • v := by rw [← smul_apply]; exact hw
    have he'' := congrArg (fun z => q⁻¹ • z) he'
    simpa only [smul_smul, inv_mul_cancel₀ hq.ne', one_smul] using he''
  · intro y hy z hz
    have e : J y - J z = (χ y - χ z) + ((J y - χ y) - (J z - χ z)) := by abel
    rw [e]
    have hdz : 0 ≤ dist y z / q := by positivity
    calc ‖(χ y - χ z) + ((J y - χ y) - (J z - χ z))‖
        ≤ ‖χ y - χ z‖ + ‖(J y - χ y) - (J z - χ z)‖ := norm_add_le _ _
      _ ≤ (1 + γ / 4) * (dist y z / q) + γ / 100 * (dist y z / q) :=
          add_le_add (hχL y hy z hz) (hdiff y hy z hz)
      _ ≤ (1 + γ) * (dist y z / q) := by nlinarith
  · intro y hy
    have h1 : infDist (J x + χ y) (ball (J x) 100) =
        infDist (χ y) (ball (0 : EuclideanSpace ℝ (Fin 2)) 100) := by
      have hb : ball (J x) 100 =
          IsometryEquiv.addLeft (J x) '' ball (0 : EuclideanSpace ℝ (Fin 2)) 100 := by
        rw [IsometryEquiv.image_ball, IsometryEquiv.addLeft_apply, add_zero]
      rw [hb]
      exact infDist_image (IsometryEquiv.addLeft (J x)).isometry
    have h2 := infDist_le_infDist_add_dist (x := J y) (y := J x + χ y) (s := ball (J x) 100)
    rw [h1, dist_eq_norm] at h2
    linarith [hχI y hy, hsmall y hy]
  · intro v hv
    have hv' : v - J x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100 := by
      rw [mem_ball, dist_zero_right, ← dist_eq_norm]
      exact hv
    obtain ⟨y, hy, hyv⟩ := hχI' _ hv'
    refine ⟨y, hy, ?_⟩
    have e : J y - v = (J y - (J x + χ y)) + (χ y - (v - J x)) := by abel
    rw [e]
    calc ‖(J y - (J x + χ y)) + (χ y - (v - J x))‖
        ≤ ‖J y - (J x + χ y)‖ + ‖χ y - (v - J x)‖ := norm_add_le _ _
      _ < γ + 25 * γ := add_lt_add (hsmall y hy) hyv
      _ ≤ 100 * γ := by linarith
  · intro y hy z hz hyz W hW hWz
    have hz' : z ∈ ball x (400 * q / γ) :=
      ball_subset_ball (div_le_div_of_nonneg_right (by nlinarith) hγ.le) hz
    have hy300 : y ∈ ball x (300 * q) := ball_subset_ball (by linarith) hy
    have hdw := hDJ y hy300 W
    rw [hW, Real.sqrt_one, mul_one] at hdw
    have ht := hχtest y hy z hz' hyz W hW hWz
    have e : q • mvfderiv I J y W - (dist y z / q)⁻¹ • (P z - P y) =
        (q • mvfderiv I J y W - q • mvfderiv I χ y W) +
          (q • mvfderiv I χ y W - (dist y z / q)⁻¹ • (P z - P y)) := by abel
    rw [e]
    calc ‖(q • mvfderiv I J y W - q • mvfderiv I χ y W) +
          (q • mvfderiv I χ y W - (dist y z / q)⁻¹ • (P z - P y))‖
        ≤ ‖q • mvfderiv I J y W - q • mvfderiv I χ y W‖ +
          ‖q • mvfderiv I χ y W - (dist y z / q)⁻¹ • (P z - P y)‖ := norm_add_le _ _
      _ < γ / 100 + γ / 4 := by linarith
      _ < γ := by linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- **LFR38, operator step.** At one point `y`, if `df` is `ι`-pinned to a unit `v₀`, the scaled
gradients of `χ₀` and of `η` are `ι`-close to `v₀` resp. `v₁`, and so is that of `χ₁`, then the
scaled differentials of `J = (f, η)` and `χ` differ by at most `10ι` in operator norm. -/
theorem edgeCollar_scaled_operator_bound (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {y : M} {f η : M → ℝ} {χ : M → EuclideanSpace ℝ (Fin 2)}
    {v₀ v₁ : TangentSpace I y} {q ι : ℝ} (hι : 0 ≤ ι) (hq : 0 ≤ q) (hq2 : q ≤ 101 / 100)
    (hq1 : |q - 1| ≤ ι)
    (hcomp : ∀ j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (![f, η] j) y)
    (hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) χ y)
    (hv₀ : g.inner y v₀ v₀ = 1)
    (hpin : ∀ X : TangentSpace I y,
      |mvfderiv I f y X - g.inner y v₀ X| ≤ ι * Real.sqrt (g.inner y X X))
    (hχ0 : Real.sqrt (g.inner y (q • gradFun g (fun z => χ z 0) y - v₀)
      (q • gradFun g (fun z => χ z 0) y - v₀)) < ι)
    (hη1 : Real.sqrt (g.inner y (q • gradFun g η y - v₁) (q • gradFun g η y - v₁)) < ι)
    (hχ1 : Real.sqrt (g.inner y (q • gradFun g (fun z => χ z 1) y - v₁)
      (q • gradFun g (fun z => χ z 1) y - v₁)) < ι)
    (w : TangentSpace I y) :
    ‖q • mvfderiv I (edgeReferenceCoordinates ![f, η]) y w - q • mvfderiv I χ y w‖ ≤
      10 * ι * Real.sqrt (g.inner y w w) := by
  have hsw := Real.sqrt_nonneg (g.inner y w w)
  have hf0 := abs_scaled_mvfderiv_sub_inner_le g hEnorm hq hv₀ hpin w
  have hχ0w := abs_mul_mvfderiv_sub_inner_le_of_gradFun g hEnorm hχ0.le w
  have hη1w := abs_mul_mvfderiv_sub_inner_le_of_gradFun g hEnorm hη1.le w
  have hχ1w := abs_mul_mvfderiv_sub_inner_le_of_gradFun g hEnorm hχ1.le w
  have hqι : q * ι ≤ 101 / 100 * ι := mul_le_mul_of_nonneg_right hq2 hι
  have hcoef : (q * ι + |q - 1|) * Real.sqrt (g.inner y w w) ≤
      (3 * ι) * Real.sqrt (g.inner y w w) :=
    mul_le_mul_of_nonneg_right (by linarith) hsw
  have hι1 : ι * Real.sqrt (g.inner y w w) ≤ ι * Real.sqrt (g.inner y w w) := le_rfl
  have hc0 : |q * mvfderiv I f y w - q * mvfderiv I (fun z => χ z 0) y w| ≤
      4 * ι * Real.sqrt (g.inner y w w) := by
    have e : q * mvfderiv I f y w - q * mvfderiv I (fun z => χ z 0) y w =
        (q * mvfderiv I f y w - g.inner y v₀ w) -
          (q * mvfderiv I (fun z => χ z 0) y w - g.inner y v₀ w) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have h4 : 4 * ι * Real.sqrt (g.inner y w w) =
        3 * ι * Real.sqrt (g.inner y w w) + ι * Real.sqrt (g.inner y w w) := by ring
    rw [h4]
    exact add_le_add (hf0.trans hcoef) hχ0w
  have hc1 : |q * mvfderiv I η y w - q * mvfderiv I (fun z => χ z 1) y w| ≤
      4 * ι * Real.sqrt (g.inner y w w) := by
    have e : q * mvfderiv I η y w - q * mvfderiv I (fun z => χ z 1) y w =
        (q * mvfderiv I η y w - g.inner y v₁ w) -
          (q * mvfderiv I (fun z => χ z 1) y w - g.inner y v₁ w) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have hιs : 0 ≤ ι * Real.sqrt (g.inner y w w) := mul_nonneg hι hsw
    have h4 : 4 * ι * Real.sqrt (g.inner y w w) =
        ι * Real.sqrt (g.inner y w w) + ι * Real.sqrt (g.inner y w w) +
          2 * (ι * Real.sqrt (g.inner y w w)) := by ring
    rw [h4]
    linarith
  have hpair := norm_le_two_mul_of_components (v := q • mvfderiv I
    (edgeReferenceCoordinates ![f, η]) y w - q • mvfderiv I χ y w)
    (a := 4 * ι * Real.sqrt (g.inner y w w)) (by positivity) (by
      intro j
      rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
        edgeReferenceCoordinates_derivative hcomp, ← mvfderiv_component_apply χ hχ]
      fin_cases j
      · exact hc0
      · exact hc1)
  have h8 : 2 * (4 * ι * Real.sqrt (g.inner y w w)) ≤ 10 * ι * Real.sqrt (g.inner y w w) := by
    have hιs : 0 ≤ ι * Real.sqrt (g.inner y w w) := mul_nonneg hι hsw
    linarith
  exact hpair.trans h8

/-! ### LFR38 at one strong-edge centre -/

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM uY

/-- **LFR38** (single centre, `ρ(p) = 1`). See the module docstring. -/
theorem exists_edge_full_collar_parameters {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 ≤ ε → ε < 1 / 100 →
        μ ≤ 1 / 1000000 → τ ≤ τ₀ → 0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type uY) [MetricSpace Y] (p : M) (y₀ : Y)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b)
        (Q : M → WithLp 2 (ℝ × ℝ)) (A : Set M) (ρ F f : M → ℝ) (O : Set M),
      (∀ z ∈ ball p (10000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2)) →
      (∀ z ∈ ball p b⁻¹, SectionalBoundedBelowAt g z (-b ^ 2)) →
      IsClosed A → Q p = 0 →
      (∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
        |dist (Q y) (Q z) - dist y z| ≤ τ * Δ) →
      (∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd) →
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ) →
      p ∈ A → (∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
        dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
      (∀ z ∈ ball p (200 * Δ), (Q z).fst = (α.toFun z).fst) →
      LipschitzWith Λ ρ → ρ p = 1 → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      IsOpen O →
      closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ O →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O → LipschitzWith (Real.toNNReal (1 + ε)) F →
      (∀ y, |F y - infDist y A| ≤ μ * Δ) →
      (∀ y ∈ closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
        ∀ v ∈ minimizingDirectionsTo g hEnorm A y,
          Real.sqrt (g.inner y (gradFun g F y + v) (gradFun g F y + v)) < ε) →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
      LipschitzWith (Real.toNNReal (1 + σ)) f →
      (∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ) →
      (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
        ∀ w : TangentSpace I x, g.inner x w w = 1 →
        intrinsicGeodesic g hEnorm x w (dist x x') = x' →
        |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
      ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ → Δ / 10 ≤ F x / ρ x → F x / ρ x ≤ 10 * Δ →
      ∃ hq : 99 / 100 ≤ ρ x ∧ ρ x ≤ 101 / 100,
        (letI := mM.rescale (ρ x)⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
          ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
            ∀ y, Φ.toFun y = @planeComparisonMap M mM Q p x Δ (ρ x) y) ∧
        let J := edgeReferenceCoordinates ![f, fun z => F z / ρ z]
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * ρ x)) ∧
        (∀ y ∈ ball x (100 * ρ x), Function.Surjective (mvfderiv (I := I) J y)) ∧
        (∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x),
          ‖J y - J z‖ ≤ (1 + γ) * (dist y z / ρ x)) ∧
        (∀ y ∈ ball x (100 * ρ x), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
        (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * ρ x), ‖J y - v‖ < 100 * γ) ∧
        ∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x / γ), ρ x < dist y z →
          ∀ W : TangentSpace I y, g.inner y W W = 1 →
          intrinsicGeodesic g hEnorm y W (dist y z) = z →
          ‖ρ x • mvfderiv (I := I) J y W - (dist y z / ρ x)⁻¹ •
            (planeReferenceIsometry (planeComparisonMap Q p x Δ (ρ x) z) -
              planeReferenceIsometry (planeComparisonMap Q p x Δ (ρ x) y))‖ < γ := by
  have hι : 0 < γ / 1000 := by positivity
  obtain ⟨Δ₁, hΔ₁, hX⟩ := exists_edge_reference_chart_parameters_uniform.{uE, uH, uM}
    hβ hβγ hγ hγ1 hι
  obtain ⟨σ₀, hσ₀, hpin⟩ := exists_edge_tangential_pinning.{uE, uH, uM, uY} hι
  set θ : ℝ := min σ₀ 1 with hθdef
  have hθpos : 0 < θ := lt_min hσ₀ one_pos
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hθσ : θ ≤ σ₀ := min_le_left _ _
  refine ⟨σ₀, hσ₀, max (max Δ₁ 1000000) (40400 / θ), by positivity, ?_⟩
  intro Δ hΔ
  have hΔΔ₁ : Δ₁ ≤ Δ := (le_max_left _ _).trans ((le_max_left _ _).trans hΔ)
  have hΔ6 : 1000000 ≤ Δ := (le_max_right _ _).trans ((le_max_left _ _).trans hΔ)
  have hΔθ' : 40400 / θ ≤ Δ := (le_max_right _ _).trans hΔ
  have hΔpos : 0 < Δ := by linarith
  have hθΔ : 40400 ≤ θ * Δ := by
    have h := (div_le_iff₀ hθpos).mp hΔθ'
    linarith
  obtain ⟨τ₁, hτ₁, κ₁, hκ₁, hXΔ⟩ := hX Δ hΔΔ₁
  obtain ⟨b₁, hb₁, hpinΔ⟩ := hpin Δ hΔpos
  refine ⟨min τ₁ (min (1 / 10000) (θ / 400)), lt_min hτ₁ (lt_min (by norm_num) (by positivity)),
    min κ₁ (1 / (100 * Δ)), lt_min hκ₁ (by positivity), b₁, hb₁, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M mM _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α Q A ρ F f O
    hsecκ hsecb hA hQp hdist hheight hcover hpA hborder hbordercover hQα hρ hρp hρs
    hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx hη hη'
  -- the ordered numerical constraints
  have hτX : τ ≤ τ₁ := hττ₀.trans (min_le_left _ _)
  have hτ1 : τ ≤ 1 / 10000 := hττ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτθ : τ ≤ θ / 400 := hττ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp200 : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ := by
    have h := hdist p hp200 p hp200
    simp only [dist_self, sub_self, abs_zero] at h
    exact (mul_nonneg_iff_of_pos_right hΔpos).mp h
  have hκX : κ ≤ κ₁ := hκκ₀.trans (min_le_left _ _)
  have hκΔ : κ * Δ ≤ 1 / 100 := by
    have h : κ ≤ 1 / (100 * Δ) := hκκ₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hsec1000 : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2) :=
    fun z hz => hsecκ z (ball_subset_ball (by linarith) hz)
  have hsecX : ∀ z ∈ ball p (10000 * Δ), SectionalBoundedBelowAt g z (-κ₁ ^ 2) :=
    fun z hz => (hsecκ z hz).mono (by
      have h := mul_le_mul hκX hκX hκ hκ₁.le
      simp only [sq]
      linarith)
  have hΔΛ : 0 ≤ Δ * Λ := by positivity
  have hsq0 := Real.sqrt_nonneg (504000 / Δ + 3780 * τ)
  have hΛγ : 300 * Δ * Λ < γ / 1000 := by linarith
  -- LFR36.3: the band point is enclosed
  obtain ⟨hx15, hxA, hxA'⟩ := edgeBand_mem_ball_and_infDist_window hΔpos hτ1 hμ hlam hQp hdist
    hheight hpA hborder hρ hρp hval hfval hx hfx hη hη'
  have hxp : dist x p < 15 * Δ := hx15
  have hρx : |ρ x - 1| ≤ 15 * Δ * Λ := by
    have hh := hρ.dist_le_mul x p
    rw [Real.dist_eq, hρp] at hh
    have h2 := mul_le_mul_of_nonneg_left hxp.le Λ.coe_nonneg
    have h3 : (Λ : ℝ) * (15 * Δ) = 15 * Δ * Λ := by ring
    linarith
  have hq1 : 99 / 100 ≤ ρ x := by linarith [(abs_le.mp hρx).1]
  have hq2 : ρ x ≤ 101 / 100 := by linarith [(abs_le.mp hρx).2]
  have hqpos : 0 < ρ x := by linarith
  -- LFR35: the actual comparison map, the SAME anchors and the reference chart
  obtain ⟨anchors, χ, hanch, hχs, hχ0, -, hgram, hgradχ, -, hχL, hχI, hχI', hχtest, -, hΦ⟩ :=
    hXΔ τ hτX E H I M g hEnorm Q p A hsecX hQp hdist hheight hcover hpA hborder hbordercover
      x hx15 hxA.le hxA'.le (ρ x) hq1 hq2
  have hanchor0 : dist (Q (anchors 0)) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) ≤ τ * Δ := by
    simpa only [planeReferenceIsometry_symm_single_zero] using (hanch 0).2
  have hanchor1 : dist (Q (anchors 1)) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ := by
    simpa only [planeReferenceIsometry_symm_single_one] using (hanch 1).2
  -- LFR36.2, vertical half, for the SAME vertical anchor
  have hCdiff : ∀ y ∈ closedBall p (20 * Δ) ∩
      {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
      MDifferentiableAt I 𝓘(ℝ, ℝ) F y :=
    fun y hy => (hFO.contMDiffAt (hO.mem_nhds (hCO hy))).mdifferentiableAt (by simp)
  have hvert := edgeBand_vertical_gradient g hEnorm hA hΔ6 hτ0 hτ1 hQp hdist hheight hpA
    hborder hbordercover hx15 hxA hxA' (hanch 1).1 hanchor1 hκ hκΔ hsec1000 hε hε1
    (by linarith) hFL hval hCdiff hFgrad hρ hρp hρs (by linarith) hbudget
  -- the buffer
  have hbuf (y : M) (hy : y ∈ ball x (300 * ρ x)) :
      dist x y < 303 ∧ y ∈ ball p (16 * Δ) ∧ y ∈ closedBall p (20 * Δ) ∩
        {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} := by
    have hxy : dist x y < 303 := by
      have hh : dist y x < 300 * ρ x := hy
      rw [dist_comm] at hh
      linarith
    obtain ⟨hyp, hyA, hyA'⟩ := edgeBand_buffer_subset hΔ6 hx15 hxA hxA' hxy
    refine ⟨hxy, hyp, ?_, hyA, hyA'⟩
    have : dist y p < 16 * Δ := hyp
    change dist y p ≤ 20 * Δ
    linarith
  have hy100 (y : M) (hy : y ∈ ball p (16 * Δ)) : y ∈ ball p (100 * Δ) :=
    ball_subset_ball (by linarith) hy
  have hρne (y : M) (hy : y ∈ ball p (16 * Δ)) : ρ y ≠ 0 := by
    have hh := hρ.dist_le_mul y p
    rw [Real.dist_eq, hρp] at hh
    have hyp : dist y p < 16 * Δ := hy
    have h2 := mul_le_mul_of_nonneg_left hyp.le Λ.coe_nonneg
    have h3 := (abs_le.mp (hh.trans h2)).1
    have h4 : (Λ : ℝ) * (16 * Δ) = 16 / 100 * (100 * Δ * Λ) := by ring
    have h5 : 0 < ρ y := by linarith
    exact h5.ne'
  have hfAt (y : M) (hy : y ∈ ball p (16 * Δ)) : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f y :=
    hfs.contMDiffAt (isOpen_ball.mem_nhds (hy100 y hy))
  have hηAt (y : M) (hy : y ∈ ball x (300 * ρ x)) :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z => F z / ρ z) y :=
    (hFO.contMDiffAt (hO.mem_nhds (hCO (hbuf y hy).2.2))).div₀ hρs.contMDiffAt
      (hρne y (hbuf y hy).2.1)
  have hcomp (y : M) (hy : y ∈ ball x (300 * ρ x)) :
      ∀ j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (![f, fun z => F z / ρ z] j) y := by
    intro j
    fin_cases j
    · exact hfAt y (hbuf y hy).2.1
    · exact hηAt y hy
  set J := edgeReferenceCoordinates ![f, fun z => F z / ρ z] with hJdef
  have hJs : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * ρ x)) := by
    refine edgeReferenceCoordinates_smooth fun j => ?_
    intro y hy
    exact (hcomp y hy j).contMDiffWithinAt
  -- LFR38's operator estimate: both components against the SAME anchor directions
  have hι10 : 10 * (γ / 1000) = γ / 100 := by ring
  have hqerr : |ρ x - 1| ≤ γ / 1000 := by
    have h15 : 15 * Δ * (Λ : ℝ) = 1 / 20 * (300 * Δ * Λ) := by ring
    linarith
  have hDJ : ∀ y ∈ ball x (300 * ρ x), ∀ w : TangentSpace I y,
      ‖ρ x • mvfderiv I J y w - ρ x • mvfderiv I χ y w‖ ≤
        γ / 100 * Real.sqrt (g.inner y w w) := by
    intro y hy w
    obtain ⟨hxy, hy16, -⟩ := hbuf y hy
    have hχy : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) χ y :=
      (hχs.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp)
    -- tangential anchor
    obtain ⟨h0lo, h0hi, hslope⟩ := edgeTangentialAnchor_slope hθpos hθ1 hθΔ hτθ hdist hx15
      (hanch 0).1 hxy hanchor0
    have hd0 : 0 < dist y (anchors 0) := by linarith
    obtain ⟨v₀, hv₀1, hv₀end⟩ := soul_unit_minimizing_initial g hEnorm y (anchors 0) hd0
    have hv₀ : v₀ ∈ minimizingDirectionsTo g hEnorm {anchors 0} y := by
      refine ⟨hv₀1, ?_⟩
      rw [Metric.infDist_singleton, hv₀end]
      exact mem_singleton _
    have ha0 : anchors 0 ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) (hanch 0).1
    have hy200 : y ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) hy16
    have hslopeα : (1 - θ) * dist y (anchors 0) ≤
        (α.toFun (anchors 0)).fst - (α.toFun y).fst := by
      rw [← hQα _ ha0, ← hQα _ hy200]
      exact hslope
    have hpin0 := hpinΔ σ θ b hσ hσσ₀ hθσ hb hbb₀ E H I M g hEnorm Y p y₀ α hsecb f hfL htest
      y hy16 ((hfAt y hy16).mdifferentiableAt (by simp)) (anchors 0) h0lo h0hi hslopeα
      v₀ hv₀1 hv₀end
    -- vertical anchor
    obtain ⟨h1lo, -⟩ := edgeAnchor_dist_window (v := WithLp.toLp 2 ((0 : ℝ), Δ / 40))
      (by linarith) (by linarith) hdist hx15 (hanch 1).1 hxy (by
        rw [WithLp.prod_norm_eq_of_L2]
        change Real.sqrt (‖(0 : ℝ)‖ ^ 2 + ‖Δ / 40‖ ^ 2) = Δ / 40
        rw [norm_zero, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Δ / 40)]
        norm_num only [zero_pow, zero_add]
        exact Real.sqrt_sq (by positivity : 0 ≤ Δ / 40)) hanchor1
    have hd1 : 0 < dist y (anchors 1) := by linarith
    obtain ⟨v₁, hv₁1, hv₁end⟩ := soul_unit_minimizing_initial g hEnorm y (anchors 1) hd1
    have hv₁ : v₁ ∈ minimizingDirectionsTo g hEnorm {anchors 1} y := by
      refine ⟨hv₁1, ?_⟩
      rw [Metric.infDist_singleton, hv₁end]
      exact mem_singleton _
    have hb := edgeCollar_scaled_operator_bound g hEnorm hι.le hqpos.le hq2 hqerr (hcomp y hy)
      hχy hv₀1 hpin0 (hgradχ 0 y hy v₀ hv₀) (hvert y hy v₁ hv₁) (hgradχ 1 y hy v₁ hv₁) w
    rw [hι10] at hb
    exact hb
  have hfin := rankTwo_adapted_of_scaled_perturbation g hEnorm
    (P := fun z => planeReferenceIsometry (planeComparisonMap Q p x Δ (ρ x) z))
    hγ hγ1 hqpos hχs hJs hχ0 hχL hχI hχI' hχtest hgram hDJ
  exact ⟨⟨hq1, hq2⟩, hΦ, hJs, hfin⟩

end DifferentialGeometry.Geometry.Collapse
