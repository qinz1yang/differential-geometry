import DifferentialGeometry.Geometry.Collapse.EdgeFullCollar
import DifferentialGeometry.Geometry.Collapse.EdgeEndpointModel

/-!
# LFR36: the prescribed pair is pinned to the same two directions (the row)

Blueprint 207A, LFR36 (`lem:collapse-edge-prescribed-gradient-pinning`, A:28073–28160), in the row's
order of choices: first `Δ` large, then `τ, σ, ε, μ, ΔΛ` small, then `b, κ` small. At EVERY point
`x` of the tested band (LFR36.1):

* (LFR36.3) `x ∈ B(p, 15Δ)`, `0.09Δ < d_A(x) < 10.1Δ`, and `q = ρ(x) ∈ [0.99, 1.01]`;
* `f` and `η = F/ρ` are smooth on `B_{d_x}(x, 300) = B(x, 300q)`;
* anchors of LFR35's shape exist: points `a₁, a₂ ∈ B(p, 20Δ)` with `Q(a₁) ≈ Q(x) + (Δ/40, 0)` and
  `Q(a₂) ≈ Q(x) + (0, Δ/40)` within `τΔ`;
* (LFR36.2) for EVERY such pair of anchors, every `y ∈ B(x, 300q)` and EVERY choice of minimizing unit
  directions `v₁` to `a₁`, `v₂` to `a₂`: in the point's own scale `g_x = q⁻²g`,
  `‖∇_{g_x} f - v_{1+}‖_{g_x} = ‖q ∇f - v₁‖_g ≤ ι/2` (covector form) and
  `‖∇_{g_x} η - v_{2+}‖_{g_x} = ‖q ∇η - v₂‖_g < ι`.

The tangential half is F7-FOLLOW's `exists_edge_tangential_pinning` (with `ι/4`) on F7-EDGE's anchor
slope `edgeTangentialAnchor_slope`; the vertical half is Codex X91's `edgeBand_vertical_gradient`
with the explicit LFR34/LFR36 budget `2ε + 300ΔΛ + √(504000/Δ + 3780τ) < ι`; the enclosure is
`edgeBand_mem_ball_and_infDist_window`, `edgeBand_buffer_subset`. Hypotheses on `F` are LFR34's
output clauses and on `f` LFR19's, as in F7-EDGE's `exists_edge_full_collar_parameters` (whose proof
this row's assembly follows). Anchors are quantified over all points of LFR35's shape (the anchors
of LFR35 are among them).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open scoped Manifold ContDiff Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup

/-- Scaling a pinned covector by `q` close to `1`: `|q φ(X) - ⟨v, X⟩| ≤ (2ι' + |q - 1|) |X|` for a
unit `v`, if `|φ(X) - ⟨v, X⟩| ≤ ι' |X|`. -/
theorem abs_mul_sub_le_of_abs_sub_le {φX vX nX q ι' : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 2) (hv : |vX| ≤ nX) (h : |φX - vX| ≤ ι' * nX) :
    |q * φX - vX| ≤ (2 * ι' + |q - 1|) * nX := by
  have h1 : q * φX - vX = q * (φX - vX) + (q - 1) * vX := by ring
  rw [h1]
  calc |q * (φX - vX) + (q - 1) * vX| ≤ |q * (φX - vX)| + |(q - 1) * vX| := abs_add_le _ _
    _ = q * |φX - vX| + |q - 1| * |vX| := by rw [abs_mul, abs_mul, abs_of_nonneg hq0]
    _ ≤ 2 * (ι' * nX) + |q - 1| * nX := by
        gcongr
    _ = (2 * ι' + |q - 1|) * nX := by ring

universe uE uH uM uY

/-- **LFR36 (the row).** Ordered choices: `ι` → `Δ ≥ Δ₀` → `τ ≤ τ₀`, `σ ≤ σ₀`, `ε, μ, ΔΛ` (with the
explicit budget) → `κ ≤ κ₀`, `b < b₀`. For any LFR34-type `F` and any LFR19-type `f`, at every point
`x` of the tested band: enclosure, the scale `q = ρ(x) ∈ [0.99, 1.01]`, smoothness of `f` and
`η = F/ρ` on `B(x, 300q)`, existence of anchors of LFR35's shape, and for all such anchors and all
minimizing unit directions the two pinning estimates (LFR36.2) in the point's own scale. -/
theorem exists_edge_prescribed_gradient_pinning {ι : ℝ} (hι : 0 < ι) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 ≤ ε → ε < 1 / 100 →
        μ ≤ 1 / 1000000 → τ ≤ τ₀ → 0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < ι →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
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
        (x ∈ ball p (15 * Δ) ∧ 9 / 100 * Δ < infDist x A ∧ infDist x A < 101 / 10 * Δ) ∧
        (99 / 100 ≤ ρ x ∧ ρ x ≤ 101 / 100) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball x (300 * ρ x)) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun z => F z / ρ z) (ball x (300 * ρ x)) ∧
        (∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) ≤ τ * Δ) ∧
        (∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ) ∧
        (∀ a ∈ ball p (20 * Δ),
          dist (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) ≤ τ * Δ →
          ∀ y ∈ ball x (300 * ρ x), ∀ v ∈ minimizingDirectionsTo g hEnorm {a} y,
            ∀ X : TangentSpace I y,
              |ρ x * mvfderiv (I := I) f y X - g.inner y v X| ≤
                ι / 2 * Real.sqrt (g.inner y X X)) ∧
        ∀ a ∈ ball p (20 * Δ),
          dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ →
          ∀ y ∈ ball x (300 * ρ x), ∀ w ∈ minimizingDirectionsTo g hEnorm {a} y,
            Real.sqrt (g.inner y (ρ x • gradFun g (fun z => F z / ρ z) y - w)
              (ρ x • gradFun g (fun z => F z / ρ z) y - w)) < ι := by
  have hι4 : 0 < ι / 8 := by positivity
  obtain ⟨σ₀, hσ₀, hpin⟩ := exists_edge_tangential_pinning.{uE, uH, uM, uY} hι4
  set θ : ℝ := min σ₀ 1 with hθdef
  have hθpos : 0 < θ := lt_min hσ₀ one_pos
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hθσ : θ ≤ σ₀ := min_le_left _ _
  refine ⟨σ₀, hσ₀, max 1000000 (40400 / θ), by positivity, ?_⟩
  intro Δ hΔ
  have hΔ6 : 1000000 ≤ Δ := (le_max_left _ _).trans hΔ
  have hΔθ' : 40400 / θ ≤ Δ := (le_max_right _ _).trans hΔ
  have hΔpos : 0 < Δ := by linarith
  have hθΔ : 40400 ≤ θ * Δ := by
    have h := (div_le_iff₀ hθpos).mp hΔθ'
    linarith
  obtain ⟨b₁, hb₁, hpinΔ⟩ := hpin Δ hΔpos
  refine ⟨min (1 / 10000) (θ / 400), lt_min (by norm_num) (by positivity),
    1 / (100 * Δ), by positivity, b₁, hb₁, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α Q A ρ F f O
    hsecκ hsecb hA hQp hdist hheight hcover hpA hborder hbordercover hQα hρ hρp hρs
    hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx hη hη'
  have hτ1 : τ ≤ 1 / 10000 := hττ₀.trans (min_le_left _ _)
  have hτθ : τ ≤ θ / 400 := hττ₀.trans (min_le_right _ _)
  have hp200 : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ := by
    have h := hdist p hp200 p hp200
    simp only [dist_self, sub_self, abs_zero] at h
    exact (mul_nonneg_iff_of_pos_right hΔpos).mp h
  have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
  have hκΔ : κ * Δ ≤ 1 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hκκ₀
    linarith
  have hsec1000 : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2) :=
    fun z hz => hsecκ z (ball_subset_ball (by linarith) hz)
  have hΔΛ : 0 ≤ Δ * Λ := by positivity
  have hsq0 := Real.sqrt_nonneg (504000 / Δ + 3780 * τ)
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
  have hqι : |ρ x - 1| ≤ ι / 4 := by
    have h15 : 15 * Δ * (Λ : ℝ) = 1 / 20 * (300 * Δ * Λ) := by ring
    linarith
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
  -- anchors of LFR35's shape exist
  have hQx : |(Q x).fst| ≤ 15 * Δ + τ * Δ ∧ 0 ≤ (Q x).snd ∧ (Q x).snd ≤ 15 * Δ + τ * Δ := by
    have hx200 : x ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) hx15
    have hd := (abs_le.mp (hdist x hx200 p hp200)).2
    rw [hQp] at hd
    have h1 := abs_fst_sub_le_dist (Q x) 0
    have h2 := abs_snd_sub_le_dist (Q x) 0
    have h0f : (0 : WithLp 2 (ℝ × ℝ)).fst = 0 := rfl
    have h0s : (0 : WithLp 2 (ℝ × ℝ)).snd = 0 := rfl
    rw [h0f, sub_zero] at h1
    rw [h0s, sub_zero] at h2
    have hxp' : dist x p < 15 * Δ := hx15
    exact ⟨by linarith, hheight x hx200, by linarith [le_abs_self (Q x).snd]⟩
  have hanchorExists : ∀ v : WithLp 2 (ℝ × ℝ), ‖v‖ = Δ / 40 → 0 ≤ v.snd →
      |(Q x + v).fst| ≤ 100 * Δ → (Q x + v).snd ≤ 100 * Δ →
      ∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + v) ≤ τ * Δ := by
    intro v hv hv0 hvf hvs
    obtain ⟨a, ha, haQ⟩ := hcover (Q x + v) hvf
      ⟨by
        change 0 ≤ (Q x).snd + v.snd
        linarith [hQx.2.1], hvs⟩
    refine ⟨a, ?_, haQ⟩
    have hd := (abs_le.mp (hdist a ha p hp200)).1
    rw [hQp] at hd
    have h1 : dist (Q a) 0 ≤ dist (Q a) (Q x + v) + dist (Q x + v) 0 := dist_triangle _ _ _
    have h2 : dist (Q x + v) 0 ≤ dist (Q x) 0 + ‖v‖ := by
      rw [dist_zero_right, dist_zero_right]
      exact norm_add_le _ _
    have hx200 : x ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) hx15
    have h3 := (abs_le.mp (hdist x hx200 p hp200)).2
    rw [hQp] at h3
    change dist a p < 20 * Δ
    nlinarith
  have hnorm1 : ‖WithLp.toLp 2 (Δ / 40, (0 : ℝ))‖ = Δ / 40 := by
    rw [WithLp.prod_norm_eq_of_L2]
    change Real.sqrt (‖Δ / 40‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2) = Δ / 40
    rw [norm_zero, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Δ / 40)]
    norm_num only [zero_pow, add_zero]
    exact Real.sqrt_sq (by positivity : 0 ≤ Δ / 40)
  have hnorm2 : ‖WithLp.toLp 2 ((0 : ℝ), Δ / 40)‖ = Δ / 40 := by
    rw [WithLp.prod_norm_eq_of_L2]
    change Real.sqrt (‖(0 : ℝ)‖ ^ 2 + ‖Δ / 40‖ ^ 2) = Δ / 40
    rw [norm_zero, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Δ / 40)]
    norm_num only [zero_pow, zero_add]
    exact Real.sqrt_sq (by positivity : 0 ≤ Δ / 40)
  refine ⟨⟨hx15, hxA, hxA'⟩, ⟨hq1, hq2⟩, fun y hy => (hfAt y (hbuf y hy).2.1).contMDiffWithinAt,
    fun y hy => (hηAt y hy).contMDiffWithinAt, ?_, ?_, ?_, ?_⟩
  · refine hanchorExists _ hnorm1 le_rfl ?_ ?_
    · change |(Q x).fst + Δ / 40| ≤ 100 * Δ
      have := abs_add_le (Q x).fst (Δ / 40)
      rw [abs_of_pos (by positivity : 0 < Δ / 40)] at this
      linarith [hQx.1]
    · change (Q x).snd + 0 ≤ 100 * Δ
      linarith [hQx.2.2]
  · refine hanchorExists _ hnorm2 (by change (0 : ℝ) ≤ Δ / 40; positivity) ?_ ?_
    · change |(Q x).fst + 0| ≤ 100 * Δ
      rw [add_zero]
      linarith [hQx.1]
    · change (Q x).snd + Δ / 40 ≤ 100 * Δ
      linarith [hQx.2.2]
  · -- LFR36.2, tangential half
    intro a ha hanchor y hy v hv X
    obtain ⟨hxy, hy16, -⟩ := hbuf y hy
    obtain ⟨h0lo, h0hi, hslope⟩ := edgeTangentialAnchor_slope hθpos hθ1 hθΔ hτθ hdist hx15
      ha hxy hanchor
    have ha200 : a ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) ha
    have hy200 : y ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) hy16
    have hslopeα : (1 - θ) * dist y a ≤ (α.toFun a).fst - (α.toFun y).fst := by
      rw [← hQα _ ha200, ← hQα _ hy200]
      exact hslope
    have hv1 : g.inner y v v = 1 := hv.1
    have hvend : intrinsicGeodesic g hEnorm y v (dist y a) = a := by
      have h := hv.2
      rw [Metric.infDist_singleton] at h
      exact h
    have hpin0 := hpinΔ σ θ b hσ hσσ₀ hθσ hb hbb₀ E H I M g hEnorm Y p y₀ α hsecb f hfL htest
      y hy16 ((hfAt y hy16).mdifferentiableAt (by simp)) a h0lo h0hi hslopeα v hv1 hvend X
    have hvX : |g.inner y v X| ≤ Real.sqrt (g.inner y X X) := by
      have hcs := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt (I := I) g y v X
      rw [hv1, Real.sqrt_one, one_mul] at hcs
      exact hcs
    have hmain := abs_mul_sub_le_of_abs_sub_le
      (by linarith : (0 : ℝ) ≤ ρ x) (by linarith : ρ x ≤ 2) hvX hpin0
    refine hmain.trans ?_
    gcongr
    linarith
  · -- LFR36.2, vertical half
    intro a ha hanchor
    have hCdiff : ∀ y ∈ closedBall p (20 * Δ) ∩
        {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
        MDifferentiableAt I 𝓘(ℝ, ℝ) F y :=
      fun y hy => (hFO.contMDiffAt (hO.mem_nhds (hCO hy))).mdifferentiableAt (by simp)
    exact edgeBand_vertical_gradient g hEnorm hA hΔ6 hτ0 hτ1 hQp hdist hheight hpA
      hborder hbordercover hx15 hxA hxA' ha hanchor hκ hκΔ hsec1000 hε hε1
      (by linarith) hFL hval hCdiff hFgrad hρ hρp hρs (by linarith) hbudget

end DifferentialGeometry.Geometry.Collapse
