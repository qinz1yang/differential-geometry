import DifferentialGeometry.Geometry.Collapse.SimultaneousAnnularStrainers
import DifferentialGeometry.Geometry.Collapse.EdgeNearestDirections
import DifferentialGeometry.Geometry.Collapse.SimultaneousCircleProduction

/-!
# The comparison tiers of F8 in their row forms: LCP03, LCP05, LPA03

Blueprint `master207A.tex`, Section "written comparison consumers" (A:29964–30260) and
"simultaneous local production" (A:30298–30440). The inputs of these rows now exist in the tree; the
rows are assembled here with the blueprint's quantifier order.

* `lcp03_original_radial_calibration` (**LCP03**, A:30063): LC69 with the ORIGINAL centre `p`, LC65's
  original constants (`δσ` explicit, curvature `-(1/60)²` on `B(p, 400)`), and the chosen outward
  point `z`: for EVERY point `x` of a minimizing segment from `q` to `z` (`t = d(q, x) ∈ (0, D]`),
  `0 ≤ D + t - d(p, x) < 2t(1 - cos θ)`; at every scale `λ > 0` (no upper bound, no `λδ` term)
  `λt - 2λt(1 - cos θ) < u(x) ≤ λt` with `u = λ(d(p, ·) - d(p, q))`; and on EVERY inward prefix
  (`d(q, x) + d(x, p) = d(q, p)`) `u(x) = -λ d(q, x)` exactly. From X77's
  `exists_simultaneous_original_annular_strainers` (whose comparison input is the eight-ball theorem
  applied to the sectional bound, not AC02).
* `lcp05_edge_nearest_directions` (**LCP05**, A:30177): ALL conclusions of LFR25 — (LFR25.2) on
  `B(p, 70Δ)`, and (LFR25.3), (LFR25.4) at every `x ∈ B(p, 30Δ)` with `Δ/2 ≤ d_A(x) ≤ 12Δ`, for EVERY
  nearest direction and EVERY minimizing direction to the outward point — under the ORIGINAL
  coarse-border hypotheses, `0 < τ < 10⁻⁴`, and `sec ≥ -κ²` on `B(p, 1000Δ)` with `κΔ ≤ 1/100` (the
  LFR25 hypotheses). The hinge comparison is the proved Riemannian one
  (`coarseBorder_nearest_directions`, W4-F7d1).
* `lpa03_circle_tolerance_precedes_noncollapse` (**LPA03**, A:30408): ONE `a₂ > 0` such that the metric
  tested-residual bound holds for all `σ, β < a₂` (`exists_simultaneous_circle_residual_threshold`)
  AND, for every coordinate quality `γ`, a `β₀ ≤ a₂` for which every actual `(2, β)`-splitting with
  `β ≤ β₀` and `sec ≥ -β²` on `B(q, β⁻¹)` gives the smooth circle packet of LFR07/LC83 (X77's
  `exists_early_simultaneous_circle_packet_parameters`). Both choices precede every manifold, hence
  `w'`, `v_*` and `𝒜`.

LCP02 is X77's `exists_simultaneous_original_annular_strainers` verbatim and LPA01 is X77's
`eventually_simultaneous_analytic_data` / `eventually_exists_simultaneous_analytic_scale` /
`eventually_simultaneous_common_test_range`; no new declaration is needed for them.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Real
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LCP03.** See the module docstring. -/
theorem lcp03_original_radial_calibration {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      let δσ := min (1 / 600 : ℝ) (min (1 / 60) ((1 - cos θ) / 600))
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)]
        [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M), IsMetricNorm g → ∀ p : M,
      (∀ y ∈ ball p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δσ →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∃ z : M, dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        (∀ x : M, 0 < dist q x → dist q x + dist x z = dist q z →
          0 ≤ dist q p + dist q x - dist p x ∧
          dist q p + dist q x - dist p x < 2 * dist q x * (1 - cos θ) ∧
          ∀ lam : ℝ, 0 < lam →
            lam * dist q x - 2 * (lam * dist q x) * (1 - cos θ) <
              lam * (dist p x - dist p q) ∧
            lam * (dist p x - dist p q) ≤ lam * dist q x) ∧
        ∀ x : M, dist q x + dist x p = dist q p → ∀ lam : ℝ,
          lam * (dist p x - dist p q) = -(lam * dist q x) := by
  obtain ⟨θ, hθ, hθone, -, h⟩ := exists_simultaneous_original_annular_strainers.{u, v}
    (E := E) (H := H) (I := I) hσ hσone
  refine ⟨θ, hθ, hθone, ?_⟩
  dsimp only at h ⊢
  intro M _ _ _ _ _ _ _ _ g hEnorm p hsec C _ o hC δ φ hδ q hq1 hq2
  obtain ⟨z, hz, he, -, hpref, -⟩ := h M g hEnorm p hsec C o hC φ hδ q hq1 hq2
  refine ⟨z, hz, he, fun x hx hxz => ?_, fun x hx lam => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hpref x hx hxz
    refine ⟨h0, h1, fun lam hlam => ?_⟩
    have h := h2 lam hlam
    rw [← mul_sub] at h
    exact h
  · have hpx : dist p x = dist p q - dist q x := by
      rw [dist_comm p x, dist_comm p q]
      linarith
    rw [hpx]
    ring

end Radial

section Edge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LCP05.** See the module docstring. -/
theorem lcp05_edge_nearest_directions (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {Δ τ κ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2)) :
    (∀ x ∈ ball p (70 * Δ), |infDist x A - (Q x).snd| ≤ 2 * (τ * Δ)) ∧
    ∀ x ∈ ball p (30 * Δ), Δ / 2 ≤ infDist x A → infDist x A ≤ 12 * Δ →
      (∃ y ∈ ball p (70 * Δ), |dist x y - infDist x A| ≤ 4 * (τ * Δ) ∧
        |infDist y A - 2 * infDist x A| ≤ 7 * (τ * Δ) ∧
        ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm y x,
          ∀ v ∈ minimizingDirectionsTo g hEnorm A x, g.inner x (v + w) (v + w) ≤ 200 * τ) ∧
      (∀ v ∈ minimizingDirectionsTo g hEnorm A x, ∀ v' ∈ minimizingDirectionsTo g hEnorm A x,
        Real.sqrt (g.inner x (v - v') (v - v')) ≤ 2 * Real.sqrt (200 * τ)) ∧
      2 * Real.sqrt (200 * τ) < 30 * Real.sqrt τ :=
  ⟨fun _ hx => coarseBorder_abs_infDist_sub_height_le hΔ (by linarith) hQp hdist hheight hpA hborder
      hbordercover hx,
    fun _ hx hlo hhi => coarseBorder_nearest_directions g hEnorm hΔ hτ hτsmall hQp hdist hheight
      hcover hpA hborder hbordercover hκ hκΔ hsec hx hlo hhi⟩

end Edge

/-- **LPA03.** See the module docstring. -/
theorem lpa03_circle_tolerance_precedes_noncollapse :
    ∃ a₂ : ℝ, 0 < a₂ ∧ a₂ < 1 / 10 ∧
      (∀ (Z : Type u) [MetricSpace Z] (z : Z)
          (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
        (∀ x y : C, ∀ e : ℝ, 0 < e →
          ∃ ξ : unitInterval → C, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
            eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) →
        dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
        ∀ (A : Type w) [MetricSpace A] (a : A) (σ β : ℝ), σ < a₂ → β < a₂ →
          KleinerLottApprox z c σ →
          ∀ F : KleinerLottApprox z (WithLp.toLp 2 ((0 : ℝ²), a)) β,
            ∀ x : Z, dist x z ≤ 201 → dist (F.toFun x).snd a < 1) ∧
      ∀ (γ : ℝ), 0 < γ → γ < 1 / 10 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (_hEnorm : IsMetricNorm (I := I) g)
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y),
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ ξ : unitInterval → C, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
          eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ {σ β : ℝ}, σ ≤ a₂ → β ≤ β₀ → KleinerLottApprox q c σ →
      ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      ∃ η : M → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200),
      ∃ hrank : ∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
        η q = 0 ∧ LipschitzOnWith 2 η (ball q 200) ∧
        (∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
        (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
        (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
        (let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
        ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
          (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
          (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
          ∀ R (hR : 0 < R) (hRr : R < 100),
            let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
            letI := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
              (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
            let U : TopologicalSpace.Opens
                (diskPreimageOpens (ball q 200) isOpen_ball η hη.continuousOn 100) :=
              ⟨f ⁻¹' planeBallInner 100 R,
                (planeBallInner 100 R).isOpen.preimage
                  (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
            ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                ({x // f x = y₀} × planeBallInner 100 R) U ∞),
              (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
        (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
          let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
          letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
            (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
          Nonempty (Circle ≃ₘ⟮𝓡 1,
            𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
        ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
          ∀ x, ζ x ≠ 0 → x ∈ ball q 200 ∧ ‖η x‖ < 9
 := by
  obtain ⟨η, hη, hη1, hres⟩ := exists_simultaneous_circle_residual_threshold.{u, v, w}
  obtain ⟨a₂, ha₂, hsm⟩ := exists_early_simultaneous_circle_packet_parameters.{uE, uH, u, v, w}
  refine ⟨min η a₂, lt_min hη ha₂, (min_le_left _ _).trans_lt hη1, ?_, ?_⟩
  · intro Z _ z C _ _ c hlen hdim hcomp A _ a σ β hσ hβ hφ F x hx
    exact hres Z z C c hlen hdim hcomp A a σ β ((hσ.trans_le (min_le_left _ _)).le)
      ((hβ.trans_le (min_le_left _ _)).le) hφ F x hx
  · intro γ hγ hγ1
    obtain ⟨β₀, hβ₀, -, h⟩ := hsm γ hγ hγ1
    refine ⟨min β₀ (min η a₂), lt_min hβ₀ (lt_min hη ha₂), min_le_right _ _, ?_⟩
    intro E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ q a C _ _ c hlen hdim hcomp σ β hσ hβ
      hφ F hsec
    exact h E H I M g hEnorm Y q a C c hlen hdim hcomp (hσ.trans (min_le_right _ _))
      (hβ.trans (min_le_left _ _)) hφ F hsec

end DifferentialGeometry.Geometry.Collapse
