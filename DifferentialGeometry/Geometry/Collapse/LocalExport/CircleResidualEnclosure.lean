import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsProducer
import DifferentialGeometry.Geometry.Metric.CircleCoordinateEnclosure

/-!
# LFR07's residual bound for the circle charts (TCP01's `|η_i| ≤ 8 ⊂ D_i`)

Blueprint 207A, LFR07 (`cor:collapse-rank-two-circle-packet`, A:25322: "The actual residual
coordinate there has distance less than one from `y₀`", value error `< 1/10`) and 207B, TCP01
(`lem:fibration-first-comparison-list`, B:5250: "Every original point `|η_i| ≤ 8` lies in `D_i`",
proof B:5300: `d(p_i, q)/R_i < √((8 + 1/10)² + 1) + 1/10 < 10`).

`CircleChart` records LC83's two enclosures (`|η| < 100 ⇒ B(q, 102)`, `η = 0 ⇒ B(q, 2)`) but not
the residual bound itself. Here:
* `circlePacket_residual_enclosure`: the third enclosure `|η| ≤ 8 ⇒ B(q, 10)` from the same data as
  `circlePacket_enclosures` (a `β`-approximation `F` by `ℝ² × Y` with `β ≤ 1/200`, residual
  coordinate within `1` of `a` on `B(q, 200)`, `η` within `1/10` of `F₁`), through the TCP01 kernel
  `dist_lt_ten_of_circle_coordinate`;
* `exists_circleChart_with_tests_residual_at_scale_LC87`: the per-centre circle producer
  `exists_circleChart_with_tests_at_scale_LC87` with the residual enclosure of the produced chart
  added (thresholds folded with the residual threshold `exists_simultaneous_circle_residual_threshold`
  of the SAME two-dimensional model data, and `β ≤ 1/200`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **LFR07's residual enclosure.** Under the hypotheses of `circlePacket_enclosures`, every point of
`B(q, 200)` with `|η| ≤ 8` lies in `B(q, 10)`. -/
theorem circlePacket_residual_enclosure {M Y : Type*} [MetricSpace M] [MetricSpace Y] {q : M}
    {a : Y} {β : ℝ} (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β) (hβ : β ≤ 1 / 200)
    (hres : ∀ x ∈ ball q 200, dist (F.toFun x).snd a < 1) {η : M → ℝ²}
    (hclose : ∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < 1 / 10) :
    ∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → x ∈ ball q 10 := by
  intro x hx h8
  have hβpos := F.error_pos
  have h200 : (200 : ℝ) ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hβpos]
    linarith
  have hxβ : x ∈ ball q β⁻¹ := ball_subset_ball h200 hx
  have hq : q ∈ ball q β⁻¹ := mem_ball_self (inv_pos.mpr hβpos)
  have hdist := F.distortion x hxβ q hq
  have hp : (F.toFun q).fst = 0 := by
    rw [F.basepoint]
    rfl
  have hsnd : (F.toFun q).snd = a := by
    rw [F.basepoint]
    rfl
  refine mem_ball.mpr (dist_lt_ten_of_circle_coordinate F.toFun η hp ?_ ?_ (hclose x hx) h8)
  · exact hdist.trans_lt (by linarith)
  · rw [hsnd]
    exact (hres x hx).le

/-- **The per-centre circle producer with LFR07's residual enclosure.** The statement of
`exists_circleChart_with_tests_at_scale_LC87` with, in addition, the residual enclosure of the
produced chart at normalized scale: `|η| ≤ 8` on `B(j, 200)` forces `B(j, 10)`. -/
theorem exists_circleChart_with_tests_residual_at_scale_LC87 :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (j : X) (r : ℝ) (hr : 0 < r) {σ β : ℝ}, σ ≤ a₂ → β ≤ β₀ →
      (∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
        CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
        fourPointComparison 0 (univ : Set C) ∧
        (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox X C (mX.rescale r⁻¹ (inv_pos.mpr hr)) mC j c σ)) →
      ∀ (Y : Type) [mY : MetricSpace Y] (a : Y)
        (F : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y))
          (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ j
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a)) β),
      (∀ y ∈ ball j (β⁻¹ * r), SectionalBoundedBelowAt g y (-(β ^ 2 * r⁻¹ ^ 2))) →
      ∃ c : (letI := mX.rescale r⁻¹ (inv_pos.mpr hr); CircleChart 𝓘(ℝ, E3) X), ∃ ζc : X → ℝ,
        (letI := mX.rescale r⁻¹ (inv_pos.mpr hr);
          c.center = j ∧ (∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → ζc x = 1) ∧
          (∀ x, ζc x ≠ 0 → x ∈ ball j 200 ∧ ‖c.coord x‖ < 9) ∧
          tsupport ζc ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
            c.contMDiffOn_coord.continuousOn 100 : Set X) ∧ ζc = c.formulaCutoff ∧
          ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10) ∧
        ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ζc ∧ (∀ x, ζc x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ ball j (2 * r), ζc x = 1) ∧ tsupport ζc ⊆ ball j (200 * r) ∧
        (letI := mX.rescale r⁻¹ (inv_pos.mpr hr)
          ∀ x ∈ ball j 200, ‖c.coord x - (F.toFun x).fst‖ < γ) ∧
        (letI := mX.rescale r⁻¹ (inv_pos.mpr hr);
          LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball j 200)) ∧
        (let hMc : CompleteSpace X := complete_of_compact
        letI := mX.rescale r⁻¹ (inv_pos.mpr hr)
        letI := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric r⁻¹ (inv_pos.mpr hr)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff r⁻¹ (inv_pos.mpr hr)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
        ∀ x ∈ ball j 200, ∀ z ∈ ball j (201 * 10000), 201 < dist x z →
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x z) = z →
          ‖mvfderiv (I := 𝓘(ℝ, E3)) c.coord x w -
            (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < γ) := by
  obtain ⟨a₀, ha₀, -, hres⟩ := exists_simultaneous_circle_residual_threshold.{u, 0, 0}
  obtain ⟨a₂, ha₂, hK⟩ := exists_circleChart_with_tests_at_scale_LC87.{u}
  refine ⟨min a₂ a₀, lt_min ha₂ ha₀, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hK⟩ := hK γ hγ hγ1
  refine ⟨min β₀ (min a₀ (1 / 200)), lt_min hβ₀ (lt_min ha₀ (by norm_num)),
    le_min ((min_le_left _ _).trans hβ₀a) ((min_le_right _ _).trans (min_le_left _ _)),
    fun X mX _ _ _ g hmetric j r hr σ β hσ hβ hmodel Y mY a F hsec1 => ?_⟩
  obtain ⟨c, ζc, ⟨hcen, h8, hne, hts, hform⟩, hsm, h01, hpl, htsb, hadapt, hlip, htest⟩ :=
    hK X g hmetric j r hr (hσ.trans (min_le_left _ _)) (hβ.trans (min_le_left _ _)) hmodel Y a F
      hsec1
  refine ⟨c, ζc, ⟨hcen, h8, hne, hts, hform, ?_⟩, hsm, h01, hpl, htsb, hadapt, hlip, htest⟩
  obtain ⟨C, mC, cC, hCc, -, hCdim, hCcomp, hCseg, ⟨f⟩⟩ := hmodel
  let mR : MetricSpace X := mX.rescale r⁻¹ (inv_pos.mpr hr)
  have hres' : ∀ x ∈ ball j 200, dist (F.toFun x).snd a < 1 := fun x hx =>
    hres X j C cC (Metric.arbitrarily_short_curves_of_metric_segments hCseg) hCdim hCcomp Y a σ β
      (hσ.trans (min_le_right _ _)) (hβ.trans ((min_le_right _ _).trans (min_le_left _ _))) f F x
      ((mem_ball.mp hx).le.trans (by norm_num))
  exact circlePacket_residual_enclosure F
    (hβ.trans ((min_le_right _ _).trans (min_le_right _ _))) hres'
    (fun x hx => (hadapt x hx).trans hγ1)

end DifferentialGeometry.Geometry.Collapse
