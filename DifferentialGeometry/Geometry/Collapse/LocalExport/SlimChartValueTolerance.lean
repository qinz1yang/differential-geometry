import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualProducer

/-!
# LFR19's separate slim value tolerance `v_s` along the LC85 → LC87 slim chain

Blueprint `master207B.tex`, SGP03 (B:4483–4600): "Use LFR19 with this separate `v_s`, not just
LFR20's default `Δ/100` bound" (B:4528), with `0 < v_s < θ/100` (B:4523). LFR19
(`exists_rankOne_coordinate_value_tolerance`) has a free value tolerance; the LC85 producer
`exists_slimChart` fixes it to `Δ/100`, and the structure field `SlimChart.value` records only that.
The three twins below keep, NEXT TO the same slim objects, the separate clause `|η − u| < v_s`:

* `exists_slimChart_vs`: `exists_slimChart` with LFR19 at the tolerance `min v_s (Δ/100)`; the same
  `SlimChart` plus `|c.coord − u| < v_s` on `B(p, L)`, `L = 10⁶Δ`;
* `exists_slimChart_at_centre_vs`: the same in the standing normalization `(R⁻¹d, R⁻²g)` (chart and
  clause; the ball clauses of `exists_slimChart_at_centre` are not needed by the LC87 centre);
* `exists_slimCentre_with_formula_threshold_vs`: `exists_slimCentre_with_formula_threshold_LC87`
  plus the clause on the PHYSICAL ball `B(j, Lρ(j))` for the coordinate `S.coord` and the actual
  splitting `S.split` of the LC87 slim centre (the coordinate is unchanged by the formula cutoff
  and by the LC85 packet, `SlimChart.withFormulaCutoff_coord`).

Design: `build-logs/resume/design-C14-SGP-vs.md` (steps 1–3).
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
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH u v

/-- **LC85's producer with LFR19's separate value tolerance `vs`.** The statement of
`exists_slimChart` with one more tolerance `vs > 0`: the slim chart can be chosen with
`|η − u| < vs` on `B(p, 10⁶Δ)` (LFR19 at the tolerance `min vs (Δ/100)`). -/
theorem exists_slimChart_vs {Δ σ vs : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100)
    (hvs : 0 < vs) :
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
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        (∀ y ∈ Metric.ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∃ c : SlimChart g hEnorm Δ σ α,
          ∀ x ∈ Metric.ball p (10 ^ 6 * Δ), |c.coord x - (α.toFun x).fst| < vs := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨β₁, hβ₁, h19⟩ := exists_rankOne_coordinate_value_tolerance
    (L := 10 ^ 6 * Δ) (T := 10 ^ 6 * Δ / σ) (e := min vs (Δ / 100)) (σ := σ) (by positivity)
    (by rw [lt_div_iff₀ hσ]; nlinarith) (lt_min hvs (by positivity)) hσ (by linarith)
  refine ⟨min β₁ (1 / (10 ^ 8 * Δ)), lt_min hβ₁ (by positivity), ?_⟩
  intro β hβ hβ₀ E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α hD hsec
  have hβΔ : β * (10 ^ 8 * Δ) ≤ 1 := by
    have h := (hβ₀.trans_le (min_le_right _ _)).le
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨η, O, hO, hLO, hη, hηp, hηl, hval, -, -, htest⟩ :=
    h19 β hβ (hβ₀.trans_le (min_le_left _ _)) E H I M g hEnorm Y p y₀ α hsec
  exact ⟨SlimChart.ofCoordinate g hEnorm hΔ hσ hσ1 hβΔ α hD η O hO hLO hη hηp hηl
    (fun x hx => (hval x hx).trans_le (min_le_right _ _)) htest,
    fun x hx => (hval x hx).trans_le (min_le_left _ _)⟩

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **An LC85 slim chart at a slim centre with the value tolerance `vs`, in the standing
convention.** `exists_slimChart_at_centre` (chart only) with the clause `|η − u| < vs` on the
normalized ball `B(p, 10⁶Δ)` of `(R⁻¹d, R⁻²g)`. -/
theorem exists_slimChart_at_centre_vs {Δ σs vs : ℝ} (hΔ : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
    ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
      (g : SmoothRiemannianMetric I M)
      (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b))
      (R : ℝ) (hR : 0 < R) (p : M) (A : Type v) [MetricSpace A] (a : A),
      (∀ y z : A, dist y z ≤ 10 ^ 3 * Δ) →
      ∀ α : @KleinerLottApprox M (WithLp 2 (ℝ × A)) (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p
        (WithLp.toLp 2 ((0 : ℝ), a)) β,
      (∀ z ∈ ball p (β⁻¹ * R), SectionalBoundedBelowAt g z (-(β / R) ^ 2)) →
      let hMc : CompleteSpace M := complete_of_compact
      letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold I M :=
        radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
      ∃ c : SlimChart gR hnR Δ σs α,
        ∀ x ∈ ball p (10 ^ 6 * Δ), |c.coord x - (α.toFun x).fst| < vs := by
  obtain ⟨β₀, hβ₀, h⟩ := exists_slimChart_vs.{uE, uH, u, v} hΔ hσs hσs1 hvs
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ M m _ _ _ g hmetric R hR p A _ a hD α hsec => ?_⟩
  have hsecR := radialScaled_sectional_bound g (r := β⁻¹) hR hsec
  intro hMc
  let mR : MetricSpace M := m.rescale R⁻¹ (inv_pos.mpr hR)
  let bR := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let cR : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let iR : IsRiemannianManifold I M :=
    radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
  let kR : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  intro gR hnR
  exact h β hβ hββ₀ E H I M gR hnR A p a α hD hsecR

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **An LC87 slim centre with the formula cutoff and LFR19's separate value tolerance `vs`
(threshold form).** `exists_slimCentre_with_formula_threshold_LC87` with one more tolerance
`vs > 0`: the centre can be chosen with `|η_j − u_j| < vs` on the physical ball `B(j, 10⁶Δρ(j))`
(`η_j = S.coord`, `u_j` the first component of the actual splitting `S.split`). -/
theorem exists_slimCentre_with_formula_threshold_vs {Δ σs vs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v)
    (𝒜 : ℝ → ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β₁ : ℝ, 0 < β₁ → β₁ < β₀ →
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
        ManifoldOrientation (𝓡 3) X 3 →
      ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) (j : X) (a : ℝ), 4 * β₁⁻¹ + 4 < a →
        (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
            (WithLp.toLp 2 ((0 : ℝ), z)) β₁)) →
        (∀ x ∈ ball j (β₁⁻¹ * ρ j), SectionalBoundedBelowAt g x (-(β₁ / ρ j) ^ 2)) →
        (0 < v ∧ v ≤ (ballVolume (normalizedCenterMetric g (ρ j) (hρpos j)) j 1).toReal ∧
          (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j (a / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ j) (hρpos j)) y
              (-((a / 4) ^ 2)⁻¹)) ∧
          ∀ R, 0 < R → 2 * R + 2 < a → ∀ k ≤ K,
            ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j R,
              curvatureDerivativeNorm (normalizedCenterMetric g (ρ j) (hρpos j)) k y ≤ 𝒜 R) →
        ∃ S : SlimCentre X g hmetric ρ hρpos β₁ Δ σs K j,
          (let P := S.packet
          letI := S.instZ
          let hMc : CompleteSpace X := complete_of_compact
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : CompleteSpace X :=
            (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
          P.cutoff = P.toSlimChart.formulaCutoff) ∧
          ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j), |S.coord x -
            (letI := S.instZ
             @KleinerLottApprox.toFun X (WithLp 2 (ℝ × S.Z))
              (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j _ β₁ S.split x).fst| < vs := by
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨βs₀, hβs₀, hslimc⟩ :=
    exists_slimChart_at_centre_vs.{0, 0, 0, 0} (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) hΔ1 hσs hσs1
      hvs
  obtain ⟨βf, hβf, hfib⟩ := exists_slimPacket_threshold.{0, 0} hΔ1 hσs hσs1 K hK one_pos hv 𝒜
  obtain ⟨βm, hβm, hmod⟩ := slimChart_model_embedding_threshold.{0, 0} hΔ1 hσs hσs1 K hK one_pos
    hv 𝒜
  refine ⟨min βs₀ (min βf βm), lt_min hβs₀ (lt_min hβf hβm),
    fun β₁ hβ1 hβ1b X mX _ _ _ g hmetric o ρ hρpos j a hαβ hJ hsecj hdata => ?_⟩
  have hβ1s : β₁ < βs₀ := hβ1b.trans_le (min_le_left _ _)
  have hβf1 : β₁ < βf := hβ1b.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβm1 : β₁ < βm := hβ1b.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hβinv : 0 < β₁⁻¹ := inv_pos.mpr hβ1
  obtain ⟨Z, mZ, z, hbdd, hdiam, ⟨αs⟩⟩ := hJ
  have hD : ∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ := fun y y' =>
    (dist_le_diam_of_mem hbdd (mem_univ y) (mem_univ y')).trans (by linarith)
  obtain ⟨c, hcv⟩ := hslimc β₁ hβ1 hβ1s X g hmetric (ρ j) (hρpos j) j Z z hD αs hsecj
  obtain ⟨-, hvol0, hsec0, hder0⟩ := hdata
  have hconn0 : ConnectedSpace X := connectedSpace_of_aligned_metric g hmetric j
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hconn : ConnectedSpace X := hconn0
  have hmeq : normalizedCenterMetric g (ρ j) (hρpos j) = gR := by
    have key : ∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d), c = d →
        scaleMetric c hc g = scaleMetric d hd g := by
      rintro c d hc hd rfl
      rfl
    exact key _ _ _ _ (inv_pow (ρ j) 2).symm
  have hball : ∀ r, riemannianBallOf gR j r = ball j r := fun r =>
    DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hnR j r
  have hvol : ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) X gR (ball j 1) := by
    rw [hmeq] at hvol0
    rw [← hball 1]
    exact (ENNReal.ofReal_le_ofReal hvol0).trans ENNReal.ofReal_toReal_le
  have hsec : ∀ y ∈ ball j β₁⁻¹, SectionalBoundedBelowAt gR y (-β₁ ^ 2) := by
    intro y hy
    have hq : β₁⁻¹ ≤ a / 4 := by linarith
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j
        (a / 4) := by
      rw [hmeq, hball]
      exact ball_subset_ball hq hy
    have hs := hsec0 y hy'
    rw [hmeq] at hs
    refine hs.mono ?_
    rw [neg_le_neg_iff, ← inv_pow]
    have hα4 : 0 < a / 4 := hβinv.trans_le hq
    have hinv : (a / 4)⁻¹ ≤ β₁ := by
      rw [inv_le_comm₀ hα4 hβ1]
      exact hq
    exact pow_le_pow_left₀ (inv_pos.mpr hα4).le hinv 2
  have hcurv : ∀ R, 0 < R → R < β₁⁻¹ → ∀ k ≤ K, ∀ y ∈ ball j R,
      curvDerivNorm k gR y ≤ 𝒜 R := by
    intro R hR hRβ k hk y hy
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j R := by
      rw [hmeq, hball]
      exact hy
    have hd := hder0 R hR (by linarith) k hk y hy'
    rw [hmeq, curvatureDerivativeNorm_eq_curvDerivNorm] at hd
    exact hd
  let c' := c.withFormulaCutoff hΔpos
  obtain ⟨-, hP⟩ := hfib β₁ hβ1 hβf1 X gR hnR o j hvol hcurv hsec Z z αs hD
  have hM := hmod β₁ hβ1 hβm1 X gR hnR o j hvol hcurv hsec Z z αs hD c'
  obtain ⟨P, hPc⟩ := hP c'
  obtain ⟨Mod⟩ := hM
  have hcut : P.cutoff = P.toSlimChart.formulaCutoff := by
    have h1 : P.cutoff = P.toSlimChart.cutoff := rfl
    rw [h1, hPc]
    rfl
  have hcoord : P.toSlimChart.coord = c.coord := by rw [hPc]; rfl
  refine ⟨@SlimCentre.mk X mX _ _ _ g hmetric ρ hρpos β₁ Δ σs K j Z mZ z hD αs
    P (hPc ▸ Mod), hcut, fun x hx => ?_⟩
  have hxR : x ∈ @ball X mR.toPseudoMetricSpace j (10 ^ 6 * Δ) := by
    have hx' : @dist X mX.toDist x j < 10 ^ 6 * Δ * ρ j := hx
    change (ρ j)⁻¹ * @dist X mX.toDist x j < 10 ^ 6 * Δ
    rw [inv_mul_lt_iff₀ (hρpos j)]
    linarith
  change |P.toSlimChart.coord x - (αs.toFun x).fst| < vs
  rw [hcoord]
  exact hcv x hxR

end DifferentialGeometry.Geometry.Collapse
