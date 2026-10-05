import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalSlim
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChartValueTolerance

/-!
# The regional slim family with LFR19's separate value tolerance `vs` (lane BCG-2, review 51 Q4)

Review 51, question 4 (binding): the boundary slim value clause of BCG02 (`|η_j − u_j| < vs` with
`vs < min(v_closed, ϑ₃/4)`, register R17) is produced inside the REGIONAL slim producer by the
general LC85 producer with a separate value tolerance, `exists_slimChart_vs` (complete, σ-compact,
boundaryless carrier; no compactness), with ONE `choose` over the whole existence statement
(chart → formula cutoff → packet equality → `SlimCentreOn` with value and cutoff clauses). The
value clause is stated on `B(j, 10⁶Δρ(j))` only (not extrapolated beyond `L = 10⁶Δ`).

* `SlimCentreOn.coord_BCG2`: the slim coordinate `η_j` of a regional slim centre as a function on
  the carrier (packet projection; the twin of the closed `SlimCentre.coord`);
* `exists_regional_slimFamily_vs_BCG2`: `exists_regional_slimFamily_BDRY4` (same hypotheses, `vs`
  after `σs`) whose centres carry, besides the formula cutoff, the value clause.
The consumer is the enriched base family kernel (`LocalPacketsOnB`, LE/BoundaryPacketsB.lean).
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
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section SlimCoord

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

/-- The slim coordinate `η_j` of a regional slim centre, as a function on the carrier (the packet's
coordinate; twin of `SlimCentre.coord` with the carrier's own completeness). -/
def SlimCentreOn.coord_BCG2 {β₁ Δ σs : ℝ} {K : ℕ} {j : X}
    (S : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) : X → ℝ :=
  let P := S.packet
  letI := S.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  P.coord

end SlimCoord

/-- **The regional slim family with formula cutoffs and LFR19's separate value tolerance `vs`.**
`exists_regional_slimFamily_BDRY4` with the slim chart of `exists_slimChart_vs` (LFR19 at
`min vs (Δ/100)`): at every selected centre `j`, besides the formula cutoff, the slim coordinate
`η_j` stays within `vs` of the real component of the actual splitting on `B(j, 10⁶Δρ(j))`. Chart,
formula cutoff, packet equality and the centre with both clauses are produced inside ONE
existence statement, chosen once. The threshold `βS` depends only on `Δ, σs, vs, K, v, A`. -/
theorem exists_regional_slimFamily_vs_BCG2 {Δ σs vs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v)
    (Aprof : ℝ → ℝ) :
    ∃ βS : ℝ, 0 < βS ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] [ProperSpace X] [ConnectedSpace X]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
        ManifoldOrientation (𝓡 3) X 3 →
        ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) {Λ : ℝ}, 0 ≤ Λ →
        LipschitzWith (Real.toNNReal Λ) ρ → Δ * Λ * 2000000 ≤ 1 / 100 →
      ∀ (β : ℕ → ℝ), 0 < β 1 → β 1 < βS →
      ∀ (U₁ U₂ Kc : Set X), IsCompact Kc → U₁ ⊆ Kc →
      (∀ p ∈ U₁, ∀ y ∈ ball p ((β 1)⁻¹ * ρ p), SectionalBoundedBelowAt g y (-(β 1 / ρ p) ^ 2)) →
      (∀ p ∈ U₁, v ≤ (DifferentialGeometry.Geometry.Collapse.ballVolume
        (normalizedCenterMetric g (ρ p) (hρpos p)) p 1).toReal) →
      (∀ p ∈ U₁, ∀ R, 0 < R → R < (β 1)⁻¹ → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
          curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Aprof R) →
      (∀ p ∈ U₁, ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * (Δ * ρ p)),
        SectionalBoundedBelowAt g y (-((2000000 * (Δ * ρ p)) ^ 2)⁻¹)) →
      ∃ S : SlimFamilyOn X g hmetric ρ hρpos β Δ σs K U₁ U₂,
        ∀ j (hj : j ∈ S.centres),
          (let P := (S.centre j hj).packet
          letI := (S.centre j hj).instZ
          let hMc : CompleteSpace X := ‹CompleteSpace X›
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : CompleteSpace X :=
            (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
          P.cutoff = P.toSlimChart.formulaCutoff) ∧
          ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j), |(S.centre j hj).coord_BCG2 x -
            (letI := (S.centre j hj).instZ
             @KleinerLottApprox.toFun X (WithLp 2 (ℝ × (S.centre j hj).Z))
              (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j _ (β 1) (S.centre j hj).split
                x).fst| < vs := by
  classical
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨βs₀, hβs₀, hslimc⟩ := exists_slimChart_vs.{0, 0, 0, 0} hΔ1 hσs hσs1 hvs
  obtain ⟨βf, hβf, hfib⟩ := exists_slimPacket_threshold.{0, 0} hΔ1 hσs hσs1 K hK one_pos hv Aprof
  obtain ⟨βm, hβm, hmod⟩ :=
    slimChart_model_embedding_threshold.{0, 0} hΔ1 hσs hσs1 K hK one_pos hv Aprof
  refine ⟨min βs₀ (min βf βm), lt_min hβs₀ (lt_min hβf hβm), fun X mX _ _ _ _ _ _ g hmetric o ρ
    hρpos Λ hΛ hρlip hΛΔ β hβ1 hβ1b U₁ U₂ Kc hKc hU₁ hsecj hvol0 hder0 hsecs => ?_⟩
  have hβ1s : β 1 < βs₀ := hβ1b.trans_le (min_le_left _ _)
  have hβf1 : β 1 < βf := hβ1b.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβm1 : β 1 < βm := hβ1b.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  -- the Riemannian instances of the aligned metric
  let instRB : RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x) := ⟨g.toRiemannianMetric⟩
  have instCRB : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g
  have instRM : IsRiemannianManifold 𝓘(ℝ, E3) X := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
  have instM1 : IsManifold 𝓘(ℝ, E3) 1 X := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have instT2 : T2Space (TangentBundle 𝓘(ℝ, E3) X) := inferInstance
  -- the support-cover selection with `r = Δ ρ` among the slim points of `U₁ ∩ Z₁`
  have hrlip : LipschitzWith (Real.toNNReal (Δ * Λ)) (fun p => Δ * ρ p) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := hρlip.dist_le_mul x y
    rw [Real.coe_toNNReal _ hΛ] at h
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hΔpos, Real.coe_toNNReal _ (by positivity),
      mul_assoc]
    rw [Real.dist_eq] at h
    exact mul_le_mul_of_nonneg_left h hΔpos.le
  have hsmall : ((Real.toNNReal (Δ * Λ) : NNReal) : ℝ) * 2000000 ≤ 1 / 100 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact hΛΔ
  obtain ⟨Js, hJsS, hJsfin, hJsdisj, hJscov, hJsmult⟩ :=
    exists_simultaneous_support_cover_proper_BDRY3 g hEnorm finrank_euclideanSpace_fin hKc
      {p | p ∈ U₁ ∧ p ∈ scaledSplittingStratum.{0, 0} ρ hρpos β 1 ∧
        (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))}
      (fun x hx => hU₁ hx.1) hrlip (fun p => mul_pos hΔpos (hρpos p)) hsmall
      (fun p hp => hsecs p hp.1)
  -- the slim centres (as in the closed producer)
  have hscent : ∀ j ∈ Js, ∃ S : SlimCentreOn X g hmetric ρ hρpos (β 1) Δ σs K j,
      (let P := S.packet
      letI := S.instZ
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
      P.cutoff = P.toSlimChart.formulaCutoff) ∧
      ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j), |S.coord_BCG2 x -
        (letI := S.instZ
         @KleinerLottApprox.toFun X (WithLp 2 (ℝ × S.Z))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j _ (β 1) S.split x).fst| < vs := by
    intro j hj
    obtain ⟨hjU, -, Z, mZ, z, hbdd, hdiam, ⟨αs⟩⟩ := hJsS hj
    have hD : ∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ := fun y y' =>
      (dist_le_diam_of_mem hbdd (mem_univ y) (mem_univ y')).trans (by linarith)
    have hsecR := radialScaled_sectional_bound g (r := (β 1)⁻¹) (hρpos j) (hsecj j hjU)
    let hMc : CompleteSpace X := ‹CompleteSpace X›
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
    obtain ⟨c, hcv⟩ := hslimc (β 1) hβ1 hβ1s E3 E3 𝓘(ℝ, E3) X gR hnR Z j z αs hD hsecR
    have hmeq : normalizedCenterMetric g (ρ j) (hρpos j) = gR := by
      have key : ∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d), c = d →
          scaleMetric c hc g = scaleMetric d hd g := by
        rintro c d hc hd rfl
        rfl
      exact key _ _ _ _ (inv_pow (ρ j) 2).symm
    have hball : ∀ r, riemannianBallOf gR j r = ball j r := fun r =>
      DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hnR j r
    have hvol : ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) X gR (ball j 1) := by
      have h0 := hvol0 j hjU
      rw [hmeq] at h0
      rw [← hball 1]
      exact (ENNReal.ofReal_le_ofReal h0).trans ENNReal.ofReal_toReal_le
    have hcurv : ∀ R, 0 < R → R < (β 1)⁻¹ → ∀ k ≤ K, ∀ y ∈ ball j R,
        curvDerivNorm k gR y ≤ Aprof R := by
      intro R hR hRβ k hk y hy
      have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j R := by
        rw [hmeq, hball]
        exact hy
      have hd := hder0 j hjU R hR hRβ k hk y hy'
      rw [hmeq, curvatureDerivativeNorm_eq_curvDerivNorm] at hd
      exact hd
    have instPR : ProperSpace X :=
      properSpace_rescale_of_properSpace mX (ρ j)⁻¹ (inv_pos.mpr (hρpos j)) ‹_›
    let c' := c.withFormulaCutoffProper_BDRY4 hΔpos
    obtain ⟨-, hP⟩ := hfib (β 1) hβ1 hβf1 X gR hnR o j hvol hcurv hsecR Z z αs hD
    have hM := hmod (β 1) hβ1 hβm1 X gR hnR o j hvol hcurv hsecR Z z αs hD c'
    obtain ⟨P, hPc⟩ := hP c'
    obtain ⟨Mod⟩ := hM
    have hcut : P.cutoff = P.toSlimChart.formulaCutoff := by
      have h1 : P.cutoff = P.toSlimChart.cutoff := rfl
      rw [h1, hPc]
      rfl
    have hcoord : P.toSlimChart.coord = c.coord := by rw [hPc]; rfl
    refine ⟨@SlimCentreOn.mk X mX _ _ _ _ g hmetric ρ hρpos (β 1) Δ σs K j Z mZ z hD αs P
      (hPc ▸ Mod), hcut, fun x hx => ?_⟩
    have hxR : x ∈ @ball X mR.toPseudoMetricSpace j (10 ^ 6 * Δ) := by
      have hx' : @dist X mX.toDist x j < 10 ^ 6 * Δ * ρ j := hx
      change (ρ j)⁻¹ * @dist X mX.toDist x j < 10 ^ 6 * Δ
      rw [inv_mul_lt_iff₀ (hρpos j)]
      linarith
    change |P.toSlimChart.coord x - (αs.toFun x).fst| < vs
    rw [hcoord]
    exact hcv x hxR
  choose sc hsc using hscent
  exact ⟨{ centres := Js
           finite_centres := hJsfin
           centres_subset := hJsS
           disjoint_centres := hJsdisj
           covers := fun p hp hsl => hJscov p ⟨hp.1, hp.2, hsl⟩
           centre := sc
           multiplicity := hJsmult }, fun j hj => hsc j hj⟩

end DifferentialGeometry.Geometry.Collapse
