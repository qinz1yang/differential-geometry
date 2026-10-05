import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalCircle

/-!
# LC88 / BCP04, packets P4c / P5: the regional slim family (BDRY-4)

Review 45 §3.3–3.4: the slim half of the shared regionalised kernel. The closed producer
(`eventually_nonempty_localChartFamilyEA`, slim block) builds at every slim centre an LC85 slim
chart (`exists_slimChart`), replaces its cutoff by the formula cutoff, and obtains the slim packet
and the LC81 product model from the threshold producers (`exists_slimPacket_threshold`,
`slimChart_model_embedding_threshold`); the centres are the support-cover selection with
`r = Δρ`. All of these are statements about ONE complete σ-compact oriented carrier; here:

* `exists_regional_slimFamily_BDRY4`: on a complete, proper, σ-compact, connected, oriented carrier
  with a `Λ`-Lipschitz scale (`2·10⁶ΔΛ ≤ 1/100`), regions `U₁ ⊆ Kc` (`Kc` compact) and, at every
  point of `U₁`, the sectional buffer on `B(p, β₁⁻¹ρ(p))`, the LPA01 volume lower bound and
  derivative bounds of `ρ(p)⁻² g` (any profile `A`) and LC87's selection buffer: a
  `SlimFamilyOn … U₁ U₂` (candidates: slim points of `U₁ ∩ Z₁`) whose packet cutoffs are the
  formula cutoffs;
* `SlimChart.withFormulaCutoffProper_BDRY4`: the formula-cutoff replacement on a PROPER carrier.
The consumer is the assembly `exists_regional_chartFamilyEA_BDRY4` (BoundaryRegionalFamily).
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

section SlimProper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

open Classical in
/-- **The same slim chart with the formula cutoff on a PROPER carrier**
(`SlimChart.withFormulaCutoff` with `[ProperSpace M]` instead of `[CompactSpace M]`: the closed
support lies in a closed ball). -/
def SlimChart.withFormulaCutoffProper_BDRY4 [ProperSpace M] (c : SlimChart g hEnorm Δ σ α)
    (hΔ : 0 < Δ) :
    SlimChart g hEnorm Δ σ α :=
  have hval : ∀ x, c.formulaCutoff x = if x ∈ ball p (10 ^ 6 * Δ) then
      slimCutoffProfile_LC87 (c.coord x / (10 ^ 5 * Δ)) else 0 := fun x => by
    classical
    simp only [SlimChart.formulaCutoff, indicator_apply]
  have hsupp : ∀ x, c.formulaCutoff x ≠ 0 →
      x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| < 89 * 10 ^ 4 * Δ := by
    intro x hx
    classical
    rw [hval] at hx
    by_cases hxW : x ∈ ball p (10 ^ 6 * Δ)
    · refine ⟨hxW, ?_⟩
      simp only [hxW, ↓reduceIte] at hx
      have hl : (-89 / 10 : ℝ) < c.coord x / (10 ^ 5 * Δ) := by
        by_contra h
        exact hx (intervalPlateauProfile_zero_left (by norm_num) (not_lt.mp h))
      have hr : c.coord x / (10 ^ 5 * Δ) < 89 / 10 := by
        by_contra h
        exact hx (intervalPlateauProfile_zero_right (by norm_num) (not_lt.mp h))
      have hpos : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
      rw [lt_div_iff₀ hpos] at hl
      rw [div_lt_iff₀ hpos] at hr
      rw [abs_lt]
      constructor <;> linarith
    · simp only [hxW, ↓reduceIte] at hx
      exact absurd rfl hx
  let T : Set M := closedBall p (91 / 100 * (10 ^ 6 * Δ)) ∩ {x | |c.coord x| ≤ 89 * 10 ^ 4 * Δ}
  have hT : IsClosed T :=
    isClosed_closedBall.inter (isClosed_le (continuous_abs.comp c.lipschitz.continuous)
      continuous_const)
  have hsuppT : support c.formulaCutoff ⊆ T := by
    intro x hx
    obtain ⟨hxW, hx9⟩ := hsupp x hx
    exact ⟨(c.enclosure x hxW (by linarith)).le, hx9.le⟩
  have htsupp : tsupport c.formulaCutoff ⊆ T := closure_minimal hsuppT hT
  { c with
    cutoff := c.formulaCutoff
    contMDiff_cutoff := by
      classical
      intro x
      by_cases hxW : x ∈ ball p (10 ^ 6 * Δ)
      · have hdom : x ∈ c.domain := c.closedBall_subset_domain (ball_subset_closedBall hxW)
        have hη : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ c.coord x :=
          (c.contMDiffOn_coord x hdom).contMDiffAt (c.isOpen_domain.mem_nhds hdom)
        have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
            (fun y => slimCutoffProfile_LC87 (c.coord y / (10 ^ 5 * Δ))) x :=
          ((contDiff_intervalPlateauProfile _ _ _ _).contMDiff.contMDiffAt).comp x
            (hη.div_const _)
        refine hcomp.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_ball.mem_nhds hxW] with y hy
        rw [hval]; simp only [hy, ↓reduceIte]
      · have hxT : x ∉ T := fun h => hxW (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp h.1)
          (by nlinarith)))
        refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [hT.isOpen_compl.mem_nhds hxT] with y hy
        by_contra hne
        exact hy (hsuppT hne)
    hasCompactSupport_cutoff :=
      (isCompact_closedBall p (91 / 100 * (10 ^ 6 * Δ))).of_isClosed_subset
        (isClosed_tsupport _) (htsupp.trans inter_subset_left)
    cutoff_mem_Icc := by
      classical
      intro x
      rw [hval]
      by_cases hxW : x ∈ ball p (10 ^ 6 * Δ)
      · simp only [hxW, ↓reduceIte]
        exact intervalPlateauProfile_mem_Icc _ _ _ _ _
      · simp only [hxW, ↓reduceIte]
        exact ⟨le_rfl, zero_le_one⟩
    cutoff_eq_one := by
      classical
      intro x hxW hx8
      rw [hval]; simp only [hxW, ↓reduceIte]
      have hpos : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
      refine intervalPlateauProfile_one (by norm_num) (by norm_num) ⟨?_, ?_⟩
      · rw [le_div_iff₀ hpos]
        linarith [(abs_le.mp hx8).1]
      · rw [div_le_iff₀ hpos]
        linarith [(abs_le.mp hx8).2]
    cutoff_ne_zero := hsupp
    tsupport_cutoff := fun x hx => ⟨mem_closedBall.mp (htsupp hx).1, (htsupp hx).2⟩ }

end SlimProper

/-- **The regional slim family with formula cutoffs.** See the module docstring. The threshold
`βS` depends only on `Δ, σs, K, v, A`. -/
theorem exists_regional_slimFamily_BDRY4 {Δ σs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v) (Aprof : ℝ → ℝ) :
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
          let P := (S.centre j hj).packet
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
          P.cutoff = P.toSlimChart.formulaCutoff := by
  classical
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨βs₀, hβs₀, hslimc⟩ := exists_slimChart.{0, 0, 0, 0} hΔ1 hσs hσs1
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
      let P := S.packet
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
      P.cutoff = P.toSlimChart.formulaCutoff := by
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
    obtain ⟨c⟩ := hslimc (β 1) hβ1 hβ1s E3 E3 𝓘(ℝ, E3) X gR hnR Z j z αs hD hsecR
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
    exact ⟨@SlimCentreOn.mk X mX _ _ _ _ g hmetric ρ hρpos (β 1) Δ σs K j Z mZ z hD αs P
      (hPc ▸ Mod), hcut⟩
  choose sc hsc using hscent
  exact ⟨{ centres := Js
           finite_centres := hJsfin
           centres_subset := hJsS
           disjoint_centres := hJsdisj
           covers := fun p hp hsl => hJscov p ⟨hp.1, hp.2, hsl⟩
           centre := sc
           multiplicity := hJsmult }, hsc⟩

end DifferentialGeometry.Geometry.Collapse
