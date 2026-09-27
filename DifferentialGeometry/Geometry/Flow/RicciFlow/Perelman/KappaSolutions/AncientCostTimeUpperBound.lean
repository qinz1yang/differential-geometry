import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import DifferentialGeometry.Topology.Manifold.ModelWithCorners

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology

section Scalar

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance timeRatioTopology : TopologicalSpace F.M := F.topology
local instance timeRatioCharted : ChartedSpace H F.M := F.charted
local instance timeRatioSmooth : IsManifold I ∞ F.M := F.smooth
local instance timeRatioC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance timeRatioT2 : T2Space F.M := F.t2
local instance timeRatioSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_scalar_le_of_time_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 0) (q : F.M) :
    F.S.scalar s q ≤ F.S.scalar t q := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨r, hr, x, hx⟩ := hF.notFlat
    exact finrank_ne_zero_of_normSq0S_ne_zero (F.S.base.metric r) x
      (by norm_num : 0 < 4) (F.S.base.rm04 r x) hx⟩
  have hcomplete : ∀ r ∈ ancientTimeInterval.regular,
      RiemannianMetricComplete (I := I) (F.S.base.metric r) :=
    fun r hr => ⟨hF.complete r (ancientTimeInterval.regular_subset hr)⟩
  have hR : ∀ r ∈ ancientTimeInterval.regular, ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro r hr x
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator r
      (ancientTimeInterval.regular_subset hr) x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  apply hamilton_ancient_scalar_two_time F.S F.isSolution hcomplete
    (ancientKappa_regularSlabBound_finrank F hF) hR hst
  intro r hr
  simpa only [ancientTimeInterval_regular, mem_Iio] using hr.trans_lt ht

end Scalar

section InnerProduct

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance timeRatioInnerTopology : TopologicalSpace F.M := F.topology
local instance timeRatioInnerCharted : ChartedSpace H F.M := F.charted
local instance timeRatioInnerSmooth : IsManifold I ∞ F.M := F.smooth
local instance timeRatioInnerC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance timeRatioInnerT2 : T2Space F.M := F.t2
local instance timeRatioInnerSigma : SigmaCompactSpace F.M := F.sigmaCompact

private theorem ancient_lCost_mul_cube_le_of_le_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a ^ 3 * lCost F.S 0 p q (b ^ 2) ≤ b ^ 3 * lCost F.S 0 p q (a ^ 2) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have hb : 0 < b := ha.trans hab
  obtain ⟨alpha, halpha, hstart, hend, hgeo, hcost⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q (sq_pos_of_pos ha)
  rw [Real.sqrt_sq ha.le] at hend hgeo hcost
  have henergy := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa
    F hF alpha halpha ha.le (fun r hr => hgeo r ⟨hr.1, hr.2.le⟩)
  rw [hcost, hend] at henergy
  have hspeed := metric_inner_self_nonneg (F.S.base.metric (-(a ^ 2))) (alpha a)
    (lVelocity (I := I) alpha a)
  dsimp only [lRegularizedLagrangian] at henergy
  rw [zero_sub, hend] at henergy
  rw [hend] at hspeed
  have hscalar : 2 * a ^ 3 * F.S.scalar (-(a ^ 2)) q ≤
      3 * lCost F.S 0 p q (a ^ 2) := by
    nlinarith [mul_nonneg ha.le hspeed]
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  have hback : ∀ r ∈ Icc (0 : ℝ) b, 0 - r ^ 2 ∈ ancientTimeInterval.carrier := by
    intro r _
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  have hRm : ∃ B : ℝ, ∀ t ∈ Icc (0 - b ^ 2) 0, ∀ y : F.M,
      normSq0S (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ B :=
    ⟨K, fun t ht y => hK t ht.2 y⟩
  have hjoin : lCost F.S 0 (alpha 0) q (b ^ 2) ≤
      lRegularizedAction F.S 0 alpha 0 a +
        lRegularizedAction F.S 0 (fun _ : ℝ => q) a b :=
    lCost_le_join_on_carrier_of_bounded_rm
      (I := I) (M := F.M) (D := ancientTimeInterval) F.S F.isSolution 0 b ha hab
      alpha (fun _ : ℝ => q) halpha.contMDiffOn contMDiffOn_const hend hback hRm
  rw [hstart, hcost, hend] at hjoin
  have hlag : lRegularizedLagrangian F.S 0 (fun _ => q) =
      fun r : ℝ => 2 * r ^ 2 * F.S.scalar (-(r ^ 2)) q := by
    funext r
    have hvel : lVelocity (I := I) (fun _ : ℝ => q) r = 0 := by
      simp only [lVelocity, mfderiv_const]
      rfl
    simp only [lRegularizedLagrangian, hvel, map_zero, mul_zero, zero_add, zero_sub]
  have hleft : IntervalIntegrable
      (fun r : ℝ => 2 * r ^ 2 * F.S.scalar (-(r ^ 2)) q) volume a b := by
    rw [← hlag]
    apply lRegLag_integrable_on_carrier F.S F.isSolution.smoothMetric
      ⟨F.isSolution.scalarCont⟩ 0 a b (fun _ => q) contMDiff_const
    intro r _
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  have hright : IntervalIntegrable
      (fun r : ℝ => 2 * r ^ 2 * F.S.scalar (-(a ^ 2)) q) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htail : lRegularizedAction F.S 0 (fun _ => q) a b ≤
      2 * F.S.scalar (-(a ^ 2)) q * (b ^ 3 - a ^ 3) / 3 := by
    have hint := intervalIntegral.integral_mono_on hab.le hleft hright
      (fun r hr => mul_le_mul_of_nonneg_left
        (ancient_scalar_le_of_time_le F hF
          (neg_le_neg ((pow_le_pow_left₀ ha.le hr.1 2)))
          (neg_neg_of_pos (sq_pos_of_pos ha)) q) (by positivity))
    change (∫ r in a..b, lRegularizedLagrangian F.S 0 (fun _ => q) r) ≤ _
    rw [hlag]
    refine hint.trans_eq ?_
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hcube : 0 ≤ b ^ 3 - a ^ 3 :=
    sub_nonneg.mpr (pow_le_pow_left₀ ha.le hab.le 3)
  have hscalar' := mul_le_mul_of_nonneg_right hscalar hcube
  have hjoin' := mul_le_mul_of_nonneg_left (hjoin.trans (add_le_add_right htail _))
    (pow_nonneg ha.le 3)
  nlinarith

end InnerProduct

section Normed

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance timeRatioTransferTopology : TopologicalSpace F.M := F.topology
local instance timeRatioTransferCharted : ChartedSpace H F.M := F.charted
local instance timeRatioTransferSmooth : IsManifold I ∞ F.M := F.smooth
local instance timeRatioTransferC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance timeRatioTransferT2 : T2Space F.M := F.t2
local instance timeRatioTransferSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_lCost_mul_cube_le_of_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a ^ 3 * lCost F.S 0 p q (b ^ 2) ≤ b ^ 3 * lCost F.S 0 p q (a ^ 2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  have h := ancient_lCost_mul_cube_le_of_le_of_innerProductSpace G hG p q ha hab
  have hcostA := lCost_pullback F.S Phi.symm 0 p q (a ^ 2)
  have hcostB := lCost_pullback F.S Phi.symm 0 p q (b ^ 2)
  change lCost (F.S.pullback Phi.symm) 0 p q (a ^ 2) = lCost F.S 0 p q (a ^ 2) at hcostA
  change lCost (F.S.pullback Phi.symm) 0 p q (b ^ 2) = lCost F.S 0 p q (b ^ 2) at hcostB
  change a ^ 3 * lCost (F.S.pullback Phi.symm) 0 p q (b ^ 2) ≤
    b ^ 3 * lCost (F.S.pullback Phi.symm) 0 p q (a ^ 2) at h
  rwa [hcostA, hcostB] at h

theorem ancient_redLength_le_mul_time_ratio_of_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau₁ tau₂ : ℝ} (h₁ : 0 < tau₁) (h₁₂ : tau₁ ≤ tau₂) :
    redLength F.S 0 p q tau₂ ≤
      (tau₂ / tau₁) * redLength F.S 0 p q tau₁ := by
  have h₂ : 0 < tau₂ := h₁.trans_le h₁₂
  have ha := Real.sqrt_pos.mpr h₁
  have hb := Real.sqrt_pos.mpr h₂
  have h := ancient_lCost_mul_cube_le_of_le F hF p q ha (Real.sqrt_le_sqrt h₁₂)
  rw [Real.sq_sqrt h₁.le, Real.sq_sqrt h₂.le] at h
  have ha3 : (Real.sqrt tau₁) ^ 3 = tau₁ * Real.sqrt tau₁ := by
    rw [pow_succ, Real.sq_sqrt h₁.le]
  have hb3 : (Real.sqrt tau₂) ^ 3 = tau₂ * Real.sqrt tau₂ := by
    rw [pow_succ, Real.sq_sqrt h₂.le]
  rw [ha3, hb3] at h
  unfold redLength
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt tau₂)).mpr
  have halgebra :
      (tau₂ / tau₁ * (lCost F.S 0 p q tau₁ / (2 * Real.sqrt tau₁))) *
          (2 * Real.sqrt tau₂) =
        (tau₂ * lCost F.S 0 p q tau₁ * (2 * Real.sqrt tau₂)) /
          (tau₁ * (2 * Real.sqrt tau₁)) := by
    field_simp
  rw [halgebra]
  apply (le_div_iff₀ (by positivity : 0 < tau₁ * (2 * Real.sqrt tau₁))).mpr
  nlinarith

end Normed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
