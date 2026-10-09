import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostDistanceSlope

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance localRicciTopology : TopologicalSpace F.M := F.topology
local instance localRicciCharted : ChartedSpace H F.M := F.charted
local instance localRicciSmooth : IsManifold I ∞ F.M := F.smooth
local instance localRicciC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance localRicciT2 : T2Space F.M := F.t2
local instance localRicciSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ricciTensor_le_of_sqrt_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p z : F.M) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (hscalar : F.S.scalar (-s) z ≤ 3 * redLength F.S 0 p z s / s)
    (hell : Real.sqrt (redLength F.S 0 p z s) ≤ B)
    (v : TangentSpace I z) :
    ricciTensor (F.S.base.metric (-s)) z v v ≤
      3 * B ^ 2 / s * (F.S.base.metric (-s)).inner z v v := by
  have htime : -s ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact neg_nonpos.mpr hs.le
  have hop : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric (-s)) z ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c u w
    have h := hF.nonnegativeCurvatureOperator (-s) htime z n c u w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hnonneg : 0 ≤ redLength F.S 0 p z s := by
    unfold redLength
    refine div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 hs.le ?_ p z) (by positivity)
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro t ht y
    exact (hC (0-t) (by simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using neg_nonpos.mpr ht.1) y).1
  have hellsq : redLength F.S 0 p z s ≤ B ^ 2 := by
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (redLength F.S 0 p z s)]
  have hR : metricScalarAt (I := I) (F.S.base.metric (-s)) z ≤ 3 * B ^ 2 / s :=
    hscalar.trans ((div_le_div_iff_of_pos_right hs).mpr (by linarith))
  have hRhalf : metricScalarAt (I := I) (F.S.base.metric (-s)) z / 2 ≤ 3 * B ^ 2 / s := by
    have hnonnegBound : 0 ≤ 3 * B ^ 2 / s := by positivity
    linarith
  have hric := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
    (F.S.base.metric (-s)) z hop v
  rw [metricRicciAt_apply_eq_ricciTensor] at hric
  exact hric.trans (mul_le_mul_of_nonneg_right hRhalf (metric_inner_self_nonneg _ _ _))

omit [I.Boundaryless] in
theorem sqrt_redLength_le_on_ball_of_lipschitz
    (p x z : F.M) {s A : ℝ} (hs : 0 < s) (hA : 0 ≤ A)
    (hcenter : Real.sqrt (redLength F.S 0 p x s) ≤ A)
    (hlip : Real.sqrt (redLength F.S 0 p z s) ≤ Real.sqrt (redLength F.S 0 p x s) +
      Real.sqrt 3 / (2 * Real.sqrt s) * (riemannianEDistOf (F.S.base.metric (-s)) x z).toReal)
    (hball : riemannianEDistOf (F.S.base.metric (-s)) x z <
      ENNReal.ofReal (Real.sqrt s / (1 + A))) :
    Real.sqrt (redLength F.S 0 p z s) ≤ 1 + A := by
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hB : 0 < 1 + A := by linarith
  have hdist := ENNReal.toReal_lt_of_lt_ofReal hball
  have hs3 : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hcoef : 0 ≤ Real.sqrt 3 / (2 * Real.sqrt s) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hdist.le hcoef
  have heq : Real.sqrt 3 / (2 * Real.sqrt s) * (Real.sqrt s / (1 + A)) =
      Real.sqrt 3 / (2 * (1 + A)) := by field_simp [hsqrt.ne', hB.ne']
  rw [heq] at hstep
  have hsmall : Real.sqrt 3 / (2 * (1 + A)) ≤ 1 := by
    apply (div_le_one (mul_pos (by norm_num) hB)).mpr
    linarith
  linarith

omit [I.Boundaryless] in
theorem sqrt_redLength_le_of_prefix_bound
    (p x y : F.M) {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau)
    (hprefix : redLength F.S 0 p x s ≤
      (Real.sqrt tau / Real.sqrt s) * redLength F.S 0 p y tau) :
    Real.sqrt (redLength F.S 0 p x s) ≤
      tau ^ ((1 / 4) : ℝ) * s ^ (-(1 / 4) : ℝ) *
        Real.sqrt (redLength F.S 0 p y tau) := by
  have h := Real.sqrt_le_sqrt hprefix
  rw [Real.sqrt_mul (div_nonneg (Real.sqrt_nonneg tau) (Real.sqrt_nonneg s)),
    Real.sqrt_div (Real.sqrt_nonneg tau)] at h
  have hquarter (t : ℝ) (ht : 0 ≤ t) : Real.sqrt (Real.sqrt t) = t ^ ((1 / 4) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
    norm_num
  rw [hquarter tau htau.le, hquarter s hs.le] at h
  have hinv : (s ^ ((1 / 4) : ℝ))⁻¹ = s ^ (-(1 / 4) : ℝ) := by
    rw [Real.rpow_neg hs.le]
  rw [div_eq_mul_inv, hinv] at h
  exact h

theorem ricciTensor_le_on_endpoint_balls_of_sqrt_redLength_lipschitz
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p x₁ x₂ q₁ q₂ : F.M) {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau)
    (hprefix₁ : redLength F.S 0 p x₁ s ≤
      (Real.sqrt tau / Real.sqrt s) * redLength F.S 0 p q₁ tau)
    (hprefix₂ : redLength F.S 0 p x₂ s ≤
      (Real.sqrt tau / Real.sqrt s) * redLength F.S 0 p q₂ tau)
    (hscalar : ∀ z, F.S.scalar (-s) z ≤ 3 * redLength F.S 0 p z s / s)
    (hlip : ∀ x y, Real.sqrt (redLength F.S 0 p y s) ≤ Real.sqrt (redLength F.S 0 p x s) +
      Real.sqrt 3 / (2 * Real.sqrt s) * (riemannianEDistOf (F.S.base.metric (-s)) x y).toReal) :
    let B := 1 + tau ^ ((1 / 4) : ℝ) * s ^ (-(1 / 4) : ℝ) *
      (Real.sqrt (redLength F.S 0 p q₁ tau) + Real.sqrt (redLength F.S 0 p q₂ tau))
    ∀ z : F.M, ∀ v : TangentSpace I z,
      (riemannianEDistOf (F.S.base.metric (-s)) x₁ z < ENNReal.ofReal (Real.sqrt s / B) ∨
        riemannianEDistOf (F.S.base.metric (-s)) x₂ z < ENNReal.ofReal (Real.sqrt s / B)) →
      ricciTensor (F.S.base.metric (-s)) z v v ≤
        3 * B ^ 2 / s * (F.S.base.metric (-s)).inner z v v := by
  let c := tau ^ ((1 / 4) : ℝ) * s ^ (-(1 / 4) : ℝ)
  let A := c * (Real.sqrt (redLength F.S 0 p q₁ tau) + Real.sqrt (redLength F.S 0 p q₂ tau))
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg htau.le _) (Real.rpow_nonneg hs.le _)
  have hA : 0 ≤ A := mul_nonneg hc (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hcenter₁ : Real.sqrt (redLength F.S 0 p x₁ s) ≤ A := by
    have h := sqrt_redLength_le_of_prefix_bound F p x₁ q₁ hs htau hprefix₁
    have hother := mul_nonneg hc (Real.sqrt_nonneg (redLength F.S 0 p q₂ tau))
    change _ ≤ c * Real.sqrt (redLength F.S 0 p q₁ tau) at h
    dsimp only [A]
    nlinarith
  have hcenter₂ : Real.sqrt (redLength F.S 0 p x₂ s) ≤ A := by
    have h := sqrt_redLength_le_of_prefix_bound F p x₂ q₂ hs htau hprefix₂
    have hother := mul_nonneg hc (Real.sqrt_nonneg (redLength F.S 0 p q₁ tau))
    change _ ≤ c * Real.sqrt (redLength F.S 0 p q₂ tau) at h
    dsimp only [A]
    nlinarith
  change ∀ z : F.M, ∀ v : TangentSpace I z,
    (riemannianEDistOf (F.S.base.metric (-s)) x₁ z < ENNReal.ofReal (Real.sqrt s / (1+A)) ∨
      riemannianEDistOf (F.S.base.metric (-s)) x₂ z < ENNReal.ofReal (Real.sqrt s / (1+A))) →
    ricciTensor (F.S.base.metric (-s)) z v v ≤ 3 * (1+A)^2 / s * (F.S.base.metric (-s)).inner z v v
  intro z v hz
  apply ricciTensor_le_of_sqrt_redLength_le F hF p z hs (by linarith) (hscalar z) _ v
  rcases hz with hz | hz
  · exact sqrt_redLength_le_on_ball_of_lipschitz F p x₁ z hs hA hcenter₁ (hlip x₁ z) hz
  · exact sqrt_redLength_le_on_ball_of_lipschitz F p x₂ z hs hA hcenter₂ (hlip x₂ z) hz

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
