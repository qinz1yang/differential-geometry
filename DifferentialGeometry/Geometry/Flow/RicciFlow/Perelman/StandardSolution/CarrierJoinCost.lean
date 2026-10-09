import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionJoin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionContinuity
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.MinimizerNonnegativity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow

section ActionLower

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem lRegAction_lower_of_rm_on_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T b : ℝ) (hb : 0 ≤ b)
    (hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ B)
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha) :
    (-2 * b ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B)) * b ≤
      lRegularizedAction S T alpha 0 b := by
  let F : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B
  have hF : 0 ≤ F := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg B)
  have hLag := lRegLag_integrable_on_carrier S hS.smoothMetric ⟨hS.scalarCont⟩
    T 0 b alpha halpha (by
      intro s hs
      exact hback s (by simpa only [uIcc_of_le hb] using hs))
  have hpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      -2 * b ^ 2 * F ≤ lRegularizedLagrangian S T alpha s := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
    have ht : T - s ^ 2 ∈ Icc (T - b ^ 2) T :=
      ⟨by linarith [hs2], sub_le_self T (sq_nonneg s)⟩
    have hscalar := scalar_abs_le_rm (I := I) (S.base.metric (T - s ^ 2)) (alpha s)
    have hscalar' : |S.scalar (T - s ^ 2) (alpha s)| ≤ F := by
      simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
        metricRm04_apply, F,
        show Module.finrank ℝ (TangentSpace I (alpha s)) = Module.finrank ℝ E by rfl]
        using hscalar.trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hRm _ ht (alpha s)))
            (sq_nonneg _))
    have hscalarLower : -F ≤ S.scalar (T - s ^ 2) (alpha s) :=
      neg_le_of_abs_le hscalar'
    have hpot := mul_le_mul_of_nonneg_left hscalarLower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg s))
    have hsq := mul_le_mul_of_nonneg_right hs2 hF
    have hkin : 0 ≤ (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) := by
      by_cases hv : lVelocity (I := I) alpha s = 0
      · rw [hv]
        simp
      · exact ((S.base.metric (T - s ^ 2)).pos (alpha s) _ hv).le
    change -2 * b ^ 2 * F ≤
      (1 / 2 : ℝ) * (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) +
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)
    nlinarith only [hkin, hpot, hsq]
  have hmono := intervalIntegral.integral_mono_on hb intervalIntegrable_const hLag hpoint
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  unfold lRegularizedAction
  simpa only [F, mul_comm b] using hmono

theorem lCost_competitors_bddBelow_of_rm_on_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (B T b : ℝ) (hb : 0 ≤ b) (x y : M)
    (hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B) :
    BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha 0 = x ∧ alpha (Real.sqrt (b ^ 2)) = y ∧
        lLength S T (squareRootReparametrization alpha) 0 (b ^ 2) = r} := by
  refine ⟨(-2 * b ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B)) * b, ?_⟩
  rintro r ⟨alpha, halpha, _hstart, _hend, hr⟩
  rw [← hr, lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha (b ^ 2) (sq_nonneg b), Real.sqrt_sq hb]
  exact lRegAction_lower_of_rm_on_carrier S hS B T b hb hback hRm alpha halpha

end ActionLower

section CostJoin

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lCost_le_join_on_carrier_of_bounded_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T b : ℝ) {c : ℝ} (hc : 0 < c) (hcb : c < b)
    (alpha beta : ℝ → M)
    (halpha : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 alpha (Icc (0 : ℝ) c))
    (hbeta : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 beta (Icc c b))
    (hnode : alpha c = beta c)
    (hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier)
    (hRm : ∃ B : ℝ, ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ B) :
    lCost S T (alpha 0) (beta b) (b ^ 2) ≤
      lRegularizedAction S T alpha 0 c + lRegularizedAction S T beta c b := by
  have hb : 0 < b := hc.trans hcb
  obtain ⟨B, hB⟩ := hRm
  have hcostSet := lCost_competitors_bddBelow_of_rm_on_carrier S hS B T b hb.le
    (alpha 0) (beta b) hback hB
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  obtain ⟨gamma, hgamma, hgamma0, hgammab, hgammaAct⟩ :=
    exists_lRegAction_join_lt_on_carrier S hS.smoothMetric ⟨hS.scalarCont⟩
      T b hc hcb alpha beta halpha hbeta hnode hback epsilon hepsilon
  have hlength : lLength S T (squareRootReparametrization gamma) 0 (b ^ 2) =
      lRegularizedAction S T gamma 0 b := by
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T gamma (b ^ 2) (sq_nonneg b), Real.sqrt_sq hb.le]
  have hcost : lCost S T (alpha 0) (beta b) (b ^ 2) ≤ lRegularizedAction S T gamma 0 b := by
    unfold lCost
    apply csInf_le hcostSet
    refine ⟨gamma, hgamma, hgamma0, ?_, hlength⟩
    simpa only [Real.sqrt_sq hb.le] using hgammab
  exact hcost.trans hgammaAct.le

end CostJoin

end DifferentialGeometry.PDE.RicciFlow

end
