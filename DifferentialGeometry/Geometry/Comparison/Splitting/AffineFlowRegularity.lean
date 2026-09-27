import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFunctionFlow
import DifferentialGeometry.Geometry.Comparison.Soul.SoulFlow
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem affineFunctionZeroLevel_completeSpace
    {X : Type*} [MetricSpace X] [CompleteSpace X] {b : X → ℝ}
    (hb : Continuous b) : CompleteSpace {p : X // b p = 0} :=
  (isClosed_eq hb continuous_const).isComplete.completeSpace_coe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem affineGradientFlow_contMDiff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun z : ℝ × M => affineGradientFlow (I := I) g hEnorm b z.2 z.1) := by
  let V : Cₛ^∞⟮I; E, TangentSpace I⟯ :=
    ⟨fun x => gradientFun (I := I) g b x, gradientFun_smooth (I := I) g hb⟩
  have hc : ∀ p : M, ∃ γ : ℝ → M, γ 0 = p ∧ IsMIntegralCurve γ V := by
    intro p
    exact ⟨affineGradientFlow (I := I) g hEnorm b p,
      affineGradientFlow_zero (I := I) g hEnorm b p,
      affineGradientFlow_isMIntegralCurve (I := I) g hEnorm hb hunit hH p⟩
  have heq (p : M) : curveAt V hc p = affineGradientFlow (I := I) g hEnorm b p := by
    apply isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (V.contMDiff.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
      (curveAt_integralCurve V hc p)
      (affineGradientFlow_isMIntegralCurve (I := I) g hEnorm hb hunit hH p)
    rw [curveAt_zero, affineGradientFlow_zero]
  simpa only [heq] using contMDiff_curveAt_joint V hc


theorem affineGradientFlow_slice_contMDiff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (t : ℝ) :
    ContMDiff I I ∞ (fun p => affineGradientFlow (I := I) g hEnorm b p t) :=
  (affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).comp
    (contMDiff_const.prodMk contMDiff_id)

def affineGradientFlowDiffeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (t : ℝ) : M ≃ₘ⟮I, I⟯ M where
  toEquiv :=
    { toFun := fun p => affineGradientFlow (I := I) g hEnorm b p t
      invFun := fun p => affineGradientFlow (I := I) g hEnorm b p (-t)
      left_inv := fun p => by
        change affineGradientFlow (I := I) g hEnorm b
          (affineGradientFlow (I := I) g hEnorm b p t) (-t) = p
        rw [← affineGradientFlow_add (I := I) g hEnorm hb hunit hH,
          neg_add_cancel, affineGradientFlow_zero]
      right_inv := fun p => by
        change affineGradientFlow (I := I) g hEnorm b
          (affineGradientFlow (I := I) g hEnorm b p (-t)) t = p
        rw [← affineGradientFlow_add (I := I) g hEnorm hb hunit hH,
          add_neg_cancel, affineGradientFlow_zero] }
  contMDiff_toFun := affineGradientFlow_slice_contMDiff (I := I) g hEnorm hb hunit hH t
  contMDiff_invFun := affineGradientFlow_slice_contMDiff (I := I) g hEnorm hb hunit hH (-t)

def affineFunctionZeroLevelHomeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) :
    ({p : M // b p = 0} × ℝ) ≃ₜ M where
  toEquiv := affineFunctionZeroLevelEquiv (I := I) g hEnorm hb hunit hH
  continuous_toFun :=
    (affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).continuous.comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    apply Continuous.prodMk _ hb.continuous
    apply Continuous.subtype_mk
    exact (affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).continuous.comp
      (hb.continuous.neg.prodMk continuous_id)

theorem affineFunctionZeroLevel_connectedSpace [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (hH : ∀ p, hessFun (I := I) g b p = 0) :
    ConnectedSpace {p : M // b p = 0} := by
  let e := affineFunctionZeroLevelHomeomorph (I := I) g hEnorm hb hunit hH
  have hsurj : Function.Surjective (fun x : M => (e.symm x).1) := by
    intro y
    refine ⟨e (y, 0), ?_⟩
    change (e.symm (e (y, 0))).1 = y
    rw [e.symm_apply_apply]
  exact hsurj.connectedSpace e.symm.continuous.fst

end DifferentialGeometry.Geometry.Topology

end
