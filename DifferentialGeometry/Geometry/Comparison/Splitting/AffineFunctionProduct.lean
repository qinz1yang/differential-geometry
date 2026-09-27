import DifferentialGeometry.Geometry.Comparison.Splitting.AffineZeroLevelCharts
import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFlowRegularity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
  {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
  (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
  (hH : ∀ p, hessFun (I := I) g b p = 0)


def affineZeroLevelRetraction (x : M) : {p : M // b p = 0} :=
  ⟨affineGradientFlow (I := I) g hEnorm b x (-b x), by
    rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, add_neg_cancel]⟩


theorem affineZeroLevelRetraction_coe (x : M) :
    (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x : M) =
      affineGradientFlow (I := I) g hEnorm b x (-b x) := rfl


theorem affineZeroLevelRetraction_inclusion (p : {q : M // b q = 0}) :
    affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH p.1 = p := by
  apply Subtype.ext
  change affineGradientFlow (I := I) g hEnorm b p.1 (-b p.1) = p.1
  rw [p.property, neg_zero, affineGradientFlow_zero]

theorem affineZeroLevelRetraction_contMDiff (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ContMDiff I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ContMDiff I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞
    (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH)
  exact affineZeroLevel_corestrict_contMDiff (I := I) g hEnorm hb hunit hH p₀
    (fun x => affineGradientFlow (I := I) g hEnorm b x (-b x))
    ((affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).comp
      (hb.neg.prodMk contMDiff_id))
    (fun x => by
      rw [affineFunction_flow_eq_add (I := I) g hEnorm hb hunit hH, add_neg_cancel])

def affineFunctionZeroLevelDiffeomorph (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ({p : M // b p = 0} × ℝ) ≃ₘ⟮
      𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ), I⟯ M := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ({p : M // b p = 0} × ℝ) ≃ₘ⟮
    𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).prod 𝓘(ℝ, ℝ), I⟯ M
  refine
    { toEquiv := affineFunctionZeroLevelEquiv (I := I) g hEnorm hb hunit hH
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (affineGradientFlow_contMDiff (I := I) g hEnorm hb hunit hH).comp
      (contMDiff_snd.prodMk
        ((affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀).comp
          contMDiff_fst))
  · exact (affineZeroLevelRetraction_contMDiff (I := I) g hEnorm hb hunit hH p₀).prodMk hb


theorem affineFunctionZeroLevelDiffeomorph_apply
    (p₀ p : {q : M // b q = 0}) (t : ℝ) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀ (p, t) =
      affineGradientFlow (I := I) g hEnorm b p.1 t := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  rfl


theorem affineFunctionZeroLevelDiffeomorph_symm_apply
    (p₀ : {q : M // b q = 0}) (x : M) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    (affineFunctionZeroLevelDiffeomorph (I := I) g hEnorm hb hunit hH p₀).symm x =
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH x, b x) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  rfl

theorem affineZeroLevel_inclusion_mfderiv_leftInverse (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ p : {q : M // b q = 0}, Function.LeftInverse
      (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
        (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) p.1)
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I
        (Subtype.val : {q : M // b q = 0} → M) p) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ∀ p : {q : M // b q = 0}, Function.LeftInverse
    (mfderiv I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)
      (affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH) p.1)
    (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p)
  intro p v
  have h := mfderiv_comp_apply p
    ((affineZeroLevelRetraction_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
      (by simp) p.1)
    ((affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
      (by simp) p) v
  have hid : affineZeroLevelRetraction (I := I) g hEnorm hb hunit hH ∘
      (Subtype.val : {q : M // b q = 0} → M) = id :=
    funext (affineZeroLevelRetraction_inclusion (I := I) g hEnorm hb hunit hH)
  rw [hid, mfderiv_id] at h
  exact h.symm


theorem affineZeroLevel_inclusion_mfderiv_injective (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ p : {q : M // b q = 0}, Function.Injective
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I
        (Subtype.val : {q : M // b q = 0} → M) p) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  exact fun p =>
    (affineZeroLevel_inclusion_mfderiv_leftInverse (I := I) g hEnorm hb hunit hH p₀ p).injective

theorem affineZeroLevel_inclusion_mvfderiv_eq_zero (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ∀ (p : {q : M // b q = 0})
      (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p),
      mvfderiv (I := I) b p.1
        (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) = 0 := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ∀ (p : {q : M // b q = 0})
    (v : TangentSpace 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) p),
    mvfderiv (I := I) b p.1
      (mfderiv 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I Subtype.val p v) = 0
  intro p v
  have h := mfderiv_comp_apply p (hb.mdifferentiable (by simp) p.1)
    ((affineZeroLevel_inclusion_contMDiff (I := I) g hEnorm hb hunit hH p₀).mdifferentiable
      (by simp) p) v
  have hzero : b ∘ (Subtype.val : {q : M // b q = 0} → M) = fun _ => 0 :=
    funext Subtype.property
  rw [hzero, mfderiv_const, zero_apply] at h
  exact h.symm

end DifferentialGeometry.Geometry.Topology

end
