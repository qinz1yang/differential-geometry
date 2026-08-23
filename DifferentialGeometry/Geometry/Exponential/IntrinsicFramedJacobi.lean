import DifferentialGeometry.Geometry.Exponential.EndpointShape
import DifferentialGeometry.Geometry.Exponential.ExpInvBranch
import DifferentialGeometry.Geometry.Exponential.IntrinsicFramedCoordinates

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrFrame_deriv
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z v : E) :
    mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) g hEnorm p) z v =
      intrinsicJacobi (I := I) g hEnorm p
        (normalFrame (I := I) g p z)
        (normalFrame (I := I) g p v) 1 := by
  simpa only [intrinsicJacobi] using
    (intrFrame_mfderiv (I := I) g hEnorm p z v)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intr_metric_jacobi
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z v w : E) :
    intrFrameMetric (I := I) g hEnorm p z v w =
      g.inner (intrinsicFramedExp (I := I) g hEnorm p z)
        (intrinsicJacobi (I := I) g hEnorm p
          (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p v) 1)
        (intrinsicJacobi (I := I) g hEnorm p
          (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p w) 1) := by
  rw [intrFrameMetric_apply, intrFrame_deriv, intrFrame_deriv]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrFrame_deriv_inj
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z : E) {c : Real} (hc : 0 < c)
    (hlower : ∀ v : E,
      c * ‖v‖ ^ 2 ≤ intrFrameMetric (I := I) g hEnorm p z v v) :
    Function.Injective
      (mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) g hEnorm p) z) := by
  intro v w hvw
  let dv : E := v - w
  let D : E →L[Real]
      TangentSpace I (intrinsicFramedExp (I := I) g hEnorm p z) :=
    mfderiv (modelWithCornersSelf Real E) I
      (intrinsicFramedExp (I := I) g hEnorm p) z
  have hDsub : D dv = 0 := by
    calc
      D dv = D v - D w := map_sub D v w
      _ = 0 := sub_eq_zero.mpr hvw
  have hmetric :
      intrFrameMetric (I := I) g hEnorm p z dv dv = 0 := by
    rw [intrFrameMetric_apply]
    change g.inner _ (D dv) (D dv) = 0
    rw [hDsub]
    simp
  have hnonneg := hlower dv
  rw [hmetric] at hnonneg
  have hnorm : ‖dv‖ = 0 := by
    apply sq_eq_zero_iff.mp
    exact le_antisymm (nonpos_of_mul_nonpos_right hnonneg hc) (sq_nonneg _)
  have hdv : dv = 0 := norm_eq_zero.mp hnorm
  apply sub_eq_zero.mp
  exact hdv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrFrame_not_conj
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z : E) {c : Real} (hc : 0 < c)
    (hlower : ∀ v : E,
      c * ‖v‖ ^ 2 ≤ intrFrameMetric (I := I) g hEnorm p z v v) :
    ¬ IsConjVec (I := I) g hEnorm p
      (normalFrame (I := I) g p z : E) := by
  let F : E → M := fun w =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from w)
  let L : E →L[Real] E := intrFrameCLM (I := I) g p
  have hF : MDifferentiableAt (modelWithCornersSelf Real E) I F (L z) :=
    (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt.mdifferentiableAt
      (by decide)
  have hL : MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun w : E => L w) z := by
    have hL_smooth : ContMDiff (modelWithCornersSelf Real E)
        (modelWithCornersSelf Real E) ∞ (fun w : E => L w) := L.contMDiff
    exact hL_smooth.contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp
    (I := modelWithCornersSelf Real E)
    (I' := modelWithCornersSelf Real E) (I'' := I) z hF hL
  have hLderiv : mfderiv (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun w : E => L w) z = L := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rw [hLderiv] at hchain
  have hchain' :
      mfderiv (modelWithCornersSelf Real E) I
          (intrinsicFramedExp (I := I) g hEnorm p) z =
        (mfderiv (modelWithCornersSelf Real E) I F (L z)).comp L := by
    simpa only [intrinsicFramedExp, F, L, Function.comp_apply] using hchain
  have hframe :
      Function.Injective
        (mfderiv (modelWithCornersSelf Real E) I
          (intrinsicFramedExp (I := I) g hEnorm p) z) :=
    intrFrame_deriv_inj (I := I) g hEnorm p z hc hlower
  have hLsurj : Function.Surjective L := by
    intro w
    refine ⟨(normalFrame (I := I) g p).symm w, ?_⟩
    simp only [L, intrFrameCLM_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hraw :
      Function.Injective
        (mfderiv (modelWithCornersSelf Real E) I F (L z)) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := hLsurj a
    obtain ⟨b, rfl⟩ := hLsurj b
    apply congrArg L
    apply hframe
    rw [hchain']
    change (mfderiv (modelWithCornersSelf Real E) I F (L z)) (L a) =
      (mfderiv (modelWithCornersSelf Real E) I F (L z)) (L b)
    exact hab
  unfold IsConjVec
  push Not
  simpa only [F, L, intrFrameCLM_apply] using hraw

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
