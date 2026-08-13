import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderFiber
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
lemma gradArmFib_moving_section_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
          (Y x))) := by
  classical
  intro x₀
  have hfrozen : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x₀) x
          (Y x))) x₀ :=
    gradArmFib_frozen_section_contMDiff (I := I) (M := M) g s
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) hY x₀
  refine hfrozen.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  refine congrArg (TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y) ?_
  rw [gradArmFib_apply, gradArmFib_apply,
    gradArmDirCLM_frame_independent (I := I) (M := M) g s y
      (fun i => smoothOrthoFrame (I := I) g y i) (fun i => smoothOrthoFrame (I := I) g x₀ i)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
      (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j) (Y y)]

noncomputable def curvatureGradContractionSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 (s + 1)) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
          (W.toSection x)
      contMDiff_toFun :=
        gradArmFib_moving_section_contMDiff (I := I) (M := M) g s W.toSection.contMDiff_toFun }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] lemma gradArmSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (curvatureGradContractionSection (I := I) (M := M) g s W).toSection x =
      curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
        (W.toSection x) := rfl

noncomputable def curvatureCommutatorRemainderSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S -
    curvatureGradContractionSection (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s S)

lemma diffArmSection_slice_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
          (smoothOrthoFrame (I := I) g x a x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x := by
  classical
  have hsub : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (curvatureGradContractionSection (I := I) (M := M) g s
            (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
    rw [curvatureCommutatorRemainderSection, SmoothCcTensor.toSection_sub]; rfl
  rw [hsub, ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply,
    tensor0SAsRS_sub' (I := I) (M := M) s x]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (curvatureGradContractionSection (I := I) (M := M) g s
          (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)) from rfl]
  rw [slot0_read_curv_eq_frameFree (I := I) (M := M) g s S
    (smoothOrthoFrame_smooth (I := I) g x a) x]
  rw [gradArmFib_covGrad_slice_eq (I := I) (M := M) g s S x a]
  abel

lemma diffArmSection_slice_toModel_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor0SToTensorRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (smoothOrthoFrame (I := I) g x a x)))
          (unitZeroSec (I := I) (M := M) x)) m =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g s S x)
            (Function.update m k
              (∑ i : Fin (Module.finrank ℝ E),
                nablaBaseSlotCurv (I := I) g
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                    (smoothOrthoFrame_smooth (I := I) g x a)) x (m k))) := by
  classical
  set Ba : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
      (smoothOrthoFrame_smooth (I := I) g x a) with hBa
  set A : Π b : M, Tensor0SSpace s I b := unitEvalSection (I := I) (M := M) g s S with hA
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor0SToTensorRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x a x))) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        ∑ i : Fin (Module.finrank ℝ E),
          nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) from
    diffArmSection_slice_eq (I := I) (M := M) g s S x a]
  rw [toModel_unit_finsum (I := I) (M := M) s x Finset.univ
    (fun i => nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) m]
  have hper : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Ba A x) m := by
    intro i
    exact nablaTensorCurvSec_tensorRSCov_unitEval (I := I) (M := M) g s
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
        (smoothOrthoFrame_smooth (I := I) g x a)) S.toSection x ▸ rfl
  rw [Finset.sum_congr rfl (fun i _ => hper i)]
  rw [frame_sum_nablaTensor0SCurv_diag_baseSlot_eval (I := I) g s Ba A
    (contMDiff_unitEvalSection (I := I) (M := M) g s S) x m]

lemma diffArmSection_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M)
    (hx : S₁.toSection x = S₂.toSection x) :
    (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₁).toSection x =
      (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₂).toSection x := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 (s + 1) x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hredD : ∀ T : TensorRSSpace 0 (s + 1) I x,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D) v =
        tensor00Scalar (I := I) (M := M) x D *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
              (unitZeroSec (I := I) (M := M) x)) v := by
    intro T
    conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
    rw [ContinuousLinearMap.map_smul]
    simp only [Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [hredD, hredD]
  apply congrArg (fun z : ℝ => tensor00Scalar (I := I) (M := M) x D * z)
  obtain ⟨w, m, hcons⟩ : ∃ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
      v = Fin.cons w m := ⟨v 0, Fin.tail v, (Fin.cons_self_tail v).symm⟩
  subst hcons
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) g _
    (fun a => smoothOrthoFrame (I := I) g x a x)
    (fun u => smoothOrthoFrame_parsevalExpand (I := I) (M := M) g x u) w m,
    tensor0S_uncurry_cons_eval_orthonormal (I := I) g _
    (fun a => smoothOrthoFrame (I := I) g x a x)
    (fun u => smoothOrthoFrame_parsevalExpand (I := I) (M := M) g x u) w m]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  apply congrArg (fun z : ℝ =>
    g.inner x (smoothOrthoFrame (I := I) g x a x) w • z)
  have hbridge : ∀ S : SmoothCcTensor g 0 s,
      Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x a x)) m =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensor0SToTensorRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                  (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x)
                  (unitZeroSec (I := I) (M := M) x))
                (smoothOrthoFrame (I := I) g x a x)))
            (unitZeroSec (I := I) (M := M) x)) m := by
    intro S
    rw [tensor0SAsRS_apply (I := I) (M := M) x _ (unitZeroSec (I := I) (M := M) x),
      tensor00Scalar_unitZeroSec' (I := I) (M := M) x, one_smul]
  rw [hbridge S₁, hbridge S₂]
  rw [diffArmSection_slice_toModel_value_local (I := I) (M := M) g s S₁ x a m,
    diffArmSection_slice_toModel_value_local (I := I) (M := M) g s S₂ x a m]
  rw [show unitEvalSection (I := I) (M := M) g s S₁ x =
      unitEvalSection (I := I) (M := M) g s S₂ x from by
    rw [unitEvalSection_apply, unitEvalSection_apply, hx]]

omit [I.Boundaryless] in
lemma gradArmSection_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W₁ W₂ : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (curvatureGradContractionSection (I := I) (M := M) g s (W₁ + W₂)).toSection x =
      (curvatureGradContractionSection (I := I) (M := M) g s W₁).toSection x +
        (curvatureGradContractionSection (I := I) (M := M) g s W₂).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection, gradArmSection_toSection]
  rw [show (W₁ + W₂).toSection x = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
  rw [map_add]

omit [I.Boundaryless] in
lemma gradArmSection_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (W : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (curvatureGradContractionSection (I := I) (M := M) g s (c • W)).toSection x =
      c • (curvatureGradContractionSection (I := I) (M := M) g s W).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection]
  rw [show (c • W).toSection x = c • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
  rw [map_smul]

omit [I.Boundaryless] in
lemma gradArmSection_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W₁ W₂ : SmoothCcTensor g 0 (s + 1)) (x : M)
    (hx : W₁.toSection x = W₂.toSection x) :
    (curvatureGradContractionSection (I := I) (M := M) g s W₁).toSection x =
      (curvatureGradContractionSection (I := I) (M := M) g s W₂).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection, hx]

omit [I.Boundaryless] in
theorem exists_gradArmSection_appFullSec (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ H_R : HomTensorRSField (E := E) (M := M) 0 (s + 1) (s + 1) I,
      ∀ W : SmoothCcTensor g 0 (s + 1),
        curvatureGradContractionSection (I := I) (M := M) g s W =
          homTensorRSFieldApply (I := I) (M := M) g 0 (s + 1) (s + 1) H_R W :=
  exists_value_local_appFullSec (I := I) (M := M) g 0 (s + 1) (s + 1)
    (fun W => curvatureGradContractionSection (I := I) (M := M) g s W)
    (fun W₁ W₂ x => gradArmSection_toSection_add (I := I) (M := M) g s W₁ W₂ x)
    (fun c W x => gradArmSection_toSection_smul (I := I) (M := M) g s c W x)
    (fun W₁ W₂ x hW => gradArmSection_value_local (I := I) (M := M) g s W₁ W₂ x hW)

lemma pointwiseTensorCurv_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s (S₁ + S₂)).toSection x =
      (pointwiseTensorCurv (I := I) (M := M) g s S₁).toSection x +
        (pointwiseTensorCurv (I := I) (M := M) g s S₂).toSection x := by
  classical
  have hRoughGrad : rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s (S₁ + S₂)) =
      rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S₁) +
        rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S₂) := by
    rw [covGrad_add (I := I) (M := M) g 0 s S₁ S₂]
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (covGrad (I := I) (M := M) g 0 s S₁ +
          covGrad (I := I) (M := M) g 0 s S₂).toSection z) =
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S₁).toSection z) +
          (fun z : M => (covGrad (I := I) (M := M) g 0 s S₂).toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
    exact rawTensorConnLap_add (I := I) g 0 (s + 1)
      (fun z => ((covGrad (I := I) (M := M) g 0 s S₁).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z => ((covGrad (I := I) (M := M) g 0 s S₂).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S₁).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S₂).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  have hGradRough : covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s (S₁ + S₂)) =
      covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S₁) +
        covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S₂) := by
    rw [← covGrad_add (I := I) (M := M) g 0 s]
    refine congrArg (covGrad (I := I) (M := M) g 0 s) ?_
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (S₁ + S₂).toSection z) =
        (fun z : M => S₁.toSection z) + (fun z : M => S₂.toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
    exact rawTensorConnLap_add (I := I) g 0 s
      (fun z => (S₁.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z => (S₂.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S₁.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S₂.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  rw [pointwiseTensorCurv_toSection_eq_sub, pointwiseTensorCurv_toSection_eq_sub,
    pointwiseTensorCurv_toSection_eq_sub, hRoughGrad, hGradRough]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  abel

lemma pointwiseTensorCurv_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s (c • S)).toSection x =
      c • (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x := by
  classical
  have hRoughGrad : rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s (c • S)) =
      c • rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) := by
    rw [covGrad_smul (I := I) (M := M) g 0 s c S]
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (c • covGrad (I := I) (M := M) g 0 s S).toSection z) =
        (fun z : M => c • (covGrad (I := I) (M := M) g 0 s S).toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
    exact rawTensorConnLap_smul (I := I) g 0 (s + 1) c
      (fun z => ((covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  have hGradRough : covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s (c • S)) =
      c • covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) := by
    rw [← covGrad_smul (I := I) (M := M) g 0 s]
    refine congrArg (covGrad (I := I) (M := M) g 0 s) ?_
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (c • S).toSection z) =
        (fun z : M => c • S.toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
    exact rawTensorConnLap_smul (I := I) g 0 s c
      (fun z => (S.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  rw [pointwiseTensorCurv_toSection_eq_sub, pointwiseTensorCurv_toSection_eq_sub,
    hRoughGrad, hGradRough]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply, smul_sub]

lemma diffArmSection_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M) :
    (curvatureCommutatorRemainderSection (I := I) (M := M) g s (S₁ + S₂)).toSection x =
      (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₁).toSection x +
        (curvatureCommutatorRemainderSection (I := I) (M := M) g s S₂).toSection x := by
  rw [curvatureCommutatorRemainderSection, curvatureCommutatorRemainderSection,
    curvatureCommutatorRemainderSection]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, Pi.sub_apply, Pi.sub_apply]
  rw [pointwiseTensorCurv_toSection_add (I := I) (M := M) g s S₁ S₂]
  rw [covGrad_add (I := I) (M := M) g 0 s S₁ S₂,
    gradArmSection_toSection_add (I := I) (M := M) g s
      (covGrad (I := I) (M := M) g 0 s S₁) (covGrad (I := I) (M := M) g 0 s S₂) x]
  abel

lemma diffArmSection_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    (curvatureCommutatorRemainderSection (I := I) (M := M) g s (c • S)).toSection x =
      c • (curvatureCommutatorRemainderSection (I := I) (M := M) g s S).toSection x := by
  rw [curvatureCommutatorRemainderSection, curvatureCommutatorRemainderSection]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_sub, Pi.sub_apply, Pi.sub_apply]
  rw [pointwiseTensorCurv_toSection_smul (I := I) (M := M) g s c S]
  rw [covGrad_smul (I := I) (M := M) g 0 s c S,
    gradArmSection_toSection_smul (I := I) (M := M) g s c
      (covGrad (I := I) (M := M) g 0 s S) x]
  rw [smul_sub]

theorem exists_diffArmSection_appFullSec (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ H_dR : HomTensorRSField (E := E) (M := M) 0 s (s + 1) I,
      ∀ S : SmoothCcTensor g 0 s,
        curvatureCommutatorRemainderSection (I := I) (M := M) g s S =
          homTensorRSFieldApply (I := I) (M := M) g 0 s (s + 1) H_dR S :=
  exists_value_local_appFullSec (I := I) (M := M) g 0 s (s + 1)
    (fun S => curvatureCommutatorRemainderSection (I := I) (M := M) g s S)
    (fun S₁ S₂ x => diffArmSection_toSection_add (I := I) (M := M) g s S₁ S₂ x)
    (fun c S x => diffArmSection_toSection_smul (I := I) (M := M) g s c S x)
    (fun S₁ S₂ x hS => diffArmSection_value_local (I := I) (M := M) g s S₁ S₂ x hS)

theorem exists_pointwiseTensorCurv_firstOrder_homField_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ (H_R : HomTensorRSField (E := E) (M := M) 0 (s + 1) (s + 1) I)
      (H_dR : HomTensorRSField (E := E) (M := M) 0 s (s + 1) I),
      ∀ S : SmoothCcTensor g 0 s,
        pointwiseTensorCurv (I := I) (M := M) g s S =
          homTensorRSFieldApply (I := I) (M := M) g 0 (s + 1) (s + 1) H_R
            (covGrad (I := I) (M := M) g 0 s S) +
          homTensorRSFieldApply (I := I) (M := M) g 0 s (s + 1) H_dR S := by
  obtain ⟨H_R, hH_R⟩ := exists_gradArmSection_appFullSec (I := I) (M := M) (E := E) g s
  obtain ⟨H_dR, hH_dR⟩ := exists_diffArmSection_appFullSec (I := I) (M := M) (E := E) g s
  refine ⟨H_R, H_dR, fun S => ?_⟩
  have hdecomp : pointwiseTensorCurv (I := I) (M := M) g s S =
      curvatureGradContractionSection (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s S) +
        curvatureCommutatorRemainderSection (I := I) (M := M) g s S := by
    rw [curvatureCommutatorRemainderSection]
    abel
  rw [hdecomp, hH_R (covGrad (I := I) (M := M) g 0 s S), hH_dR S]

end Curvature
end Geometry
end DifferentialGeometry

end
