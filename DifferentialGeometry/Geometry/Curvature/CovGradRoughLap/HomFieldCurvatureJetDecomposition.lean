import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MetricDoubleTrace
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.TensorSlotSwapSmoothness
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSValueLocal
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
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciDefect_eval (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W : SmoothCcTensor g r t) (x : M) (D : Tensor0SSpace r I x)
    (v0 v1 : TangentSpace I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
          (iteratedCovGrad g r t 2 W -
            homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r t)
              (iteratedCovGrad g r t 2 W)).toSection x) D)
        (Fin.cons v0 (Fin.cons v1 m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          riemannOp (tensorCov (I := I) g r t) x v0 v1 (W.toSection x)) D) m := by
  classical
  set X : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v0 with hX_def
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v1 with hY_def
  have hXx : X x = v0 := smoothExtensionTangent_eq (I := I) x v0
  have hYx : Y x = v1 := smoothExtensionTangent_eq (I := I) x v1
  have hXsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v0
  have hYsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x v1
  have hfib : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (iteratedCovGrad g r t 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t)
            (iteratedCovGrad g r t 2 W)).toSection x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (iteratedCovGrad g r t 2 W).toSection x) -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
        (homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t)
          (iteratedCovGrad g r t 2 W)).toSection x) := by
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hfib, ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  rw [appFullSec_toSection, swapTwoSec_apply,
    swapTwoFib_eval (I := I) (M := M) r t x ((iteratedCovGrad g r t 2 W).toSection x) v0 v1 D m]
  rw [show (iteratedCovGrad g r t 2 W).toSection x =
      (covGrad (I := I) (M := M) g r (t + 1)
        (covGrad (I := I) (M := M) g r t W)).toSection x from rfl]
  rw [show v0 = X x from hXx.symm, show v1 = Y x from hYx.symm]
  rw [secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r t W hXsm hYsm x D m,
    secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r t W hYsm hXsm x D m]
  rw [← ContinuousMultilinearMap.sub_apply, ← Tensor0SSpace.toModel_sub,
    ← ContinuousLinearMap.sub_apply]
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        tensorSecondCovDeriv (I := I) g r t X Y (fun y : M => W.toSection y) x) -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        tensorSecondCovDeriv (I := I) g r t Y X (fun y : M => W.toSection y) x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        riemannOp (tensorCov (I := I) g r t) x (X x) (Y x) (W.toSection x)) from
    tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g r t hXsm hYsm
      W.toSection.contMDiff]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciDefect_value_local (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W₁ W₂ : SmoothCcTensor g r t) (x : M)
    (hW : W₁.toSection x = W₂.toSection x) :
    (iteratedCovGrad g r t 2 W₁ -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W₁)).toSection x =
      (iteratedCovGrad g r t 2 W₂ -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W₂)).toSection
            x := by
  classical
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D v
  rw [show v = Fin.cons (v 0) (Fin.cons (Matrix.vecTail v 0) (Matrix.vecTail (Matrix.vecTail v)))
      from by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Fin.cons_zero]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [Matrix.vecTail, Function.comp]
      · simp [Fin.cons_succ, Matrix.vecTail, Function.comp]]
  rw [ricciDefect_eval (I := I) (M := M) g r t W₁ x D (v 0) (Matrix.vecTail v 0)
      (Matrix.vecTail (Matrix.vecTail v)),
    ricciDefect_eval (I := I) (M := M) g r t W₂ x D (v 0) (Matrix.vecTail v 0)
      (Matrix.vecTail (Matrix.vecTail v))]
  rw [hW]

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciDefect_toSection_add (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W₁ W₂ : SmoothCcTensor g r t) (x : M) :
    (iteratedCovGrad g r t 2 (W₁ + W₂) -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t)
          (iteratedCovGrad g r t 2 (W₁ + W₂))).toSection x =
      (iteratedCovGrad g r t 2 W₁ -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W₁)).toSection x +
        (iteratedCovGrad g r t 2 W₂ -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t)
            (iteratedCovGrad g r t 2 W₂)).toSection x := by
  simp only [iteratedCovGrad_add]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((iteratedCovGrad g r t 2 W₁ + iteratedCovGrad g r t 2 W₂).toSection x
        : TensorRSSpace r (t + 2) I x) =
      (iteratedCovGrad g r t 2 W₁).toSection x + (iteratedCovGrad g r t 2 W₂).toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
  rw [map_add (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
    swapTwoSec (I := I) (M := M) (E := E) r t x)]
  abel

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciDefect_toSection_smul (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (k : ℝ) (W : SmoothCcTensor g r t) (x : M) :
    (iteratedCovGrad g r t 2 (k • W) -
        homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r t)
          (iteratedCovGrad g r t 2 (k • W))).toSection x =
      k • (iteratedCovGrad g r t 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r t)
            (iteratedCovGrad g r t 2 W)).toSection x := by
  have hsmul2 : iteratedCovGrad g r t 2 (k • W) = k • iteratedCovGrad g r t 2 W := by
    change covGrad (I := I) (M := M) g r (t + 1) (covGrad (I := I) (M := M) g r t (k • W)) =
      k • covGrad (I := I) (M := M) g r (t + 1) (covGrad (I := I) (M := M) g r t W)
    rw [covGrad_smul, covGrad_smul]
  rw [hsmul2]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [appFullSec_toSection, appFullSec_toSection]
  rw [show ((k • iteratedCovGrad g r t 2 W).toSection x : TensorRSSpace r (t + 2) I x) =
      k • (iteratedCovGrad g r t 2 W).toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
  rw [map_smul (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
    swapTwoSec (I := I) (M := M) (E := E) r t x)]
  rw [smul_sub]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_ricciDefect_homField (g : SmoothRiemannianMetric I M) (r t : ℕ) :
    ∃ RActF : HomTensorRSField (E := E) (M := M) r t (t + 2) I,
      ∀ W : SmoothCcTensor g r t,
        iteratedCovGrad g r t 2 W -
            homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W) =
          homTensorRSFieldApply (I := I) (M := M) g r t (t + 2) RActF W :=
  exists_value_local_appFullSec (I := I) (M := M) g r t (t + 2)
    (fun W => iteratedCovGrad g r t 2 W -
      homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2)
        (swapTwoSec (I := I) (M := M) (E := E) r t) (iteratedCovGrad g r t 2 W))
    (fun W₁ W₂ x => ricciDefect_toSection_add (I := I) (M := M) g r t W₁ W₂ x)
    (fun k W x => ricciDefect_toSection_smul (I := I) (M := M) g r t k W x)
    (fun W₁ W₂ x hW => ricciDefect_value_local (I := I) (M := M) g r t W₁ W₂ x hW)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma slotExtTrace_eval (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (V : TensorRSSpace r (s + 1 + 2) I x) (D : Tensor0SSpace r I x)
    (v0 : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) s x
            (metricDoubleTraceFib (I := I) (M := M) g r s x) V) D) (Fin.cons v0 m) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1 + 2) I x from V) D)
          (Fin.cons v0 (Fin.cons (smoothOrthoFrame (I := I) g x i x)
            (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))) := by
  classical
  rw [slotExtendFullFib_apply_eval (I := I) (M := M) g r (s + 2) s x
    (metricDoubleTraceFib (I := I) (M := M) g r s x) V D v0 m]
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        metricDoubleTraceFib (I := I) (M := M) g r s x
          ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          curryLastTwoTensorSlots (I := I) (M := M) r s x
            ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)) from
    metricDoubleTraceFib_apply (I := I) (M := M) g r s x
      ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)]
  rw [ContinuousLinearMap.sum_apply, toModel_sum_eval]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [twoSlotPeel_eval (I := I) (M := M) r s x
    ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm V v0)
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) D m]
  exact covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r (s + 2) x V v0 D
    (Fin.cons (smoothOrthoFrame (I := I) g x i x)
      (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma traceConj_eval (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (V : TensorRSSpace r (s + 1 + 2) I x) (D : Tensor0SSpace r I x)
    (v0 : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          metricDoubleTraceFib (I := I) (M := M) g r (s + 1) x
            (slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) (s + 2) x
              (swapTwoFib (I := I) (M := M) r s x)
              (swapTwoFib (I := I) (M := M) r (s + 1) x V))) D) (Fin.cons v0 m) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1 + 2) I x from V) D)
          (Fin.cons v0 (Fin.cons (smoothOrthoFrame (I := I) g x i x)
            (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))) := by
  classical
  set W : TensorRSSpace r (s + 1 + 2) I x :=
    slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) (s + 2) x
      (swapTwoFib (I := I) (M := M) r s x) (swapTwoFib (I := I) (M := M) r (s + 1) x V) with hW_def
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        metricDoubleTraceFib (I := I) (M := M) g r (s + 1) x W) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          curryLastTwoTensorSlots (I := I) (M := M) r (s + 1) x W
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)) from
    metricDoubleTraceFib_apply (I := I) (M := M) g r (s + 1) x W]
  rw [ContinuousLinearMap.sum_apply, toModel_sum_eval]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [twoSlotPeel_eval (I := I) (M := M) r (s + 1) x W
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) D
    (Fin.cons v0 m)]
  rw [hW_def]
  rw [slotExtendFullFib_apply_eval (I := I) (M := M) g r (s + 2) (s + 2) x
    (swapTwoFib (I := I) (M := M) r s x) (swapTwoFib (I := I) (M := M) r (s + 1) x V) D
    (smoothOrthoFrame (I := I) g x i x)
    (Fin.cons (smoothOrthoFrame (I := I) g x i x) (Fin.cons v0 m))]
  rw [swapTwoFib_eval (I := I) (M := M) r s x
    ((covGradBundleEquiv (I := I) (M := M) r (s + 2) x).symm
      (swapTwoFib (I := I) (M := M) r (s + 1) x V) (smoothOrthoFrame (I := I) g x i x))
    (smoothOrthoFrame (I := I) g x i x) v0 D m]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r (s + 2) x
    (swapTwoFib (I := I) (M := M) r (s + 1) x V) (smoothOrthoFrame (I := I) g x i x) D
    (Fin.cons v0 (Fin.cons (smoothOrthoFrame (I := I) g x i x) m))]
  rw [swapTwoFib_eval (I := I) (M := M) r (s + 1) x V
    (smoothOrthoFrame (I := I) g x i x) v0
    D (Fin.cons (smoothOrthoFrame (I := I) g x i x) m)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma slotExtTrace_eq_traceConj (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (V : TensorRSSpace r (s + 1 + 2) I x) :
    (show TensorRSSpace r (s + 1 + 2) I x →L[ℝ] TensorRSSpace r (s + 1) I x from
        slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) s x
          (metricDoubleTraceFib (I := I) (M := M) g r s x)) V =
      metricDoubleTraceFib (I := I) (M := M) g r (s + 1) x
        (slotInsertHomTensorRSFib (I := I) (M := M) g r (s + 2) (s + 2) x
          (swapTwoFib (I := I) (M := M) r s x)
          (swapTwoFib (I := I) (M := M) r (s + 1) x V)) := by
  classical
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D v
  rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from by
    funext j; refine Fin.cases ?_ (fun k => ?_) j
    · simp [Fin.cons_zero]
    · simp [Fin.cons_succ, Matrix.vecTail, Function.comp]]
  rw [slotExtTrace_eval (I := I) (M := M) g r s x V D (v 0) (Matrix.vecTail v),
    traceConj_eval (I := I) (M := M) g r s x V D (v 0) (Matrix.vecTail v)]

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] in
private theorem appFullSec_slotExtTrace_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (V : SmoothCcTensor g r (s + 1 + 2)) :
    homTensorRSFieldApply (I := I) (M := M) g r (s + 2 + 1) (s + 1)
        (slotExtendFullSec (I := I) g r (s + 2) s
          (metricDoubleTraceField (I := I) (M := M) (E := E) g r s)) V =
      homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1)
        (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1 + 2)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1 + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) V)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  simp only [slotExtendFullSec_apply, metricDoubleTraceField_apply, swapTwoSec_apply]
  exact slotExtTrace_eq_traceConj (I := I) (M := M) g r s x (V.toSection x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem exists_appFullSec_comp (g : SmoothRiemannianMetric I M) (r a b c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r b c I)
    (Q' : HomTensorRSField (E := E) (M := M) r a b I) :
    ∃ QQ' : HomTensorRSField (E := E) (M := M) r a c I,
      ∀ W : SmoothCcTensor g r a,
        homTensorRSFieldApply (I := I) (M := M) g r b c Q
          (homTensorRSFieldApply (I := I) (M := M) g r a b Q' W) =
          homTensorRSFieldApply (I := I) (M := M) g r a c QQ' W :=
  exists_value_local_appFullSec (I := I) (M := M) g r a c
    (fun W => homTensorRSFieldApply (I := I) (M := M) g r b c Q
      (homTensorRSFieldApply (I := I) (M := M) g r a b Q' W))
    (fun W₁ W₂ x => by
      simp only [appFullSec_toSection]
      rw [show ((W₁ + W₂).toSection x : TensorRSSpace r a I x) =
          W₁.toSection x + W₂.toSection x from by
        rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
      rw [map_add (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x from Q' x),
        map_add (show TensorRSSpace r b I x →L[ℝ] TensorRSSpace r c I x from Q x)])
    (fun k W x => by
      simp only [appFullSec_toSection]
      rw [show ((k • W).toSection x : TensorRSSpace r a I x) = k • W.toSection x from by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
      rw [map_smul (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r b I x from Q' x),
        map_smul (show TensorRSSpace r b I x →L[ℝ] TensorRSSpace r c I x from Q x)])
    (fun W₁ W₂ x hW => by
      simp only [appFullSec_toSection]
      rw [hW])

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
private theorem appFullSec_sub_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W₁ W₂ : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c Q (W₁ - W₂) =
      homTensorRSFieldApply (I := I) (M := M) g r a c Q W₁ - homTensorRSFieldApply (I := I) (M := M)
        g r a c Q W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((W₁ - W₂).toSection x : TensorRSSpace r a I x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]]
  rw [map_sub (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Q x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
private theorem appFullSec_add_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W₁ W₂ : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c Q (W₁ + W₂) =
      homTensorRSFieldApply (I := I) (M := M) g r a c Q W₁ + homTensorRSFieldApply (I := I) (M := M)
        g r a c Q W₂ :=
  appFullRS_add_right (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff W₁ W₂

set_option backward.isDefEq.respectTransparency true in

omit [NeZero (Module.finrank ℝ E)] in
private theorem headDifferenceDrop_bracket (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (RA_s : HomTensorRSField (E := E) (M := M) r s (s + 2) I)
    (RA_s1 : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 3) I)
    (hRA_s : ∀ W : SmoothCcTensor g r s,
      iteratedCovGrad g r s 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 W) =
        homTensorRSFieldApply (I := I) (M := M) g r s (s + 2) RA_s W)
    (hRA_s1 : ∀ W : SmoothCcTensor g r (s + 1),
      iteratedCovGrad g r (s + 1) 2 W -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) (iteratedCovGrad g r (s + 1) 2 W) =
        homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3) RA_s1 W)
    (S : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) -
        homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (swapTwoSec (I := I) (M := M) (E := E) r (s + 1))
            (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S))) =
      (homTensorRSFieldApply (I := I) (M := M) g r s (s + 3)
            (homTensorRSCovGradSec (I := I) g r s (s + 2) RA_s) S +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3)
            (slotExtendFullSec (I := I) g r s (s + 2) RA_s)
            (covGrad (I := I) (M := M) g r s S) +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
            (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s))
            (iteratedCovGrad g r s 2 S)) +
        homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3) RA_s1
            (covGrad (I := I) (M := M) g r s S)) := by
  have hT3 : iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S) =
      covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) := rfl
  have hR1 := hRA_s1 (covGrad (I := I) (M := M) g r s S)
  rw [hT3] at hR1
  have hcg1 := covGrad_appFullSec_eq (I := I) (M := M) g r (s + 2) (s + 2)
    (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)
  have hR0 := hRA_s S
  have hcg2 := covGrad_appFullSec_eq (I := I) (M := M) g r s (s + 2) RA_s S
  have hsplit : ∀ A C : SmoothCcTensor g r (s + 3),
      A - homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s)) A =
        C →
      A - homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
            (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s))
            (homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
              (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) A) =
        C + homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
              (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
                (swapTwoSec (I := I) (M := M) (E := E) r s))
              (A - homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
                (swapTwoSec (I := I) (M := M) (E := E) r (s + 1)) A) := by
    intro A C hC
    rw [appFullSec_sub_right, ← hC]
    abel
  have hT3sub : covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) -
      homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
        (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
          (swapTwoSec (I := I) (M := M) (E := E) r s))
        (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
      homTensorRSFieldApply (I := I) (M := M) g r s (s + 3)
          (homTensorRSCovGradSec (I := I) g r s (s + 2) RA_s) S +
        homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3)
          (slotExtendFullSec (I := I) g r s (s + 2) RA_s)
          (covGrad (I := I) (M := M) g r s S) +
        homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
          (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (iteratedCovGrad g r s 2 S) := by
    have hσ₂₃T3 : homTensorRSFieldApply (I := I) (M := M) g r (s + 3) (s + 3)
          (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
            (swapTwoSec (I := I) (M := M) (E := E) r s))
          (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
        covGrad (I := I) (M := M) g r (s + 2)
            (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)) -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
            (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s)) (iteratedCovGrad g r s 2 S) := by
      rw [hcg1]; abel
    rw [hσ₂₃T3]
    rw [show covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) -
          (covGrad (I := I) (M := M) g r (s + 2)
            (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)) -
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
              (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
                (swapTwoSec (I := I) (M := M) (E := E) r s)) (iteratedCovGrad g r s 2 S)) =
        covGrad (I := I) (M := M) g r (s + 2)
            (iteratedCovGrad g r s 2 S -
              homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 2)
                (swapTwoSec (I := I) (M := M) (E := E) r s) (iteratedCovGrad g r s 2 S)) +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 3)
            (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
              (swapTwoSec (I := I) (M := M) (E := E) r s)) (iteratedCovGrad g r s 2 S) from by
      rw [covGrad_sub]; abel]
    rw [hR0, hcg2]
  rw [hsplit (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) _ hT3sub]
  rw [hR1]

set_option backward.isDefEq.respectTransparency true in

private theorem exists_headDifferenceDrop_metricDoubleTrace (g : SmoothRiemannianMetric I M)
    (r s : ℕ) :
    ∃ (P₀ : HomTensorRSField (E := E) (M := M) r s (s + 1) I)
      (P₁ : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 1) I)
      (P₂ : HomTensorRSField (E := E) (M := M) r (s + 2) (s + 1) I),
      ∀ S : SmoothCcTensor g r s,
        homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1)
            (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
            (iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S)) -
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2 + 1) (s + 1)
            (slotExtendFullSec (I := I) g r (s + 2) s
              (metricDoubleTraceField (I := I) (M := M) (E := E) g r s))
            (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
        homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) P₀ S +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) P₁
            (covGrad (I := I) (M := M) g r s S) +
          homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) P₂
            (iteratedCovGrad g r s 2 S) := by
  classical
  obtain ⟨RA_s, hRA_s⟩ := exists_ricciDefect_homField (I := I) (M := M) (E := E) g r s
  obtain ⟨RA_s1, hRA_s1⟩ := exists_ricciDefect_homField (I := I) (M := M) (E := E) g r (s + 1)
  obtain ⟨P₀, hP₀⟩ := exists_appFullSec_comp (I := I) (M := M) g r s (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (homTensorRSCovGradSec (I := I) g r s (s + 2) RA_s)
  obtain ⟨P₂, hP₂⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 2) (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (homTensorRSCovGradSec (I := I) g r (s + 2) (s + 2)
      (swapTwoSec (I := I) (M := M) (E := E) r s))
  obtain ⟨PA, hPA⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 1) (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (slotExtendFullSec (I := I) g r s (s + 2) RA_s)
  obtain ⟨Tσ₂₃, hTσ₂₃⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 3) (s + 3) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (slotExtendFullSec (I := I) g r (s + 2) (s + 2)
      (swapTwoSec (I := I) (M := M) (E := E) r s))
  obtain ⟨PB, hPB⟩ := exists_appFullSec_comp (I := I) (M := M) g r (s + 1) (s + 3) (s + 1)
    Tσ₂₃ RA_s1
  refine ⟨P₀, PA + PB, P₂, fun S => ?_⟩
  rw [show iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S) =
      covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S) from rfl]
  rw [appFullSec_slotExtTrace_eq (I := I) (M := M) (E := E) g r s
    (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S))]
  rw [← appFullSec_sub_right (I := I) (M := M) g r (s + 1 + 2) (s + 1)
    (metricDoubleTraceField (I := I) (M := M) (E := E) g r (s + 1))
    (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S))]
  rw [headDifferenceDrop_bracket (I := I) (M := M) (E := E) g r s RA_s RA_s1 hRA_s hRA_s1 S]
  rw [appFullSec_add_right, appFullSec_add_right, appFullSec_add_right]
  rw [hP₀ S, hP₂ (iteratedCovGrad g r s 2 S), hPA (covGrad (I := I) (M := M) g r s S)]
  rw [hTσ₂₃ (homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 3) RA_s1
    (covGrad (I := I) (M := M) g r s S))]
  rw [hPB (covGrad (I := I) (M := M) g r s S)]
  rw [appFullSec_add_left (I := I) (M := M) g r (s + 1) (s + 1) PA PB
    (covGrad (I := I) (M := M) g r s S)]
  abel

set_option backward.isDefEq.respectTransparency false in

private theorem exists_roughLapCommutatorTrace_homField
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ (Tr : (t : ℕ) → HomTensorRSField (E := E) (M := M) r (t + 2) t I)
      (P₀ : HomTensorRSField (E := E) (M := M) r s (s + 1) I)
      (P₁ : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 1) I)
      (P₂ : HomTensorRSField (E := E) (M := M) r (s + 2) (s + 1) I),
      (∀ (t : ℕ) (W : SmoothCcTensor g r t),
          rawTensorConnLapSmooth (I := I) g r t W =
            homTensorRSFieldApply (I := I) (M := M) g r (t + 2) t (Tr t)
              (iteratedCovGrad g r t 2 W)) ∧
        ∀ S : SmoothCcTensor g r s,
          homTensorRSFieldApply (I := I) (M := M) g r (s + 1 + 2) (s + 1) (Tr (s + 1))
              (iteratedCovGrad g r (s + 1) 2 (covGrad (I := I) (M := M) g r s S)) -
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2 + 1) (s + 1)
              (slotExtendFullSec (I := I) g r (s + 2) s (Tr s))
              (covGrad (I := I) (M := M) g r (s + 2) (iteratedCovGrad g r s 2 S)) =
          homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) P₀ S +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) P₁
              (covGrad (I := I) (M := M) g r s S) +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) P₂
              (iteratedCovGrad g r s 2 S) := by
  obtain ⟨P₀, P₁, P₂, hdrop⟩ :=
    exists_headDifferenceDrop_metricDoubleTrace (I := I) (M := M) (E := E) g r s
  refine ⟨metricDoubleTraceField (I := I) (M := M) (E := E) g r, P₀, P₁, P₂, ?_, hdrop⟩
  intro t W
  exact roughLap_eq_metricDoubleTrace (I := I) (M := M) (E := E) g r t W

set_option backward.isDefEq.respectTransparency false in

theorem exists_pointwiseTensorCurvRS_homField_jetDecomposition
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ (Q₀ : HomTensorRSField (E := E) (M := M) r s (s + 1) I)
      (Q₁ : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 1) I)
      (Q₂ : HomTensorRSField (E := E) (M := M) r (s + 2) (s + 1) I),
      ∀ S : SmoothCcTensor g r s,
        pointwiseTensorCurvRS (I := I) (M := M) g r s S =
          homTensorRSFieldApply (I := I) (M := M) g r s (s + 1) Q₀ S +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 1) (s + 1) Q₁
              (covGrad (I := I) (M := M) g r s S) +
            homTensorRSFieldApply (I := I) (M := M) g r (s + 2) (s + 1) Q₂
              (iteratedCovGrad g r s 2 S) := by
  obtain ⟨Tr, P₀, P₁, P₂, hfac, hhead⟩ :=
    exists_roughLapCommutatorTrace_homField (I := I) (M := M) (E := E) g r s
  refine ⟨P₀, P₁,
    P₂ - homTensorRSCovGradSec (I := I) g r (s + 2) s (Tr s), fun S => ?_⟩
  have hdef : pointwiseTensorCurvRS (I := I) (M := M) g r s S =
      rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
        covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) := rfl
  rw [hdef]
  rw [hfac (s + 1) (covGrad (I := I) (M := M) g r s S)]
  rw [show covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) =
      covGrad (I := I) (M := M) g r s
        (homTensorRSFieldApply (I := I) (M := M) g r (s + 2) s (Tr s)
          (iteratedCovGrad g r s 2 S)) from
    congrArg (covGrad (I := I) (M := M) g r s) (hfac s S)]
  rw [covGrad_appFullSec_eq (I := I) (M := M) g r (s + 2) s (Tr s) (iteratedCovGrad g r s 2 S)]
  rw [appFullSec_sub_left (I := I) (M := M) g r (s + 2) (s + 1) P₂
    (homTensorRSCovGradSec (I := I) g r (s + 2) s (Tr s)) (iteratedCovGrad g r s 2 S)]
  rw [sub_add_eq_sub_sub, sub_right_comm, hhead S]
  abel

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_secondCovGrad_swap_ricciDefect_homField (g : SmoothRiemannianMetric I M)
    (r t : ℕ) :
    ∃ (F : HomTensorRSField (E := E) (M := M) r (t + 2) (t + 2) I)
      (R : HomTensorRSField (E := E) (M := M) r t (t + 2) I),
      (∀ (x : M) (T : TensorRSSpace r (t + 2) I x) (D : Tensor0SSpace r I x)
        (a b : TangentSpace I x) (m : Fin t → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
              (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from F x) T) D)
            (Fin.cons a (Fin.cons b m)) =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
            (Fin.cons b (Fin.cons a m))) ∧
      ∀ W : SmoothCcTensor g r t,
        iteratedCovGrad g r t 2 W =
          homTensorRSFieldApply (I := I) (M := M) g r (t + 2) (t + 2) F (iteratedCovGrad g r t 2 W)
            +
            homTensorRSFieldApply (I := I) (M := M) g r t (t + 2) R W := by
  classical
  obtain ⟨R, hR⟩ := exists_ricciDefect_homField (I := I) (M := M) g r t
  refine ⟨swapTwoSec (I := I) (M := M) (E := E) r t, R, ?_, fun W => ?_⟩
  · intro x T D a b m
    rw [show (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
        swapTwoSec (I := I) (M := M) (E := E) r t x) = swapTwoFib (I := I) (M := M) r t x from
      swapTwoSec_apply (I := I) (M := M) (E := E) r t x]
    exact swapTwoFib_eval (I := I) (M := M) r t x T a b D m
  · have h := hR W
    exact sub_eq_iff_eq_add'.mp h

end Curvature
end Geometry
end DifferentialGeometry

end
