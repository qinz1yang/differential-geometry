import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Retag
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffPassZero

noncomputable section


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rank0_eq_smul_unit (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) •
      unitZeroSec (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, smul_apply]
  rw [show Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitZeroSec_apply, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

def slotExtendTwo (g : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g 0 4) : SmoothCcTensor g 2 6 :=
  slotExtend (I := I) (M := M) g 1 5
    (slotExtend (I := I) (M := M) g 0 4 X)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtend_toModel_cons
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Phi : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace (r + 1) I x) (v0 : E)
    (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s Phi).toSection x) D)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          Phi.toSection x)
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v0))) vs := by
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g r s Phi).toSection x) D) =
      slotExtendFib (I := I) (M := M) r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          Phi.toSection x) D from rfl]
  exact DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval (I := I) (M := M) r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      Phi.toSection x) D v0 vs

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendTwo_toModel
    (g : SmoothRiemannianMetric I M) (X : SmoothCcTensor g 0 4)
    (x : M) (D : Tensor0SSpace 2 I x) (u : Fin 6 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendTwo (I := I) (M := M) g X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            X.toSection x) (unitZeroSec (I := I) (M := M) x))
          (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  have hu : (fun k : Fin 6 => u k) =
      Fin.cons (u 0)
        (Fin.cons (u 1)
          (fun k : Fin 4 => u (Fin.natAdd 2 k))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    change u (Fin.succ (Fin.succ k2)) = u (Fin.natAdd 2 k2)
    congr 1
    exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendTwo (I := I) (M := M) g X).toSection x) D) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4 X)).toSection x) D)
        (fun k : Fin 6 => u k) from rfl]
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g 1 5
    (slotExtend (I := I) (M := M) g 0 4 X) x D (u 0)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtend (I := I) (M := M) g 0 4 X).toSection x)
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtend (I := I) (M := M) g 0 4 X).toSection x)
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0))))
      from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g 0 4 X x
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0))) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 1))
    with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_toModel_apply
      (I := I) (M := M) (n := 0)
      (T := tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))
      (v0 := u 1) (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_toModel_apply
      (I := I) (M := M) (n := 1) (T := D) (v0 := u 0)
      (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul,
    smul_apply, smul_eq_mul]

def movingMetricPairTracePermutation : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def movingMetricDoubleTraceField (g gm : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 2) s :=
  SmoothCcTensor.retagEquiv gm g (s + 2) s
    (cometricDoubleTraceField (I := I) gm s)

def movingMetricPairTraceOperator (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 6 4 2
    (movingMetricDoubleTraceField (I := I) (M := M) g gm 2)
    (movingMetricDoubleTraceField (I := I) (M := M) g gm 4)

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem movingMetricPairTraceOperator_apply
    (g gm : SmoothRiemannianMetric I M) (X : SmoothCcTensor g 0 4)
    (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
            (movingMetricPairTraceOperator (I := I) (M := M) g gm)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
              (slotExtendTwo (I := I) (M := M) g X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) gm x a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) gm x b x)] *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              X.toSection x) (unitZeroSec (I := I) (M := M) x))
            ![v 0, v 1,
              tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) gm x a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) gm x b x)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
        (slotExtendTwo (I := I) (M := M) g X)).toSection x) D
    with hY_def
  have hYval : ∀ w : Fin 6 → E,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              X.toSection x) (unitZeroSec (I := I) (M := M) x))
            ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
          (slotExtendTwo (I := I) (M := M) g X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr movingMetricPairTracePermutation
            ((slotExtendTwo (I := I) (M := M) g X).toSection x)) D)
        from by rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) movingMetricPairTracePermutation
      ((slotExtendTwo (I := I) (M := M) g X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendTwo_toModel (I := I) (M := M) g X x D
      (fun i => w (movingMetricPairTracePermutation i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (movingMetricPairTraceOperator (I := I) (M := M) g gm)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
          (slotExtendTwo (I := I) (M := M) g X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) gm 2 x
        (cometricDoubleTraceFib (I := I) gm 4 x Y) from by
    rw [hY_def, operatorFieldComposition_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) gm 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) gm 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) gm 4 x]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (smoothOrthoFrame (I := I) gm x b x))
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (smoothOrthoFrame (I := I) gm x b x))
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
