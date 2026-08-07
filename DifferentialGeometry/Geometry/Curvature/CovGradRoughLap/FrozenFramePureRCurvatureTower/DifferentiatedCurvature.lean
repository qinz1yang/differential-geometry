import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower.GCurvatureGrid
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature


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

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

noncomputable def curvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0) :=
  (Classical.choose (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g)) s

theorem curvOpField_apply_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g)
    s S).symm

noncomputable def genuineDiffCurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S

@[simp] lemma genuineDiffCurvSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
        (covGrad (I := I) (M := M) g (s + 0) (s + 0)
          (curvOpField (I := I) (M := M) g s)).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from S.toSection x) := by
  rw [genuineDiffCurvSection,
    appCc_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S x]
  rfl

theorem genuineDiffCurvSection_eq_covGrad_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    genuineDiffCurvSection (I := I) (M := M) g s S =
      covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) -
        operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
            (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hbase : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M)
      g) s S).symm
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  have hgds : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  have hB' := eq_sub_of_add_eq (hB.symm)
  rw [hB', hbase]

theorem appCc_slotExtend_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          (curvOpField (I := I) (M := M) g s).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [appCc_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g (s + 0) (s + 0) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
      (curvOpField (I := I) (M := M) g s).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g (s + 0) S x d v0]

set_option backward.isDefEq.respectTransparency false in

theorem covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
        vs =
      Tensor0SSpace.toModel
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d)
          (Fin.cons v0 vs) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hbase : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M)
      g) s S).symm
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hB
  have hsec := congrArg (fun T : SmoothCcTensor g 0 (s + 0 + 1) => T.toSection x) hB
  simp only at hsec
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply] at hsec
  have happ :
      (covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d =
        (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d +
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec, ContinuousLinearMap.add_apply]
    rfl
  have hlhs :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
          vs =
        Tensor0SSpace.toModel
          ((covGrad (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d)
          (Fin.cons v0 vs) := by
    have h := covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0)
      (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x d (Fin.cons v0 vs)
    refine Eq.symm (h.trans ?_)
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1) → E) = vs := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1) → E) 0 = v0 := by simp [Fin.cons_zero]
    rw [htail, hhead]
  have hterm2 :
      Tensor0SSpace.toModel
          ((operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs :=
    appCc_slotExtend_curvOpField_covGrad_unit_eval (I := I) (M := M) g s S x d v0 vs
  rw [hlhs, happ, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, hterm2]

theorem appCc_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
          (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))) S =
      covGrad (I := I) (M := M) g 0 (s + 0 + 1)
          (genuineDiffCurvSection (I := I) (M := M) g s S) -
        operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S
  have hgds : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  exact (eq_sub_of_add_eq hB.symm)

theorem appCc_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 0) (s + 0)
            (curvOpField (I := I) (M := M) g s)).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [appCc_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g (s + 0) (s + 0 + 1) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g (s + 0) S x d v0]

theorem appCc_covGrad_covGrad_curvOpField_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            (covGrad (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s)).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hsec := appCc_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (I := I) (M := M) g s S
  have happ :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d =
        (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
            (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x d -
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply]
  rw [happ, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  have hT1 :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
            (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x) d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs := by
    rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0 + 1)
      (genuineDiffCurvSection (I := I) (M := M) g s S) x d (Fin.cons v0 vs)]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) 0 = v0 := by
      simp [Fin.cons_zero]
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) =
        (vs : Fin (s + 0 + 1) → E) := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    rw [hhead, htail]
  have hT2 := appCc_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (I := I) (M := M) g s S x d v0 vs
  rw [hT1, hT2]

end Curvature
end Geometry
end DifferentialGeometry

end
