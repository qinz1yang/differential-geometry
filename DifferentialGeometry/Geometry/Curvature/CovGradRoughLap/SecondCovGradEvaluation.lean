import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
lemma tensorRS_eq_of_eval_eq {r a : ℕ} {x : M}
    {T T' : TensorRSSpace r a I x}
    (h : ∀ (D : Tensor0SSpace r I x) (v : Fin a → TangentSpace I x),
      Tensor0SSpace.eval
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x from T) D) v =
        Tensor0SSpace.eval
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x from T') D) v) :
    T = T' := by
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) a x).injective
  exact ContinuousMultilinearMap.ext (fun v => h D v)

lemma vecTail_cons' {n : ℕ} {α : Type*} (a : α) (v : Fin n → α) :
    Matrix.vecTail (Fin.cons a v) = v := by
  funext j
  simp [Matrix.vecTail, Fin.cons_succ]

private lemma eq_add_of_eq_sub {A : Type*} [AddCommGroup A] {a b c : A}
    (h : a = b - c) : b = a + c :=
  sub_eq_iff_eq_add.mp h.symm

section Bridge

variable (g : SmoothRiemannianMetric I M)

private noncomputable def covApplyCcSec (r t : ℕ) (W : SmoothCcTensor g r t)
    {Y : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    Cₛ^∞⟮I; TensorRSModel r t ℝ E, (fun x : M => TensorRSSpace r t I x)⟯ where
  toFun := fun y : M =>
    covApply (tensorCov (I := I) g r t) Y (fun z : M => W.toSection z) y
  contMDiff_toFun :=
    covApplyRS_contMDiff (I := I) g r t W.toSection.contMDiff_toFun hY

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma curried_covGrad_apply_eq_tensorCovDerivAt_apply (r t : ℕ)
    (W : SmoothCcTensor g r t)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun z : M => Tensor0SSpace r I z)⟯)
    (y : M) (v : TangentSpace I y) :
    Tensor0SNabla.curriedSection I M
        (fun y' : M =>
          (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
            (covGrad (I := I) (M := M) g r t W).toSection y') (w y')) y v =
      (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
        TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
          W.toSection y v) (w y) := by
  rw [show Tensor0SNabla.curriedSection I M
      (fun y' : M =>
        (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
          (covGrad (I := I) (M := M) g r t W).toSection y') (w y')) y =
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t y
      ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
        (covGrad (I := I) (M := M) g r t W).toSection y) (w y)) from rfl]
  have h := tensor0S_curry_covGrad_operatorFieldComposition_eq (I := I) (M := M)
    g r t W y (w y) (tangentSpaceModelContinuousLinearEquiv (I := I) y v)
  simpa only [tensorCovDerivAt_def, ContinuousLinearEquiv.symm_apply_apply] using h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma covApply_covDeriv_apply_eq_add (r t : ℕ) (W : SmoothCcTensor g r t)
    {X Y : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun z : M => Tensor0SSpace r I z)⟯) (x : M) :
    Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            covApply (tensorCov (I := I) g r t) Y (fun z : M => W.toSection z) y) (w y)) x (X x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
          (covApplyCcSec (I := I) (M := M) g r t W hY) x (X x)) (w x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
            W.toSection x (Y x))
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
            w x (X x)) := by
  have h := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r t
    (LeviCivita (I := I) g) (covApplyCcSec (I := I) (M := M) g r t W hY) w x (X x)
  exact eq_add_of_eq_sub h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma covGrad_covDeriv_eval (r t : ℕ) (W : SmoothCcTensor g r t)
    {X Y : Π b : M, TangentSpace I b}
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun z : M => Tensor0SSpace r I z)⟯)
    (x : M) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from
          (covGrad (I := I) (M := M) g r t W).toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
            w x (X x))) (Fin.cons (Y x) m) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
            W.toSection x (Y x))
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
            w x (X x))) m := by
  rw [covGrad_toSection_apply_natural (I := I) (M := M) g r t W x
    (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w x (X x))
    (Fin.cons (Y x) m)]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' (Y x) m]
  rw [tensorCovDerivAt_def, ContinuousLinearEquiv.symm_apply_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem secondCovGrad_eval_eq_tensorSecondCovDeriv (r t : ℕ)
    (W : SmoothCcTensor g r t)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (x : M) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
          (covGrad (I := I) (M := M) g r (t + 1)
            (covGrad (I := I) (M := M) g r t W)).toSection x) D)
        (Fin.cons (X x) (Fin.cons (Y x) m)) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          tensorSecondCovDeriv (I := I) g r t X Y (fun y : M => W.toSection y) x) D) m := by
  classical
  obtain ⟨w, hwx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := Tensor0SModel r ℝ E)
    (V := fun z : M => Tensor0SSpace r I z) (n := (⊤ : ℕ∞)) x D
  subst hwx
  set GW : SmoothCcTensor g r (t + 1) := covGrad (I := I) (M := M) g r t W with hGW_def
  rw [covGrad_toSection_apply_natural (I := I) (M := M) g r (t + 1) GW x (w x)
    (Fin.cons (X x) (Fin.cons (Y x) m))]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' (X x) (Fin.cons (Y x) m)]
  have happly₁ : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from
      TensorRSNabla.tensorRSCovariantDerivative I M r (t + 1) (LeviCivita (I := I) g)
        GW.toSection x (X x)) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
          (fun y : M =>
            (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
              GW.toSection y) (w y)) x (X x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 1) I x from GW.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w x (X x)) :=
    TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r (t + 1)
      (LeviCivita (I := I) g) GW.toSection w x (X x)
  rw [tensorCovDerivAt_def, ContinuousLinearEquiv.symm_apply_apply]
  rw [happly₁, Tensor0SSpace.eval_sub]
  have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (t + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (t + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (t + 1) I z) y
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y))) :=
    ContMDiff.clm_bundle_apply (b := id) GW.toSection.contMDiff w.contMDiff
  have hP_curried : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel t ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace t I z) y
        (Tensor0SNabla.curriedSection I M
          (fun y' : M =>
            (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
              GW.toSection y') (w y')) y)) x :=
    TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y)) x (hP_smooth x)
  rw [show Tensor0SSpace.eval
      (Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
            GW.toSection y) (w y)) x (X x))
      (Fin.cons (Y x) m) =
    Tensor0SSpace.eval
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
        (Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
          (fun y : M =>
            (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
              GW.toSection y) (w y)) x (X x)) (Y x)) m from
    (tensor0S_curry_apply_eval (I := I) (M := M)
      (Tensor0SNabla.tensor0SCovariantDerivative I M (t + 1) (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y)) x (X x)) (Y x) m).symm]
  have habs :=
    curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g t
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (t + 1) I y from
          GW.toSection y) (w y))
      (Vfield := X) (Y := Y) (x := x)
      (hP_curried.mdifferentiableAt (by simp))
      ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))
  rw [habs, Tensor0SSpace.eval_sub]
  rw [hGW_def]
  have hsec : (fun y : M => Tensor0SNabla.curriedSection I M
      (fun y' : M =>
        (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
          (covGrad (I := I) (M := M) g r t W).toSection y') (w y')) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          covApply (tensorCov (I := I) g r t) Y (fun z : M => W.toSection z) y) (w y)) := by
    funext y
    rw [curried_covGrad_apply_eq_tensorCovDerivAt_apply (I := I) (M := M)
      g r t W w y (Y y)]
    rfl
  rw [hsec]
  rw [covApply_covDeriv_apply_eq_add (I := I) (M := M) g r t W hY w x,
    Tensor0SSpace.eval_add]
  rw [covGrad_covDeriv_eval (I := I) (M := M) g r t W w x m]
  have hC₁ : Tensor0SSpace.eval
      (Tensor0SNabla.curriedSection I M
        (fun y' : M =>
          (show Tensor0SSpace r I y' →L[ℝ] Tensor0SSpace (t + 1) I y' from
            (covGrad (I := I) (M := M) g r t W).toSection y') (w y')) x
              ((LeviCivita (I := I) g).toFun Y x (X x))) m =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
            W.toSection x ((LeviCivita (I := I) g).toFun Y x (X x))) (w x)) m := by
    rw [curried_covGrad_apply_eq_tensorCovDerivAt_apply (I := I) (M := M)
      g r t W w x ((LeviCivita (I := I) g).toFun Y x (X x))]
  rw [hC₁]
  have hSCD : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
      tensorSecondCovDeriv (I := I) g r t X Y (fun y : M => W.toSection y) x) (w x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
        TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
          (covApplyCcSec (I := I) (M := M) g r t W hY) x (X x)) (w x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          TensorRSNabla.tensorRSCovariantDerivative I M r t (LeviCivita (I := I) g)
            W.toSection x ((LeviCivita (I := I) g).toFun Y x (X x))) (w x) := rfl
  rw [hSCD, Tensor0SSpace.eval_sub]
  ring

end Bridge

end Curvature
end Geometry
end DifferentialGeometry
