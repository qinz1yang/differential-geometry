import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Uniqueness
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Smoothness
import DifferentialGeometry.Geometry.Connection.Realization.Tensor0SBridge
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.TensorSectionMDifferentiability
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral.OneFormRealization

open MeasureTheory
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic
open Bundle Tensor0SBundle
open Tensor0SNabla
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma toModel0S_apply {s : ℕ} {z : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z)
    (m : Fin s -> TangentSpace I z) :
    Tensor0SSpace.toModel T m = T m := rfl

private lemma toModel0S_sum {s : ℕ} {z : M} {ι : Type*} (t : Finset ι)
    (f : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s z) :
    Tensor0SSpace.toModel (∑ i ∈ t, f i) = ∑ i ∈ t, Tensor0SSpace.toModel (f i) :=
  map_sum (tensor0SSpace_continuousLinearEquiv (I := I) s z) f t

private lemma peel1_koszul
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (W : (y : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    {x : M} (hW : TensorSectionMDiffAt (I := I) 1 W x)
    (Zf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g) W x v)
        ![Zf x] =
      extDerivFun (I := I)
          (scalarFn I M (fun z : M => curriedSection I M W z (Zf z))) x v
        - Tensor0SSpace.toModel (W x)
            ![(LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M) g 0 W hW
    Zf v (fun i : Fin 0 => i.elim0)
  have hcons : (Fin.cons (Zf x) (fun i : Fin 0 => (i.elim0 : E)) : Fin 1 -> TangentSpace I x) =
      ![Zf x] := by
    funext i; fin_cases i; rfl
  have hcons2 : (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => Zf y) x v)
      (fun i : Fin 0 => (i.elim0 : E)) : Fin 1 -> TangentSpace I x) =
      ![(LeviCivita (I := I) g).toFun (fun y => Zf y) x v] := by
    funext i; fin_cases i; rfl
  rw [hcons, hcons2] at hpeel
  have hd0 : Tensor0SSpace.toModel
      (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => curriedSection I M W y (Zf y)) x v)
      (fun i : Fin 0 => i.elim0) =
      extDerivFun (I := I)
        (scalarFn I M (fun z : M => curriedSection I M W z (Zf z))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g
      (fun y : M => curriedSection I M W y (Zf y)) x v]
    rfl
  rw [hpeel, hd0]


private lemma abstract1
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hLC : IsLeviCivita (I := I) cov g)
    (α : OneFormSection (I := I) (M := M))
    (β : TwoTensorSection (I := I) (M := M))
    (hreal : NablaOneFormSectionRealizes (I := I) cov α β)
    (Xf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (y : M) (w : TangentSpace I y) :
    Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
          (fun z => α z) y (Xf y)) (fun _ : Fin 1 => w) =
      β y (vec2 (Xf y) w) := by
  classical
  set Zf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) y w, smoothExtensionTangent_contMDiff (I := I) y w⟩
    with hZfdef
  have hZfy : Zf y = w := smoothExtensionTangent_eq (I := I) y w
  have htmd : TensorSectionMDiffAt (I := I) 1 (fun z => α z) y :=
    α.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hpeel := peel1_koszul (I := I) (M := M) g (fun z => α z) htmd Zf (Xf y)
  have hLCeq : (LeviCivita (I := I) g).toFun (fun z => Zf z) y (Xf y) =
      (cov (fun z => Zf z) y) (Xf y) :=
    leviCivita_apply_eq_of_smooth_direction
      (I := I) (cov := LeviCivita (I := I) g) (cov' := cov)
      inferInstance inferInstance
      (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g) hLC
      (fun z => Zf z) (Zf.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Xf y)
  have hev := nabla0SFun_one_eval_smooth_slots (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    cov Xf Zf α y
  have hreal_y := (hreal y) Xf (Zf y)
  have hsc : scalarFn I M (fun z : M => curriedSection I M (fun z' => α z') z (Zf z)) =
      (fun p : M => α p (fun _ : Fin 1 => Zf p)) := by
    funext z
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M), curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := α z) (v0 := Zf z) (vs := fun i => Fin.elim0 i), toModel0S_apply]
    congr 1
    funext i; fin_cases i; rfl
  rw [← hZfy, show (fun _ : Fin 1 => Zf y) = ![Zf y] from by funext i; fin_cases i; rfl,
    hpeel, hreal_y, hev, hsc]
  congr 1
  rw [toModel0S_apply, hLCeq]
  congr 1
  funext i; fin_cases i; rfl

private lemma nabla0SFun_two_koszul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (A : TwoTensorSection (I := I) (M := M)) (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X A x
        (vec2 (Y x) (Z x)) =
      extDerivFun (I := I) (fun p : M => A p (vec2 (Y p) (Z p))) x (X x) -
        A x (vec2 ((cov (fun p => Y p) x) (X x)) (Z x)) -
        A x (vec2 (Y x) ((cov (fun p => Z p) x) (X x))) := by
  classical
  have h := nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s := 2) cov X ![Y, Z] A x
  have hslots : (fun a : Fin 2 => (![Y, Z] a) x) = vec2 (Y x) (Z x) := by
    funext a; fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hp : (fun p : M => A p (fun a : Fin 2 => (![Y, Z] a) p)) =
      (fun p : M => A p (vec2 (Y p) (Z p))) := by
    funext p; congr 1; funext a; fin_cases a <;>
      simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hslots, hp, Fin.sum_univ_two] at h
  have hu0 : (Function.update (vec2 (Y x) (Z x)) 0
        ((cov (fun p => (![Y, Z] 0) p) x) (X x))) =
      vec2 ((cov (fun p => Y p) x) (X x)) (Z x) := by
    funext a; fin_cases a <;>
      simp [Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hu1 : (Function.update (vec2 (Y x) (Z x)) 1
        ((cov (fun p => (![Y, Z] 1) p) x) (X x))) =
      vec2 (Y x) ((cov (fun p => Z p) x) (X x)) := by
    funext a; fin_cases a <;>
      simp [Function.update, vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hu0, hu1] at h
  rw [h]; ring




theorem wrapped_covGrad_rawConnLap_realizes_of_isLeviCivita
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hLC : IsLeviCivita (I := I) cov g)
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (W : SmoothCcTensor g 0 1)
    (hW : ∀ y : M, W.toSection y =
      Tensor0SSpace.toRS0 (alpha y))
    (x : M)
    (hreal : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x (nabla2Alpha x)) :
    (TensorSpectral.covGrad (I := I) (M := M) (g) 0 1 W).toFun x =
        TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaAlpha x))
      ∧ (rawTensorConnLapSmooth (I := I) (g) 0 1 W).toFun x =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) (g) (s := 1)
              (nabla2Alpha x))) := by
  classical
  have hreal1 : NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha := hreal.1
  have hWsec : (fun y : M => W.toSection y) =
      (fun y : M => (alpha).toTensorRSField ∞ y) := by
    funext y
    rw [hW y]
    exact (Tensor0SField.toRS0_eq (I := I) (M := M) ∞ (alpha) y).symm
  refine ⟨?_, ?_⟩
  · rw [SmoothCcTensor.toFun_apply]
    refine congrArg TensorRSSpace.toModel ?_
    refine ContinuousLinearMap.ext (fun D => ?_)
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    have hconv : TensorRSNabla.tensorRSCovariantDerivative I M 0 1
          (LeviCivita (I := I) (g))
          (fun y : M => W.toSection y) x (v 0) =
        Tensor0SSpace.toRS0
          (tensor0SCovariantDerivative I M 1
            (LeviCivita (I := I) (g)) (alpha) x (v 0)) := by
      rw [hWsec]
      exact nablaRS_toRS0 (I := I) (M := M)
        (LeviCivita (I := I) (g)) (alpha) x (v 0)
    change Tensor0SSpace.toModel
        ((TensorSpectral.covGrad (I := I) (M := M) (g) 0 1 W).toSection x
          D) v =
      Tensor0SSpace.toModel (Tensor0SSpace.toRS0 (nablaAlpha x) D) v
    rw [TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M)
        (g) 0 1 W x D v,
      TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) (g) 0 1 W x (v 0),
      hconv,
      Tensor0SSpace.toRS0_apply, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toRS0_apply,
      Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
      toModel0S_apply, toModel0S_apply]
    congr 1
    set Xf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hXfdef
    have hXfx : Xf x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
    have hab := abstract1 (I := I) (M := M) (g)
      (cov) hLC (alpha) (nablaAlpha)
      hreal1 Xf x (v 1)
    rw [hXfx, toModel0S_apply] at hab
    rw [show Matrix.vecTail v = (fun _ : Fin 1 => v 1) from by
      funext i; fin_cases i; rfl, hab,
      show vec2 (I := I) (v 0) (v 1) = v from by funext i; fin_cases i <;> rfl]
  · have hreal2 := hreal.2
    have hAsmooth : ContMDiff I (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) (∞ + 1)
        (fun z : M => TotalSpace.mk' (Tensor0SModel 1 Real E)
          (E := fun y : M => Tensor0SSpace 1 I y) z ((alpha) z)) := by
      simpa using (alpha).contMDiff
    let dA : Fin (Module.finrank Real E) -> OneFormSection (I := I) (M := M) :=
      fun i => ⟨fun z : M => tensor0SCovariantDerivative I M 1
          (LeviCivita (I := I) (g)) (alpha) z
          (smoothOrthoFrame (I := I) (g) x i z),
        by
          have hc := covApply_contMDiffOn
            (cov := tensor0SCovariantDerivative I M 1
              (LeviCivita (I := I) (g)))
            (smoothOrthoFrame_smooth (I := I) (g) x i) hAsmooth
          rwa [contMDiffOn_univ] at hc⟩
    have hdAeq : ∀ i (z : M), dA i z =
        tensor0SCovariantDerivative I M 1
          (LeviCivita (I := I) (g)) (alpha) z
          (smoothOrthoFrame (I := I) (g) x i z) := fun i z => rfl
    have hinner : ∀ (i : Fin (Module.finrank Real E)) (tail : Fin 1 -> TangentSpace I x),
        Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 1
              (LeviCivita (I := I) (g)) (dA i) x
              (smoothOrthoFrame (I := I) (g) x i x)) tail -
          Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 1
              (LeviCivita (I := I) (g)) (alpha) x
              ((LeviCivita (I := I) (g)).toFun
                (smoothOrthoFrame (I := I) (g) x i) x
                (smoothOrthoFrame (I := I) (g) x i x))) tail =
          nabla2Alpha x
            (vec3 (smoothOrthoFrame (I := I) (g) x i x)
              (smoothOrthoFrame (I := I) (g) x i x) (tail 0)) := by
      intro i tail
      set Zf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
        ⟨smoothExtensionTangent (I := I) x (tail 0),
          smoothExtensionTangent_contMDiff (I := I) x (tail 0)⟩ with hZf_def
      have hZfx : Zf x = tail 0 := smoothExtensionTangent_eq (I := I) x (tail 0)
      set Wf : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
        ⟨smoothExtensionTangent (I := I) x
            ((LeviCivita (I := I) (g)).toFun
              (smoothOrthoFrame (I := I) (g) x i) x
              (smoothOrthoFrame (I := I) (g) x i x)),
          smoothExtensionTangent_contMDiff (I := I) x _⟩ with hWf_def
      have hWfx : Wf x =
          (LeviCivita (I := I) (g)).toFun
            (smoothOrthoFrame (I := I) (g) x i) x
            (smoothOrthoFrame (I := I) (g) x i x) :=
        smoothExtensionTangent_eq (I := I) x _
      have htmddA : TensorSectionMDiffAt (I := I) 1 (fun z => dA i z) x :=
        (dA i).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hpeel := peel1_koszul (I := I) (M := M) (g)
        (fun z => dA i z) htmddA Zf
        (smoothOrthoFrame (I := I) (g) x i x)
      have hsc : scalarFn I M (fun z : M => curriedSection I M (fun w => dA i w) z (Zf z)) =
          (fun z : M => nablaAlpha z
            (vec2 (smoothOrthoFrame (I := I) (g) x i z) (Zf z))) := by
        funext z
        rw [scalarFn_eq_toModel_elim0 (I := I) (M := M), curriedSection_apply,
          TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := dA i z) (v0 := Zf z) (vs := fun k => Fin.elim0 k), toModel0S_apply,
          show (Fin.cons (Zf z) (fun k : Fin 0 => (k.elim0 : E)) : Fin 1 -> TangentSpace I z) =
              (fun _ : Fin 1 => Zf z) from by funext k; fin_cases k; rfl,
          hdAeq i z]
        have hab := abstract1 (I := I) (M := M) (g)
          (cov) hLC (alpha) (nablaAlpha) hreal1
          ⟨smoothOrthoFrame (I := I) (g) x i,
            smoothOrthoFrame_smooth (I := I) (g) x i⟩ z (Zf z)
        rw [toModel0S_apply] at hab
        exact hab
      have hfirst : Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 1
            (LeviCivita (I := I) (g)) (dA i) x
            (smoothOrthoFrame (I := I) (g) x i x)) tail =
          extDerivFun (I := I)
              (fun z : M => nablaAlpha z
                (vec2 (smoothOrthoFrame (I := I) (g) x i z) (Zf z))) x
              (smoothOrthoFrame (I := I) (g) x i x) -
            nablaAlpha x
              (vec2 (smoothOrthoFrame (I := I) (g) x i x)
                ((LeviCivita (I := I) (g)).toFun (fun w => Zf w) x
                  (smoothOrthoFrame (I := I) (g) x i x))) := by
        rw [show tail = ![Zf x] from by funext k; fin_cases k; exact hZfx.symm, hpeel, hsc]
        congr 1
        rw [toModel0S_apply, hdAeq i x,
          show (![(LeviCivita (I := I) (g)).toFun (fun w => Zf w) x
                (smoothOrthoFrame (I := I) (g) x i x)] :
              Fin 1 -> TangentSpace I x) =
              (fun _ : Fin 1 =>
                (LeviCivita (I := I) (g)).toFun (fun w => Zf w) x
                  (smoothOrthoFrame (I := I) (g) x i x)) from by
            funext k; fin_cases k; rfl]
        have hab2 := abstract1 (I := I) (M := M) (g)
          (cov) hLC (alpha) (nablaAlpha) hreal1
          ⟨smoothOrthoFrame (I := I) (g) x i,
            smoothOrthoFrame_smooth (I := I) (g) x i⟩ x
          ((LeviCivita (I := I) (g)).toFun (fun w => Zf w) x
            (smoothOrthoFrame (I := I) (g) x i x))
        rw [toModel0S_apply] at hab2
        exact hab2
      have hsecond : Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 1
            (LeviCivita (I := I) (g)) (alpha) x
            ((LeviCivita (I := I) (g)).toFun
              (smoothOrthoFrame (I := I) (g) x i) x
              (smoothOrthoFrame (I := I) (g) x i x))) tail =
          nablaAlpha x
            (vec2 ((LeviCivita (I := I) (g)).toFun
                (smoothOrthoFrame (I := I) (g) x i) x
                (smoothOrthoFrame (I := I) (g) x i x)) (tail 0)) := by
        rw [show tail = (fun _ : Fin 1 => tail 0) from by funext k; fin_cases k; rfl]
        have hab3 := abstract1 (I := I) (M := M) (g)
          (cov) hLC (alpha) (nablaAlpha) hreal1
          Wf x (tail 0)
        rw [hWfx] at hab3
        exact hab3
      have hR : nabla2Alpha x
            (vec3 (smoothOrthoFrame (I := I) (g) x i x)
              (smoothOrthoFrame (I := I) (g) x i x) (tail 0)) =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (cov)
            ⟨smoothOrthoFrame (I := I) (g) x i,
              smoothOrthoFrame_smooth (I := I) (g) x i⟩
            (nablaAlpha) x
            (vec2 (smoothOrthoFrame (I := I) (g) x i x) (tail 0)) :=
        hreal2 ⟨smoothOrthoFrame (I := I) (g) x i,
            smoothOrthoFrame_smooth (I := I) (g) x i⟩
          (smoothOrthoFrame (I := I) (g) x i x) (tail 0)
      rw [hfirst, hsecond, hR]
      have hev2 : nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
            (cov)
            ⟨smoothOrthoFrame (I := I) (g) x i,
              smoothOrthoFrame_smooth (I := I) (g) x i⟩
            (nablaAlpha) x
            (vec2 (smoothOrthoFrame (I := I) (g) x i x) (tail 0)) =
          extDerivFun (I := I) (fun p : M => nablaAlpha p
              (vec2 (smoothOrthoFrame (I := I) (g) x i p) (Zf p))) x
              (smoothOrthoFrame (I := I) (g) x i x) -
            nablaAlpha x
              (vec2 ((cov)
                  (fun p => smoothOrthoFrame (I := I) (g) x i p) x
                  (smoothOrthoFrame (I := I) (g) x i x)) (tail 0)) -
            nablaAlpha x
              (vec2 (smoothOrthoFrame (I := I) (g) x i x)
                ((cov) (fun p => Zf p) x
                  (smoothOrthoFrame (I := I) (g) x i x))) := by
        have hk := nabla0SFun_two_koszul (I := I) (M := M) (cov)
          ⟨smoothOrthoFrame (I := I) (g) x i,
            smoothOrthoFrame_smooth (I := I) (g) x i⟩
          ⟨smoothOrthoFrame (I := I) (g) x i,
            smoothOrthoFrame_smooth (I := I) (g) x i⟩ Zf
          (nablaAlpha) x
        rw [hZfx] at hk
        exact hk
      rw [hev2]
      have hLCa : (cov) (fun p => Zf p) x
            (smoothOrthoFrame (I := I) (g) x i x) =
          (LeviCivita (I := I) (g)).toFun (fun w => Zf w) x
            (smoothOrthoFrame (I := I) (g) x i x) :=
        leviCivita_apply_eq_of_smooth_direction (I := I)
          (cov := cov)
          (cov' := LeviCivita (I := I) (g)) inferInstance inferInstance
          hLC (leviCivitaConnectionOfMetric_isLeviCivita (I := I) (g))
          (fun z => Zf z) (Zf.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (smoothOrthoFrame (I := I) (g) x i x)
      have hLCb : (cov)
            (fun p => smoothOrthoFrame (I := I) (g) x i p) x
            (smoothOrthoFrame (I := I) (g) x i x) =
          (LeviCivita (I := I) (g)).toFun
            (smoothOrthoFrame (I := I) (g) x i) x
            (smoothOrthoFrame (I := I) (g) x i x) :=
        leviCivita_apply_eq_of_smooth_direction (I := I)
          (cov := cov)
          (cov' := LeviCivita (I := I) (g)) inferInstance inferInstance
          hLC (leviCivitaConnectionOfMetric_isLeviCivita (I := I) (g))
          (fun z => smoothOrthoFrame (I := I) (g) x i z)
          ((smoothOrthoFrame_smooth (I := I) (g) x i).contMDiffAt.mdifferentiableAt
            (by simp))
          (smoothOrthoFrame (I := I) (g) x i x)
      rw [hLCa, hLCb]
      ring
    have hterm : ∀ i : Fin (Module.finrank Real E),
        tensorSecondCovDeriv (I := I) (g) 0 1
            (smoothOrthoFrame (I := I) (g) x i)
            (smoothOrthoFrame (I := I) (g) x i)
            (fun z => W.toSection z) x =
          Tensor0SSpace.toRS0
              (tensor0SCovariantDerivative I M 1
                (LeviCivita (I := I) (g)) (dA i) x
                (smoothOrthoFrame (I := I) (g) x i x)) -
            Tensor0SSpace.toRS0
              (tensor0SCovariantDerivative I M 1
                (LeviCivita (I := I) (g)) (alpha) x
                ((LeviCivita (I := I) (g)).toFun
                  (smoothOrthoFrame (I := I) (g) x i) x
                  (smoothOrthoFrame (I := I) (g) x i x))) := by
      intro i
      have hcovApply : covApply (tensorCov (I := I) (g) 0 1)
            (smoothOrthoFrame (I := I) (g) x i)
            (fun z => W.toSection z) =
          (fun z : M => (dA i).toTensorRSField ∞ z) := by
        funext z
        rw [covApply_apply,
          show (tensorCov (I := I) (g) 0 1).toFun
                (fun w => W.toSection w) z
                (smoothOrthoFrame (I := I) (g) x i z) =
              TensorRSNabla.tensorRSCovariantDerivative I M 0 1
                (LeviCivita (I := I) (g))
                (fun w => W.toSection w) z
                (smoothOrthoFrame (I := I) (g) x i z) from rfl, hWsec,
          nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) (g))
            (alpha) z (smoothOrthoFrame (I := I) (g) x i z),
          Tensor0SField.toRS0_eq]
        rfl
      rw [tensorSecondCovDeriv_def, hcovApply,
        show (tensorCov (I := I) (g) 0 1).toFun
              (fun z : M => (dA i).toTensorRSField ∞ z) x
              (smoothOrthoFrame (I := I) (g) x i x) =
            TensorRSNabla.tensorRSCovariantDerivative I M 0 1
              (LeviCivita (I := I) (g))
              ((dA i).toTensorRSField ∞) x
              (smoothOrthoFrame (I := I) (g) x i x) from rfl,
        nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) (g))
          (dA i) x (smoothOrthoFrame (I := I) (g) x i x),
        show (tensorCov (I := I) (g) 0 1).toFun
              (fun z => W.toSection z) x
              ((LeviCivita (I := I) (g)).toFun
                (smoothOrthoFrame (I := I) (g) x i) x
                (smoothOrthoFrame (I := I) (g) x i x)) =
            TensorRSNabla.tensorRSCovariantDerivative I M 0 1
              (LeviCivita (I := I) (g)) (fun w => W.toSection w) x
              ((LeviCivita (I := I) (g)).toFun
                (smoothOrthoFrame (I := I) (g) x i) x
                (smoothOrthoFrame (I := I) (g) x i x)) from rfl,
        hWsec,
        nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) (g))
          (alpha) x
          ((LeviCivita (I := I) (g)).toFun
            (smoothOrthoFrame (I := I) (g) x i) x
            (smoothOrthoFrame (I := I) (g) x i x))]
    have horth : ∀ a b : Fin (Module.finrank Real E),
        (g).inner x
            (smoothOrthoFrame (I := I) (g) x a x)
            (smoothOrthoFrame (I := I) (g) x b x) =
          if a = b then 1 else 0 :=
      fun a b => smoothOrthoFrame_orthonormal_at_center (I := I)
        (g) x a b
    have hli : LinearIndependent Real
        (fun i : Fin (Module.finrank Real E) =>
          smoothOrthoFrame (I := I) (g) x i x) := by
      classical
      rw [Fintype.linearIndependent_iff]
      intro c hc j
      have hpair : (g).inner x
          (∑ a, c a • smoothOrthoFrame (I := I) (g) x a x)
          (smoothOrthoFrame (I := I) (g) x j x) = 0 := by
        rw [hc]; simp
      rw [map_sum, ContinuousLinearMap.sum_apply, Finset.sum_eq_single j] at hpair
      · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth j j,
          if_pos rfl, smul_eq_mul, mul_one] at hpair
        exact hpair
      · intro a _ haj
        rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth a j,
          if_neg (by simpa using haj), smul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    let basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
      basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; rfl)
    have hbasis : ∀ i, basis i = smoothOrthoFrame (I := I) (g) x i x := by
      intro i
      change (basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; rfl)) i =
        smoothOrthoFrame (I := I) (g) x i x
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    have hinv : MetricInverseInBasis_gen (I := I) (g) x basis
        (identityInvMetric (Idx := Fin (Module.finrank Real E))) := by
      intro a b
      simp only [identityInvMetric, diagonalInvMetric, hbasis]
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_eq_single a]
        · rw [if_pos rfl, one_mul, horth]
        · intro c _ hc; rw [if_neg (fun heq => hc heq.symm), zero_mul]
        · intro hcon; exact absurd (Finset.mem_univ a) hcon
      · rw [Finset.sum_eq_single b]
        · rw [if_pos rfl, mul_one, horth]
        · intro c _ hc; rw [if_neg hc, mul_zero]
        · intro hcon; exact absurd (Finset.mem_univ b) hcon
    have hcollapse : ∀ tail : Fin 1 -> TangentSpace I x,
        roughLap0STensor (I := I) (g) (s := 1)
          (nabla2Alpha x) tail =
          ∑ i : Fin (Module.finrank Real E),
            nabla2Alpha x
              (vec3 (smoothOrthoFrame (I := I) (g) x i x)
                (smoothOrthoFrame (I := I) (g) x i x) (tail 0)) := by
      intro tail
      rw [roughLap0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (g) basis
          (identityInvMetric (Idx := Fin (Module.finrank Real E))) hinv]
      unfold metricTrace0S2InBasis
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_eq_single a]
      · rw [identityInvMetric_apply_self, one_mul, hbasis,
          show metricTraceInput (I := I)
                (smoothOrthoFrame (I := I) (g) x a x)
                (smoothOrthoFrame (I := I) (g) x a x) tail =
              metricTraceInput (I := I)
                (smoothOrthoFrame (I := I) (g) x a x)
                (smoothOrthoFrame (I := I) (g) x a x)
                (fun _ : Fin 1 => tail 0) from by
            congr 1; funext k; fin_cases k; rfl,
          metricTraceInput_one_eq_vec3]
      · intro b _ hba
        rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun heq => hba heq.symm),
          zero_mul]
      · intro hcon; exact absurd (Finset.mem_univ a) hcon
    rw [SmoothCcTensor.toFun_apply]
    refine congrArg TensorRSSpace.toModel ?_
    rw [rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv]
    refine ContinuousLinearMap.ext (fun D => ?_)
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun tail => ?_)
    change Tensor0SSpace.toModel
        ((∑ i : Fin (Module.finrank Real E),
            tensorSecondCovDeriv (I := I) (g) 0 1
              (smoothOrthoFrame (I := I) (g) x i)
              (smoothOrthoFrame (I := I) (g) x i)
              (fun z => W.toSection z) x) D) tail =
      Tensor0SSpace.toModel
        (Tensor0SSpace.toRS0
          (roughLap0STensor (I := I) (g) (s := 1)
            (nabla2Alpha x)) D) tail
    rw [ContinuousLinearMap.sum_apply, toModel0S_sum, ContinuousMultilinearMap.sum_apply,
      Tensor0SSpace.toRS0_apply, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, toModel0S_apply, hcollapse, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hterm i, ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply, Tensor0SSpace.toRS0_apply, Tensor0SSpace.toRS0_apply,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
      ← smul_sub, hinner i tail]



theorem wrapped_covGrad_rawConnLap_realizes
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (W : SmoothCcTensor g 0 1)
    (hW : ∀ y : M, W.toSection y = Tensor0SSpace.toRS0 (alpha y))
    (x : M)
    (hreal : Nabla2OneFormRealizesAt (I := I) (LeviCivita (I := I) g)
      alpha nablaAlpha x (nabla2Alpha x)) :
    (TensorSpectral.covGrad (I := I) (M := M) g 0 1 W).toFun x =
        TensorRSSpace.toModel (Tensor0SSpace.toRS0 (nablaAlpha x))
      ∧ (rawTensorConnLapSmooth (I := I) g 0 1 W).toFun x =
        TensorRSSpace.toModel
          (Tensor0SSpace.toRS0
            (roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x))) :=
  wrapped_covGrad_rawConnLap_realizes_of_isLeviCivita g (LeviCivita (I := I) g)
    (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g)
    alpha nablaAlpha nabla2Alpha W hW x hreal

end DifferentialGeometry.Analysis.Spectral.OneFormRealization

end
