import DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Norm.Product
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Geometry.Operator.MetricFamily
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem inner0S_contMDiff {s : ℕ}
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M => inner0S (I := I) g y s (A y) (B y)) := by
  classical
  intro x
  set Idx : Type := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
    with hIdx
  set frame : Idx -> (y : M) -> TangentSpace I y :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x with hframe
  set U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
        (I := I) g x i j (extChartAt I x y) with hU
  set cA : M -> (Fin s -> Idx) -> Real :=
    fun y I0 => A y (fun a => frame (I0 a) y) with hcAdef
  set cB : M -> (Fin s -> Idx) -> Real :=
    fun y J0 => B y (fun a => frame (J0 a) y) with hcBdef
  have hx : x ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x
  have hlocal :
      (fun y : M => inner0S (I := I) g y s (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => coordContract (U y) (cA y) (cB y) := by
    filter_upwards
      [(DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    rw [inner0S_eq_coord (I := I) g y s
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtBasis (I := I) x hy)
      (U y) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)]
    rw [← coordContract_eq_coordInner0S (I := I) (U y) (A y) (B y)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtBasis (I := I) x hy)]
    refine congrArg₂ (fun f h => coordContract (U y) f h) ?_ ?_
    · funext I0
      simp only [tensor0SComponent, cA, frame]
      refine congrArg (fun w => A y w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
    · funext J0
      simp only [tensor0SComponent, cB, frame]
      refine congrArg (fun w => B y w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
  have hcontr : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M => coordContract (U y) (cA y) (cB y)) x := by
    unfold coordContract
    refine ContMDiffAt.sum fun I0 _ => ContMDiffAt.sum fun J0 _ => ?_
    have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    have hprodU : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => ∏ a : Fin s, U y (I0 a) (J0 a)) x := by
      exact ContMDiffAt.prod fun a _ =>
        DifferentialGeometry.Tensor.Coordinates.gInvComp_contMDiffAt (I := I) g x (I0 a) (J0 a)
    have hcAat : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => cA y I0) x := by
      simpa [cA, frame] using
        DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
          (𝕜 := Real) (I := I) (M := M) A x I0
    have hcBat : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => cB y J0) x := by
      simpa [cB, frame] using
        DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
          (𝕜 := Real) (I := I) (M := M) B x J0
    exact (hprodU.mul hcAat).mul hcBat
  exact hcontr.congr_of_eventuallyEq hlocal

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem inner0S_sum_smul_left {s : ℕ} {Idx : Type*} [Fintype Idx]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (c : Idx -> Idx -> Real)
    (T : Idx -> Idx -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (S : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s (∑ i : Idx, ∑ j : Idx, c i j • T i j) S =
      ∑ i : Idx, ∑ j : Idx, c i j * inner0S (I := I) g x s (T i j) S := by
  classical
  simp only [inner0S, MetricFiberData.inner, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply]
  simp only [smul_eq_mul]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem inner0S_sum_smul_right {s : ℕ} {Idx : Type*} [Fintype Idx]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (c : Idx -> Idx -> Real)
    (T : Idx -> Idx -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (S : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s S (∑ i : Idx, ∑ j : Idx, c i j • T i j) =
      ∑ i : Idx, ∑ j : Idx, c i j * inner0S (I := I) g x s S (T i j) := by
  classical
  rw [inner0S_symm (I := I) g x S (∑ i : Idx, ∑ j : Idx, c i j • T i j)]
  rw [inner0S_sum_smul_left (I := I) g x c T S]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [inner0S_symm (I := I) g x (T i j) S]

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem hessianSec_inner0S_slots {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov (∞ : WithTop ℕ∞))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov nablaA nabla2A)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov B nablaB)
    (h2B : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov nablaB nabla2B)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) (Y : TangentSpace I x) :
    hessianSec (I := I) cov hcov
        (fun y : M => inner0S (I := I) g y s (A y) (B y))
        (inner0S_contMDiff g A B) x (vec2 (I := I) (X x) Y) =
      inner0S (I := I) g x s
        (freezeFirstTwoArgs0S (I := I) (nabla2A x) (X x) Y) (B x) +
      inner0S (I := I) g x s
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) Y)
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (X x)) +
      inner0S (I := I) g x s
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (X x))
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) Y) +
      inner0S (I := I) g x s (A x)
        (freezeFirstTwoArgs0S (I := I) (nabla2B x) (X x) Y) := by
  classical
  let phi : M -> Real := fun y => inner0S (I := I) g y s (A y) (B y)
  have hphi : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) phi := inner0S_contMDiff g A B
  let du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    duSec (I := I) phi hphi
  let Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y).choose
  have hZ : Z x = Y :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y).choose_spec
  have hHess := hessianSec_realizesAt (I := I) cov hcov phi hphi x
  have hduZ : ∀ y : M,
      du y (fun _ : Fin 1 => Z y) =
        inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y) +
          inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y) := by
    intro y
    rw [duSec_apply]
    rw [differential1FormFun_apply_eq_mvfderiv]
    have hL := inner0S_nabla (I := I) cov g hmc A B Z y
    have hAderiv :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov Z A y =
          tensor0SCurry (I := I) (𝕜 := Real) (M := M) s y (nablaA y) (Z y) := by
      ext v
      rw [tensor0S_curry_apply_cons]
      exact (TotalNabla0SRealizes.apply (I := I) hA Z y v).symm
    have hBderiv :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov Z B y =
          tensor0SCurry (I := I) (𝕜 := Real) (M := M) s y (nablaB y) (Z y) := by
      ext v
      rw [tensor0S_curry_apply_cons]
      exact (TotalNabla0SRealizes.apply (I := I) hB Z y v).symm
    rw [hL, hAderiv, hBderiv]
    rw [partialEval0SField_apply, partialEval0SField_apply]
  have hfun :
      (fun y : M => du y (fun _ : Fin 1 => Z y)) =
        fun y : M =>
          inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y) +
            inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y) :=
    funext hduZ
  have hFmdiff : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y)) x :=
    inner0S_mdiff (I := I) g (partialEval0SField (I := I) nablaA Z) B x
  have hGmdiff : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y)) x :=
    inner0S_mdiff (I := I) g A (partialEval0SField (I := I) nablaB Z) x
  have hderF :
      mvfderiv (I := I)
        (fun y : M =>
          inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y)) x (X x) =
        inner0S (I := I) g x s
          (freezeFirstTwoArgs0S (I := I) (nabla2A x) (X x) (Z x)) (B x) +
        inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x)
            ((cov (fun y : M => Z y) x) (X x))) (B x) +
        inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (Z x))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (X x)) := by
    have h := inner0S_nabla (I := I) cov g hmc (partialEval0SField (I := I) nablaA Z) B X x
    have hP := nabla_partialEval0S (I := I) cov nablaA nabla2A h2A X Z x
    have hBderiv :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X B x =
          tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (X x) := by
      ext v
      rw [tensor0S_curry_apply_cons]
      exact (TotalNabla0SRealizes.apply (I := I) hB X x v).symm
    have hPx : partialEval0SField (I := I) nablaA Z x =
        tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (Z x) :=
      partialEval0SField_apply (I := I) nablaA Z x
    have hadd : ∀ (P Q R : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x),
        inner0S (I := I) g x s (P + Q) R =
          inner0S (I := I) g x s P R + inner0S (I := I) g x s Q R := by
      intro P Q R
      simp only [inner0S, MetricFiberData.inner, map_add, LinearMap.add_apply]
    rw [h, hP, hBderiv, hPx]
    rw [hadd]
  have hderG :
      mvfderiv (I := I)
        (fun y : M =>
          inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y)) x (X x) =
        inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (X x))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (Z x)) +
        inner0S (I := I) g x s (A x)
          (freezeFirstTwoArgs0S (I := I) (nabla2B x) (X x) (Z x)) +
        inner0S (I := I) g x s (A x)
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x)
            ((cov (fun y : M => Z y) x) (X x))) := by
    have h := inner0S_nabla (I := I) cov g hmc A (partialEval0SField (I := I) nablaB Z) X x
    have hAderiv :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X A x =
          tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (X x) := by
      ext v
      rw [tensor0S_curry_apply_cons]
      exact (TotalNabla0SRealizes.apply (I := I) hA X x v).symm
    have hQ := nabla_partialEval0S (I := I) cov nablaB nabla2B h2B X Z x
    have hQx : partialEval0SField (I := I) nablaB Z x =
        tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (Z x) :=
      partialEval0SField_apply (I := I) nablaB Z x
    have hadd : ∀ (P Q R : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x),
        inner0S (I := I) g x s P (Q + R) =
          inner0S (I := I) g x s P Q + inner0S (I := I) g x s P R := by
      intro P Q R
      simp only [inner0S, MetricFiberData.inner, map_add]
    rw [h, hAderiv, hQ, hQx]
    rw [hadd]
    ring
  have hcorr : du x (fun _ : Fin 1 => (cov (fun y : M => Z y) x) (X x)) =
      inner0S (I := I) g x s
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x)
          ((cov (fun y : M => Z y) x) (X x))) (B x) +
      inner0S (I := I) g x s (A x)
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x)
          ((cov (fun y : M => Z y) x) (X x))) := by
    rw [duSec_apply]
    rw [differential1FormFun_apply_eq_mvfderiv]
    let W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
        ((cov (fun y : M => Z y) x) (X x))).choose
    have hW : W x = (cov (fun y : M => Z y) x) (X x) :=
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
        ((cov (fun y : M => Z y) x) (X x))).choose_spec
    have hL := inner0S_nabla (I := I) cov g hmc A B W x
    have hAderiv :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov W A x =
          tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (W x) := by
      ext v
      rw [tensor0S_curry_apply_cons]
      exact (TotalNabla0SRealizes.apply (I := I) hA W x v).symm
    have hBderiv :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov W B x =
          tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (W x) := by
      ext v
      rw [tensor0S_curry_apply_cons]
      exact (TotalNabla0SRealizes.apply (I := I) hB W x v).symm
    rw [← hW, hL, hAderiv, hBderiv, hW]
  have hEval' :
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X du x)
        (fun _ : Fin 1 => Y) =
      mvfderiv (I := I) (fun y : M => du y (fun _ : Fin 1 => Z y)) x (X x) -
        du x (fun _ : Fin 1 => (cov (fun y : M => Z y) x) (X x)) := by
    simpa [hZ] using (nabla0SFun_one_eval_smooth_slots (I := I) cov X Z du x)
  have hfun' :
      mvfderiv (I := I) (fun y : M => du y (fun _ : Fin 1 => Z y)) x (X x) =
        mvfderiv (I := I)
            (fun y : M =>
              inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y)) x (X x) +
          mvfderiv (I := I)
            (fun y : M =>
              inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y)) x (X x) := by
    rw [hfun]
    change mvfderiv (I := I)
        ((fun y : M =>
            inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y)) +
          (fun y : M =>
            inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y))) x (X x) =
      mvfderiv (I := I)
          (fun y : M =>
            inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y)) x (X x) +
        mvfderiv (I := I)
          (fun y : M =>
            inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y)) x (X x)
    rw [mvfderiv_add (I := I)
      (g := fun y : M =>
        inner0S (I := I) g y s (partialEval0SField (I := I) nablaA Z y) (B y))
      (g' := fun y : M =>
        inner0S (I := I) g y s (A y) (partialEval0SField (I := I) nablaB Z y))
      (x := x) hFmdiff hGmdiff]
    rw [add_apply]
  have hmain :
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X du x)
        (fun _ : Fin 1 => Y) =
      inner0S (I := I) g x s
        (freezeFirstTwoArgs0S (I := I) (nabla2A x) (X x) (Z x)) (B x) +
      inner0S (I := I) g x s
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (Z x))
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (X x)) +
      inner0S (I := I) g x s
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (X x))
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (Z x)) +
      inner0S (I := I) g x s (A x)
        (freezeFirstTwoArgs0S (I := I) (nabla2B x) (X x) (Z x)) := by
    rw [hEval']
    rw [hfun']
    rw [hderF, hderG]
    rw [hcorr]
    ring
  rw [show hessianSec (I := I) cov hcov phi hphi x (vec2 (I := I) (X x) Y) =
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X du x)
          (fun _ : Fin 1 => Y) from by
    simpa [nablaDuAt, du] using (hHess X Y)]
  rw [hmain]
  rw [hZ]

omit [CompleteSpace E] [SigmaCompactSpace M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [T2Space M] in
private theorem metricTraceInput_elim0_eq_vec2 {x : M} (X Y : TangentSpace I x) :
    metricTraceInput (I := I) X Y Fin.elim0 = vec2 (I := I) X Y := by
  funext i
  fin_cases i <;> rfl

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem laplacianAt_inner0S_eq_inner_roughLap_of_flat
    {s : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s (G.connection t) A nablaA)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (G.connection t) nablaA nabla2A)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s (G.connection t) B nablaB)
    (h2B : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (G.connection t) nablaB nabla2B)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally (G.connection t)
      (∞ : WithTop ℕ∞))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (G.metric t) x basis gInv)
    (hBflat1 : nablaB x = 0)
    (hBflat2 : metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2B x) = 0) :
    laplacianAt (I := I) G t
        (fun y : M => inner0S (I := I) (G.metric t) y s (A y) (B y)) x =
      inner0S (I := I) (G.metric t) x s
        (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2A x)) (B x) := by
  classical
  let g : DifferentialGeometry.SmoothRiemannianMetric I M := G.metric t
  let cov : CovariantDerivative I E (TangentSpace I : M -> Type _) := G.connection t
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen (I := I) cov g := by
    simpa [cov, g] using (G.metricCompatible t)
  let phi : M -> Real := fun y => inner0S (I := I) g y s (A y) (B y)
  have hphi : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) phi := inner0S_contMDiff g A B
  have hlap : ScalarLaplacianRealizesTraceAt (I := I) cov g phi
      (hessianSec (I := I) cov hcov phi hphi x) :=
    scalarLap_smooth (I := I) (M := M) (cov := cov) hcov g hmc phi hphi
  unfold ScalarLaplacianRealizesTraceAt at hlap
  have hlapAt : laplacianAt (I := I) G t phi x =
      metricTraceFirstTwo0SAt (I := I) g
        (hessianSec (I := I) cov hcov phi hphi x) Fin.elim0 := by
    simpa [laplacianAt, phi, g, cov] using hlap
  rw [hlapAt]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis g basis gInv hinv
    (hessianSec (I := I) cov hcov phi hphi x) Fin.elim0]
  let Ei : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun i => (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose
  have hEi : ∀ i : Idx, Ei i x = basis i := fun i =>
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose_spec
  have hslot : ∀ i j : Idx,
      (hessianSec (I := I) cov hcov phi hphi x) (vec2 (I := I) (basis i) (basis j)) =
        inner0S (I := I) g x s
          (freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j)) (B x) +
        inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (basis j))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (basis i)) +
        inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (basis i))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (basis j)) +
        inner0S (I := I) g x s (A x)
          (freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j)) := by
    intro i j
    have h := hessianSec_inner0S_slots (I := I) cov hcov g hmc A B nablaA nabla2A nablaB nabla2B
      hA h2A hB h2B (Ei i) x (basis j)
    simpa [phi, hEi i] using h
  have hcurryB : ∀ w : TangentSpace I x,
      tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) w = 0 := by
    intro w
    rw [hBflat1]
    ext v
    rw [tensor0S_curry_apply_cons]
    rfl
  have hsumA : (∑ i : Idx, ∑ j : Idx,
        gInv i j * inner0S (I := I) g x s
          (freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j)) (B x)) =
      inner0S (I := I) g x s
        (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2A x)) (B x) := by
    rw [metricTrace0S2TensorInBasis]
    exact (inner0S_sum_smul_left (I := I) g x gInv
      (fun i j : Idx => freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j))
      (B x)).symm
  have hsumB : (∑ i : Idx, ∑ j : Idx,
        gInv i j * inner0S (I := I) g x s (A x)
          (freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j))) =
      inner0S (I := I) g x s (A x)
        (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2B x)) := by
    rw [metricTrace0S2TensorInBasis]
    exact (inner0S_sum_smul_right (I := I) g x gInv
      (fun i j : Idx => freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j))
      (A x)).symm
  have hB2zero : inner0S (I := I) g x s (A x)
      (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2B x)) = 0 := by
    rw [hBflat2]
    simp [inner0S]
  have hcross1 : (∑ i : Idx, ∑ j : Idx,
        gInv i j * inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (basis j))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (basis i))) = 0 := by
    simp [hcurryB, inner0S]
  have hcross2 : (∑ i : Idx, ∑ j : Idx,
        gInv i j * inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (basis i))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (basis j))) = 0 := by
    simp [hcurryB, inner0S]
  unfold metricTrace0S2InBasis
  simp_rw [metricTraceInput_elim0_eq_vec2]
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * (hessianSec (I := I) cov hcov phi hphi x) (vec2 (I := I) (basis i) (basis j)))
        = ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (inner0S (I := I) g x s
            (freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j)) (B x) +
          inner0S (I := I) g x s
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (basis j))
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (basis i)) +
          inner0S (I := I) g x s
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaA x) (basis i))
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x (nablaB x) (basis j)) +
          inner0S (I := I) g x s (A x)
            (freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hslot i j]
    _ = inner0S (I := I) (G.metric t) x s
        (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2A x)) (B x) := by
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib]
      rw [hsumA, hcross1, hcross2, hsumB, hB2zero]
      simp [g]

end

end DifferentialGeometry.Geometry.Operator
