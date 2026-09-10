import DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Norm.Product
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Operator.Family.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ProductLeibniz
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.FiniteArrayNorm
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
theorem metricTrace0S2TensorInBasis_tensor0SProductNabla2
    {p q : Nat} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (nabla2A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 2))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1))
    (nabla2B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 2)) :
    metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx))
        (tensor0SProductNabla2 A nablaA nabla2A B nablaB nabla2B x) =
      (metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Idx)) (nabla2A x)).product (B x) +
        (A x).product
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Idx)) (nabla2B x)) +
        (2 : Real) • ∑ e : Idx,
          (tensor0SCurry (I := I) (M := M) p x (nablaA x) (basis e)).product
            (tensor0SCurry (I := I) (M := M) q x (nablaB x) (basis e)) := by
  apply tensor0SSpace_ext (I := I) (p + q) x
  intro v
  let vA : Fin p -> TangentSpace I x := v ∘ Fin.castAdd q
  let vB : Fin q -> TangentSpace I x := v ∘ Fin.natAdd p
  have hv : Fin.append vA vB = v := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro a
      simp [vA, Fin.append]
    · intro b
      simp [vB, Fin.append]
  have hvA : Fin.append vA vB ∘ Fin.castAdd q = vA := by
    rw [hv]
  have hvB : Fin.append vA vB ∘ Fin.natAdd p = vB := by
    rw [hv]
  have hcollapse (F : Idx -> Idx -> Real) :
      (∑ i : Idx, ∑ j : Idx, if i = j then F i j else 0) =
        ∑ i : Idx, F i i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [metricTrace0S2TensorInBasis_apply]
  unfold metricTrace0S2InBasis
  simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul]
  rw [hcollapse]
  rw [show v = Fin.append vA vB from hv.symm]
  simp_rw [show ∀ e : Idx,
      metricTraceInput (I := I) (basis e) (basis e) (Fin.append vA vB) =
        Fin.cons (basis e) (Fin.cons (basis e) (Fin.append vA vB)) by
    intro e
    rfl]
  simp_rw [tensor0SProductNabla2_apply A nablaA nabla2A B nablaB nabla2B
    x]
  simp only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.sum_apply, Tensor0SSpace.product_apply,
    tensor0S_curry_apply_cons, smul_eq_mul]
  rw [metricTrace0S2TensorInBasis_apply,
    metricTrace0S2TensorInBasis_apply]
  unfold metricTrace0S2InBasis
  simp only [diagonalInvMetric, ite_mul, one_mul, zero_mul]
  rw [hvA, hvB]
  rw [hcollapse, hcollapse]
  simp_rw [show ∀ e : Idx,
      metricTraceInput (I := I) (basis e) (basis e) vA =
        Fin.cons (basis e) (Fin.cons (basis e) vA) by
    intro e
    rfl]
  simp_rw [show ∀ e : Idx,
      metricTraceInput (I := I) (basis e) (basis e) vB =
        Fin.cons (basis e) (Fin.cons (basis e) vB) by
    intro e
    rfl]
  simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  have hcomm :
      (∑ e : Idx,
          nabla2A x (Fin.cons (basis e) (Fin.cons (basis e) vA)) * B x vB) =
        ∑ e : Idx,
          B x vB * nabla2A x (Fin.cons (basis e) (Fin.cons (basis e) vA)) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [mul_comm]
  rw [hcomm]
  have hcross :
      (2 : Real) • ∑ e : Idx,
          nablaA x (Fin.cons (basis e) vA) *
            nablaB x (Fin.cons (basis e) vB) =
        ∑ e : Idx,
          (2 : Real) * (nablaA x (Fin.cons (basis e) vA) *
            nablaB x (Fin.cons (basis e) vB)) := by
    change (2 : Real) * (∑ e : Idx,
      nablaA x (Fin.cons (basis e) vA) *
        nablaB x (Fin.cons (basis e) vB)) = _
    rw [Finset.mul_sum]
  rw [← hcross]
  let first : Real := ∑ e : Idx,
    B x vB * nabla2A x (Fin.cons (basis e) (Fin.cons (basis e) vA))
  let cross : Real := ∑ e : Idx,
    nablaA x (Fin.cons (basis e) vA) *
      nablaB x (Fin.cons (basis e) vB)
  let second : Real := ∑ e : Idx,
    A x vA * nabla2B x (Fin.cons (basis e) (Fin.cons (basis e) vB))
  have htwo : (2 : Real) • cross = cross + cross := by
    change (2 : Real) * cross = cross + cross
    ring
  rw [htwo]
  change first + cross + cross + second =
    first + second + (cross + cross)
  ac_rfl

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
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
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
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
theorem laplacianAt_inner0S_eq_orthonormal
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
    (horth : ∀ i j,
      (G.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    laplacianAt (I := I) G t
        (fun y : M => inner0S (I := I) (G.metric t) y s (A y) (B y)) x =
      inner0S (I := I) (G.metric t) x s
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Idx)) (nabla2A x)) (B x) +
        2 * ∑ e : Idx,
          inner0S (I := I) (G.metric t) x s
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaA x) (basis e))
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaB x) (basis e)) +
        inner0S (I := I) (G.metric t) x s (A x)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Idx)) (nabla2B x)) := by
  classical
  let g : DifferentialGeometry.SmoothRiemannianMetric I M := G.metric t
  let cov : CovariantDerivative I E (TangentSpace I : M -> Type _) := G.connection t
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g := by
    simpa [cov, g] using G.metricCompatible t
  let phi : M -> Real := fun y => inner0S (I := I) g y s (A y) (B y)
  have hphi : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) phi :=
    inner0S_contMDiff g A B
  have hlap : ScalarLaplacianRealizesTraceAt (I := I) cov g phi
      (hessianSec (I := I) cov hcov phi hphi x) :=
    scalarLap_smooth (I := I) (M := M) (cov := cov) hcov g hmc phi hphi
  have hlapAt : laplacianAt (I := I) G t phi x =
      metricTraceFirstTwo0SAt (I := I) g
        (hessianSec (I := I) cov hcov phi hphi x) Fin.elim0 := by
    simpa [laplacianAt, phi, g, cov, ScalarLaplacianRealizesTraceAt] using hlap
  rw [hlapAt]
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [metricTraceFirstTwo0SAt_eq_sum_basis g basis
    (identityInvMetric (Idx := Idx)) hinv
    (hessianSec (I := I) cov hcov phi hphi x) Fin.elim0]
  let Ei : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun i =>
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose
  have hEi : ∀ i : Idx, Ei i x = basis i := fun i =>
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)).choose_spec
  have hslot : ∀ i j : Idx,
      (hessianSec (I := I) cov hcov phi hphi x)
          (vec2 (I := I) (basis i) (basis j)) =
        inner0S (I := I) g x s
            (freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j)) (B x) +
          inner0S (I := I) g x s
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaA x) (basis j))
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaB x) (basis i)) +
          inner0S (I := I) g x s
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaA x) (basis i))
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaB x) (basis j)) +
          inner0S (I := I) g x s (A x)
            (freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j)) := by
    intro i j
    simpa [phi, hEi i] using
      hessianSec_inner0S_slots (I := I) cov hcov g hmc A B
        nablaA nabla2A nablaB nabla2B hA h2A hB h2B (Ei i) x (basis j)
  have hsumA :
      (∑ i : Idx, ∑ j : Idx,
          identityInvMetric i j * inner0S (I := I) g x s
            (freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j)) (B x)) =
        inner0S (I := I) g x s
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Idx)) (nabla2A x)) (B x) := by
    rw [metricTrace0S2TensorInBasis]
    exact (inner0S_sum_smul_left (I := I) g x identityInvMetric
      (fun i j : Idx => freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j))
      (B x)).symm
  have hsumB :
      (∑ i : Idx, ∑ j : Idx,
          identityInvMetric i j * inner0S (I := I) g x s (A x)
            (freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j))) =
        inner0S (I := I) g x s (A x)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Idx)) (nabla2B x)) := by
    rw [metricTrace0S2TensorInBasis]
    exact (inner0S_sum_smul_right (I := I) g x identityInvMetric
      (fun i j : Idx => freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j))
      (A x)).symm
  have hcross1 :
      (∑ i : Idx, ∑ j : Idx,
          identityInvMetric i j * inner0S (I := I) g x s
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaA x) (basis j))
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaB x) (basis i))) =
        ∑ e : Idx, inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
            (nablaA x) (basis e))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
            (nablaB x) (basis e)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      rw [show identityInvMetric (Idx := Idx) i j = 0 from
        diagonalInvMetric_eq_zero_of_ne (Ne.symm hji), zero_mul]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  have hcross2 :
      (∑ i : Idx, ∑ j : Idx,
          identityInvMetric i j * inner0S (I := I) g x s
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaA x) (basis i))
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
              (nablaB x) (basis j))) =
        ∑ e : Idx, inner0S (I := I) g x s
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
            (nablaA x) (basis e))
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
            (nablaB x) (basis e)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      rw [show identityInvMetric (Idx := Idx) i j = 0 from
        diagonalInvMetric_eq_zero_of_ne (Ne.symm hji), zero_mul]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  unfold metricTrace0S2InBasis
  simp_rw [metricTraceInput_elim0_eq_vec2]
  calc
    (∑ i : Idx, ∑ j : Idx,
        identityInvMetric i j *
          (hessianSec (I := I) cov hcov phi hphi x)
            (vec2 (I := I) (basis i) (basis j))) =
      ∑ i : Idx, ∑ j : Idx,
        identityInvMetric i j *
          (inner0S (I := I) g x s
              (freezeFirstTwoArgs0S (I := I) (nabla2A x) (basis i) (basis j)) (B x) +
            inner0S (I := I) g x s
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaA x) (basis j))
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaB x) (basis i)) +
            inner0S (I := I) g x s
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaA x) (basis i))
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaB x) (basis j)) +
            inner0S (I := I) g x s (A x)
              (freezeFirstTwoArgs0S (I := I) (nabla2B x) (basis i) (basis j))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hslot i j]
    _ = _ := by
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib]
      rw [hsumA, hcross1, hcross2, hsumB]
      simp only [g]
      ring

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem ricciReaction0S_eq_inner_covariantEndomorphismAction0S_add_of_symmetric
    {s : Nat} {x : M}
    (g : SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace 2 I x)
    (A B : Tensor0SSpace s I x)
    (L : TangentSpace I x →L[Real] TangentSpace I x)
    (hQ : ∀ X Y : TangentSpace I x,
      Q (fun a : Fin 2 => if a = 0 then X else Y) =
        Q (fun a : Fin 2 => if a = 0 then Y else X))
    (hL : ∀ X Y : TangentSpace I x,
      g.inner x (L X) Y = Q (fun a : Fin 2 => if a = 0 then X else Y)) :
    ricciReaction0S (I := I) g x s Q A B =
      inner0S (I := I) g x s
          (covariantEndomorphismAction0S (I := I) A L) B +
        inner0S (I := I) g x s A
          (covariantEndomorphismAction0S (I := I) B L) := by
  classical
  let basis := Module.finBasis Real (TangentSpace I x)
  let gInv := basisInvMetric (I := I) g x basis
  let q : Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i j =>
    Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let raised : Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i e =>
    ∑ j, gInv e j * q i j
  let cA : (Fin s → Fin (Module.finrank Real (TangentSpace I x))) → Real :=
    fun slots => tensor0SComponent (I := I) A basis slots
  let cB : (Fin s → Fin (Module.finrank Real (TangentSpace I x))) → Real :=
    fun slots => tensor0SComponent (I := I) B basis slots
  have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
    simpa only [gInv] using basisInvMetric_isInverse (I := I) g x basis
  have hgInv : ∀ i j, gInv i j = gInv j i := by
    intro i j
    exact basisInvMetric_symm (I := I) g x basis i j
  have hq : ∀ i j, q i j = q j i := by
    intro i j
    exact hQ (basis i) (basis j)
  have hLcomp : ∀ i e, basis.repr (L (basis i)) e = raised i e := by
    intro i e
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hL]
  have hinner (C D : Tensor0SSpace s I x) :
      inner0S (I := I) g x s C
          (covariantEndomorphismAction0S (I := I) D L) =
        coordContract gInv
          (fun slots => tensor0SComponent (I := I) C basis slots)
          (ricStarArray raised
            (fun slots => tensor0SComponent (I := I) D basis slots)) := by
    rw [inner0S_eq_coord (I := I) g x s basis gInv hinv C
      (covariantEndomorphismAction0S (I := I) D L)]
    rw [← coordContract_eq_coordInner0S (I := I) gInv C
      (covariantEndomorphismAction0S (I := I) D L) basis]
    change coordContract gInv
        (fun slots => tensor0SComponent (I := I) C basis slots)
        (fun slots => tensor0SComponent (I := I)
          (covariantEndomorphismAction0S (I := I) D L) basis slots) = _
    congr 1
    funext slots
    rw [tensor0SComponent_covariantEndomorphismAction0S]
    congr 1
    funext i e
    exact hLcomp i e
  have hreaction :
      ricciReaction0S (I := I) g x s Q A B =
        2 * coordContract gInv cA (ricStarArray raised cB) := by
    simpa only [ricciReaction0S, basis, gInv, q, raised, cA, cB] using
      ricReactionContract_eq_two_mul_coordContract_ricStarArray_raise
        gInv q cA cB
  have hcoord :
      coordContract gInv cB (ricStarArray raised cA) =
        coordContract gInv cA (ricStarArray raised cB) := by
    have hsymm := ricReactionContract_symm gInv q cA cB hgInv hq
    rw [ricReactionContract_eq_two_mul_coordContract_ricStarArray_raise,
      ricReactionContract_eq_two_mul_coordContract_ricStarArray_raise] at hsymm
    change 2 * coordContract gInv cA (ricStarArray raised cB) =
      2 * coordContract gInv cB (ricStarArray raised cA) at hsymm
    linarith
  have hright :
      inner0S (I := I) g x s A
          (covariantEndomorphismAction0S (I := I) B L) =
        coordContract gInv cA (ricStarArray raised cB) := by
    simpa only [cA, cB] using hinner A B
  have hleft :
      inner0S (I := I) g x s
          (covariantEndomorphismAction0S (I := I) A L) B =
        coordContract gInv cA (ricStarArray raised cB) := by
    rw [inner0S_symm (I := I) g x
      (covariantEndomorphismAction0S (I := I) A L) B]
    rw [show inner0S (I := I) g x s B
        (covariantEndomorphismAction0S (I := I) A L) =
          coordContract gInv cB (ricStarArray raised cA) by
      simpa only [cA, cB] using hinner B A]
    exact hcoord
  rw [hreaction, hleft, hright]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem inner0S_time_deriv_sub_laplacianAt_eq_orthonormal
    {s : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (Q : Tensor0SSpace 2 I x)
    (A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2))
    (B : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2))
    (Adot Bdot : Tensor0SSpace s I x)
    (hg : forall X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (G.metric r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t)
    (hAt : forall v : Fin s -> TangentSpace I x,
      HasDerivAt (fun r : Real => A r x v) (Adot v) t)
    (hBt : forall v : Fin s -> TangentSpace I x,
      HasDerivAt (fun r : Real => B r x v) (Bdot v) t)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s (G.connection t) (A t) nablaA)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) (G.connection t) nablaA nabla2A)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s (G.connection t) (B t) nablaB)
    (h2B : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) (G.connection t) nablaB nabla2B)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally (G.connection t)
      (∞ : WithTop ℕ∞))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      (G.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    let roughA := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Idx)) (nabla2A x)
    let roughB := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Idx)) (nabla2B x)
    let timeDeriv :=
      ricciReaction0S (I := I) (G.metric t) x s Q (A t x) (B t x) +
        inner0S (I := I) (G.metric t) x s Adot (B t x) +
        inner0S (I := I) (G.metric t) x s (A t x) Bdot
    HasDerivAt
        (fun r : Real => inner0S (I := I) (G.metric r) x s (A r x) (B r x))
        timeDeriv t ∧
      timeDeriv - laplacianAt (I := I) G t
          (fun y : M => inner0S (I := I) (G.metric t) y s (A t y) (B t y)) x =
        ricciReaction0S (I := I) (G.metric t) x s Q (A t x) (B t x) +
          inner0S (I := I) (G.metric t) x s (Adot - roughA) (B t x) +
          inner0S (I := I) (G.metric t) x s (A t x) (Bdot - roughB) -
          2 * ∑ e : Idx,
            inner0S (I := I) (G.metric t) x s
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaA x) (basis e))
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaB x) (basis e)) := by
  dsimp only
  have htime := inner0S_moving_deriv (I := I)
    (fun r => G.metric r) Q (fun r => A r x) (fun r => B r x)
      Adot Bdot hg hAt hBt
  refine ⟨htime, ?_⟩
  rw [laplacianAt_inner0S_eq_orthonormal
    (I := I) (G := G) (t := t) (x := x)
    (A t) nablaA nabla2A (B t) nablaB nabla2B
    hA h2A hB h2B hcov basis horth]
  rw [inner0S_sub_left, Tensor0SBundle.inner0S_sub_right]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem inner0S_time_deriv_sub_laplacianAt_eq_fixed_metric_orthonormal
    {s : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (Q : Tensor0SSpace 2 I x)
    (L : TangentSpace I x →L[Real] TangentSpace I x)
    (A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2))
    (B : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2))
    (Adot Bdot : Tensor0SSpace s I x)
    (hQ : ∀ X Y : TangentSpace I x,
      Q (fun a : Fin 2 => if a = 0 then X else Y) =
        Q (fun a : Fin 2 => if a = 0 then Y else X))
    (hL : ∀ X Y : TangentSpace I x,
      (G.metric t).inner x (L X) Y =
        Q (fun a : Fin 2 => if a = 0 then X else Y))
    (hg : forall X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (G.metric r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t)
    (hAt : forall v : Fin s -> TangentSpace I x,
      HasDerivAt (fun r : Real => A r x v) (Adot v) t)
    (hBt : forall v : Fin s -> TangentSpace I x,
      HasDerivAt (fun r : Real => B r x v) (Bdot v) t)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s (G.connection t) (A t) nablaA)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) (G.connection t) nablaA nabla2A)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s (G.connection t) (B t) nablaB)
    (h2B : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) (G.connection t) nablaB nabla2B)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally (G.connection t)
      (∞ : WithTop ℕ∞))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      (G.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    let roughA := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Idx)) (nabla2A x)
    let roughB := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Idx)) (nabla2B x)
    let timeDeriv :=
      ricciReaction0S (I := I) (G.metric t) x s Q (A t x) (B t x) +
        inner0S (I := I) (G.metric t) x s Adot (B t x) +
        inner0S (I := I) (G.metric t) x s (A t x) Bdot
    let fixedHeatA := Adot - roughA +
      covariantEndomorphismAction0S (I := I) (A t x) L
    let fixedHeatB := Bdot - roughB +
      covariantEndomorphismAction0S (I := I) (B t x) L
    HasDerivAt
        (fun r : Real => inner0S (I := I) (G.metric r) x s (A r x) (B r x))
        timeDeriv t ∧
      timeDeriv - laplacianAt (I := I) G t
          (fun y : M => inner0S (I := I) (G.metric t) y s (A t y) (B t y)) x =
        inner0S (I := I) (G.metric t) x s fixedHeatA (B t x) +
          inner0S (I := I) (G.metric t) x s (A t x) fixedHeatB -
          2 * ∑ e : Idx,
            inner0S (I := I) (G.metric t) x s
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaA x) (basis e))
              (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
                (nablaB x) (basis e)) := by
  dsimp only
  obtain ⟨htime, hevolution⟩ :=
    inner0S_time_deriv_sub_laplacianAt_eq_orthonormal
      (I := I) (G := G) (t := t) (x := x) Q A nablaA nabla2A
        B nablaB nabla2B Adot Bdot hg hAt hBt hA h2A hB h2B hcov basis horth
  refine ⟨htime, ?_⟩
  rw [hevolution]
  rw [ricciReaction0S_eq_inner_covariantEndomorphismAction0S_add_of_symmetric
    (I := I) (G.metric t) Q (A t x) (B t x) L hQ hL]
  rw [inner0S_add_left, inner0S_add_right, inner0S_sub_left,
    Tensor0SBundle.inner0S_sub_right]
  ring

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor0SCurry_tensor0SProductNabla
    {p q : Nat} {x : M}
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1))
    (X : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) (p + q) x
        (tensor0SProductNabla A nablaA B nablaB x) X =
      (tensor0SCurry (I := I) (M := M) p x (nablaA x) X).product (B x) +
        (A x).product
          (tensor0SCurry (I := I) (M := M) q x (nablaB x) X) := by
  apply tensor0SSpace_ext (I := I) (p + q) x
  intro v
  let vA : Fin p -> TangentSpace I x := v ∘ Fin.castAdd q
  let vB : Fin q -> TangentSpace I x := v ∘ Fin.natAdd p
  have hv : Fin.append vA vB = v := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro a
      simp [vA, Fin.append]
    · intro b
      simp [vB, Fin.append]
  have hvA : Fin.append vA vB ∘ Fin.castAdd q = vA := by
    funext a
    simp [Fin.append]
  have hvB : Fin.append vA vB ∘ Fin.natAdd p = vB := by
    funext b
    simp [Fin.append]
  rw [show v = Fin.append vA vB from hv.symm]
  rw [tensor0S_curry_apply_cons]
  rw [tensor0SProductNabla_apply A nablaA B nablaB x X vA vB]
  simp only [Tensor0SSpace.add_apply, Tensor0SSpace.product_apply,
    tensor0S_curry_apply_cons]
  rw [hvA, hvB]

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem inner0S_product_time_deriv_sub_laplacianAt_eq_fixed_metric_orthonormal
    {p q : Nat} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (Q : Tensor0SSpace 2 I x)
    (L : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Real -> Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + q))
    (nablaT : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + q + 1))
    (nabla2T : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + q + 2))
    (A : Real -> Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + 1))
    (nabla2A : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + 2))
    (B : Real -> Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (q + 1))
    (nabla2B : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (q + 2))
    (Tdot : Tensor0SSpace (p + q) I x)
    (Adot : Tensor0SSpace p I x) (Bdot : Tensor0SSpace q I x)
    (hQ : ∀ X Y : TangentSpace I x,
      Q (vec2 (I := I) X Y) = Q (vec2 (I := I) Y X))
    (hL : ∀ X Y : TangentSpace I x,
      (G.metric t).inner x (L X) Y = Q (vec2 (I := I) X Y))
    (hg : forall X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (G.metric r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t)
    (hTt : forall v : Fin (p + q) -> TangentSpace I x,
      HasDerivAt (fun r : Real => T r x v) (Tdot v) t)
    (hAt : forall v : Fin p -> TangentSpace I x,
      HasDerivAt (fun r : Real => A r x v) (Adot v) t)
    (hBt : forall v : Fin q -> TangentSpace I x,
      HasDerivAt (fun r : Real => B r x v) (Bdot v) t)
    (hT : TotalNabla0SRealizes (p + q) (G.connection t) (T t) nablaT)
    (h2T : TotalNabla0SRealizes (p + q + 1) (G.connection t) nablaT nabla2T)
    (hA : TotalNabla0SRealizes p (G.connection t) (A t) nablaA)
    (h2A : TotalNabla0SRealizes (p + 1) (G.connection t) nablaA nabla2A)
    (hB : TotalNabla0SRealizes q (G.connection t) (B t) nablaB)
    (h2B : TotalNabla0SRealizes (q + 1) (G.connection t) nablaB nabla2B)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally (G.connection t)
      (∞ : WithTop ℕ∞))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j,
      (G.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    let roughT := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Idx)) (nabla2T x)
    let roughA := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Idx)) (nabla2A x)
    let roughB := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Idx)) (nabla2B x)
    let fixedHeatT := Tdot - roughT +
      covariantEndomorphismAction0S (I := I) (T t x) L
    let fixedHeatA := Adot - roughA +
      covariantEndomorphismAction0S (I := I) (A t x) L
    let fixedHeatB := Bdot - roughB +
      covariantEndomorphismAction0S (I := I) (B t x) L
    let productValue := (A t x).product (B t x)
    let productDot := Adot.product (B t x) + (A t x).product Bdot
    let timeDeriv :=
      ricciReaction0S (I := I) (G.metric t) x (p + q) Q (T t x) productValue +
        inner0S (I := I) (G.metric t) x (p + q) Tdot productValue +
        inner0S (I := I) (G.metric t) x (p + q) (T t x) productDot
    HasDerivAt
        (fun r : Real => inner0S (I := I) (G.metric r) x (p + q)
          (T r x) ((A r x).product (B r x)))
        timeDeriv t ∧
      timeDeriv - laplacianAt (I := I) G t
          (fun y : M => inner0S (I := I) (G.metric t) y (p + q)
            (T t y) ((A t y).product (B t y))) x =
        inner0S (I := I) (G.metric t) x (p + q) fixedHeatT productValue +
          inner0S (I := I) (G.metric t) x (p + q) (T t x)
            (fixedHeatA.product (B t x)) +
          inner0S (I := I) (G.metric t) x (p + q) (T t x)
            ((A t x).product fixedHeatB) -
          2 * ∑ e : Idx,
            inner0S (I := I) (G.metric t) x (p + q)
              (tensor0SCurry (I := I) (M := M) (p + q) x
                (nablaT x) (basis e))
              ((tensor0SCurry (I := I) (M := M) p x
                    (nablaA x) (basis e)).product (B t x) +
                (A t x).product
                  (tensor0SCurry (I := I) (M := M) q x
                    (nablaB x) (basis e))) -
          2 * ∑ e : Idx,
            inner0S (I := I) (G.metric t) x (p + q) (T t x)
              ((tensor0SCurry (I := I) (M := M) p x
                    (nablaA x) (basis e)).product
                (tensor0SCurry (I := I) (M := M) q x
                  (nablaB x) (basis e))) := by
  dsimp only
  let productFamily : Real -> Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + q) := fun r =>
    tensor0SFieldProduct ∞ (A r) (B r)
  let productNabla := tensor0SProductNabla (A t) nablaA (B t) nablaB
  let productNabla2 := tensor0SProductNabla2
    (A t) nablaA nabla2A (B t) nablaB nabla2B
  let productDot := Adot.product (B t x) + (A t x).product Bdot
  let roughA := metricTrace0S2TensorInBasis (I := I) basis
    (identityInvMetric (Idx := Idx)) (nabla2A x)
  let roughB := metricTrace0S2TensorInBasis (I := I) basis
    (identityInvMetric (Idx := Idx)) (nabla2B x)
  have hProductTime : forall v : Fin (p + q) -> TangentSpace I x,
      HasDerivAt (fun r : Real => productFamily r x v) (productDot v) t := by
    intro v
    exact tensor0SFieldProduct_hasDerivAt A B Adot Bdot hAt hBt v
  have hProduct := tensor0SProductNabla_realizes (G.connection t)
    (A t) nablaA (B t) nablaB hA hB
  have h2Product := tensor0SProductNabla2_realizes (G.connection t)
    (A t) nablaA nabla2A (B t) nablaB nabla2B hA h2A hB h2B
  have hProductValue (r : Real) (y : M) :
      productFamily r y = (A r y).product (B r y) := by
    apply tensor0SSpace_ext (I := I) (p + q) y
    intro v
    simp only [productFamily, tensor0SField_product_apply,
      Tensor0SSpace.product_apply]
  obtain ⟨htime, hevolution⟩ :=
    inner0S_time_deriv_sub_laplacianAt_eq_fixed_metric_orthonormal
      (I := I) (G := G) (t := t) (x := x) Q L
      T nablaT nabla2T productFamily productNabla productNabla2
      Tdot productDot hQ hL hg hTt hProductTime hT h2T
      hProduct h2Product hcov basis horth
  simp_rw [hProductValue] at htime hevolution
  refine ⟨?_, ?_⟩
  · simpa only [productDot] using htime
  · have hevolution' := hevolution
    simp only [productDot] at hevolution'
    rw [hevolution']
    have hrough := metricTrace0S2TensorInBasis_tensor0SProductNabla2 basis
      (A t) nablaA nabla2A (B t) nablaB nabla2B
    have hfixedProduct :
        productDot -
              metricTrace0S2TensorInBasis (I := I) basis
                (identityInvMetric (Idx := Idx)) (productNabla2 x) +
              covariantEndomorphismAction0S (I := I)
                ((A t x).product (B t x)) L =
          (Adot - roughA + covariantEndomorphismAction0S (I := I) (A t x) L).product
              (B t x) +
            (A t x).product
              (Bdot - roughB + covariantEndomorphismAction0S (I := I) (B t x) L) -
            (2 : Real) • ∑ e : Idx,
              (tensor0SCurry (I := I) (M := M) p x
                    (nablaA x) (basis e)).product
                (tensor0SCurry (I := I) (M := M) q x
                  (nablaB x) (basis e)) := by
      rw [show metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Idx)) (productNabla2 x) =
          (metricTrace0S2TensorInBasis (I := I) basis
              (identityInvMetric (Idx := Idx)) (nabla2A x)).product (B t x) +
            (A t x).product
              (metricTrace0S2TensorInBasis (I := I) basis
                (identityInvMetric (Idx := Idx)) (nabla2B x)) +
            (2 : Real) • ∑ e : Idx,
              (tensor0SCurry (I := I) (M := M) p x
                    (nablaA x) (basis e)).product
                (tensor0SCurry (I := I) (M := M) q x
                  (nablaB x) (basis e)) by
        simpa only [productNabla2] using hrough]
      rw [covariantEndomorphismAction0S_product]
      apply tensor0SSpace_ext (I := I) (p + q) x
      intro v
      simp only [productDot, roughA, roughB, Tensor0SSpace.add_apply,
        Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
        Tensor0SSpace.sum_apply, Tensor0SSpace.product_apply, smul_eq_mul]
      ring
    rw [hfixedProduct]
    have hnabla (e : Idx) :
        tensor0SCurry (I := I) (M := M) (p + q) x
            (productNabla x) (basis e) =
          (tensor0SCurry (I := I) (M := M) p x
              (nablaA x) (basis e)).product (B t x) +
            (A t x).product
              (tensor0SCurry (I := I) (M := M) q x
                (nablaB x) (basis e)) := by
      simpa only [productNabla] using
        tensor0SCurry_tensor0SProductNabla
          (A t) nablaA (B t) nablaB (basis e)
    simp_rw [hnabla]
    rw [Tensor0SBundle.inner0S_sub_right, inner0S_add_right,
      Tensor0SBundle.inner0S_smul_right]
    have hsum :
        inner0S (I := I) (G.metric t) x (p + q) (T t x)
            (∑ e : Idx,
              (tensor0SCurry (I := I) (M := M) p x
                    (nablaA x) (basis e)).product
                (tensor0SCurry (I := I) (M := M) q x
                  (nablaB x) (basis e))) =
          ∑ e : Idx,
            inner0S (I := I) (G.metric t) x (p + q) (T t x)
              ((tensor0SCurry (I := I) (M := M) p x
                    (nablaA x) (basis e)).product
                (tensor0SCurry (I := I) (M := M) q x
                  (nablaB x) (basis e))) := by
      classical
      let C : Idx -> Tensor0SSpace (p + q) I x := fun e =>
        (tensor0SCurry (I := I) (M := M) p x
              (nablaA x) (basis e)).product
          (tensor0SCurry (I := I) (M := M) q x
            (nablaB x) (basis e))
      have hind : forall s : Finset Idx,
          inner0S (I := I) (G.metric t) x (p + q) (T t x)
              (∑ e ∈ s, C e) =
            ∑ e ∈ s,
              inner0S (I := I) (G.metric t) x (p + q) (T t x) (C e) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [inner0S]
        | @insert e s he ih =>
            simp only [Finset.sum_insert he,
              inner0S_add_right, ih]
      simpa only [C] using hind Finset.univ
    rw [hsum]
    ring

omit [CompleteSpace E] [SigmaCompactSpace M] in
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
    (hinv : MetricInverseInBasis (I := I) (G.metric t) x basis gInv)
    (hBflat1 : nablaB x = 0)
    (hBflat2 : metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2B x) = 0) :
    laplacianAt (I := I) G t
        (fun y : M => inner0S (I := I) (G.metric t) y s (A y) (B y)) x =
      inner0S (I := I) (G.metric t) x s
        (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2A x)) (B x) := by
  classical
  let g : DifferentialGeometry.SmoothRiemannianMetric I M := G.metric t
  let cov : CovariantDerivative I E (TangentSpace I : M -> Type _) := G.connection t
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g := by
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
