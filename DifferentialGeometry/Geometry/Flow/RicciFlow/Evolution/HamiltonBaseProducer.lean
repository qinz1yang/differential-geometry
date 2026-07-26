import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04Variation
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Hamilton

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Arbitrary-dimensional Hamilton base producer

This module transports the coordinate-frame time variation of lowered Riemann
to fixed tangent vectors and then combines it with the static Hamilton
curvature identity.  It stays below the `StarSum` consumer layer.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

private def permAC : Equiv.Perm (Fin 4) where
  toFun := fun i ↦ if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else 3
  invFun := fun i ↦ if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else 3
  left_inv := by intro i; fin_cases i <;> simp
  right_inv := by intro i; fin_cases i <;> simp

private def permADBC : Equiv.Perm (Fin 4) where
  toFun := fun i ↦ if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1 else 2
  invFun := fun i ↦ if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else 1
  left_inv := by intro i; fin_cases i <;> simp
  right_inv := by intro i; fin_cases i <;> simp

private def permBA : Equiv.Perm (Fin 4) where
  toFun := fun i ↦ if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else 3
  invFun := fun i ↦ if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else 3
  left_inv := by intro i; fin_cases i <;> simp
  right_inv := by intro i; fin_cases i <;> simp

private def permBCA : Equiv.Perm (Fin 4) where
  toFun := fun i ↦ if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else 3
  invFun := fun i ↦ if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else 3
  left_inv := by intro i; fin_cases i <;> simp
  right_inv := by intro i; fin_cases i <;> simp

private def permBDAC : Equiv.Perm (Fin 4) where
  toFun := fun i ↦ if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 0 else 2
  invFun := fun i ↦ if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 3 else 1
  left_inv := by intro i; fin_cases i <;> simp
  right_inv := by intro i; fin_cases i <;> simp

private def reindex4 {x : M}
    (N : Tensor04At (I := I) (M := M) x) (e : Equiv.Perm (Fin 4)) :
    Tensor04At (I := I) (M := M) x :=
  N.domDomCongr e

/-- The metric-raised Ricci endomorphism associated to a pointwise two-tensor. -/
private def ricciSharpCLM
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x) :
    TangentSpace I x →L[Real] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    ((cotangentSharpLinear_gen (I := I) g x).comp
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x Ric).toLinearMap)

@[simp] private theorem ricciSharpCLM_apply
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    (X : TangentSpace I x) :
    ricciSharpCLM (I := I) g Ric X =
      cotangentSharp_gen (I := I) g x
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x Ric X) := by
  rfl

/-- The invariant contraction `Rm04(A, B, C, Ric♯ D)`. -/
private def rawTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x) :
    Tensor04At (I := I) (M := M) x :=
  Rm04.compContinuousLinearMap fun i ↦
    if i = 3 then ricciSharpCLM (I := I) g Ric
    else ContinuousLinearMap.id Real (TangentSpace I x)

/-- The six second-Ricci-derivative terms in the lowered-Riemann variation. -/
private def hessVarTensor {x : M}
    (N : Tensor04At (I := I) (M := M) x) :
    Tensor04At (I := I) (M := M) x :=
  -N - reindex4 N permAC + reindex4 N permADBC +
    reindex4 N permBA + reindex4 N permBCA - reindex4 N permBDAC

/-- The canonical pointwise tensor represented by `rm04VarRHS`. -/
private def varTensor
    (g : SmoothRiemannianMetric I M) {x : M}
    (N : Tensor04At (I := I) (M := M) x)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x) :
    Tensor04At (I := I) (M := M) x :=
  hessVarTensor N - (2 : Real) • rawTensor (I := I) g Ric Rm04

/-- The canonical first covariant derivative of the solution Ricci tensor. -/
private def solNablaRic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 (S.family.connection t) (S.ricci t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (connSmoothInf (I := I) S t) (S.ricci t))

/-- The canonical second covariant derivative of the solution Ricci tensor. -/
private def solNabla2Ric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (S.family.connection t) (solNablaRic (I := I) S t) x

private theorem coordNab2_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) (t : Real)
    (d a i j : CoordinateIdx (𝕜 := Real) E) :
    coordNab2Ric (I := I) S x₀ t x₀ d a i j =
      solNabla2Ric (I := I) S t x₀
        (vec4 (I := I)
          (coordinateFrameAt (I := I) x₀ d x₀)
          (coordinateFrameAt (I := I) x₀ a x₀)
          (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) := by
  simpa only [solNabla2Ric, solNablaRic] using
    coordNab2Ric_eq_nabla2RicField (I := I) S x₀ t d a i j

private theorem tensor04_sum_last
    {Idx : Type*} [Fintype Idx] {x : M}
    (T : Tensor04At (I := I) (M := M) x)
    (A B C : TangentSpace I x)
    (coef : Idx → Real) (vecs : Idx → TangentSpace I x) :
    T (vec4 (I := I) A B C (∑ i : Idx, coef i • vecs i)) =
      ∑ i : Idx, coef i * T (vec4 (I := I) A B C (vecs i)) := by
  classical
  have hupd : ∀ Z : TangentSpace I x,
      vec4 (I := I) A B C Z =
        Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 Z := by
    intro Z
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [hupd]
  rw [show T (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ i : Idx, coef i • vecs i)) =
      T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ i : Idx, coef i • vecs i)) from rfl]
  rw [T.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 (coef i • vecs i)) =
      T (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 (coef i • vecs i)) from rfl]
  rw [T.map_update_smul, ← hupd]
  simp [smul_eq_mul]

private theorem invContract
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (d : Idx) (F : Idx → Real) :
    (∑ p : Idx, (∑ l : Idx, gInv p l * F l) *
        g.inner x (basis d) (basis p)) = F d := by
  classical
  calc
    _ = ∑ p : Idx, ∑ l : Idx,
        (gInv p l * F l) * g.inner x (basis d) (basis p) := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.sum_mul]
    _ = ∑ l : Idx, ∑ p : Idx,
        (gInv p l * F l) * g.inner x (basis d) (basis p) := by
      rw [Finset.sum_comm]
    _ = ∑ l : Idx, F l *
        (∑ p : Idx, g.inner x (basis d) (basis p) * gInv p l) := by
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      ring
    _ = ∑ l : Idx, F l * (if d = l then 1 else 0) := by
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [(hinv d l).2]
    _ = F d := by simp

private theorem rawTensor_eval
    (g : SmoothRiemannianMetric I M) {x : M}
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (A B C D : TangentSpace I x) :
    rawTensor (I := I) g Ric Rm04 (vec4 (I := I) A B C D) =
      Rm04 (vec4 (I := I) A B C
        (cotangentSharp_gen (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x Ric D))) := by
  unfold rawTensor
  change Rm04 (fun i : Fin 4 ↦
      (if i = 3 then ricciSharpCLM (I := I) g Ric
        else ContinuousLinearMap.id Real (TangentSpace I x))
        (vec4 (I := I) A B C D i)) = _
  have hslots :
      (fun i : Fin 4 ↦
        (if i = 3 then ricciSharpCLM (I := I) g Ric
          else ContinuousLinearMap.id Real (TangentSpace I x))
          (vec4 (I := I) A B C D i)) =
        vec4 (I := I) A B C (ricciSharpCLM (I := I) g Ric D) := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hslots, ricciSharpCLM_apply]

private theorem rawTensor_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (A B C D : TangentSpace I x) :
    rawTensor (I := I) g Ric Rm04 (vec4 (I := I) A B C D) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * Ric (vec2 (I := I) D (basis j)) *
          Rm04 (vec4 (I := I) A B C (basis i)) := by
  classical
  rw [rawTensor_eval]
  let β := tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x Ric D
  have hβ (j : Idx) :
      cotangentToDual_gen (I := I) β (basis j) =
        Ric (vec2 (I := I) D (basis j)) := by
    rw [cotangentToDual_apply_gen, tensor0S_curry_apply_cons]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv β]
  rw [tensor04_sum_last]
  simp_rw [hβ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul]

private theorem hessVar_apply {x : M}
    (N : Tensor04At (I := I) (M := M) x)
    (A B C D : TangentSpace I x) :
    hessVarTensor N (vec4 (I := I) A B C D) =
      -N (vec4 (I := I) A B C D) -
        N (vec4 (I := I) A C B D) +
        N (vec4 (I := I) A D B C) +
        N (vec4 (I := I) B A C D) +
        N (vec4 (I := I) B C A D) -
        N (vec4 (I := I) B D A C) := by
  have hAC :
      (fun i ↦ vec4 (I := I) A B C D (permAC i)) =
        vec4 (I := I) A C B D := by
    funext i
    fin_cases i <;> simp [permAC, vec4]
  have hADBC :
      (fun i ↦ vec4 (I := I) A B C D (permADBC i)) =
        vec4 (I := I) A D B C := by
    funext i
    fin_cases i <;> simp [permADBC, vec4]
  have hBA :
      (fun i ↦ vec4 (I := I) A B C D (permBA i)) =
        vec4 (I := I) B A C D := by
    funext i
    fin_cases i <;> simp [permBA, vec4]
  have hBCA :
      (fun i ↦ vec4 (I := I) A B C D (permBCA i)) =
        vec4 (I := I) B C A D := by
    funext i
    fin_cases i <;> simp [permBCA, vec4]
  have hBDAC :
      (fun i ↦ vec4 (I := I) A B C D (permBDAC i)) =
        vec4 (I := I) B D A C := by
    funext i
    fin_cases i <;> simp [permBDAC, vec4]
  change
    (-N (vec4 (I := I) A B C D) -
          N (fun i ↦ vec4 (I := I) A B C D (permAC i)) +
        N (fun i ↦ vec4 (I := I) A B C D (permADBC i)) +
        N (fun i ↦ vec4 (I := I) A B C D (permBA i)) +
        N (fun i ↦ vec4 (I := I) A B C D (permBCA i)) -
        N (fun i ↦ vec4 (I := I) A B C D (permBDAC i))) = _
  rw [hAC, hADBC, hBA, hBCA, hBDAC]

private theorem gammaLower_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (d i j z : CoordinateIdx (𝕜 := Real) E) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        nablaGammaDtFromNabla2RicInFrame
            (M := M) (coordInv (I := I) S x₀) (coordNab2Ric (I := I) S x₀)
            t x₀ d p i j *
          metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
            t x₀ z p) =
      -coordNab2Ric (I := I) S x₀ t x₀ d i j z -
        coordNab2Ric (I := I) S x₀ t x₀ d j i z +
        coordNab2Ric (I := I) S x₀ t x₀ d z i j := by
  let basis := coordinateFrameAt_toBasis (I := I) x₀
  have h := invContract (I := I) (M := M) (S.family.metric t) basis
    (fun p l ↦ coordInv (I := I) S x₀ t x₀ p l)
    (by simpa [basis] using coordInvReal (I := I) S x₀ t)
    z (fun l ↦
      -coordNab2Ric (I := I) S x₀ t x₀ d i j l -
        coordNab2Ric (I := I) S x₀ t x₀ d j i l +
        coordNab2Ric (I := I) S x₀ t x₀ d l i j)
  simpa [nablaGammaDtFromNabla2RicInFrame, metricCompInFrame, basis,
    coordinateFrameAt_toBasis_apply] using h

private theorem rawCoord_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : Real) (ht : t ∈ D.carrier)
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
            (I := I) (S.family.connection t) x₀ (m 0) (m 1) (m 2) p *
          ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
            t x₀ (m 3) p) =
      rawTensor (I := I) (S.base.metric t) (S.base.ricciAt t x₀)
        (S.base.rm04 t x₀)
        (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀) := by
  classical
  let A := coordinateFrameAt (I := I) x₀ (m 0) x₀
  let B := coordinateFrameAt (I := I) x₀ (m 1) x₀
  let C := coordinateFrameAt (I := I) x₀ (m 2) x₀
  let Dv := coordinateFrameAt (I := I) x₀ (m 3) x₀
  let β := tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
    (S.base.ricciAt t x₀) Dv
  have hcov := connSmoothOfSol (I := I) S hS t ht
  have hcoord :=
    DifferentialGeometry.Integral.Connection.rm13_eval_eq_christoffelCurvCoord
      (I := I) (S.family.connection t) hcov (S.base.rm13 t) x₀ β
      (rm13OfSol (I := I) S t ht) (connCurvOfSol (I := I) S hS x₀ t ht)
      (m 0) (m 1) (m 2)
  have hβ (p : CoordinateIdx (𝕜 := Real) E) :
      β (fun _ : Fin 1 ↦ coordinateFrameAt (I := I) x₀ p x₀) =
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          t x₀ (m 3) p := by
    rw [show β (fun _ : Fin 1 ↦ coordinateFrameAt (I := I) x₀ p x₀) =
        S.ricci t x₀
          (Fin.cons Dv (fun _ : Fin 1 ↦ coordinateFrameAt (I := I) x₀ p x₀)) by
      simp [β, tensor0S_curry_apply_cons]]
    unfold ricciCompInFrame
    congr 1
    funext q
    fin_cases q <;> rfl
  have hraise := rm13_apply_eq_rm04_raise
    (I := I) (S.base.metric t) (S.base.rm13 t x₀) (S.base.rm04 t x₀)
    (solution_rm04LowersRm13At (I := I) S t x₀) β A B C
  calc
    _ = ∑ p : CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
            (I := I) (S.family.connection t) x₀ (m 0) (m 1) (m 2) p *
          β (fun _ : Fin 1 ↦ coordinateFrameAt (I := I) x₀ p x₀) := by
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [hβ]
    _ = S.base.rm13 t x₀ β (vec3 (I := I) A B C) := by
      simpa [A, B, C] using hcoord.symm
    _ = S.base.rm04 t x₀
        (vec4 (I := I) A B C
          (cotangentSharp_gen (I := I) (S.base.metric t) x₀ β)) := hraise
    _ = rawTensor (I := I) (S.base.metric t) (S.base.ricciAt t x₀)
        (S.base.rm04 t x₀)
        (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀) := by
      rw [show (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀) =
          vec4 (I := I) A B C Dv by
        funext q
        fin_cases q <;> rfl]
      rw [rawTensor_eval]

private theorem rm04Var_eq_tensor
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : Real) (ht : t ∈ D.carrier)
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    rm04VarRHS (I := I) S x₀ (coordNab2Ric (I := I) S x₀) t m =
      varTensor (I := I) (S.base.metric t) (solNabla2Ric (I := I) S t x₀)
        (S.base.ricciAt t x₀) (S.base.rm04 t x₀)
        (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀) := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let ΓA := fun p : CoordinateIdx (𝕜 := Real) E ↦
    nablaGammaDtFromNabla2RicInFrame
      (M := M) (coordInv (I := I) S x₀) (coordNab2Ric (I := I) S x₀)
      t x₀ (m 0) p (m 1) (m 2)
  let ΓB := fun p : CoordinateIdx (𝕜 := Real) E ↦
    nablaGammaDtFromNabla2RicInFrame
      (M := M) (coordInv (I := I) S x₀) (coordNab2Ric (I := I) S x₀)
      t x₀ (m 1) p (m 0) (m 2)
  let G := fun p : CoordinateIdx (𝕜 := Real) E ↦
    metricCompInFrame (I := I) S frame t x₀ (m 3) p
  let R := fun p : CoordinateIdx (𝕜 := Real) E ↦
    DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
      (I := I) (S.family.connection t) x₀ (m 0) (m 1) (m 2) p
  let Rc := fun p : CoordinateIdx (𝕜 := Real) E ↦
    ricciCompInFrame (I := I) S frame t x₀ (m 3) p
  have hfirst :
      (∑ p, (ΓA p - ΓB p) * G p) =
        (∑ p, ΓA p * G p) - ∑ p, ΓB p * G p := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    ring
  have hrawsum :
      (∑ p, R p * ((-2 : Real) * Rc p)) =
        (-2 : Real) * ∑ p, R p * Rc p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    ring
  have hΓA := gammaLower_eq (I := I) S x₀ t (m 0) (m 1) (m 2) (m 3)
  have hΓB := gammaLower_eq (I := I) S x₀ t (m 1) (m 0) (m 2) (m 3)
  have hraw := rawCoord_eq (I := I) S hS x₀ t ht m
  have hvec :
      (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀) =
        vec4 (I := I)
          (coordinateFrameAt (I := I) x₀ (m 0) x₀)
          (coordinateFrameAt (I := I) x₀ (m 1) x₀)
          (coordinateFrameAt (I := I) x₀ (m 2) x₀)
          (coordinateFrameAt (I := I) x₀ (m 3) x₀) := by
    funext q
    fin_cases q <;> rfl
  calc
    _ = (∑ p, ΓA p * G p) - (∑ p, ΓB p * G p) -
        2 * ∑ p, R p * Rc p := by
      unfold rm04VarRHS
      rw [Finset.sum_add_distrib]
      change (∑ p, (ΓA p - ΓB p) * G p) +
          ∑ p, R p * ((-2 : Real) * Rc p) = _
      rw [hfirst, hrawsum]
      ring
    _ = (-coordNab2Ric (I := I) S x₀ t x₀ (m 0) (m 1) (m 2) (m 3) -
          coordNab2Ric (I := I) S x₀ t x₀ (m 0) (m 2) (m 1) (m 3) +
          coordNab2Ric (I := I) S x₀ t x₀ (m 0) (m 3) (m 1) (m 2) +
          coordNab2Ric (I := I) S x₀ t x₀ (m 1) (m 0) (m 2) (m 3) +
          coordNab2Ric (I := I) S x₀ t x₀ (m 1) (m 2) (m 0) (m 3) -
          coordNab2Ric (I := I) S x₀ t x₀ (m 1) (m 3) (m 0) (m 2)) -
        2 * rawTensor (I := I) (S.base.metric t) (S.base.ricciAt t x₀)
          (S.base.rm04 t x₀)
          (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀) := by
      rw [show (∑ p, ΓA p * G p) = _ by simpa [ΓA, G, frame] using hΓA]
      rw [show (∑ p, ΓB p * G p) = _ by simpa [ΓB, G, frame] using hΓB]
      rw [show (∑ p, R p * Rc p) = _ by simpa [R, Rc, frame] using hraw]
      ring
    _ = _ := by
      rw [hvec]
      change _ = hessVarTensor (solNabla2Ric (I := I) S t x₀)
          (vec4 (I := I)
            (coordinateFrameAt (I := I) x₀ (m 0) x₀)
            (coordinateFrameAt (I := I) x₀ (m 1) x₀)
            (coordinateFrameAt (I := I) x₀ (m 2) x₀)
            (coordinateFrameAt (I := I) x₀ (m 3) x₀)) -
        2 * rawTensor (I := I) (S.base.metric t) (S.base.ricciAt t x₀)
          (S.base.rm04 t x₀)
          (vec4 (I := I)
            (coordinateFrameAt (I := I) x₀ (m 0) x₀)
            (coordinateFrameAt (I := I) x₀ (m 1) x₀)
            (coordinateFrameAt (I := I) x₀ (m 2) x₀)
            (coordinateFrameAt (I := I) x₀ (m 3) x₀))
      rw [hessVar_apply]
      simp only [coordNab2_eq]

private theorem varTensor_eq_ham
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
      (identityInvMetric (Idx := Idx)))
    (m : Fin 4 → Idx) :
    varTensor (I := I) (S.base.metric t) (solNabla2Ric (I := I) S t x)
        (S.base.ricciAt t x) (S.base.rm04 t x) (fun q ↦ basis (m q)) =
      tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Idx))
            (nablaKRm04Field (I := I) S t 2 x))
          (fun i ↦ basis i) m +
        hamiltonRmReact
          (fun q : Fin 4 → Idx ↦
            S.base.rm04 t x (fun p ↦ basis (q p))) m := by
  classical
  have hstatic := hamiltonRm04Id (I := I) (M := M) (S.base.metric t) basis hinv m
  rw [show (fun q ↦ basis (m q)) =
      vec4 (I := I) (basis (m 0)) (basis (m 1)) (basis (m 2)) (basis (m 3)) by
    funext q
    fin_cases q <;> rfl]
  change hessVarTensor (solNabla2Ric (I := I) S t x)
      (vec4 (I := I) (basis (m 0)) (basis (m 1)) (basis (m 2)) (basis (m 3))) -
    2 * rawTensor (I := I) (S.base.metric t) (S.base.ricciAt t x)
      (S.base.rm04 t x)
      (vec4 (I := I) (basis (m 0)) (basis (m 1)) (basis (m 2)) (basis (m 3))) = _
  rw [hessVar_apply]
  rw [rawTensor_apply (I := I) (S.base.metric t) basis
    (identityInvMetric (Idx := Idx)) hinv]
  simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul]
  have htraceInput (i : Idx) :
      metricTraceInput (I := I) (basis i) (basis i)
          (vec4 (I := I) (basis (m 0)) (basis (m 1)) (basis (m 2)) (basis (m 3))) =
        Fin.cons (basis i)
          (vec5 (I := I) (basis i) (basis (m 0)) (basis (m 1))
            (basis (m 2)) (basis (m 3))) := by
    funext q
    fin_cases q <;> rfl
  have hvec (q : Fin 4 → Idx) :
      (fun p ↦ basis (q p)) =
        vec4 (I := I) (basis (q 0)) (basis (q 1)) (basis (q 2)) (basis (q 3)) := by
    funext p
    fin_cases p <;> rfl
  simpa [solNabla2Ric, solNablaRic, nablaKRm04Field_succ,
    SolutionFamily.connection, SolutionFamily.rm04, SolutionFamily.ricci,
    SolutionFamily.ricciAt, metricRm04, metricRicci, metricTrace0S2InBasis,
    htraceInput, hvec, identityInvMetric, diagonalInvMetric, metricCov,
    DifferentialGeometry.Integral.Connection.metricRm04,
    DifferentialGeometry.Integral.Connection.metricRicci,
    DifferentialGeometry.Integral.Connection.metricRicciAt,
    DifferentialGeometry.Integral.Connection.metricCov] using hstatic

/-- Coordinate derivatives of the lowered-Riemann components determine the
time derivative on any four fixed tangent vectors.  The coefficients are the
time-independent coordinates of those vectors in the centered chart basis. -/
theorem rm04Deriv_of_coord
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (V : (Fin 4 → CoordinateIdx (𝕜 := Real) E) → Real)
    (hD : ∀ m, HasDerivWithinAt
      (fun s : Real ↦ S.base.rm04 s x₀
        (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀))
      (V m) D.carrier (t : Real))
    (v : Fin 4 → TangentSpace I x₀) :
    HasDerivWithinAt
      (fun s : Real ↦ S.base.rm04 s x₀ v)
      (∑ m : Fin 4 → CoordinateIdx (𝕜 := Real) E,
        V m * ∏ q : Fin 4,
          (coordinateFrameAt_toBasis (I := I) x₀).coord (m q) (v q))
      D.carrier (t : Real) := by
  classical
  have hexp :
      (fun s : Real ↦ S.base.rm04 s x₀ v) =
        fun s : Real ↦
          ∑ m : Fin 4 → CoordinateIdx (𝕜 := Real) E,
            S.base.rm04 s x₀
                (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀) *
              ∏ q : Fin 4,
                (coordinateFrameAt_toBasis (I := I) x₀).coord (m q) (v q) := by
    funext s
    rw [tensor0S_apply_eq_sum
      (I := I) (coordinateFrameAt_toBasis (I := I) x₀) (S.base.rm04 s x₀) v]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [component0S_apply]
    congr 2
    funext q
    exact coordinateFrameAt_toBasis_apply (I := I) x₀ (m q)
  rw [hexp]
  refine HasDerivWithinAt.fun_sum ?_
  intro m _
  exact (hD m).mul_const _

private theorem rm04Var_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (v : Fin 4 → TangentSpace I x₀) :
    HasDerivWithinAt
      (fun s : Real ↦ S.base.rm04 s x₀ v)
      (varTensor (I := I) (S.base.metric (t : Real))
        (solNabla2Ric (I := I) S (t : Real) x₀)
        (S.base.ricciAt (t : Real) x₀) (S.base.rm04 (t : Real) x₀) v)
      D.carrier (t : Real) := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let nablaRic := nablaRicComp (I := I) S frame
  let nabla2Ric := coordNab2Ric (I := I) S x₀
  let rhs := christoffelEvolutionRHSInFrame
    (M := M) (coordInv (I := I) S x₀) nablaRic
  have hmetric := coordMetricMix (I := I) S hS x₀
    (coordMetricDeriv (I := I) S hS x₀)
  have hGamma :
      ChristoffelEvolutionEquationInFrameOn
        (I := I) S (coordInv (I := I) S x₀) frame
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic := by
    simpa [frame, nablaRic] using coordGammaEvol (I := I) S hS x₀ hmetric
  have hvar :
      ChristoffelVariationEquationInFrameOn
        (I := I) S frame
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs := by
    simpa [ChristoffelVariationEquationInFrameOn,
      ChristoffelEvolutionEquationInFrameOn, rhs, frame, nablaRic] using hGamma
  have hmix :
      ChristoffelVariationMixedDerivativeInFrameOnRegular
        (I := I) S frame (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs := by
    simpa [rhs, frame, nablaRic] using coordGammaMix (I := I) S hS x₀ hGamma
  have hnablaReg := coordNab2Reg (I := I) S x₀
  have hgamma
      (d k i j : CoordinateIdx (𝕜 := Real) E) :
      christoffelVariationCovDerivCoordAt
          (I := I) (S.family.connection (t : Real)) rhs
          (t : Real) x₀ d k i j =
        nablaGammaDtFromNabla2RicInFrame
          (M := M) (coordInv (I := I) S x₀) nabla2Ric
          (t : Real) x₀ d k i j := by
    simpa [rhs, nablaRic, nabla2Ric] using
      gammaCovNab2Core
        (I := I) S (coordInv (I := I) S x₀) nablaRic nabla2Ric
        x₀ t d k i j
        (fun a b ↦ coordInvMdiff (I := I) S x₀ (t : Real) a b)
        (fun a b c ↦ hnablaReg.first.mdiffAt
          (t : Real) x₀ (coordinateFrameAt_mem (I := I) x₀) a b c)
        (fun a b ↦ coordInvCovZero (I := I) S x₀ t d a b)
        (fun a b c e ↦ coordNab2At (I := I) S x₀ (t : Real) a b c e)
  have hcoord
      (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
      HasDerivWithinAt
        (fun s : Real ↦ S.base.rm04 s x₀
          (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀))
        (varTensor (I := I) (S.base.metric (t : Real))
          (solNabla2Ric (I := I) S (t : Real) x₀)
          (S.base.ricciAt (t : Real) x₀) (S.base.rm04 (t : Real) x₀)
          (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀))
        D.carrier (t : Real) := by
    have hbase : ∀ s, s ∈ D.carrier →
        realizedRmBase (I := I) S x₀ s x₀ m =
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
                (I := I) (S.family.connection s) x₀ (m 0) (m 1) (m 2) p *
              metricCompInFrame (I := I) S frame s x₀ (m 3) p := by
      intro s hs
      simpa [frame] using realizedRmBase_eq_curvCoeff_lower
        (I := I) S x₀ s (rm13OfSol (I := I) S s hs)
        (connCurvOfSol (I := I) S hS x₀ s hs) m
    have hraw :
        HasDerivWithinAt
          (fun s : Real ↦ realizedRmBase (I := I) S x₀ s x₀ m)
          (∑ p : CoordinateIdx (𝕜 := Real) E,
            ((christoffelVariationCovDerivCoordAt
                  (I := I) (S.family.connection (t : Real)) rhs
                  (t : Real) x₀ (m 0) p (m 1) (m 2) -
                christoffelVariationCovDerivCoordAt
                  (I := I) (S.family.connection (t : Real)) rhs
                  (t : Real) x₀ (m 1) p (m 0) (m 2)) *
                metricCompInFrame (I := I) S frame
                  (t : Real) x₀ (m 3) p +
              DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
                  (I := I) (S.family.connection (t : Real))
                  x₀ (m 0) (m 1) (m 2) p *
                ((-2 : Real) * ricciCompInFrame
                  (I := I) S frame (t : Real) x₀ (m 3) p)))
          D.carrier (t : Real) := by
      have hterm : ∀ p ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)),
          HasDerivWithinAt
            (fun s : Real ↦
              DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
                  (I := I) (S.family.connection s) x₀ (m 0) (m 1) (m 2) p *
                metricCompInFrame (I := I) S frame s x₀ (m 3) p)
            ((christoffelVariationCovDerivCoordAt
                  (I := I) (S.family.connection (t : Real)) rhs
                  (t : Real) x₀ (m 0) p (m 1) (m 2) -
                christoffelVariationCovDerivCoordAt
                  (I := I) (S.family.connection (t : Real)) rhs
                  (t : Real) x₀ (m 1) p (m 0) (m 2)) *
                metricCompInFrame (I := I) S frame
                  (t : Real) x₀ (m 3) p +
              DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
                  (I := I) (S.family.connection (t : Real))
                  x₀ (m 0) (m 1) (m 2) p *
                ((-2 : Real) * ricciCompInFrame
                  (I := I) S frame (t : Real) x₀ (m 3) p))
            D.carrier (t : Real) := by
        intro p _hp
        have hcurv :=
          christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation
            (I := I) S hS rhs x₀ hvar hmix t
            (m 0) (m 1) (m 2) p
        have hmetricDt := metricCompInFrame_timeDeriv
          (I := I) S hS frame t x₀ (m 3) p
        exact hcurv.mul hmetricDt
      exact (HasDerivWithinAt.sum hterm).congr
        (fun s hs ↦ by rw [Finset.sum_apply]; exact hbase s hs)
        (by rw [Finset.sum_apply]; exact hbase (t : Real) (D.regular_subset t.2))
    have hderiv :
        (∑ p : CoordinateIdx (𝕜 := Real) E,
            ((christoffelVariationCovDerivCoordAt
                  (I := I) (S.family.connection (t : Real)) rhs
                  (t : Real) x₀ (m 0) p (m 1) (m 2) -
                christoffelVariationCovDerivCoordAt
                  (I := I) (S.family.connection (t : Real)) rhs
                  (t : Real) x₀ (m 1) p (m 0) (m 2)) *
                metricCompInFrame (I := I) S frame
                  (t : Real) x₀ (m 3) p +
              DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
                  (I := I) (S.family.connection (t : Real))
                  x₀ (m 0) (m 1) (m 2) p *
                ((-2 : Real) * ricciCompInFrame
                  (I := I) S frame (t : Real) x₀ (m 3) p))) =
          rm04VarRHS (I := I) S x₀ nabla2Ric (t : Real) m := by
      unfold rm04VarRHS
      refine Finset.sum_congr rfl fun p _hp ↦ ?_
      rw [hgamma (m 0) p (m 1) (m 2), hgamma (m 1) p (m 0) (m 2)]
    have h := hraw.congr_deriv
      (hderiv.trans (rm04Var_eq_tensor
        (I := I) S hS x₀ (t : Real) (D.regular_subset t.2) m))
    simpa only [realizedRmBase_apply] using h
  have htransport := rm04Deriv_of_coord (I := I) S x₀ t
    (fun m ↦ varTensor (I := I) (S.base.metric (t : Real))
      (solNabla2Ric (I := I) S (t : Real) x₀)
      (S.base.ricciAt (t : Real) x₀) (S.base.rm04 (t : Real) x₀)
      (fun q ↦ coordinateFrameAt (I := I) x₀ (m q) x₀))
    hcoord v
  refine htransport.congr_deriv ?_
  have hexp := tensor0S_apply_eq_sum
    (I := I) (coordinateFrameAt_toBasis (I := I) x₀)
    (varTensor (I := I) (S.base.metric (t : Real))
      (solNabla2Ric (I := I) S (t : Real) x₀)
      (S.base.ricciAt (t : Real) x₀) (S.base.rm04 (t : Real) x₀)) v
  simpa only [component0S_apply, coordinateFrameAt_toBasis_apply] using hexp.symm

/-- The arbitrary-dimensional Hamilton evolution of lowered Riemann in a
fixed orthonormal basis, produced directly from a Ricci-flow solution. -/
theorem rm04Base_of_solution_any
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (m : Fin 4 → Idx) :
    HasDerivWithinAt
      (fun s : Real ↦ S.base.rm04 s x (fun q ↦ basis (m q)))
      (tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Idx))
            (nablaKRm04Field (I := I) S (t : Real) 2 x))
          (fun i ↦ basis i) m +
        hamiltonRmReact
          (fun q : Fin 4 → Idx ↦
            S.base.rm04 (t : Real) x (fun p ↦ basis (q p))) m)
      D.carrier (t : Real) := by
  have hvar := rm04Var_of_solution
    (I := I) S hS x t (fun q ↦ basis (m q))
  have hinv : MetricInverseInBasis_gen
      (I := I) (S.base.metric (t : Real)) x basis
      (identityInvMetric (Idx := Idx)) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal
        (I := I) (S.base.metric (t : Real)) basis horth
  exact hvar.congr_deriv (varTensor_eq_ham (I := I) S (t : Real) x basis hinv m)

end DifferentialGeometry.PDE.RicciFlow
