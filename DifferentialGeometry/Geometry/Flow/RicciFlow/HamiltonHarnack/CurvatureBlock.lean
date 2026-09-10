import DifferentialGeometry.Geometry.Curvature.Algebraic.Tensor
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricCongr
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Tensor.RSTensor.Algebra.Product
import DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable local instance harnackTwoFormFiniteDimensional (x : M) :
    FiniteDimensional Real
      (HamiltonHarnackTwoForm (TangentSpace I x)) := by
  let _ : FiniteDimensional Real
      (ContinuousMultilinearMap Real
        (fun _ : Fin 2 ↦ TangentSpace I x) Real) :=
    DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional 2
  exact FiniteDimensional.of_injective
    ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

namespace HamiltonHarnackTwoForm

noncomputable def toTensor0S {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    Tensor0SSpace 2 I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    U.toContinuousMultilinearMap

omit [FiniteDimensional Real E] in
@[simp]
theorem toTensor0S_apply {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (v : Fin 2 → TangentSpace I x) :
    U.toTensor0S v = U v :=
  rfl

omit [FiniteDimensional Real E] in
@[simp]
theorem toTensor0S_add {x : M}
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    (U + V).toTensor0S = U.toTensor0S + V.toTensor0S := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).injective
  ext v
  rfl

omit [FiniteDimensional Real E] in
@[simp]
theorem toTensor0S_smul {x : M} (c : Real)
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    (c • U).toTensor0S = c • U.toTensor0S := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).injective
  ext v
  rfl

omit [FiniteDimensional Real E] in
noncomputable def ofTensor0S {x : M}
    (U : Tensor0SSpace (I := I) 2 x)
    (hU : ∀ X Y : TangentSpace I x, U ![X, Y] = -U ![Y, X]) :
    HamiltonHarnackTwoForm (TangentSpace I x) := by
  refine ContinuousAlternatingMap.mk
    ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x) U) ?_
  intro v i j hv hij
  change U v = 0
  have hvslots : v = ![v 0, v 1] := by
    funext a
    fin_cases a <;> rfl
  rw [hvslots]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · have heq : v 0 = v 1 := hv
    rw [heq]
    have hskew := hU (v 1) (v 1)
    linarith
  · have heq : v 0 = v 1 := hv.symm
    rw [heq]
    have hskew := hU (v 1) (v 1)
    linarith
  · exact (hij rfl).elim

omit [FiniteDimensional Real E] in
@[simp] theorem toTensor0S_ofTensor0S {x : M}
    (U : Tensor0SSpace (I := I) 2 x)
    (hU : ∀ X Y : TangentSpace I x, U ![X, Y] = -U ![Y, X]) :
    (ofTensor0S (I := I) U hU).toTensor0S = U := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).injective
  rfl

omit [FiniteDimensional Real E] in
theorem toTensor0S_injective {x : M} :
    Function.Injective
      (toTensor0S (I := I) (M := M) (x := x)) := by
  intro U V h
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  exact (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm.injective h

def component {Idx : Type*} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (a b : Idx) : Real :=
  component0S (I := I) basis U.toTensor0S ![a, b]

omit [FiniteDimensional Real E] in
theorem component_skew {Idx : Type*} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (a b : Idx) :
    component (I := I) basis U a b = -component (I := I) basis U b a := by
  unfold component
  simp only [component0S_apply, toTensor0S_apply]
  have hswap := U.map_swap (v := ![basis b, basis a]) (i := (0 : Fin 2))
    (j := (1 : Fin 2)) (by decide)
  have hslots :
      ![basis b, basis a] ∘ (Equiv.swap (0 : Fin 2) 1) =
        ![basis a, basis b] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots] at hswap
  have hab : (fun i => basis (![a, b] i)) = ![basis a, basis b] := by
    funext i
    fin_cases i <;> rfl
  have hba : (fun i => basis (![b, a] i)) = ![basis b, basis a] := by
    funext i
    fin_cases i <;> rfl
  rw [hab, hba]
  exact hswap

def rawInner (g : SmoothRiemannianMetric I M) {x : M}
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) : Real :=
  inner0S (I := I) g x 2 U.toTensor0S V.toTensor0S

def inner (g : SmoothRiemannianMetric I M) {x : M}
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) : Real :=
  (2 : Real)⁻¹ * rawInner g U V

def rawNormSq (g : SmoothRiemannianMetric I M) {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) : Real :=
  normSq0S (I := I) g x 2 U.toTensor0S

def normSq (g : SmoothRiemannianMetric I M) {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) : Real :=
  inner g U U

theorem rawInner_self (g : SmoothRiemannianMetric I M) {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    rawInner g U U = rawNormSq g U :=
  rfl

theorem normSq_eq_half_rawNormSq (g : SmoothRiemannianMetric I M) {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    normSq g U = (2 : Real)⁻¹ * rawNormSq g U :=
  rfl

theorem rawNormSq_eq_two_mul_normSq (g : SmoothRiemannianMetric I M) {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    rawNormSq g U = 2 * normSq g U := by
  rw [normSq_eq_half_rawNormSq]
  ring

theorem inner_comm (g : SmoothRiemannianMetric I M) {x : M}
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    inner g U V = inner g V U := by
  unfold inner rawInner
  rw [_root_.Tensor0SBundle.inner0S_comm]

noncomputable def metricData (g : SmoothRiemannianMetric I M) (x : M) :
    MetricFiberData (HamiltonHarnackTwoForm (TangentSpace I x)) := by
  let flat : HamiltonHarnackTwoForm (TangentSpace I x) →ₗ[Real]
      Module.Dual Real (HamiltonHarnackTwoForm (TangentSpace I x)) :=
    { toFun := fun U =>
        { toFun := fun V => inner g U V
          map_add' := by
            intro V W
            simp only [inner, rawInner, toTensor0S_add, inner0S_add_right]
            ring
          map_smul' := by
            intro c V
            change inner g U (c • V) = c • inner g U V
            simp only [inner, rawInner, toTensor0S_smul,
              _root_.Tensor0SBundle.inner0S_smul_right, smul_eq_mul]
            ring }
      map_add' := by
        intro U V
        ext W
        change inner g (U + V) W = inner g U W + inner g V W
        simp only [inner, rawInner, toTensor0S_add, inner0S_add_left]
        ring
      map_smul' := by
        intro c U
        ext V
        change inner g (c • U) V = c • inner g U V
        simp only [inner, rawInner, toTensor0S_smul,
          _root_.Tensor0SBundle.inner0S_smul_left, smul_eq_mul]
        ring }
  refine MetricFiberData.ofFlat flat ?_ ?_ ?_
  · intro U V hUV
    have hsub : flat (U - V) = 0 := by
      rw [map_sub, hUV, sub_self]
    have hzero : inner g (U - V) (U - V) = 0 := by
      change flat (U - V) (U - V) = 0
      rw [hsub]
      rfl
    have htensor : (U - V).toTensor0S = 0 := by
      apply ((tensor0SMetricData (I := I) g x 2).inner_self_eq_zero_iff _).mp
      change rawInner g (U - V) (U - V) = 0
      unfold inner at hzero
      linarith
    have huv : U - V = 0 := by
      apply toTensor0S_injective (I := I) (M := M)
      rw [htensor]
      rfl
    exact sub_eq_zero.mp huv
  · intro U V
    exact inner_comm g U V
  · intro U
    change 0 ≤ inner g U U
    unfold inner rawInner
    rw [show inner0S (I := I) g x 2 U.toTensor0S U.toTensor0S =
      normSq0S (I := I) g x 2 U.toTensor0S from rfl]
    exact mul_nonneg (by norm_num) (normSq0S_nonneg (I := I) g x 2 U.toTensor0S)

theorem metricData_inner (g : SmoothRiemannianMetric I M) (x : M)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    (metricData g x).inner U V = inner g U V :=
  rfl

end HamiltonHarnackTwoForm

def curvatureSlotSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap 2 3

@[simp]
theorem curvatureSlotSwap_zero : curvatureSlotSwap 0 = 0 := by
  decide

@[simp]
theorem curvatureSlotSwap_one : curvatureSlotSwap 1 = 1 := by
  decide

@[simp]
theorem curvatureSlotSwap_two : curvatureSlotSwap 2 = 3 := by
  decide

@[simp]
theorem curvatureSlotSwap_three : curvatureSlotSwap 3 = 2 := by
  decide

def curvatureBlock {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) : Real :=
  inner0S (I := I) g x 4
    ((A : Tensor0SSpace 4 I x).domDomCongr curvatureSlotSwap)
    (U.toTensor0S.product V.toTensor0S)

def hamiltonQuadraticAt {x : M}
    (g : SmoothRiemannianMetric I M)
    (R : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (P : Tensor0SSpace 3 I x) (Mbar : Tensor0SSpace 2 I x)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) : Real :=
  curvatureBlock g R U U +
    2 * inner0S (I := I) g x 3 P (U.toTensor0S.product W) +
    inner0S (I := I) g x 2 Mbar (W.product W)

theorem curvatureBlock_eq_sum {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx))) :
    curvatureBlock g A U V =
      ∑ slots : Fin 4 → Idx,
        tensor04StandardAt (I := I) (M := M)
            (A : Tensor04At (I := I) (M := M) x)
            (basis (slots 0)) (basis (slots 1))
            (basis (slots 3)) (basis (slots 2)) *
          (U (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) *
            V (vec2 (I := I) (basis (slots 2)) (basis (slots 3)))) := by
  rw [curvatureBlock,
    Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 4 basis hinv]
  apply Finset.sum_congr rfl
  intro slots _
  rw [component0S_apply, component0S_apply,
    Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.product_apply]
  congr 1
  · change (A : Tensor04At (I := I) (M := M) x)
      (fun i => basis (slots (curvatureSlotSwap i))) = _
    congr 1
    funext i
    fin_cases i <;> simp [vec4]
  · congr 1
    · rw [HamiltonHarnackTwoForm.toTensor0S_apply]
      congr 1
      funext i
      fin_cases i <;> simp [vec2]
    · rw [HamiltonHarnackTwoForm.toTensor0S_apply]
      congr 1
      funext i
      fin_cases i <;> simp [vec2]

omit [FiniteDimensional Real E] in
private theorem curvatureKernel_finAddFlip {x : M}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (((A : Tensor0SSpace 4 I x).domDomCongr curvatureSlotSwap).domDomCongr
        (finAddFlip (m := 2) (n := 2))) =
      (A : Tensor0SSpace 4 I x).domDomCongr curvatureSlotSwap := by
  ext v
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply]
  have hleft :
      (fun i => v ((finAddFlip (m := 2) (n := 2)) (curvatureSlotSwap i))) =
        vec4 (I := I) (v 2) (v 3) (v 1) (v 0) := by
    funext i
    fin_cases i <;> rfl
  have hright :
      (fun i => v (curvatureSlotSwap i)) =
        vec4 (I := I) (v 0) (v 1) (v 3) (v 2) := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright]
  have hA := mem_algebraicCurvatureTensorSubmodule.mp A.2
  calc
    tensor04StandardAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (v 2) (v 3) (v 1) (v 0) =
      -tensor04StandardAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (v 3) (v 2) (v 1) (v 0) := hA.anti_first _ _ _ _
    _ = tensor04StandardAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (v 3) (v 2) (v 0) (v 1) := (hA.anti_last _ _ _ _).symm
    _ = tensor04StandardAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (v 0) (v 1) (v 3) (v 2) := (hA.pair_swap _ _ _ _).symm

omit [FiniteDimensional Real E] in
private theorem product_finAddFlip {x : M}
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    (U.toTensor0S.product V.toTensor0S).domDomCongr
        (finAddFlip (m := 2) (n := 2)) =
      V.toTensor0S.product U.toTensor0S := by
  ext v
  rw [Tensor0SSpace.domDomCongr_apply,
    Tensor0SSpace.product_apply, Tensor0SSpace.product_apply]
  rw [HamiltonHarnackTwoForm.toTensor0S_apply,
    HamiltonHarnackTwoForm.toTensor0S_apply,
    HamiltonHarnackTwoForm.toTensor0S_apply,
    HamiltonHarnackTwoForm.toTensor0S_apply]
  have hleft0 :
      (fun i => v ((finAddFlip (m := 2) (n := 2)) i)) ∘ Fin.castAdd 2 =
        vec2 (I := I) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  have hleft1 :
      (fun i => v ((finAddFlip (m := 2) (n := 2)) i)) ∘ Fin.natAdd 2 =
        vec2 (I := I) (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  have hright0 : v ∘ Fin.castAdd 2 = vec2 (I := I) (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  have hright1 : v ∘ Fin.natAdd 2 = vec2 (I := I) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hleft0, hleft1, hright0, hright1, mul_comm]

theorem curvatureBlock_comm {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    curvatureBlock g A U V = curvatureBlock g A V U := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have h := Tensor0SBundle.inner0S_domDomCongr (I := I) g x basis hinv
    (finAddFlip (m := 2) (n := 2))
    ((A : Tensor0SSpace 4 I x).domDomCongr curvatureSlotSwap)
    (U.toTensor0S.product V.toTensor0S)
  rw [curvatureKernel_finAddFlip, product_finAddFlip] at h
  exact h.symm

omit [FiniteDimensional Real E] in
private theorem product_add_right {x : M}
    (U V W : HamiltonHarnackTwoForm (TangentSpace I x)) :
    U.toTensor0S.product (V + W).toTensor0S =
      U.toTensor0S.product V.toTensor0S +
        U.toTensor0S.product W.toTensor0S := by
  ext v
  simp only [DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply,
    HamiltonHarnackTwoForm.toTensor0S_add, Tensor0SSpace.add_apply]
  ring

omit [FiniteDimensional Real E] in
private theorem product_add_left {x : M}
    (U V W : HamiltonHarnackTwoForm (TangentSpace I x)) :
    (U + V).toTensor0S.product W.toTensor0S =
      U.toTensor0S.product W.toTensor0S +
        V.toTensor0S.product W.toTensor0S := by
  ext v
  simp only [DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply,
    HamiltonHarnackTwoForm.toTensor0S_add, Tensor0SSpace.add_apply]
  ring

omit [FiniteDimensional Real E] in
private theorem product_smul_right {x : M} (c : Real)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    U.toTensor0S.product (c • V).toTensor0S =
      c • (U.toTensor0S.product V.toTensor0S) := by
  ext v
  simp only [DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply,
    HamiltonHarnackTwoForm.toTensor0S_smul, Tensor0SSpace.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional Real E] in
private theorem product_smul_left {x : M} (c : Real)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    (c • U).toTensor0S.product V.toTensor0S =
      c • (U.toTensor0S.product V.toTensor0S) := by
  ext v
  simp only [DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.product_apply,
    HamiltonHarnackTwoForm.toTensor0S_smul, Tensor0SSpace.smul_apply, smul_eq_mul]
  ring

private theorem curvatureBlock_add_right {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V W : HamiltonHarnackTwoForm (TangentSpace I x)) :
    curvatureBlock g A U (V + W) =
      curvatureBlock g A U V + curvatureBlock g A U W := by
  unfold curvatureBlock
  rw [product_add_right, inner0S_add_right]

private theorem curvatureBlock_add_left {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V W : HamiltonHarnackTwoForm (TangentSpace I x)) :
    curvatureBlock g A (U + V) W =
      curvatureBlock g A U W + curvatureBlock g A V W := by
  unfold curvatureBlock
  rw [product_add_left, inner0S_add_right]

private theorem curvatureBlock_smul_right {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Real) (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    curvatureBlock g A U (c • V) = c * curvatureBlock g A U V := by
  unfold curvatureBlock
  rw [product_smul_right, _root_.Tensor0SBundle.inner0S_smul_right]

private theorem curvatureBlock_smul_left {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Real) (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    curvatureBlock g A (c • U) V = c * curvatureBlock g A U V := by
  unfold curvatureBlock
  rw [product_smul_left, _root_.Tensor0SBundle.inner0S_smul_right]

noncomputable def curvatureBlockDual {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    Module.Dual Real (HamiltonHarnackTwoForm (TangentSpace I x)) where
  toFun V := (2 : Real)⁻¹ * curvatureBlock g A U V
  map_add' V W := by
    rw [curvatureBlock_add_right]
    ring
  map_smul' c V := by
    rw [curvatureBlock_smul_right]
    simp only [RingHom.id_apply]
    ring

noncomputable def curvatureBlockDualLinear {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    HamiltonHarnackTwoForm (TangentSpace I x) →ₗ[Real]
      Module.Dual Real (HamiltonHarnackTwoForm (TangentSpace I x)) where
  toFun U := curvatureBlockDual g A U
  map_add' U V := by
    ext W
    change (2 : Real)⁻¹ * curvatureBlock g A (U + V) W =
      (2 : Real)⁻¹ * curvatureBlock g A U W +
        (2 : Real)⁻¹ * curvatureBlock g A V W
    rw [curvatureBlock_add_left]
    ring
  map_smul' c U := by
    ext V
    change (2 : Real)⁻¹ * curvatureBlock g A (c • U) V =
      c • ((2 : Real)⁻¹ * curvatureBlock g A U V)
    rw [curvatureBlock_smul_left]
    simp only [smul_eq_mul]
    ring

noncomputable def curvatureOperator {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    HamiltonHarnackTwoForm (TangentSpace I x) →ₗ[Real]
      HamiltonHarnackTwoForm (TangentSpace I x) :=
  (HamiltonHarnackTwoForm.metricData g x).sharp.toLinearMap.comp
    (curvatureBlockDualLinear g A)

theorem curvatureOperator_inner {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    HamiltonHarnackTwoForm.inner g (curvatureOperator g A U) V =
      (2 : Real)⁻¹ * curvatureBlock g A U V := by
  change (HamiltonHarnackTwoForm.metricData g x).flat
      ((HamiltonHarnackTwoForm.metricData g x).flat.symm
        (curvatureBlockDual g A U)) V = _
  rw [(HamiltonHarnackTwoForm.metricData g x).flat.apply_symm_apply]
  rfl

theorem curvatureOperator_inner_comm {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) :
    HamiltonHarnackTwoForm.inner g (curvatureOperator g A U) V =
      HamiltonHarnackTwoForm.inner g U (curvatureOperator g A V) := by
  calc
    HamiltonHarnackTwoForm.inner g (curvatureOperator g A U) V =
        (2 : Real)⁻¹ * curvatureBlock g A U V :=
      curvatureOperator_inner g A U V
    _ = (2 : Real)⁻¹ * curvatureBlock g A V U := by
      rw [curvatureBlock_comm]
    _ = HamiltonHarnackTwoForm.inner g (curvatureOperator g A V) U :=
      (curvatureOperator_inner g A V U).symm
    _ = HamiltonHarnackTwoForm.inner g U (curvatureOperator g A V) :=
      HamiltonHarnackTwoForm.inner_comm g _ _

theorem curvatureBlock_eq_two_inner_curvatureOperator {x : M}
    (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    curvatureBlock g A U U =
      2 * HamiltonHarnackTwoForm.inner g (curvatureOperator g A U) U := by
  rw [curvatureOperator_inner]
  ring

noncomputable def metricCurvatureBlock [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (U V : HamiltonHarnackTwoForm (TangentSpace I x)) : Real :=
  curvatureBlock g
    (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) U V

noncomputable def metricCurvatureOperator [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    HamiltonHarnackTwoForm (TangentSpace I x) →ₗ[Real]
      HamiltonHarnackTwoForm (TangentSpace I x) :=
  curvatureOperator g
    (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x)

theorem metricCurvatureBlock_eq_two_inner_metricCurvatureOperator [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (U : HamiltonHarnackTwoForm (TangentSpace I x)) :
    metricCurvatureBlock g U U =
      2 * HamiltonHarnackTwoForm.inner g
        (metricCurvatureOperator g x U) U := by
  exact curvatureBlock_eq_two_inner_curvatureOperator g
    (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x) U

end DifferentialGeometry.PDE.RicciFlow
