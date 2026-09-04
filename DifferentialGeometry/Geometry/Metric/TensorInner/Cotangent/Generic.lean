import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Generic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dual.Basis
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def cotangentToCLMGen {x : M} (α : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[Real] Real :=
  continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) 1 x α)

def cotangentToDualGen {x : M} (α : Tensor0SSpace 1 I x) :
    Module.Dual Real (TangentSpace I x) :=
  (cotangentToCLMGen (I := I) α).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDual_apply_gen {x : M}
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    cotangentToDualGen (I := I) α X = α (fun _ : Fin 1 => X) := by
  let hM : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  change continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
      (@tensor0SSpaceFiberContinuousLinearEquiv Real _ E _ _ H _ I M _ _ hM 1 x α) X =
      α (fun _ : Fin 1 => X)
  rw [continuousMultilinearCurryFin1_apply,
    @tensor0SSpaceFiberContinuousLinearEquiv_apply Real _ E _ _ H _ I M _ _ hM]
  congr 1

def cotangentToDualLinearGen {x : M} :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun := cotangentToDualGen (I := I)
  map_add' α β := by
    ext X
    rfl
  map_smul' c α := by
    ext X
    rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDualLinear_apply_gen {x : M}
    (α : Tensor0SSpace 1 I x) :
    cotangentToDualLinearGen (I := I) α = cotangentToDualGen (I := I) α := by
  rfl

omit [FiniteDimensional ℝ E] in
theorem cotangentToDualLinear_injective_gen {x : M} :
    Function.Injective (cotangentToDualLinearGen (I := I) (x := x)) := by
  intro α β h
  ext v
  have hv :
      (fun _ : Fin 1 => v 0) = v := by
    funext i
    fin_cases i
    rfl
  have h0 := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L (v 0)) h
  simpa [cotangentToDualLinearGen, cotangentToDual_apply_gen, hv] using h0

def dualToCotangentGen {x : M} (α : Module.Dual Real (TangentSpace I x)) :
    Tensor0SSpace 1 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (LinearMap.toContinuousLinearMap α))

def dualToCotangentLinear {x : M} :
    Module.Dual Real (TangentSpace I x) →ₗ[Real] Tensor0SSpace 1 I x where
  toFun := dualToCotangentGen (I := I)
  map_add' α β := by
    apply cotangentToDualLinear_injective_gen (I := I) (x := x)
    ext X
    change (α + β) X = α X + β X
    rfl
  map_smul' c α := by
    apply cotangentToDualLinear_injective_gen (I := I) (x := x)
    ext X
    change (c • α) X = c * α X
    rfl

@[simp] theorem dualToCotangentLinear_apply {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    dualToCotangentLinear (I := I) α = dualToCotangentGen (I := I) α := by
  rfl

@[simp] theorem dualToCotangent_apply_gen {x : M}
    (α : Module.Dual Real (TangentSpace I x)) (X : TangentSpace I x) :
    Tensor0SSpace.eval (dualToCotangentGen (I := I) α) (fun _ : Fin 1 => X) = α X := by
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
        (LinearMap.toContinuousLinearMap α)) (fun _ : Fin 1 => X) = α X
  rfl

@[simp] theorem cotangentToDual_dualToCotangent_gen {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    cotangentToDualGen (I := I) (dualToCotangentGen (I := I) α) = α := by
  ext X
  change Tensor0SSpace.eval (dualToCotangentGen (I := I) α) (fun _ : Fin 1 => X) = α X
  exact dualToCotangent_apply_gen α X

def cotangentSharpLinearGen (g : SmoothMetricGen I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] TangentSpace I x :=
  ((tangentMetricDataGen (I := I) g x).metric.sharp).toLinearMap.comp
    (cotangentToDualLinearGen (I := I) (x := x))

def cotangentSharpGen (g : SmoothMetricGen I M) (x : M)
    (α : Tensor0SSpace 1 I x) : TangentSpace I x :=
  cotangentSharpLinearGen (I := I) g x α

@[simp] theorem cotangentSharpLinear_apply_gen
    (g : SmoothMetricGen I M) (x : M) (α : Tensor0SSpace 1 I x) :
    cotangentSharpLinearGen (I := I) g x α = cotangentSharpGen (I := I) g x α := by
  rfl

theorem cotangentSharpLinear_injective_gen
    (g : SmoothMetricGen I M) (x : M) :
    Function.Injective (cotangentSharpLinearGen (I := I) g x) := by
  intro α β h
  apply cotangentToDualLinear_injective_gen (I := I) (x := x)
  exact ((tangentMetricDataGen (I := I) g x).metric.sharp.injective h)

def cotangentInnerGen (g : SmoothMetricGen I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : Real :=
  g.inner x
    (cotangentSharpLinearGen (I := I) g x α)
    (cotangentSharpLinearGen (I := I) g x β)

@[simp] theorem cotangentInner_eq_sharp_gen
    (g : SmoothMetricGen I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInnerGen (I := I) g x α β =
      g.inner x (cotangentSharpGen (I := I) g x α)
        (cotangentSharpGen (I := I) g x β) := by
  rfl

def cotangentFlatLinearGen (g : SmoothMetricGen I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (Tensor0SSpace 1 I x) where
  toFun α :=
    { toFun := fun β => cotangentInnerGen (I := I) g x α β
      map_add' := by
        intro β γ
        let S := cotangentSharpLinearGen (I := I) g x
        have hS : S (β + γ) = S β + S γ := map_add S β γ
        change g.inner x (S α) (S (β + γ)) =
          g.inner x (S α) (S β) + g.inner x (S α) (S γ)
        rw [hS]
        simp
      map_smul' := by
        intro c β
        let S := cotangentSharpLinearGen (I := I) g x
        have hS : S (c • β) = c • S β := map_smul S c β
        change g.inner x (S α) (S (c • β)) = c * g.inner x (S α) (S β)
        rw [hS]
        simp }
  map_add' α β := by
    ext γ
    let S := cotangentSharpLinearGen (I := I) g x
    have hS : S (α + β) = S α + S β := map_add S α β
    change g.inner x (S (α + β)) (S γ) =
      g.inner x (S α) (S γ) + g.inner x (S β) (S γ)
    rw [hS]
    simp
  map_smul' c α := by
    ext β
    let S := cotangentSharpLinearGen (I := I) g x
    have hS : S (c • α) = c • S α := map_smul S c α
    change g.inner x (S (c • α)) (S β) = c * g.inner x (S α) (S β)
    rw [hS]
    simp

@[simp] theorem cotangentFlatLinear_apply_gen
    (g : SmoothMetricGen I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentFlatLinearGen (I := I) g x α β =
      cotangentInnerGen (I := I) g x α β := by
  rfl

theorem cotangentFlatLinear_injective_gen
    (g : SmoothMetricGen I M) (x : M) :
    Function.Injective (cotangentFlatLinearGen (I := I) g x) := by
  intro α β h
  have hsub : cotangentSharpLinearGen (I := I) g x (α - β) = 0 := by
    by_contra hsharp
    have hpos :
        0 <
          g.inner x
            (cotangentSharpLinearGen (I := I) g x (α - β))
            (cotangentSharpLinearGen (I := I) g x (α - β)) :=
      g.pos x (cotangentSharpLinearGen (I := I) g x (α - β)) hsharp
    have h_eval :
        cotangentFlatLinearGen (I := I) g x α (α - β) =
          cotangentFlatLinearGen (I := I) g x β (α - β) :=
      congrArg
        (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β)) h
    have hdiff : cotangentFlatLinearGen (I := I) g x (α - β) (α - β) = 0 := by
      calc
        cotangentFlatLinearGen (I := I) g x (α - β) (α - β)
            = (cotangentFlatLinearGen (I := I) g x α -
                cotangentFlatLinearGen (I := I) g x β) (α - β) := by
                exact congrArg
                  (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β))
                  (map_sub (cotangentFlatLinearGen (I := I) g x) α β)
        _ = cotangentFlatLinearGen (I := I) g x α (α - β) -
              cotangentFlatLinearGen (I := I) g x β (α - β) := rfl
        _ = 0 := sub_eq_zero.mpr h_eval
    have hzero :
        g.inner x
            (cotangentSharpLinearGen (I := I) g x (α - β))
            (cotangentSharpLinearGen (I := I) g x (α - β)) = 0 := by
      simpa [cotangentFlatLinearGen, cotangentInnerGen] using hdiff
    exact (lt_irrefl (0 : Real)) (hzero ▸ hpos)
  apply cotangentSharpLinear_injective_gen (I := I) g x
  have hdiff :
      cotangentSharpLinearGen (I := I) g x α -
        cotangentSharpLinearGen (I := I) g x β = 0 := by
    have hmap :
        cotangentSharpLinearGen (I := I) g x (α - β) =
          cotangentSharpLinearGen (I := I) g x α -
            cotangentSharpLinearGen (I := I) g x β :=
      map_sub (cotangentSharpLinearGen (I := I) g x) α β
    rwa [hmap] at hsub
  exact sub_eq_zero.mp hdiff

def cotangentMetricDataGen (g : SmoothMetricGen I M) (x : M) :
    MetricFiberData (Tensor0SSpace 1 I x) :=
  MetricFiberData.ofFlat
    (cotangentFlatLinearGen (I := I) g x)
    (cotangentFlatLinear_injective_gen (I := I) g x)
    (by
      intro α β
      change g.inner x
          (cotangentSharpLinearGen (I := I) g x α)
          (cotangentSharpLinearGen (I := I) g x β) =
        g.inner x
          (cotangentSharpLinearGen (I := I) g x β)
          (cotangentSharpLinearGen (I := I) g x α)
      exact g.symm x _ _)
    (by
      intro α
      by_cases hα : cotangentSharpLinearGen (I := I) g x α = 0
      · change 0 <=
          g.inner x
            (cotangentSharpLinearGen (I := I) g x α)
            (cotangentSharpLinearGen (I := I) g x α)
        rw [hα]
        simp
      · exact le_of_lt (g.pos x (cotangentSharpLinearGen (I := I) g x α) hα))

theorem cotangentMetricData_inner_gen
    (g : SmoothMetricGen I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricDataGen (I := I) g x).inner α β =
      cotangentInnerGen (I := I) g x α β := by
  rfl

def MetricInverseOnFiniteFrameGramGen {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (frame k) (frame j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i) (frame k) * gInv k j) =
        (if i = j then 1 else 0)

def MetricInverseInBasisGen {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (basis k) (basis j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (basis i) (basis k) * gInv k j) =
        (if i = j then 1 else 0)

noncomputable def basisInvMetric {Idx : Type*}
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) : Real :=
  basis.coord j ((tangentFlatEquivGen (I := I) g x).symm (basis.coord i))

theorem basisInvMetric_symm {Idx : Type*}
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    forall i j : Idx,
      basisInvMetric (I := I) g x basis i j =
        basisInvMetric (I := I) g x basis j i := by
  intro i j
  let sharp := (tangentFlatEquivGen (I := I) g x).symm
  have hleft :
      basis.coord j (sharp (basis.coord i)) =
        g.inner x (sharp (basis.coord j)) (sharp (basis.coord i)) := by
    change basis.coord j (sharp (basis.coord i)) =
      (tangentFlatEquivGen (I := I) g x (sharp (basis.coord j)))
        (sharp (basis.coord i))
    rw [(tangentFlatEquivGen (I := I) g x).apply_symm_apply]
  have hright :
      basis.coord i (sharp (basis.coord j)) =
        g.inner x (sharp (basis.coord i)) (sharp (basis.coord j)) := by
    change basis.coord i (sharp (basis.coord j)) =
      (tangentFlatEquivGen (I := I) g x (sharp (basis.coord i)))
        (sharp (basis.coord j))
    rw [(tangentFlatEquivGen (I := I) g x).apply_symm_apply]
  calc
    basisInvMetric (I := I) g x basis i j =
        g.inner x (sharp (basis.coord j)) (sharp (basis.coord i)) := by
          simpa [basisInvMetric, sharp] using hleft
    _ = g.inner x (sharp (basis.coord i)) (sharp (basis.coord j)) := by
          exact g.symm x _ _
    _ = basisInvMetric (I := I) g x basis j i := by
          simpa [basisInvMetric, sharp] using hright.symm

theorem basisInvMetric_real {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    MetricInverseInBasisGen (I := I) g x basis
      (basisInvMetric (I := I) g x basis) := by
  classical
  let sharp := (tangentFlatEquivGen (I := I) g x).symm
  have hleft (i j : Idx) :
      (∑ k : Idx,
          basisInvMetric (I := I) g x basis i k *
            g.inner x (basis k) (basis j)) =
        (if i = j then 1 else 0) := by
    have hsum :
        (∑ k : Idx,
            basisInvMetric (I := I) g x basis i k • basis k) =
          sharp (basis.coord i) := by
      simp [basisInvMetric, sharp]
    calc
      (∑ k : Idx,
          basisInvMetric (I := I) g x basis i k *
            g.inner x (basis k) (basis j)) =
          g.inner x
            (∑ k : Idx,
              basisInvMetric (I := I) g x basis i k • basis k)
            (basis j) := by
            simp [map_sum, map_smul, smul_eq_mul]
      _ = g.inner x (sharp (basis.coord i)) (basis j) := by
            rw [hsum]
      _ = basis.coord i (basis j) := by
            change
              (tangentFlatEquivGen (I := I) g x (sharp (basis.coord i)))
                (basis j) =
              basis.coord i (basis j)
            rw [(tangentFlatEquivGen (I := I) g x).apply_symm_apply]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · simp [hij]
  have hsym :
      forall i j : Idx,
        basisInvMetric (I := I) g x basis i j =
          basisInvMetric (I := I) g x basis j i :=
    basisInvMetric_symm (I := I) g x basis
  intro i j
  constructor
  · exact hleft i j
  · calc
      (∑ k : Idx,
          g.inner x (basis i) (basis k) *
            basisInvMetric (I := I) g x basis k j) =
          ∑ k : Idx,
            basisInvMetric (I := I) g x basis j k *
              g.inner x (basis k) (basis i) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym k j, g.symm x (basis i) (basis k), mul_comm]
      _ = (if j = i then 1 else 0) := hleft j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]

omit [FiniteDimensional ℝ E] in
theorem invBasis_unique {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv₁ gInv₂ : Idx → Idx → Real)
    (h₁ : MetricInverseInBasisGen (I := I) g x basis gInv₁)
    (h₂ : MetricInverseInBasisGen (I := I) g x basis gInv₂) :
    gInv₁ = gInv₂ := by
  classical
  let A : Matrix Idx Idx Real := gInv₁
  let B : Matrix Idx Idx Real := gInv₂
  let G : Matrix Idx Idx Real := fun i j => g.inner x (basis i) (basis j)
  have hAG : A * G = 1 := by
    ext i j
    change (∑ k, gInv₁ i k * g.inner x (basis k) (basis j)) = (1 : Matrix Idx Idx Real) i j
    rw [Matrix.one_apply]
    exact (h₁ i j).1
  have hGB : G * B = 1 := by
    ext i j
    change (∑ k, g.inner x (basis i) (basis k) * gInv₂ k j) = (1 : Matrix Idx Idx Real) i j
    rw [Matrix.one_apply]
    exact (h₂ i j).2
  have hAB : A = B := by
    calc
      A = A * 1 := by simp
      _ = A * (G * B) := by rw [hGB]
      _ = (A * G) * B := by rw [Matrix.mul_assoc]
      _ = 1 * B := by rw [hAG]
      _ = B := by simp
  funext i j
  exact congrArg (fun C : Matrix Idx Idx Real => C i j) hAB

omit [FiniteDimensional ℝ E] in
theorem invMetric_symm {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv) :
    forall i j : Idx, gInv i j = gInv j i := by
  classical
  let A : Matrix Idx Idx Real := fun i j => gInv i j
  let G : Matrix Idx Idx Real := fun i j => g.inner x (basis i) (basis j)
  have hAG : A * G = 1 := by
    ext i j
    change (∑ k, gInv i k * g.inner x (basis k) (basis j)) = (1 : Matrix Idx Idx Real) i j
    rw [Matrix.one_apply]
    exact (hinv i j).1
  have hGA : G * A = 1 := by
    ext i j
    change (∑ k, g.inner x (basis i) (basis k) * gInv k j) = (1 : Matrix Idx Idx Real) i j
    rw [Matrix.one_apply]
    exact (hinv i j).2
  have hGt : Matrix.transpose G = G := by
    ext i j
    rw [Matrix.transpose_apply]
    exact g.symm x (basis j) (basis i)
  have hAtG : Matrix.transpose A * G = 1 := by
    calc
      Matrix.transpose A * G = Matrix.transpose A * Matrix.transpose G := by rw [hGt]
      _ = Matrix.transpose (G * A) := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hGA]; simp
  have hAt : Matrix.transpose A = A := by
    calc
      Matrix.transpose A = Matrix.transpose A * 1 := by simp
      _ = Matrix.transpose A * (G * A) := by rw [hGA]
      _ = (Matrix.transpose A * G) * A := by rw [← Matrix.mul_assoc]
      _ = 1 * A := by rw [hAtG]
      _ = A := by simp
  intro i j
  have hentry := congrArg (fun B : Matrix Idx Idx Real => B j i) hAt
  change A i j = A j i
  exact (Matrix.transpose_apply A j i).symm.trans hentry

omit [FiniteDimensional ℝ E] in
theorem coord_eq_invInner {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V =
      ∑ k : Idx, gInv a k * g.inner x (basis k) V := by
  classical
  symm
  calc
    (∑ k : Idx, gInv a k * g.inner x (basis k) V)
        = ∑ k : Idx, gInv a k *
            g.inner x (basis k) (∑ j : Idx, basis.coord j V • basis j) := by
          rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
    _ = ∑ k : Idx, ∑ j : Idx,
          gInv a k * (basis.coord j V * g.inner x (basis k) (basis j)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_sum]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul]
          simp [smul_eq_mul]
    _ = ∑ j : Idx, basis.coord j V *
          (∑ k : Idx, gInv a k * g.inner x (basis k) (basis j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ = ∑ j : Idx, basis.coord j V * (if a = j then 1 else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [(hinv a j).1]
    _ = basis.coord a V := by
          simp

theorem cotangentSharp_inner_gen
    (g : SmoothMetricGen I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharpGen (I := I) g x α) X =
      cotangentToDualGen (I := I) α X := by
  have h :=
    congrArg
      (fun L : Module.Dual Real (TangentSpace I x) => L X)
      ((tangentMetricDataGen (I := I) g x).metric.flat.apply_symm_apply
        (cotangentToDualGen (I := I) α))
  change
    (tangentMetricDataGen (I := I) g x).metric.flat
        ((tangentMetricDataGen (I := I) g x).metric.sharp
          (cotangentToDualGen (I := I) α)) X =
      cotangentToDualGen (I := I) α X
  exact h

theorem cotangentSharp_inner_eval
    (g : SmoothMetricGen I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharpGen (I := I) g x α) X =
      α (fun _ : Fin 1 => X) := by
  rw [cotangentSharp_inner_gen, cotangentToDual_apply_gen]

theorem cotangentSharp_dualToCotangent_tangentFlat_gen
    (g : SmoothMetricGen I M) (x : M) (X : TangentSpace I x) :
    cotangentSharpGen (I := I) g x
      (dualToCotangentGen (I := I) (tangentFlatLinearGen (I := I) g x X)) = X := by
  apply tangentFlatLinear_injective_gen (I := I) g x
  ext Y
  simp [tangentFlatLinear_apply_gen, cotangentSharp_inner_gen]

theorem cotangentInner_dualToCotangent_tangentFlat_gen
    (g : SmoothMetricGen I M) (x : M) (X Y : TangentSpace I x) :
    cotangentInnerGen (I := I) g x
      (dualToCotangentGen (I := I) (tangentFlatLinearGen (I := I) g x X))
      (dualToCotangentGen (I := I) (tangentFlatLinearGen (I := I) g x Y)) =
        g.inner x X Y := by
  rw [cotangentInner_eq_sharp_gen,
    cotangentSharp_dualToCotangent_tangentFlat_gen,
    cotangentSharp_dualToCotangent_tangentFlat_gen]

omit [FiniteDimensional ℝ E] in
theorem eq_of_inner_basis_eq_gen
    {Idx : Type*} [Finite Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {X Y : TangentSpace I x}
    (h : forall i : Idx, g.inner x X (basis i) = g.inner x Y (basis i)) :
    X = Y := by
  let : Fintype Idx := Fintype.ofFinite Idx
  apply tangentFlatLinear_injective_gen (I := I) g x
  ext Z
  have hcoord (L : TangentSpace I x →ₗ[Real] Real) :
      L Z = ∑ i : Idx, basis.repr Z i • L (basis i) := by
    conv_lhs => rw [← basis.sum_repr Z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  calc
    tangentFlatLinearGen (I := I) g x X Z
        = ∑ i : Idx, basis.repr Z i • tangentFlatLinearGen (I := I) g x X (basis i) :=
          hcoord (tangentFlatLinearGen (I := I) g x X)
    _ = ∑ i : Idx, basis.repr Z i • tangentFlatLinearGen (I := I) g x Y (basis i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [tangentFlatLinear_apply_gen, tangentFlatLinear_apply_gen, h i]
    _ = tangentFlatLinearGen (I := I) g x Y Z := by
          exact (hcoord (tangentFlatLinearGen (I := I) g x Y)).symm

theorem cotangentSharp_eq_sum_inv_gen
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (β : Tensor0SSpace 1 I x) :
    cotangentSharpGen (I := I) g x β =
      ∑ i : Idx,
        (∑ j : Idx, gInv i j * cotangentToDualGen (I := I) β (basis j)) •
          basis i := by
  apply eq_of_inner_basis_eq_gen (I := I) g x basis
  intro l
  calc
    g.inner x (cotangentSharpGen (I := I) g x β) (basis l)
        = cotangentToDualGen (I := I) β (basis l) := by
          rw [cotangentSharp_inner_gen]
    _ = ∑ j : Idx, (if l = j then 1 else 0) *
          cotangentToDualGen (I := I) β (basis j) := by
          simp
    _ = ∑ j : Idx,
          (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
            cotangentToDualGen (I := I) β (basis j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [(hinv l j).2]
    _ = ∑ i : Idx,
          (∑ j : Idx, gInv i j * cotangentToDualGen (I := I) β (basis j)) *
            g.inner x (basis i) (basis l) := by
          calc
            (∑ j : Idx,
                (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
                  cotangentToDualGen (I := I) β (basis j))
                = ∑ j : Idx, ∑ i : Idx,
                    (g.inner x (basis l) (basis i) * gInv i j) *
                      cotangentToDualGen (I := I) β (basis j) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [Finset.sum_mul]
            _ = ∑ i : Idx, ∑ j : Idx,
                    (g.inner x (basis l) (basis i) * gInv i j) *
                      cotangentToDualGen (I := I) β (basis j) := by
                    rw [Finset.sum_comm]
            _ = ∑ i : Idx,
                  (∑ j : Idx, gInv i j * cotangentToDualGen (I := I) β (basis j)) *
                    g.inner x (basis i) (basis l) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [g.symm x (basis l) (basis i)]
                    ring
    _ = g.inner x
          (∑ i : Idx,
            (∑ j : Idx, gInv i j * cotangentToDualGen (I := I) β (basis j)) •
              basis i)
          (basis l) := by
          simp [map_sum]

theorem cotangentInner_eq_coord_gen
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInnerGen (I := I) g x α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDualGen (I := I) α (basis i) *
          cotangentToDualGen (I := I) β (basis j) := by
  calc
    cotangentInnerGen (I := I) g x α β
        = g.inner x (cotangentSharpGen (I := I) g x α)
            (cotangentSharpGen (I := I) g x β) := rfl
    _ = cotangentToDualGen (I := I) α (cotangentSharpGen (I := I) g x β) := by
          rw [cotangentSharp_inner_gen]
    _ = cotangentToDualGen (I := I) α
          (∑ i : Idx,
            (∑ j : Idx, gInv i j * cotangentToDualGen (I := I) β (basis j)) •
              basis i) := by
          rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv β]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * cotangentToDualGen (I := I) α (basis i) *
            cotangentToDualGen (I := I) β (basis j) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul]
          change (∑ j : Idx, gInv i j * cotangentToDualGen (I := I) β (basis j)) *
              cotangentToDualGen (I := I) α (basis i) =
            ∑ j : Idx,
              gInv i j * cotangentToDualGen (I := I) α (basis i) *
                cotangentToDualGen (I := I) β (basis j)
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          change (gInv i j * cotangentToDualGen (I := I) β (basis j)) *
              cotangentToDualGen (I := I) α (basis i) =
            gInv i j * cotangentToDualGen (I := I) α (basis i) *
              cotangentToDualGen (I := I) β (basis j)
          ring

theorem cotangentMetricData_inner_eq_coord_gen
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetricGen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricDataGen (I := I) g x).inner α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDualGen (I := I) α (basis i) *
          cotangentToDualGen (I := I) β (basis j) := by
  rw [cotangentMetricData_inner_gen, cotangentInner_eq_coord_gen (I := I) g x basis gInv hinv]

end

end Tensor0SBundle
end DifferentialGeometry
