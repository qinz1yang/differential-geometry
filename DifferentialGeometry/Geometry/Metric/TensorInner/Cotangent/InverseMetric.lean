import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dual.Basis

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def dualToCotangentLinear {x : M} :
    Module.Dual Real (TangentSpace I x) →ₗ[Real] Tensor0SSpace 1 I x where
  toFun := dualToCotangent (I := I)
  map_add' α β := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext X
    change (α + β) X = α X + β X
    rfl
  map_smul' c α := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext X
    change (c • α) X = c * α X
    rfl

@[simp] theorem dualToCotangentLinear_apply {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    dualToCotangentLinear (I := I) α = dualToCotangent (I := I) α := by
  rfl

noncomputable def basisInvMetric {Idx : Type*}
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) : Real :=
  basis.coord j ((tangentFlatEquiv (I := I) g x).symm (basis.coord i))

theorem basisInvMetric_symm {Idx : Type*}
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    forall i j : Idx,
      basisInvMetric (I := I) g x basis i j =
        basisInvMetric (I := I) g x basis j i := by
  intro i j
  let sharp := (tangentFlatEquiv (I := I) g x).symm
  have hleft :
      basis.coord j (sharp (basis.coord i)) =
        g.inner x (sharp (basis.coord j)) (sharp (basis.coord i)) := by
    change basis.coord j (sharp (basis.coord i)) =
      (tangentFlatEquiv (I := I) g x (sharp (basis.coord j)))
        (sharp (basis.coord i))
    rw [(tangentFlatEquiv (I := I) g x).apply_symm_apply]
  have hright :
      basis.coord i (sharp (basis.coord j)) =
        g.inner x (sharp (basis.coord i)) (sharp (basis.coord j)) := by
    change basis.coord i (sharp (basis.coord j)) =
      (tangentFlatEquiv (I := I) g x (sharp (basis.coord i)))
        (sharp (basis.coord j))
    rw [(tangentFlatEquiv (I := I) g x).apply_symm_apply]
  calc
    basisInvMetric (I := I) g x basis i j =
        g.inner x (sharp (basis.coord j)) (sharp (basis.coord i)) := by
          simpa [basisInvMetric, sharp] using hleft
    _ = g.inner x (sharp (basis.coord i)) (sharp (basis.coord j)) := by
          exact g.symm x _ _
    _ = basisInvMetric (I := I) g x basis j i := by
          simpa [basisInvMetric, sharp] using hright.symm

theorem basisInvMetric_isInverse {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    MetricInverseInBasis (I := I) g x basis
      (basisInvMetric (I := I) g x basis) := by
  classical
  let sharp := (tangentFlatEquiv (I := I) g x).symm
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
              (tangentFlatEquiv (I := I) g x (sharp (basis.coord i)))
                (basis j) =
              basis.coord i (basis j)
            rw [(tangentFlatEquiv (I := I) g x).apply_symm_apply]
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
theorem MetricInverseInBasis.unique {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv₁ gInv₂ : Idx → Idx → Real)
    (h₁ : MetricInverseInBasis (I := I) g x basis gInv₁)
    (h₂ : MetricInverseInBasis (I := I) g x basis gInv₂) :
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
theorem MetricInverseInBasis.symmetric {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
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
theorem coord_eq_sum_inverseMetric_mul_inner {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
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

theorem cotangentSharp_inner_eval
    (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharp (I := I) g x α) X =
      α (fun _ : Fin 1 => X) := by
  rw [cotangentSharp_inner, cotangentToDual_apply]

theorem cotangentSharp_dualToCotangent_tangentFlat
    (g : SmoothRiemannianMetric I M) (x : M) (X : TangentSpace I x) :
    cotangentSharp (I := I) g x
      (dualToCotangent (I := I) (tangentFlatLinear (I := I) g x X)) = X := by
  apply tangentFlatLinear_injective (I := I) g x
  ext Y
  simp [tangentFlatLinear_apply, cotangentSharp_inner]

theorem cotangentInner_dualToCotangent_tangentFlat
    (g : SmoothRiemannianMetric I M) (x : M) (X Y : TangentSpace I x) :
    cotangentInner (I := I) g x
      (dualToCotangent (I := I) (tangentFlatLinear (I := I) g x X))
      (dualToCotangent (I := I) (tangentFlatLinear (I := I) g x Y)) =
        g.inner x X Y := by
  rw [cotangentInner_eq_sharp,
    cotangentSharp_dualToCotangent_tangentFlat,
    cotangentSharp_dualToCotangent_tangentFlat]

end

end Tensor0SBundle
end DifferentialGeometry
