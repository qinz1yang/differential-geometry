import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen
import DifferentialGeometry.Geometry.Curvature.QuadraticContraction
import DifferentialGeometry.Geometry.Curvature.EuclideanQuadratic
import Mathlib.LinearAlgebra.Multilinear.Basis

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]


def curvatureQuadraticPairing (g : SmoothRiemannianMetric I M) (σ : Fin 8 ≃ Fin 8)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  metricTraceFirstTwoField (I := I) (M := M) (s := 4) g
    (metricTraceFirstTwoField (I := I) (M := M) (s := 6) g
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B)))

def curvatureQuadraticPairingPermutationZeroOneTwoThree : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![4, 0, 5, 2, 6, 1, 7, 3] (by decide)

def curvatureQuadraticPairingPermutationZeroOneThreeTwo : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![4, 0, 5, 2, 7, 1, 6, 3] (by decide)

def curvatureQuadraticPairingPermutationZeroTwoOneThree : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![4, 0, 6, 2, 5, 1, 7, 3] (by decide)

def curvatureQuadraticPairingPermutationZeroThreeOneTwo : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![4, 0, 7, 2, 5, 1, 6, 3] (by decide)


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_zero_one_two_three_component {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (m : Fin 4 → Idx) :
    component0S (I := I) basis (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneTwoThree A B x) m =
      ∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 1, f] *
            component0S (I := I) basis (B x) ![m 2, q, m 3, r] := by
  classical
  simp only [component0S_apply]
  unfold curvatureQuadraticPairing
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun r _ => ?_
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  change gInv f r * (gInv e q *
    Tensor0SSpace.eval
      ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
        curvatureQuadraticPairingPermutationZeroOneTwoThree)
      (metricTraceInput (I := I) (basis e) (basis q)
        (metricTraceInput (I := I) (basis f) (basis r)
          (fun p => basis (m p))))) =
      (gInv f r * gInv e q *
          Tensor0SSpace.eval (A x) (fun p => basis (![m 0, e, m 1, f] p))) *
        Tensor0SSpace.eval (B x) (fun p => basis (![m 2, q, m 3, r] p))
  have hroute :
      Tensor0SSpace.eval
          ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
            curvatureQuadraticPairingPermutationZeroOneTwoThree)
          (metricTraceInput (I := I) (basis e) (basis q)
            (metricTraceInput (I := I) (basis f) (basis r)
              (fun p => basis (m p)))) =
        Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x)
          (fun i =>
            metricTraceInput (I := I) (basis e) (basis q)
              (metricTraceInput (I := I) (basis f) (basis r)
                (fun p => basis (m p)))
              (curvatureQuadraticPairingPermutationZeroOneTwoThree i)) := by
    exact Tensor0SSpace.domDomCongr_apply (I := I)
      curvatureQuadraticPairingPermutationZeroOneTwoThree _ _
  rw [hroute, tensor0SField_product_eval]
  have hA :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroOneTwoThree i)) ∘ Fin.castAdd 4 =
        fun p => basis (![m 0, e, m 1, f] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroOneTwoThree, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hB :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroOneTwoThree i)) ∘ Fin.natAdd 4 =
        fun p => basis (![m 2, q, m 3, r] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroOneTwoThree, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hA, hB]
  ring


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_zero_one_three_two_component {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (m : Fin 4 → Idx) :
    component0S (I := I) basis (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneThreeTwo A B x) m =
      ∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 1, f] *
            component0S (I := I) basis (B x) ![m 3, q, m 2, r] := by
  classical
  simp only [component0S_apply]
  unfold curvatureQuadraticPairing
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun r _ => ?_
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  change gInv f r * (gInv e q *
    Tensor0SSpace.eval
      ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
        curvatureQuadraticPairingPermutationZeroOneThreeTwo)
      (metricTraceInput (I := I) (basis e) (basis q)
        (metricTraceInput (I := I) (basis f) (basis r)
          (fun p => basis (m p))))) =
      (gInv f r * gInv e q *
          Tensor0SSpace.eval (A x) (fun p => basis (![m 0, e, m 1, f] p))) *
        Tensor0SSpace.eval (B x) (fun p => basis (![m 3, q, m 2, r] p))
  have hroute :
      Tensor0SSpace.eval
          ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
            curvatureQuadraticPairingPermutationZeroOneThreeTwo)
          (metricTraceInput (I := I) (basis e) (basis q)
            (metricTraceInput (I := I) (basis f) (basis r)
              (fun p => basis (m p)))) =
        Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x)
          (fun i =>
            metricTraceInput (I := I) (basis e) (basis q)
              (metricTraceInput (I := I) (basis f) (basis r)
                (fun p => basis (m p)))
              (curvatureQuadraticPairingPermutationZeroOneThreeTwo i)) := by
    exact Tensor0SSpace.domDomCongr_apply (I := I)
      curvatureQuadraticPairingPermutationZeroOneThreeTwo _ _
  rw [hroute, tensor0SField_product_eval]
  have hA :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroOneThreeTwo i)) ∘ Fin.castAdd 4 =
        fun p => basis (![m 0, e, m 1, f] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroOneThreeTwo, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hB :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroOneThreeTwo i)) ∘ Fin.natAdd 4 =
        fun p => basis (![m 3, q, m 2, r] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroOneThreeTwo, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hA, hB]
  ring


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_zero_two_one_three_component {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (m : Fin 4 → Idx) :
    component0S (I := I) basis (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroTwoOneThree A B x) m =
      ∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 2, f] *
            component0S (I := I) basis (B x) ![m 1, q, m 3, r] := by
  classical
  simp only [component0S_apply]
  unfold curvatureQuadraticPairing
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun r _ => ?_
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  change gInv f r * (gInv e q *
    Tensor0SSpace.eval
      ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
        curvatureQuadraticPairingPermutationZeroTwoOneThree)
      (metricTraceInput (I := I) (basis e) (basis q)
        (metricTraceInput (I := I) (basis f) (basis r)
          (fun p => basis (m p))))) =
      (gInv f r * gInv e q *
          Tensor0SSpace.eval (A x) (fun p => basis (![m 0, e, m 2, f] p))) *
        Tensor0SSpace.eval (B x) (fun p => basis (![m 1, q, m 3, r] p))
  have hroute :
      Tensor0SSpace.eval
          ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
            curvatureQuadraticPairingPermutationZeroTwoOneThree)
          (metricTraceInput (I := I) (basis e) (basis q)
            (metricTraceInput (I := I) (basis f) (basis r)
              (fun p => basis (m p)))) =
        Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x)
          (fun i =>
            metricTraceInput (I := I) (basis e) (basis q)
              (metricTraceInput (I := I) (basis f) (basis r)
                (fun p => basis (m p)))
              (curvatureQuadraticPairingPermutationZeroTwoOneThree i)) := by
    exact Tensor0SSpace.domDomCongr_apply (I := I)
      curvatureQuadraticPairingPermutationZeroTwoOneThree _ _
  rw [hroute, tensor0SField_product_eval]
  have hA :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroTwoOneThree i)) ∘ Fin.castAdd 4 =
        fun p => basis (![m 0, e, m 2, f] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroTwoOneThree, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hB :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroTwoOneThree i)) ∘ Fin.natAdd 4 =
        fun p => basis (![m 1, q, m 3, r] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroTwoOneThree, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hA, hB]
  ring


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_zero_three_one_two_component {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (m : Fin 4 → Idx) :
    component0S (I := I) basis (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroThreeOneTwo A B x) m =
      ∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 3, f] *
            component0S (I := I) basis (B x) ![m 1, q, m 2, r] := by
  classical
  simp only [component0S_apply]
  unfold curvatureQuadraticPairing
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun r _ => ?_
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  change gInv f r * (gInv e q *
    Tensor0SSpace.eval
      ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
        curvatureQuadraticPairingPermutationZeroThreeOneTwo)
      (metricTraceInput (I := I) (basis e) (basis q)
        (metricTraceInput (I := I) (basis f) (basis r)
          (fun p => basis (m p))))) =
      (gInv f r * gInv e q *
          Tensor0SSpace.eval (A x) (fun p => basis (![m 0, e, m 3, f] p))) *
        Tensor0SSpace.eval (B x) (fun p => basis (![m 1, q, m 2, r] p))
  have hroute :
      Tensor0SSpace.eval
          ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr
            curvatureQuadraticPairingPermutationZeroThreeOneTwo)
          (metricTraceInput (I := I) (basis e) (basis q)
            (metricTraceInput (I := I) (basis f) (basis r)
              (fun p => basis (m p)))) =
        Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x)
          (fun i =>
            metricTraceInput (I := I) (basis e) (basis q)
              (metricTraceInput (I := I) (basis f) (basis r)
                (fun p => basis (m p)))
              (curvatureQuadraticPairingPermutationZeroThreeOneTwo i)) := by
    exact Tensor0SSpace.domDomCongr_apply (I := I)
      curvatureQuadraticPairingPermutationZeroThreeOneTwo _ _
  rw [hroute, tensor0SField_product_eval]
  have hA :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroThreeOneTwo i)) ∘ Fin.castAdd 4 =
        fun p => basis (![m 0, e, m 3, f] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroThreeOneTwo, Equiv.ofBijective, Fin.castAdd, Fin.castLE, metricTraceInput_apply]
  have hB :
      (fun i : Fin 8 =>
        metricTraceInput (I := I) (basis e) (basis q)
          (metricTraceInput (I := I) (basis f) (basis r) (fun p => basis (m p)))
          (curvatureQuadraticPairingPermutationZeroThreeOneTwo i)) ∘ Fin.natAdd 4 =
        fun p => basis (![m 1, q, m 2, r] p) := by
    funext p
    fin_cases p <;>
      simp [curvatureQuadraticPairingPermutationZeroThreeOneTwo, Equiv.ofBijective, Fin.natAdd, metricTraceInput_apply]
  rw [hA, hB]
  ring

def curvatureQuadraticCombination (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneTwoThree A A - curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneThreeTwo A A) +
    (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroTwoOneThree A A - curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroThreeOneTwo A A)


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticCombination_component {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (m : Fin 4 → Idx) :
    component0S (I := I) basis (curvatureQuadraticCombination (I := I) g A x) m =
      (∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 1, f] *
            component0S (I := I) basis (A x) ![m 2, q, m 3, r]) -
      (∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 1, f] *
            component0S (I := I) basis (A x) ![m 3, q, m 2, r]) +
      (∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 2, f] *
            component0S (I := I) basis (A x) ![m 1, q, m 3, r]) -
      (∑ f : Idx, ∑ r : Idx, ∑ e : Idx, ∑ q : Idx,
        gInv f r * gInv e q *
          component0S (I := I) basis (A x) ![m 0, e, m 3, f] *
            component0S (I := I) basis (A x) ![m 1, q, m 2, r]) := by
  have h1 := curvatureQuadraticPairing_zero_one_two_three_component (I := I) g basis gInv hinv A A m
  have h2 := curvatureQuadraticPairing_zero_one_three_two_component (I := I) g basis gInv hinv A A m
  have h3 := curvatureQuadraticPairing_zero_two_one_three_component (I := I) g basis gInv hinv A A m
  have h4 := curvatureQuadraticPairing_zero_three_one_two_component (I := I) g basis gInv hinv A A m
  change
    (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneTwoThree A A x) (fun p => basis (m p)) = _ at h1
  change
    (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneThreeTwo A A x) (fun p => basis (m p)) = _ at h2
  change
    (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroTwoOneThree A A x) (fun p => basis (m p)) = _ at h3
  change
    (curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroThreeOneTwo A A x) (fun p => basis (m p)) = _ at h4
  simp only [curvatureQuadraticCombination, component0S_apply, ContMDiffSection.coe_add,
    ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply,
    Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply]
  rw [h1, h2, h3, h4]
  simp only [component0S_apply]
  ring

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem curvatureQuadraticCombination_apply_isometry_basis
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (ι : F ≃L[ℝ] TangentSpace I x) (h : F →L[ℝ] F →L[ℝ] ℝ)
    (hι : ∀ v w, g.inner x (ι v) (ι w) = h v w)
    (b : Module.Basis Idx ℝ F) (hInv : Idx → Idx → ℝ)
    (hinv : ∀ i j,
      (∑ k, hInv i k * h (b k) (b j)) = (if i = j then 1 else 0) ∧
      (∑ k, h (b i) (b k) * hInv k j) = (if i = j then 1 else 0))
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4)
    (m : Fin 4 → Idx) :
    curvatureQuadraticCombination g A x (fun q => ι (b (m q))) =
      bComp hInv (fun a b' c d => A x (vec4 (ι (b a)) (ι (b b')) (ι (b c)) (ι (b d))))
          (m 0) (m 1) (m 2) (m 3) -
        bComp hInv (fun a b' c d => A x (vec4 (ι (b a)) (ι (b b')) (ι (b c)) (ι (b d))))
          (m 0) (m 1) (m 3) (m 2) +
        bComp hInv (fun a b' c d => A x (vec4 (ι (b a)) (ι (b b')) (ι (b c)) (ι (b d))))
          (m 0) (m 2) (m 1) (m 3) -
        bComp hInv (fun a b' c d => A x (vec4 (ι (b a)) (ι (b b')) (ι (b c)) (ι (b d))))
          (m 0) (m 3) (m 1) (m 2) := by
  let basis := b.map ι.toLinearEquiv
  have hb (a : Idx) : basis a = ι (b a) := rfl
  have hreal : MetricInverseInBasisGen (I := I) g x basis hInv := by
    intro i j
    change (∑ k, hInv i k * g.inner x (basis k) (basis j)) = _ ∧
      (∑ k, g.inner x (basis i) (basis k) * hInv k j) = _
    simpa only [hb, hι] using hinv i j
  let R := fun a b' c d => A x (vec4 (ι (b a)) (ι (b b')) (ι (b c)) (ι (b d)))
  have hRm (a b' c d : Idx) :
      component0S (I := I) basis (A x) ![a, b', c, d] = R a b' c d := by
    change A x _ = A x _
    congr 1
    funext q
    fin_cases q <;> rfl
  have hB (a b' c d : Idx) :
      bComp hInv R a b' c d =
        ∑ f, ∑ r, ∑ e, ∑ q, hInv f r * hInv e q * R a e b' f * R c q d r := by
    unfold bComp
    rw [DifferentialGeometry.Tensor.SlotAlgebra.sum_rotate4_two]
    refine Finset.sum_congr rfl fun f _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcomp := curvatureQuadraticCombination_component g basis hInv hreal A m
  simp only [hRm] at hcomp
  rw [← hB, ← hB, ← hB, ← hB] at hcomp
  exact hcomp

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open PDE.RicciFlow
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem curvatureQuadraticContraction_compContinuousLinearMap
    {Idx : Type*} [Fintype Idx] (b : OrthonormalBasis Idx ℝ F)
    (g : SmoothRiemannianMetric I M) (x : M)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hι : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4) :
    curvatureQuadraticContraction b
        ((A x).compContinuousLinearMap (fun _ => ι.toContinuousLinearMap)) =
      -((curvatureQuadraticPairing g curvatureQuadraticPairingPermutationZeroOneTwoThree A A x).compContinuousLinearMap
        (fun _ => ι.toContinuousLinearMap)) := by
  classical
  let basis := b.toBasis.map ι.toLinearEquiv
  let δ : Idx → Idx → ℝ := fun i j => if i = j then 1 else 0
  have hb (i : Idx) : basis i = ι (b i) := rfl
  have hinv : MetricInverseInBasisGen g x basis δ := by
    intro i j
    change (∑ k, δ i k * g.inner x (basis k) (basis j)) = _ ∧
      (∑ k, g.inner x (basis i) (basis k) * δ k j) = _
    simp only [hb, hι]
    simp [δ, b.inner_eq_ite]
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin 4 => b.toBasis)
  intro m
  change curvatureQuadraticContraction b _ (fun q => b (m q)) =
    -((curvatureQuadraticPairing g curvatureQuadraticPairingPermutationZeroOneTwoThree A A x).compContinuousLinearMap
      (fun _ => ι.toContinuousLinearMap)) (fun q => b (m q))
  have hvec : (fun q : Fin 4 => b (m q)) = ![b (m 0), b (m 1), b (m 2), b (m 3)] := by
    ext q
    fin_cases q <;> rfl
  rw [hvec, curvatureQuadraticContraction_apply]
  have hcomp := curvatureQuadraticPairing_zero_one_two_three_component
    g basis δ hinv A A m
  have heval (a c d e : F) :
      ((A x).compContinuousLinearMap (fun _ => ι.toContinuousLinearMap)) ![a, c, d, e] =
        A x ![ι a, ι c, ι d, ι e] := by
    change A x _ = _
    congr 1
    ext q
    fin_cases q <;> rfl
  simp only [heval]
  have hc : ∀ a c d e : Idx,
      component0S basis (A x) ![a, c, d, e] = A x ![ι (b a), ι (b c), ι (b d), ι (b e)] := by
    intro a c d e
    change A x _ = _
    congr 1
    ext q
    fin_cases q <;> rfl
  simp only [hc] at hcomp
  have hsum :
      (curvatureQuadraticPairing g curvatureQuadraticPairingPermutationZeroOneTwoThree A A x)
        (fun q => basis (m q)) =
      ∑ f, ∑ e, A x ![ι (b (m 0)), ι (b e), ι (b (m 1)), ι (b f)] *
        A x ![ι (b (m 2)), ι (b e), ι (b (m 3)), ι (b f)] := by
    simpa [δ] using hcomp
  change _ = -(curvatureQuadraticPairing g
    curvatureQuadraticPairingPermutationZeroOneTwoThree A A x)
      (fun q => ι (![b (m 0), b (m 1), b (m 2), b (m 3)] q))
  have harg : (fun q : Fin 4 => ι (![b (m 0), b (m 1), b (m 2), b (m 3)] q)) =
      fun q => basis (m q) := by
    ext q
    fin_cases q <;> rfl
  rw [harg, hsum]
  congr 1
  exact Finset.sum_comm

theorem curvatureQuadraticReactionTensor_compContinuousLinearMap
    (g : SmoothRiemannianMetric I M) (x : M)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hι : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4) :
    curvatureQuadraticReactionTensor
        ((A x).compContinuousLinearMap (fun _ => ι.toContinuousLinearMap)) =
      (-2 : ℝ) • (curvatureQuadraticCombination g A x).compContinuousLinearMap
        (fun _ => ι.toContinuousLinearMap) := by
  classical
  let b := stdOrthonormalBasis ℝ F
  let δ : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) → ℝ :=
    fun i j => if i = j then 1 else 0
  let T := (A x).compContinuousLinearMap (fun _ => ι.toContinuousLinearMap)
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin 4 => b.toBasis)
  intro m
  change curvatureQuadraticReactionTensor T (fun q => b (m q)) =
    (-2 : ℝ) * ((curvatureQuadraticCombination g A x).compContinuousLinearMap
      (fun _ => ι.toContinuousLinearMap)) (fun q => b (m q))
  have hvec : (fun q : Fin 4 => b (m q)) = ![b (m 0), b (m 1), b (m 2), b (m 3)] := by
    ext q
    fin_cases q <;> rfl
  rw [hvec, curvatureQuadraticReactionTensor_eq_of_orthonormalBasis b,
    curvatureQuadraticReaction_apply]
  have hinv : ∀ i j,
      (∑ k, δ i k * ⟪b k, b j⟫) = (if i = j then 1 else 0) ∧
      (∑ k, ⟪b i, b k⟫ * δ k j) = (if i = j then 1 else 0) := by
    intro i j
    simp [δ, b.inner_eq_ite]
  have hr := curvatureQuadraticCombination_apply_isometry_basis g x ι
    (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) hι b.toBasis δ hinv A m
  simp only [OrthonormalBasis.coe_toBasis] at hr
  have heval : ((curvatureQuadraticCombination g A x).compContinuousLinearMap
      (fun _ => ι.toContinuousLinearMap)) ![b (m 0), b (m 1), b (m 2), b (m 3)] =
      curvatureQuadraticCombination g A x (fun q => ι (b (m q))) := by
    change curvatureQuadraticCombination g A x _ = _
    congr 1
    ext q
    fin_cases q <;> rfl
  rw [heval, hr]
  have hB (a c d e : Fin (Module.finrank ℝ F)) :
      curvatureQuadraticContraction b T ![b a, b c, b d, b e] =
        -bComp δ (fun a c d e => A x (vec4 (ι (b a)) (ι (b c)) (ι (b d)) (ι (b e))))
          a c d e := by
    have heval (a c d e : F) : T ![a, c, d, e] = A x (vec4 (ι a) (ι c) (ι d) (ι e)) := by
      change A x _ = A x _
      congr 1
      ext q
      fin_cases q <;> rfl
    simp [curvatureQuadraticContraction_apply, bComp, δ, heval]
  dsimp only
  rw [hB, hB, hB, hB]
  ring

end DifferentialGeometry.Geometry.Curvature
