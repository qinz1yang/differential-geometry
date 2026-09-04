import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Remainder
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
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
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
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
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
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
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
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
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
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
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
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

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem quad_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData.inner_eq
    (tangentMetricData (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem routeProdSq (g : SmoothRiemannianMetric I M) (σ : Fin 8 ≃ Fin 8)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    normSq0S (I := I) g x 8
        ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr σ) =
      normSq0S (I := I) g x 4 (A x) * normSq0S (I := I) g x 4 (B x) := by
  classical
  obtain ⟨basis, hON⟩ := quad_onFrame (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
  rw [Tensor0SBundle.normSq0S_domDomCongr (I := I) g x basis hinv σ]
  exact normSq0S_product (I := I) g x basis hinv A B

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_norm_sq_le (g : SmoothRiemannianMetric I M) (σ : Fin 8 ≃ Fin 8)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    normSq0S (I := I) g x 4 (curvatureQuadraticPairing (I := I) g σ A B x) ≤
      (Module.finrank Real E : Real) ^ 14 *
        (normSq0S (I := I) g x 4 (A x) * normSq0S (I := I) g x 4 (B x)) := by
  let X : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8 :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B)
  let W : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
    metricTraceFirstTwoField (I := I) (M := M) (s := 6) g X
  have houter := traceNormSq_le (I := I) (s := 4) g x (W x)
  have hinner0 := traceNormSq_le (I := I) (s := 6) g x (X x)
  have hX :
      normSq0S (I := I) g x 8 (X x) =
        normSq0S (I := I) g x 4 (A x) * normSq0S (I := I) g x 4 (B x) := by
    have hXx :
        X x = (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr σ := by
      dsimp only [X]
      exact Tensor0SField.domDomCongr_apply (∞ : WithTop ℕ∞) σ _ x
    rw [hXx]
    exact routeProdSq (I := I) g σ A B x
  have hinner :
      normSq0S (I := I) g x 6 (W x) ≤
        (Module.finrank Real E : Real) ^ 8 *
          (normSq0S (I := I) g x 4 (A x) *
            normSq0S (I := I) g x 4 (B x)) := by
    change
      normSq0S (I := I) g x 6
          (metricTraceFirstTwo0STensor (I := I) g (X x)) ≤ _ at hinner0
    change normSq0S (I := I) g x 6 (W x) ≤ _ at hinner0
    rw [hX] at hinner0
    exact hinner0
  change normSq0S (I := I) g x 4
      (metricTraceFirstTwo0STensor (I := I) g (W x)) ≤ _
  calc
    normSq0S (I := I) g x 4
        (metricTraceFirstTwo0STensor (I := I) g (W x))
        ≤ (Module.finrank Real E : Real) ^ 6 *
            normSq0S (I := I) g x 6 (W x) := houter
    _ ≤ (Module.finrank Real E : Real) ^ 6 *
          ((Module.finrank Real E : Real) ^ 8 *
            (normSq0S (I := I) g x 4 (A x) *
              normSq0S (I := I) g x 4 (B x))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (Module.finrank Real E : Real) ^ 14 *
          (normSq0S (I := I) g x 4 (A x) *
            normSq0S (I := I) g x 4 (B x)) := by ring


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticCombination_norm_sq_le (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    normSq0S (I := I) g x 4 (curvatureQuadraticCombination (I := I) g A x) ≤
      16 * (Module.finrank Real E : Real) ^ 14 *
        normSq0S (I := I) g x 4 (A x) ^ 2 := by
  let P1 := curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneTwoThree A A x
  let P2 := curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroOneThreeTwo A A x
  let P3 := curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroTwoOneThree A A x
  let P4 := curvatureQuadraticPairing (I := I) g curvatureQuadraticPairingPermutationZeroThreeOneTwo A A x
  let K : Real :=
    (Module.finrank Real E : Real) ^ 14 *
      normSq0S (I := I) g x 4 (A x) ^ 2
  have h1 : normSq0S (I := I) g x 4 P1 ≤ K := by
    simpa only [P1, K, pow_two] using
      curvatureQuadraticPairing_norm_sq_le (I := I) g curvatureQuadraticPairingPermutationZeroOneTwoThree A A x
  have h2 : normSq0S (I := I) g x 4 P2 ≤ K := by
    simpa only [P2, K, pow_two] using
      curvatureQuadraticPairing_norm_sq_le (I := I) g curvatureQuadraticPairingPermutationZeroOneThreeTwo A A x
  have h3 : normSq0S (I := I) g x 4 P3 ≤ K := by
    simpa only [P3, K, pow_two] using
      curvatureQuadraticPairing_norm_sq_le (I := I) g curvatureQuadraticPairingPermutationZeroTwoOneThree A A x
  have h4 : normSq0S (I := I) g x 4 P4 ≤ K := by
    simpa only [P4, K, pow_two] using
      curvatureQuadraticPairing_norm_sq_le (I := I) g curvatureQuadraticPairingPermutationZeroThreeOneTwo A A x
  have h12 : normSq0S (I := I) g x 4 (P1 - P2) ≤ 4 * K := by
    calc
      normSq0S (I := I) g x 4 (P1 - P2)
          ≤ 2 * normSq0S (I := I) g x 4 P1 +
              2 * normSq0S (I := I) g x 4 P2 :=
        normSq0S_sub_le (I := I) g x 4 P1 P2
      _ ≤ 2 * K + 2 * K :=
        add_le_add
          (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * K := by ring
  have h34 : normSq0S (I := I) g x 4 (P3 - P4) ≤ 4 * K := by
    calc
      normSq0S (I := I) g x 4 (P3 - P4)
          ≤ 2 * normSq0S (I := I) g x 4 P3 +
              2 * normSq0S (I := I) g x 4 P4 :=
        normSq0S_sub_le (I := I) g x 4 P3 P4
      _ ≤ 2 * K + 2 * K :=
        add_le_add
          (mul_le_mul_of_nonneg_left h3 (by norm_num))
          (mul_le_mul_of_nonneg_left h4 (by norm_num))
      _ = 4 * K := by ring
  have hsplit :
      curvatureQuadraticCombination (I := I) g A x = (P1 - P2) + (P3 - P4) := by
    simp only [curvatureQuadraticCombination, P1, P2, P3, P4, ContMDiffSection.coe_sub,
      ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
  rw [hsplit]
  calc
    normSq0S (I := I) g x 4 ((P1 - P2) + (P3 - P4))
        ≤ 2 * normSq0S (I := I) g x 4 (P1 - P2) +
            2 * normSq0S (I := I) g x 4 (P3 - P4) :=
      normSq0S_add_le (I := I) g x 4 (P1 - P2) (P3 - P4)
    _ ≤ 2 * (4 * K) + 2 * (4 * K) :=
      add_le_add
        (mul_le_mul_of_nonneg_left h12 (by norm_num))
        (mul_le_mul_of_nonneg_left h34 (by norm_num))
    _ = 16 * K := by ring
    _ = _ := by
      dsimp only [K]
      ring


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_sub (g : SmoothRiemannianMetric I M) (σ : Fin 8 ≃ Fin 8)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    curvatureQuadraticPairing (I := I) g σ A A - curvatureQuadraticPairing (I := I) g σ B B =
      curvatureQuadraticPairing (I := I) g σ (A - B) A + curvatureQuadraticPairing (I := I) g σ B (A - B) := by
  have hroute :
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A A) -
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) B B) =
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) (A - B) A) +
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) B (A - B)) := by
    refine DFunLike.ext _ _ fun y => ?_
    refine tensor0SSpace_ext (𝕜 := Real) 8 y fun V => ?_
    change Tensor0SSpace.eval
        ((Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
            (tensor0SFieldProduct (∞ : WithTop ℕ∞) A A) -
          Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
            (tensor0SFieldProduct (∞ : WithTop ℕ∞) B B)) y) V =
      Tensor0SSpace.eval
        ((Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
            (tensor0SFieldProduct (∞ : WithTop ℕ∞) (A - B) A) +
          Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
            (tensor0SFieldProduct (∞ : WithTop ℕ∞) B (A - B))) y) V
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.eval_sub,
      ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.eval_add,
      Tensor0SField.domDomCongr_apply]
    have hAA :
        Tensor0SSpace.eval
            ((tensor0SFieldProduct (∞ : WithTop ℕ∞) A A y).domDomCongr σ) V =
          Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) A A y)
            (fun i => V (σ i)) := by
      exact Tensor0SSpace.domDomCongr_apply (I := I) σ _ V
    have hBB :
        Tensor0SSpace.eval
            ((tensor0SFieldProduct (∞ : WithTop ℕ∞) B B y).domDomCongr σ) V =
          Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) B B y)
            (fun i => V (σ i)) := by
      exact Tensor0SSpace.domDomCongr_apply (I := I) σ _ V
    have hDA :
        Tensor0SSpace.eval
            ((tensor0SFieldProduct (∞ : WithTop ℕ∞) (A - B) A y).domDomCongr σ) V =
          Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) (A - B) A y)
            (fun i => V (σ i)) := by
      exact Tensor0SSpace.domDomCongr_apply (I := I) σ _ V
    have hBD :
        Tensor0SSpace.eval
            ((tensor0SFieldProduct (∞ : WithTop ℕ∞) B (A - B) y).domDomCongr σ) V =
          Tensor0SSpace.eval (tensor0SFieldProduct (∞ : WithTop ℕ∞) B (A - B) y)
            (fun i => V (σ i)) := by
      exact Tensor0SSpace.domDomCongr_apply (I := I) σ _ V
    rw [hAA, hBB, hDA, hBD]
    rw [tensor0SField_product_eval, tensor0SField_product_eval,
      tensor0SField_product_eval, tensor0SField_product_eval]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.eval_sub]
    ring
  unfold curvatureQuadraticPairing
  rw [← traceFirstTwo_sub (I := I) (M := M) (s := 4) g]
  rw [← traceFirstTwo_sub (I := I) (M := M) (s := 6) g]
  rw [hroute]
  rw [metricTraceFirstTwoField_add (I := I) (M := M) (s := 6) g]
  rw [metricTraceFirstTwoField_add (I := I) (M := M) (s := 4) g]


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_metric_difference_norm_sq_le (g₁ g₂ : SmoothRiemannianMetric I M) (σ : Fin 8 ≃ Fin 8)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {Λ BH : Real} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hH : metricDiffSq (I := I) g₁ g₂ x ≤ BH) :
    normSq0S (I := I) g₁ x 4
        (curvatureQuadraticPairing (I := I) g₁ σ A B x - curvatureQuadraticPairing (I := I) g₂ σ A B x) ≤
      (6 * (Module.finrank Real E : Real) ^ 18 * Λ ^ 2 +
          4 * (Module.finrank Real E : Real) ^ 22 * Λ ^ 4 * BH) *
        metricDiffSq (I := I) g₁ g₂ x *
          (normSq0S (I := I) g₁ x 4 (A x) *
            normSq0S (I := I) g₁ x 4 (B x)) := by
  let X : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 8 :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) σ
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B)
  let Y1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
    metricTraceFirstTwoField (I := I) (M := M) (s := 6) g₁ X
  let Y2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
    metricTraceFirstTwoField (I := I) (M := M) (s := 6) g₂ X
  let Z1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
    metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁ (Y1 - Y2)
  let Z2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
    metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁ Y2 -
      metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₂ Y2
  set nR : Real := (Module.finrank Real E : Real) with hnR
  set H0 : Real := metricDiffSq (I := I) g₁ g₂ x with hH0
  set NA : Real := normSq0S (I := I) g₁ x 4 (A x) with hNA
  set NB : Real := normSq0S (I := I) g₁ x 4 (B x) with hNB
  have hH0nn : 0 ≤ H0 := by
    rw [hH0, metricDiffSq_def]
    exact normSq0S_nonneg (I := I) g₁ x 2 _
  have hNAnn : 0 ≤ NA := by
    rw [hNA]
    exact normSq0S_nonneg (I := I) g₁ x 4 _
  have hNBnn : 0 ≤ NB := by
    rw [hNB]
    exact normSq0S_nonneg (I := I) g₁ x 4 _
  have hX :
      normSq0S (I := I) g₁ x 8 (X x) = NA * NB := by
    rw [hNA, hNB]
    have hXx :
        X x = (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x).domDomCongr σ := by
      dsimp only [X]
      exact Tensor0SField.domDomCongr_apply (∞ : WithTop ℕ∞) σ _ x
    rw [hXx]
    exact routeProdSq (I := I) g₁ σ A B x
  have hYD :
      normSq0S (I := I) g₁ x 6 (Y1 x - Y2 x) ≤
        nR ^ 12 * Λ ^ 2 * H0 * (NA * NB) := by
    have h := traceDiffNormSq_le (I := I) g₁ g₂ x (s := 6) hΛ0 hΛ (X x)
    change
      normSq0S (I := I) g₁ x 6
          (metricTraceFirstTwo0STensor (I := I) g₁ (X x) -
            metricTraceFirstTwo0STensor (I := I) g₂ (X x)) ≤ _ at h
    change
      normSq0S (I := I) g₁ x 6 (Y1 x - Y2 x) ≤ _ at h
    rw [← hnR, ← hH0, hX] at h
    exact h
  have hY1 :
      normSq0S (I := I) g₁ x 6 (Y1 x) ≤ nR ^ 8 * (NA * NB) := by
    have h := traceNormSq_le (I := I) (s := 6) g₁ x (X x)
    change normSq0S (I := I) g₁ x 6 (Y1 x) ≤ _ at h
    rw [← hnR, hX] at h
    exact h
  have hY2 :
      normSq0S (I := I) g₁ x 6 (Y2 x) ≤
        2 * nR ^ 8 * (NA * NB) +
          2 * nR ^ 12 * Λ ^ 2 * H0 * (NA * NB) := by
    have hsub := normSq0S_sub_le (I := I) g₁ x 6 (Y1 x) (Y1 x - Y2 x)
    have heq : Y1 x - (Y1 x - Y2 x) = Y2 x := by abel
    rw [heq] at hsub
    calc
      normSq0S (I := I) g₁ x 6 (Y2 x)
          ≤ 2 * normSq0S (I := I) g₁ x 6 (Y1 x) +
              2 * normSq0S (I := I) g₁ x 6 (Y1 x - Y2 x) := hsub
      _ ≤ 2 * (nR ^ 8 * (NA * NB)) +
            2 * (nR ^ 12 * Λ ^ 2 * H0 * (NA * NB)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hY1 (by norm_num))
          (mul_le_mul_of_nonneg_left hYD (by norm_num))
      _ = 2 * nR ^ 8 * (NA * NB) +
            2 * nR ^ 12 * Λ ^ 2 * H0 * (NA * NB) := by ring
  have hZ1 :
      normSq0S (I := I) g₁ x 4 (Z1 x) ≤
        nR ^ 18 * Λ ^ 2 * H0 * (NA * NB) := by
    have h := traceNormSq_le (I := I) (s := 4) g₁ x ((Y1 - Y2) x)
    rw [ContMDiffSection.coe_sub, Pi.sub_apply] at h
    change normSq0S (I := I) g₁ x 4 (Z1 x) ≤
      (Module.finrank Real E : Real) ^ 6 *
        normSq0S (I := I) g₁ x 6 (Y1 x - Y2 x) at h
    calc
      normSq0S (I := I) g₁ x 4 (Z1 x)
          ≤ nR ^ 6 * normSq0S (I := I) g₁ x 6 (Y1 x - Y2 x) := by
            simpa only [hnR] using h
      _ ≤ nR ^ 6 * (nR ^ 12 * Λ ^ 2 * H0 * (NA * NB)) :=
        mul_le_mul_of_nonneg_left hYD (by positivity)
      _ = nR ^ 18 * Λ ^ 2 * H0 * (NA * NB) := by ring
  have hZ2 :
      normSq0S (I := I) g₁ x 4 (Z2 x) ≤
        2 * nR ^ 18 * Λ ^ 2 * H0 * (NA * NB) +
          2 * nR ^ 22 * Λ ^ 4 * H0 ^ 2 * (NA * NB) := by
    have h := traceDiffNormSq_le (I := I) g₁ g₂ x (s := 4) hΛ0 hΛ (Y2 x)
    change normSq0S (I := I) g₁ x 4 (Z2 x) ≤
      (Module.finrank Real E : Real) ^ 10 * Λ ^ 2 *
        metricDiffSq (I := I) g₁ g₂ x *
          normSq0S (I := I) g₁ x 6 (Y2 x) at h
    calc
      normSq0S (I := I) g₁ x 4 (Z2 x)
          ≤ nR ^ 10 * Λ ^ 2 * H0 *
              normSq0S (I := I) g₁ x 6 (Y2 x) := by
            simpa only [hnR, hH0] using h
      _ ≤ nR ^ 10 * Λ ^ 2 * H0 *
          (2 * nR ^ 8 * (NA * NB) +
            2 * nR ^ 12 * Λ ^ 2 * H0 * (NA * NB)) :=
        mul_le_mul_of_nonneg_left hY2 (by positivity)
      _ = 2 * nR ^ 18 * Λ ^ 2 * H0 * (NA * NB) +
            2 * nR ^ 22 * Λ ^ 4 * H0 ^ 2 * (NA * NB) := by ring
  have hsplit :
      curvatureQuadraticPairing (I := I) g₁ σ A B - curvatureQuadraticPairing (I := I) g₂ σ A B = Z1 + Z2 := by
    change
      metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁ Y1 -
          metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₂ Y2 =
        Z1 + Z2
    rw [show Z1 =
        metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁ Y1 -
          metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁ Y2 by
      exact traceFirstTwo_sub (I := I) (M := M) (s := 4) g₁ Y1 Y2]
    dsimp only [Z2]
    abel
  have hsplitx :
      curvatureQuadraticPairing (I := I) g₁ σ A B x - curvatureQuadraticPairing (I := I) g₂ σ A B x =
        Z1 x + Z2 x := by
    simpa only [ContMDiffSection.coe_sub, ContMDiffSection.coe_add,
      Pi.sub_apply, Pi.add_apply] using DFunLike.congr_fun hsplit x
  have hadd := normSq0S_add_le (I := I) g₁ x 4 (Z1 x) (Z2 x)
  have hHsq : H0 ^ 2 ≤ BH * H0 := by
    have hm := mul_le_mul_of_nonneg_right hH hH0nn
    simpa only [hH0, pow_two] using hm
  have hN : 0 ≤ NA * NB := mul_nonneg hNAnn hNBnn
  rw [hsplitx]
  calc
    normSq0S (I := I) g₁ x 4 (Z1 x + Z2 x)
        ≤ 2 * normSq0S (I := I) g₁ x 4 (Z1 x) +
            2 * normSq0S (I := I) g₁ x 4 (Z2 x) := hadd
    _ ≤ 2 * (nR ^ 18 * Λ ^ 2 * H0 * (NA * NB)) +
          2 * (2 * nR ^ 18 * Λ ^ 2 * H0 * (NA * NB) +
            2 * nR ^ 22 * Λ ^ 4 * H0 ^ 2 * (NA * NB)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hZ1 (by norm_num))
        (mul_le_mul_of_nonneg_left hZ2 (by norm_num))
    _ = 6 * nR ^ 18 * Λ ^ 2 * H0 * (NA * NB) +
          4 * nR ^ 22 * Λ ^ 4 * H0 ^ 2 * (NA * NB) := by ring
    _ ≤ 6 * nR ^ 18 * Λ ^ 2 * H0 * (NA * NB) +
          4 * nR ^ 22 * Λ ^ 4 * (BH * H0) * (NA * NB) := by
      have hlast :
          4 * nR ^ 22 * Λ ^ 4 * H0 ^ 2 * (NA * NB) ≤
            4 * nR ^ 22 * Λ ^ 4 * (BH * H0) * (NA * NB) := by
        calc
          4 * nR ^ 22 * Λ ^ 4 * H0 ^ 2 * (NA * NB)
              = (4 * nR ^ 22 * Λ ^ 4 * (NA * NB)) * H0 ^ 2 := by ring
          _ ≤ (4 * nR ^ 22 * Λ ^ 4 * (NA * NB)) * (BH * H0) :=
            mul_le_mul_of_nonneg_left hHsq
              (mul_nonneg (by positivity) hN)
          _ = 4 * nR ^ 22 * Λ ^ 4 * (BH * H0) * (NA * NB) := by ring
      exact add_le_add (le_refl _) hlast
    _ = (6 * nR ^ 18 * Λ ^ 2 + 4 * nR ^ 22 * Λ ^ 4 * BH) *
          H0 * (NA * NB) := by ring
    _ = _ := by rw [hnR, hH0, hNA, hNB]


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticPairing_difference_norm_sq_le (g₁ g₂ : SmoothRiemannianMetric I M) (σ : Fin 8 ≃ Fin 8)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {Λ BH : Real} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hH : metricDiffSq (I := I) g₁ g₂ x ≤ BH) :
    normSq0S (I := I) g₁ x 4
        (curvatureQuadraticPairing (I := I) g₁ σ A A x - curvatureQuadraticPairing (I := I) g₂ σ B B x) ≤
      4 * (Module.finrank Real E : Real) ^ 14 *
          normSq0S (I := I) g₁ x 4 (A x - B x) *
            (normSq0S (I := I) g₁ x 4 (A x) +
              normSq0S (I := I) g₁ x 4 (B x)) +
        2 * (6 * (Module.finrank Real E : Real) ^ 18 * Λ ^ 2 +
            4 * (Module.finrank Real E : Real) ^ 22 * Λ ^ 4 * BH) *
          metricDiffSq (I := I) g₁ g₂ x *
            normSq0S (I := I) g₁ x 4 (B x) ^ 2 := by
  let D : Real := normSq0S (I := I) g₁ x 4 (A x - B x)
  let NA : Real := normSq0S (I := I) g₁ x 4 (A x)
  let NB : Real := normSq0S (I := I) g₁ x 4 (B x)
  let C : Real :=
    6 * (Module.finrank Real E : Real) ^ 18 * Λ ^ 2 +
      4 * (Module.finrank Real E : Real) ^ 22 * Λ ^ 4 * BH
  have hpol :
      curvatureQuadraticPairing (I := I) g₁ σ A A x - curvatureQuadraticPairing (I := I) g₁ σ B B x =
        curvatureQuadraticPairing (I := I) g₁ σ (A - B) A x +
          curvatureQuadraticPairing (I := I) g₁ σ B (A - B) x := by
    simpa only [ContMDiffSection.coe_sub, ContMDiffSection.coe_add,
      Pi.sub_apply, Pi.add_apply] using
        DFunLike.congr_fun (curvatureQuadraticPairing_sub (I := I) g₁ σ A B) x
  have hPA := curvatureQuadraticPairing_norm_sq_le (I := I) g₁ σ (A - B) A x
  have hPB := curvatureQuadraticPairing_norm_sq_le (I := I) g₁ σ B (A - B) x
  have hfixed :
      normSq0S (I := I) g₁ x 4
          (curvatureQuadraticPairing (I := I) g₁ σ A A x - curvatureQuadraticPairing (I := I) g₁ σ B B x) ≤
        2 * (Module.finrank Real E : Real) ^ 14 * D * (NA + NB) := by
    rw [hpol]
    refine (normSq0S_add_le (I := I) g₁ x 4 _ _).trans ?_
    change
      2 * normSq0S (I := I) g₁ x 4 (curvatureQuadraticPairing (I := I) g₁ σ (A - B) A x) +
          2 * normSq0S (I := I) g₁ x 4 (curvatureQuadraticPairing (I := I) g₁ σ B (A - B) x) ≤ _
    have hPA' :
        normSq0S (I := I) g₁ x 4 (curvatureQuadraticPairing (I := I) g₁ σ (A - B) A x) ≤
          (Module.finrank Real E : Real) ^ 14 * (D * NA) := by
      simpa only [D, NA, ContMDiffSection.coe_sub, Pi.sub_apply] using hPA
    have hPB' :
        normSq0S (I := I) g₁ x 4 (curvatureQuadraticPairing (I := I) g₁ σ B (A - B) x) ≤
          (Module.finrank Real E : Real) ^ 14 * (NB * D) := by
      simpa only [D, NB, ContMDiffSection.coe_sub, Pi.sub_apply] using hPB
    calc
      2 * normSq0S (I := I) g₁ x 4 (curvatureQuadraticPairing (I := I) g₁ σ (A - B) A x) +
          2 * normSq0S (I := I) g₁ x 4 (curvatureQuadraticPairing (I := I) g₁ σ B (A - B) x)
          ≤ 2 * ((Module.finrank Real E : Real) ^ 14 * (D * NA)) +
              2 * ((Module.finrank Real E : Real) ^ 14 * (NB * D)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hPA' (by norm_num))
          (mul_le_mul_of_nonneg_left hPB' (by norm_num))
      _ = 2 * (Module.finrank Real E : Real) ^ 14 * D * (NA + NB) := by ring
  have hmetric :
      normSq0S (I := I) g₁ x 4
          (curvatureQuadraticPairing (I := I) g₁ σ B B x - curvatureQuadraticPairing (I := I) g₂ σ B B x) ≤
        C * metricDiffSq (I := I) g₁ g₂ x * NB ^ 2 := by
    have h := curvatureQuadraticPairing_metric_difference_norm_sq_le (I := I) g₁ g₂ σ B B x hΛ0 hΛ hH
    simpa only [C, NB, pow_two] using h
  have hsplit :
      curvatureQuadraticPairing (I := I) g₁ σ A A x - curvatureQuadraticPairing (I := I) g₂ σ B B x =
        (curvatureQuadraticPairing (I := I) g₁ σ A A x - curvatureQuadraticPairing (I := I) g₁ σ B B x) +
          (curvatureQuadraticPairing (I := I) g₁ σ B B x - curvatureQuadraticPairing (I := I) g₂ σ B B x) := by
    abel
  rw [hsplit]
  refine (normSq0S_add_le (I := I) g₁ x 4 _ _).trans ?_
  calc
    2 * normSq0S (I := I) g₁ x 4
          (curvatureQuadraticPairing (I := I) g₁ σ A A x - curvatureQuadraticPairing (I := I) g₁ σ B B x) +
        2 * normSq0S (I := I) g₁ x 4
          (curvatureQuadraticPairing (I := I) g₁ σ B B x - curvatureQuadraticPairing (I := I) g₂ σ B B x)
        ≤ 2 * (2 * (Module.finrank Real E : Real) ^ 14 * D * (NA + NB)) +
            2 * (C * metricDiffSq (I := I) g₁ g₂ x * NB ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hfixed (by norm_num))
        (mul_le_mul_of_nonneg_left hmetric (by norm_num))
    _ = _ := by
      dsimp only [C, D, NA, NB]
      ring


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem curvatureQuadraticCombination_difference_norm_sq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {Λ BH : Real} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hH : metricDiffSq (I := I) g₁ g₂ x ≤ BH) :
    normSq0S (I := I) g₁ x 4
        (curvatureQuadraticCombination (I := I) g₁ A x - curvatureQuadraticCombination (I := I) g₂ B x) ≤
      16 * (4 * (Module.finrank Real E : Real) ^ 14 *
          normSq0S (I := I) g₁ x 4 (A x - B x) *
            (normSq0S (I := I) g₁ x 4 (A x) +
              normSq0S (I := I) g₁ x 4 (B x)) +
        2 * (6 * (Module.finrank Real E : Real) ^ 18 * Λ ^ 2 +
            4 * (Module.finrank Real E : Real) ^ 22 * Λ ^ 4 * BH) *
          metricDiffSq (I := I) g₁ g₂ x *
            normSq0S (I := I) g₁ x 4 (B x) ^ 2) := by
  let D1 :=
    curvatureQuadraticPairing (I := I) g₁ curvatureQuadraticPairingPermutationZeroOneTwoThree A A x - curvatureQuadraticPairing (I := I) g₂ curvatureQuadraticPairingPermutationZeroOneTwoThree B B x
  let D2 :=
    curvatureQuadraticPairing (I := I) g₁ curvatureQuadraticPairingPermutationZeroOneThreeTwo A A x - curvatureQuadraticPairing (I := I) g₂ curvatureQuadraticPairingPermutationZeroOneThreeTwo B B x
  let D3 :=
    curvatureQuadraticPairing (I := I) g₁ curvatureQuadraticPairingPermutationZeroTwoOneThree A A x - curvatureQuadraticPairing (I := I) g₂ curvatureQuadraticPairingPermutationZeroTwoOneThree B B x
  let D4 :=
    curvatureQuadraticPairing (I := I) g₁ curvatureQuadraticPairingPermutationZeroThreeOneTwo A A x - curvatureQuadraticPairing (I := I) g₂ curvatureQuadraticPairingPermutationZeroThreeOneTwo B B x
  let K : Real :=
    4 * (Module.finrank Real E : Real) ^ 14 *
        normSq0S (I := I) g₁ x 4 (A x - B x) *
          (normSq0S (I := I) g₁ x 4 (A x) +
            normSq0S (I := I) g₁ x 4 (B x)) +
      2 * (6 * (Module.finrank Real E : Real) ^ 18 * Λ ^ 2 +
          4 * (Module.finrank Real E : Real) ^ 22 * Λ ^ 4 * BH) *
        metricDiffSq (I := I) g₁ g₂ x *
          normSq0S (I := I) g₁ x 4 (B x) ^ 2
  have h1 : normSq0S (I := I) g₁ x 4 D1 ≤ K := by
    simpa only [D1, K] using
      curvatureQuadraticPairing_difference_norm_sq_le (I := I) g₁ g₂ curvatureQuadraticPairingPermutationZeroOneTwoThree A B x hΛ0 hΛ hH
  have h2 : normSq0S (I := I) g₁ x 4 D2 ≤ K := by
    simpa only [D2, K] using
      curvatureQuadraticPairing_difference_norm_sq_le (I := I) g₁ g₂ curvatureQuadraticPairingPermutationZeroOneThreeTwo A B x hΛ0 hΛ hH
  have h3 : normSq0S (I := I) g₁ x 4 D3 ≤ K := by
    simpa only [D3, K] using
      curvatureQuadraticPairing_difference_norm_sq_le (I := I) g₁ g₂ curvatureQuadraticPairingPermutationZeroTwoOneThree A B x hΛ0 hΛ hH
  have h4 : normSq0S (I := I) g₁ x 4 D4 ≤ K := by
    simpa only [D4, K] using
      curvatureQuadraticPairing_difference_norm_sq_le (I := I) g₁ g₂ curvatureQuadraticPairingPermutationZeroThreeOneTwo A B x hΛ0 hΛ hH
  have h12 : normSq0S (I := I) g₁ x 4 (D1 - D2) ≤ 4 * K := by
    calc
      normSq0S (I := I) g₁ x 4 (D1 - D2)
          ≤ 2 * normSq0S (I := I) g₁ x 4 D1 +
              2 * normSq0S (I := I) g₁ x 4 D2 :=
        normSq0S_sub_le (I := I) g₁ x 4 D1 D2
      _ ≤ 2 * K + 2 * K :=
        add_le_add
          (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * K := by ring
  have h34 : normSq0S (I := I) g₁ x 4 (D3 - D4) ≤ 4 * K := by
    calc
      normSq0S (I := I) g₁ x 4 (D3 - D4)
          ≤ 2 * normSq0S (I := I) g₁ x 4 D3 +
              2 * normSq0S (I := I) g₁ x 4 D4 :=
        normSq0S_sub_le (I := I) g₁ x 4 D3 D4
      _ ≤ 2 * K + 2 * K :=
        add_le_add
          (mul_le_mul_of_nonneg_left h3 (by norm_num))
          (mul_le_mul_of_nonneg_left h4 (by norm_num))
      _ = 4 * K := by ring
  have hsplit :
      curvatureQuadraticCombination (I := I) g₁ A x - curvatureQuadraticCombination (I := I) g₂ B x =
        (D1 - D2) + (D3 - D4) := by
    simp only [curvatureQuadraticCombination, D1, D2, D3, D4, ContMDiffSection.coe_sub,
      ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
    abel
  rw [hsplit]
  calc
    normSq0S (I := I) g₁ x 4 ((D1 - D2) + (D3 - D4))
        ≤ 2 * normSq0S (I := I) g₁ x 4 (D1 - D2) +
            2 * normSq0S (I := I) g₁ x 4 (D3 - D4) :=
      normSq0S_add_le (I := I) g₁ x 4 (D1 - D2) (D3 - D4)
    _ ≤ 2 * (4 * K) + 2 * (4 * K) :=
      add_le_add
        (mul_le_mul_of_nonneg_left h12 (by norm_num))
        (mul_le_mul_of_nonneg_left h34 (by norm_num))
    _ = 16 * K := by ring
    _ = _ := by rfl

end DifferentialGeometry.PDE.RicciFlow
