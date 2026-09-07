import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen

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
