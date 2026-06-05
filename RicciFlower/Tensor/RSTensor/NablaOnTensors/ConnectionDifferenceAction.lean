import RicciFlower.Tensor.RSTensor.TensorRSRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Connection-Difference Action On Mixed Tensor Components

This file contains the finite-dimensional component estimate used in MSM135
Chapter 4, Lemma "Norms of covariant derivatives of tensors, I".  The
geometric connection-change identity is proved elsewhere; here we only record
the algebraic action of a `(1,2)` connection-difference tensor on the upper and
lower slots of an `(r,s)` tensor.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]

/-- Tail of the lower slots after the derivative-direction slot of a
covariant derivative has been removed. -/
def connActLowerTail {s : Nat} (lower : Fin (s + 1) -> Idx) : Fin s -> Idx :=
  fun b => lower b.succ

/-- Component-level action of a `(1,2)` connection difference `A` on an
`(r,s)` tensor component array `T`.

The first lower slot of the output is the derivative direction.  The first sum
is the upper-index correction and the second sum is the lower-index correction,
matching the convention in MSM135 Chapter 4, equation following `lbl369`. -/
def connActComp {r s : Nat}
    (A : Idx -> Idx -> Idx -> Real)
    (T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) : Real :=
  (∑ a : Fin r, ∑ k : Idx,
      A (upper a) (lower 0) k *
        T (Function.update upper a k) (connActLowerTail lower)) -
    (∑ b : Fin s, ∑ k : Idx,
      A k (lower 0) (lower b.succ) *
        T upper (Function.update (connActLowerTail lower) b k))

/-- The actual mixed tensor whose components are the connection-difference
action `connActComp A T`.  This turns the component formula into a tensor
object without unfolding the Hom implementation downstream. -/
noncomputable def connActTensorAt {r s : Nat} [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : TensorRSSpace 1 2 I x) (T : TensorRSSpace r s I x) :
    TensorRSSpace r (s + 1) I x :=
  ofComponentsRS (I := I) basis r (s + 1)
    (fun upper lower =>
      connActComp
        (fun l i j =>
          componentRS (I := I) basis A
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' => componentRS (I := I) basis T upper' lower')
        upper lower)

@[simp]
theorem connActTensorAt_comp {r s : Nat} [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : TensorRSSpace 1 2 I x) (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    componentRS (I := I) basis (connActTensorAt (I := I) basis A T) upper lower =
      connActComp
        (fun l i j =>
          componentRS (I := I) basis A
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' => componentRS (I := I) basis T upper' lower')
        upper lower := by
  simpa [connActTensorAt] using
    (componentRS_ofComponentsRS (I := I) (basis := basis) (r := r) (s := s + 1)
      (c := fun upper lower =>
        connActComp
          (fun l i j =>
            componentRS (I := I) basis A
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' => componentRS (I := I) basis T upper' lower')
          upper lower)
      upper lower)

/-- The tensor with antidiagonal Leibniz-sum components expected from repeated
covariant derivatives of the connection-difference action.  The derivative
realization is a separate theorem; this definition only packages the component
array as an actual mixed tensor. -/
noncomputable def connActAntiTensorAt {r s : Nat} [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x)) (k : Nat)
    (A : Nat -> TensorRSSpace 1 2 I x) (T : Nat -> TensorRSSpace r s I x) :
    TensorRSSpace r (s + 1) I x :=
  ofComponentsRS (I := I) basis r (s + 1)
    (fun upper lower =>
      Finset.sum (Finset.antidiagonal k) fun ab =>
        connActComp
          (fun l i j =>
            componentRS (I := I) basis (A ab.1)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            componentRS (I := I) basis (T ab.2) upper' lower')
          upper lower)

@[simp]
theorem connActAntiTensorAt_comp {r s : Nat} [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x)) (k : Nat)
    (A : Nat -> TensorRSSpace 1 2 I x) (T : Nat -> TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    componentRS (I := I) basis
        (connActAntiTensorAt (I := I) basis k A T) upper lower =
      Finset.sum (Finset.antidiagonal k) fun ab =>
        connActComp
          (fun l i j =>
            componentRS (I := I) basis (A ab.1)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            componentRS (I := I) basis (T ab.2) upper' lower')
          upper lower := by
  simpa [connActAntiTensorAt] using
    (componentRS_ofComponentsRS (I := I) (basis := basis) (r := r) (s := s + 1)
      (c := fun upper lower =>
        Finset.sum (Finset.antidiagonal k) fun ab =>
          connActComp
            (fun l i j =>
              componentRS (I := I) basis (A ab.1)
                (fun _ : Fin 1 => l)
                (fun q : Fin 2 => if q = 0 then i else j))
            (fun upper' lower' =>
              componentRS (I := I) basis (T ab.2) upper' lower')
            upper lower)
      upper lower)

theorem connActComp_addL {r s : Nat}
    (A B : Idx -> Idx -> Idx -> Real)
    (T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    connActComp (fun i j k => A i j k + B i j k) T upper lower =
      connActComp A T upper lower + connActComp B T upper lower := by
  unfold connActComp
  simp [add_mul, Finset.sum_add_distrib]
  ring

theorem connActComp_smulL {r s : Nat}
    (c : Real) (A : Idx -> Idx -> Idx -> Real)
    (T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    connActComp (fun i j k => c * A i j k) T upper lower =
      c * connActComp A T upper lower := by
  unfold connActComp
  have hupper :
      (∑ a : Fin r, ∑ k : Idx,
        c * A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)) =
        c * (∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) := by
    calc
      (∑ a : Fin r, ∑ k : Idx,
        c * A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower))
          =
        ∑ a : Fin r, c * (∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          calc
            (∑ k : Idx, c * A (upper a) (lower 0) k *
              T (Function.update upper a k) (connActLowerTail lower))
                =
              ∑ k : Idx, c *
                (A (upper a) (lower 0) k *
                  T (Function.update upper a k) (connActLowerTail lower)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                ring
            _ = c * (∑ k : Idx,
              A (upper a) (lower 0) k *
                T (Function.update upper a k) (connActLowerTail lower)) := by
                rw [← Finset.mul_sum]
      _ = c * (∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) := by
          rw [← Finset.mul_sum]
  have hlower :
      (∑ b : Fin s, ∑ k : Idx,
        c * A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)) =
        c * (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)) := by
    calc
      (∑ b : Fin s, ∑ k : Idx,
        c * A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k))
          =
        ∑ b : Fin s, c * (∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          calc
            (∑ k : Idx, c * A k (lower 0) (lower b.succ) *
              T upper (Function.update (connActLowerTail lower) b k))
                =
              ∑ k : Idx, c *
                (A k (lower 0) (lower b.succ) *
                  T upper (Function.update (connActLowerTail lower) b k)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                ring
            _ = c * (∑ k : Idx,
              A k (lower 0) (lower b.succ) *
                T upper (Function.update (connActLowerTail lower) b k)) := by
                rw [← Finset.mul_sum]
      _ = c * (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)) := by
          rw [← Finset.mul_sum]
  rw [hupper, hlower]
  ring

theorem connActComp_addR {r s : Nat}
    (A : Idx -> Idx -> Idx -> Real)
    (T U : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    connActComp A (fun upper lower => T upper lower + U upper lower) upper lower =
      connActComp A T upper lower + connActComp A U upper lower := by
  unfold connActComp
  simp [mul_add, Finset.sum_add_distrib]
  ring

theorem connActComp_smulR {r s : Nat}
    (c : Real) (A : Idx -> Idx -> Idx -> Real)
    (T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    connActComp A (fun upper lower => c * T upper lower) upper lower =
      c * connActComp A T upper lower := by
  unfold connActComp
  have hupper :
      (∑ a : Fin r, ∑ k : Idx,
        A (upper a) (lower 0) k *
          (c * T (Function.update upper a k) (connActLowerTail lower))) =
        c * (∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) := by
    calc
      (∑ a : Fin r, ∑ k : Idx,
        A (upper a) (lower 0) k *
          (c * T (Function.update upper a k) (connActLowerTail lower)))
          =
        ∑ a : Fin r, c * (∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          calc
            (∑ k : Idx, A (upper a) (lower 0) k *
              (c * T (Function.update upper a k) (connActLowerTail lower)))
                =
              ∑ k : Idx, c *
                (A (upper a) (lower 0) k *
                  T (Function.update upper a k) (connActLowerTail lower)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                ring
            _ = c * (∑ k : Idx,
              A (upper a) (lower 0) k *
                T (Function.update upper a k) (connActLowerTail lower)) := by
                rw [← Finset.mul_sum]
      _ = c * (∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) := by
          rw [← Finset.mul_sum]
  have hlower :
      (∑ b : Fin s, ∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          (c * T upper (Function.update (connActLowerTail lower) b k))) =
        c * (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)) := by
    calc
      (∑ b : Fin s, ∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          (c * T upper (Function.update (connActLowerTail lower) b k)))
          =
        ∑ b : Fin s, c * (∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          calc
            (∑ k : Idx, A k (lower 0) (lower b.succ) *
              (c * T upper (Function.update (connActLowerTail lower) b k)))
                =
              ∑ k : Idx, c *
                (A k (lower 0) (lower b.succ) *
                  T upper (Function.update (connActLowerTail lower) b k)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                ring
            _ = c * (∑ k : Idx,
              A k (lower 0) (lower b.succ) *
                T upper (Function.update (connActLowerTail lower) b k)) := by
                rw [← Finset.mul_sum]
      _ = c * (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)) := by
          rw [← Finset.mul_sum]
  rw [hupper, hlower]
  ring

theorem connActComp_sumL {ι : Type*} {r s : Nat}
    (S : Finset ι) (A : ι -> Idx -> Idx -> Idx -> Real)
    (T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    connActComp
        (fun i j k => ∑ a ∈ S, A a i j k) T upper lower =
      ∑ a ∈ S, connActComp (A a) T upper lower := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [connActComp]
  | insert a S ha ih =>
      simp [Finset.sum_insert, ha, connActComp_addL, ih]

theorem connActComp_sumR {ι : Type*} {r s : Nat}
    (S : Finset ι) (A : Idx -> Idx -> Idx -> Real)
    (T : ι -> (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    connActComp A
        (fun upper lower => ∑ a ∈ S, T a upper lower) upper lower =
      ∑ a ∈ S, connActComp A (T a) upper lower := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [connActComp]
  | insert a S ha ih =>
      simp [Finset.sum_insert, ha, connActComp_addR, ih]

/-- Coarse finite-dimensional constant for the component action bound. -/
def connActConst (r s : Nat) (A0 T0 : Real) : Real :=
  ((r + s : Nat) : Real) * ((Fintype.card Idx : Real) * (A0 * T0))

theorem connActConst_nonneg {r s : Nat} {A0 T0 : Real}
    (hA0 : 0 <= A0) (hT0 : 0 <= T0) :
    0 <= connActConst (Idx := Idx) r s A0 T0 := by
  unfold connActConst
  exact mul_nonneg
    (by exact_mod_cast Nat.zero_le (r + s))
    (mul_nonneg
      (by exact_mod_cast Nat.zero_le (Fintype.card Idx))
      (mul_nonneg hA0 hT0))

theorem connActConst_mono {r s : Nat} {A0 A1 T0 T1 : Real}
    (hA0 : 0 <= A0) (hT0 : 0 <= T0)
    (hA : A0 <= A1) (hT : T0 <= T1) :
    connActConst (Idx := Idx) r s A0 T0 <=
      connActConst (Idx := Idx) r s A1 T1 := by
  have hcard_nonneg : 0 <= (Fintype.card Idx : Real) := by
    exact_mod_cast Nat.zero_le (Fintype.card Idx)
  have hvalence_nonneg : 0 <= ((r + s : Nat) : Real) := by
    exact_mod_cast Nat.zero_le (r + s)
  have hA1 : 0 <= A1 := le_trans hA0 hA
  have hmul : A0 * T0 <= A1 * T1 :=
    mul_le_mul hA hT hT0 hA1
  unfold connActConst
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hmul hcard_nonneg)
    hvalence_nonneg

theorem connActConst_mul_left {r s : Nat} (eps A0 T0 : Real) :
    connActConst (Idx := Idx) r s (eps * A0) T0 =
      eps * connActConst (Idx := Idx) r s A0 T0 := by
  unfold connActConst
  ring

theorem connActConst_mul_right {r s : Nat} (eps A0 T0 : Real) :
    connActConst (Idx := Idx) r s A0 (eps * T0) =
      eps * connActConst (Idx := Idx) r s A0 T0 := by
  unfold connActConst
  ring

theorem connActConst_le_mul_left {r s : Nat}
    {eps A0 B T0 N : Real}
    (hA0 : 0 <= A0) (hT0 : 0 <= T0)
    (hA : A0 <= eps * B) (hT : T0 <= N) :
    connActConst (Idx := Idx) r s A0 T0 <=
      eps * connActConst (Idx := Idx) r s B N := by
  calc
    connActConst (Idx := Idx) r s A0 T0
        <= connActConst (Idx := Idx) r s (eps * B) N :=
          connActConst_mono (Idx := Idx) hA0 hT0 hA hT
    _ = eps * connActConst (Idx := Idx) r s B N :=
          connActConst_mul_left (Idx := Idx) eps B N

/-- Component-count square-root constant used after converting componentwise
action bounds into a mixed-tensor norm bound. -/
def connActNormConst (r s : Nat) (A0 T0 : Real) : Real :=
  Real.sqrt
    ((Fintype.card (Fin r -> Idx) : Real) *
      ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
        (connActConst (Idx := Idx) r s A0 T0) ^ 2))

theorem connActNormConst_nonneg {r s : Nat} {A0 T0 : Real} :
    0 <= connActNormConst (Idx := Idx) r s A0 T0 := by
  exact Real.sqrt_nonneg _

theorem connActNormConst_mono {r s : Nat} {A0 A1 T0 T1 : Real}
    (hA0 : 0 <= A0) (hT0 : 0 <= T0)
    (hA : A0 <= A1) (hT : T0 <= T1) :
    connActNormConst (Idx := Idx) r s A0 T0 <=
      connActNormConst (Idx := Idx) r s A1 T1 := by
  have hC :
      connActConst (Idx := Idx) r s A0 T0 <=
        connActConst (Idx := Idx) r s A1 T1 :=
    connActConst_mono (Idx := Idx) hA0 hT0 hA hT
  have hC0 :
      0 <= connActConst (Idx := Idx) r s A0 T0 :=
    connActConst_nonneg (Idx := Idx) hA0 hT0
  have hC1 :
      0 <= connActConst (Idx := Idx) r s A1 T1 :=
    le_trans hC0 hC
  have hsq :
      (connActConst (Idx := Idx) r s A0 T0) ^ 2 <=
        (connActConst (Idx := Idx) r s A1 T1) ^ 2 :=
    (sq_le_sq₀ hC0 hC1).2 hC
  have hcardUpper :
      0 <= (Fintype.card (Fin r -> Idx) : Real) := by positivity
  have hcardLower :
      0 <= (Fintype.card (Fin (s + 1) -> Idx) : Real) := by positivity
  unfold connActNormConst
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsq hcardLower)
      hcardUpper)

theorem connActNormConst_mul_left {r s : Nat} {eps A0 T0 : Real}
    (heps : 0 <= eps) :
    connActNormConst (Idx := Idx) r s (eps * A0) T0 =
      eps * connActNormConst (Idx := Idx) r s A0 T0 := by
  let U : Real :=
    (Fintype.card (Fin r -> Idx) : Real) *
      ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
        (connActConst (Idx := Idx) r s A0 T0) ^ 2)
  have hU : 0 <= U := by
    unfold U
    positivity
  unfold connActNormConst
  rw [connActConst_mul_left (Idx := Idx) eps A0 T0]
  have hrewrite :
      (Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (eps * connActConst (Idx := Idx) r s A0 T0) ^ 2) =
        eps ^ 2 * U := by
    unfold U
    ring
  rw [hrewrite]
  rw [Real.sqrt_mul (sq_nonneg eps)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg heps]

theorem connActNormConst_mul_right {r s : Nat} {eps A0 T0 : Real}
    (heps : 0 <= eps) :
    connActNormConst (Idx := Idx) r s A0 (eps * T0) =
      eps * connActNormConst (Idx := Idx) r s A0 T0 := by
  let U : Real :=
    (Fintype.card (Fin r -> Idx) : Real) *
      ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
        (connActConst (Idx := Idx) r s A0 T0) ^ 2)
  unfold connActNormConst
  rw [connActConst_mul_right (Idx := Idx) eps A0 T0]
  have hrewrite :
      (Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (eps * connActConst (Idx := Idx) r s A0 T0) ^ 2) =
        eps ^ 2 * U := by
    unfold U
    ring
  rw [hrewrite]
  rw [Real.sqrt_mul (sq_nonneg eps)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg heps]

theorem connActNormConst_le_mul_left {r s : Nat}
    {eps A0 B T0 N : Real}
    (heps : 0 <= eps) (hA0 : 0 <= A0) (hT0 : 0 <= T0)
    (hA : A0 <= eps * B) (hT : T0 <= N) :
    connActNormConst (Idx := Idx) r s A0 T0 <=
      eps * connActNormConst (Idx := Idx) r s B N := by
  calc
    connActNormConst (Idx := Idx) r s A0 T0
        <= connActNormConst (Idx := Idx) r s (eps * B) N :=
          connActNormConst_mono (Idx := Idx) hA0 hT0 hA hT
    _ = eps * connActNormConst (Idx := Idx) r s B N :=
          connActNormConst_mul_left (Idx := Idx) heps

/-- Norm-level antidiagonal action constant.  It is the component-count
square-root factor applied to the sum of the component action constants. -/
def connActAntiNormConst (r s k : Nat) (A0 T0 : Nat -> Real) : Real :=
  Real.sqrt
    ((Fintype.card (Fin r -> Idx) : Real) *
      ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
        (Finset.sum (Finset.antidiagonal k) fun ab =>
          (Nat.choose k ab.1 : Real) *
            connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)) ^ 2))

theorem connActAntiNormConst_nonneg {r s k : Nat} {A0 T0 : Nat -> Real} :
    0 <= connActAntiNormConst (Idx := Idx) r s k A0 T0 := by
  exact Real.sqrt_nonneg _

theorem connActAntiNormConst_mono {r s k : Nat} {A0 A1 T0 T1 : Nat -> Real}
    (hA0 : forall a : Nat, 0 <= A0 a)
    (hT0 : forall b : Nat, 0 <= T0 b)
    (hA : forall a : Nat, A0 a <= A1 a)
    (hT : forall b : Nat, T0 b <= T1 b) :
    connActAntiNormConst (Idx := Idx) r s k A0 T0 <=
      connActAntiNormConst (Idx := Idx) r s k A1 T1 := by
  let C0 : Real := Finset.sum (Finset.antidiagonal k) fun ab =>
    (Nat.choose k ab.1 : Real) *
      connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)
  let C1 : Real := Finset.sum (Finset.antidiagonal k) fun ab =>
    (Nat.choose k ab.1 : Real) *
      connActConst (Idx := Idx) r s (A1 ab.1) (T1 ab.2)
  have hC0 : 0 <= C0 := by
    unfold C0
    refine Finset.sum_nonneg ?_
    intro ab _hab
    exact mul_nonneg (by positivity)
      (connActConst_nonneg (Idx := Idx) (hA0 ab.1) (hT0 ab.2))
  have hC : C0 <= C1 := by
    unfold C0 C1
    refine Finset.sum_le_sum ?_
    intro ab _hab
    have hchoose : 0 <= (Nat.choose k ab.1 : Real) := by positivity
    exact mul_le_mul_of_nonneg_left
      (connActConst_mono (Idx := Idx) (hA0 ab.1) (hT0 ab.2)
        (hA ab.1) (hT ab.2))
      hchoose
  have hC1 : 0 <= C1 := le_trans hC0 hC
  have hsq : C0 ^ 2 <= C1 ^ 2 := (sq_le_sq₀ hC0 hC1).2 hC
  have hcardUpper : 0 <= (Fintype.card (Fin r -> Idx) : Real) := by positivity
  have hcardLower : 0 <= (Fintype.card (Fin (s + 1) -> Idx) : Real) := by positivity
  unfold connActAntiNormConst
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsq hcardLower)
      hcardUpper)

theorem connActAntiNormConst_mul_left {r s k : Nat}
    {eps : Real} (heps : 0 <= eps) (A0 T0 : Nat -> Real) :
    connActAntiNormConst (Idx := Idx) r s k (fun a => eps * A0 a) T0 =
      eps * connActAntiNormConst (Idx := Idx) r s k A0 T0 := by
  let C : Real := Finset.sum (Finset.antidiagonal k) fun ab =>
    (Nat.choose k ab.1 : Real) *
      connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)
  unfold connActAntiNormConst
  have hsum :
      (Finset.sum (Finset.antidiagonal k) fun ab =>
        (Nat.choose k ab.1 : Real) *
          connActConst (Idx := Idx) r s (eps * A0 ab.1) (T0 ab.2)) =
        eps * C := by
    unfold C
    calc
      (Finset.sum (Finset.antidiagonal k) fun ab =>
        (Nat.choose k ab.1 : Real) *
          connActConst (Idx := Idx) r s (eps * A0 ab.1) (T0 ab.2))
          =
        Finset.sum (Finset.antidiagonal k) fun ab =>
          eps * ((Nat.choose k ab.1 : Real) *
            connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)) := by
          refine Finset.sum_congr rfl ?_
          intro ab _hab
          rw [connActConst_mul_left (Idx := Idx) eps (A0 ab.1) (T0 ab.2)]
          ring
      _ = eps * Finset.sum (Finset.antidiagonal k) (fun ab =>
          (Nat.choose k ab.1 : Real) *
            connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)) := by
          rw [Finset.mul_sum]
  rw [hsum]
  let U : Real :=
    (Fintype.card (Fin r -> Idx) : Real) *
      ((Fintype.card (Fin (s + 1) -> Idx) : Real) * C ^ 2)
  have hU : 0 <= U := by
    unfold U
    positivity
  have hrewrite :
      (Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) * (eps * C) ^ 2) =
        eps ^ 2 * U := by
    unfold U
    ring
  rw [hrewrite]
  rw [Real.sqrt_mul (sq_nonneg eps)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg heps]

theorem connActAntiNormConst_mul_right {r s k : Nat}
    {eps : Real} (heps : 0 <= eps) (A0 T0 : Nat -> Real) :
    connActAntiNormConst (Idx := Idx) r s k A0 (fun b => eps * T0 b) =
      eps * connActAntiNormConst (Idx := Idx) r s k A0 T0 := by
  let C : Real := Finset.sum (Finset.antidiagonal k) fun ab =>
    (Nat.choose k ab.1 : Real) *
      connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)
  unfold connActAntiNormConst
  have hsum :
      (Finset.sum (Finset.antidiagonal k) fun ab =>
        (Nat.choose k ab.1 : Real) *
          connActConst (Idx := Idx) r s (A0 ab.1) (eps * T0 ab.2)) =
        eps * C := by
    unfold C
    calc
      (Finset.sum (Finset.antidiagonal k) fun ab =>
        (Nat.choose k ab.1 : Real) *
          connActConst (Idx := Idx) r s (A0 ab.1) (eps * T0 ab.2))
          =
        Finset.sum (Finset.antidiagonal k) fun ab =>
          eps * ((Nat.choose k ab.1 : Real) *
            connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)) := by
          refine Finset.sum_congr rfl ?_
          intro ab _hab
          rw [connActConst_mul_right (Idx := Idx) eps (A0 ab.1) (T0 ab.2)]
          ring
      _ = eps * Finset.sum (Finset.antidiagonal k) (fun ab =>
          (Nat.choose k ab.1 : Real) *
            connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2)) := by
          rw [Finset.mul_sum]
  rw [hsum]
  let U : Real :=
    (Fintype.card (Fin r -> Idx) : Real) *
      ((Fintype.card (Fin (s + 1) -> Idx) : Real) * C ^ 2)
  have hrewrite :
      (Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) * (eps * C) ^ 2) =
        eps ^ 2 * U := by
    unfold U
    ring
  rw [hrewrite]
  rw [Real.sqrt_mul (sq_nonneg eps)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg heps]

theorem connActAntiNormConst_le_mul_left {r s k : Nat}
    {eps : Real} {A0 B T0 N : Nat -> Real}
    (heps : 0 <= eps)
    (hA0 : forall a : Nat, 0 <= A0 a)
    (hT0 : forall b : Nat, 0 <= T0 b)
    (hA : forall a : Nat, A0 a <= eps * B a)
    (hT : forall b : Nat, T0 b <= N b) :
    connActAntiNormConst (Idx := Idx) r s k A0 T0 <=
      eps * connActAntiNormConst (Idx := Idx) r s k B N := by
  calc
    connActAntiNormConst (Idx := Idx) r s k A0 T0
        <= connActAntiNormConst (Idx := Idx) r s k (fun a => eps * B a) N :=
          connActAntiNormConst_mono (Idx := Idx) hA0 hT0 hA hT
    _ = eps * connActAntiNormConst (Idx := Idx) r s k B N :=
          connActAntiNormConst_mul_left (Idx := Idx) heps B N

/-- Step constant obtained by factoring a common tensor bound out of the
antidiagonal action estimate. -/
def connActAntiStepConst (r s k : Nat) (A0 : Nat -> Real) : Real :=
  connActAntiNormConst (Idx := Idx) r s k A0 (fun _ => 1)

theorem connActAntiStepConst_nonneg {r s k : Nat} {A0 : Nat -> Real} :
    0 <= connActAntiStepConst (Idx := Idx) r s k A0 := by
  exact connActAntiNormConst_nonneg (Idx := Idx)

theorem connActAntiNormConst_le_step_mul {r s k : Nat}
    {A0 T0 : Nat -> Real} {S : Real}
    (hA0 : forall a : Nat, 0 <= A0 a)
    (hT0 : forall b : Nat, 0 <= T0 b)
    (hS : 0 <= S)
    (hT : forall b : Nat, T0 b <= S) :
    connActAntiNormConst (Idx := Idx) r s k A0 T0 <=
      connActAntiStepConst (Idx := Idx) r s k A0 * S := by
  have hmono :
      connActAntiNormConst (Idx := Idx) r s k A0 T0 <=
        connActAntiNormConst (Idx := Idx) r s k A0 (fun _ => S) :=
    connActAntiNormConst_mono (Idx := Idx) hA0 hT0
      (fun a => le_rfl) hT
  have hscale :
      connActAntiNormConst (Idx := Idx) r s k A0 (fun _ => S) =
        S * connActAntiStepConst (Idx := Idx) r s k A0 := by
    simpa [connActAntiStepConst] using
      (connActAntiNormConst_mul_right (Idx := Idx) (r := r) (s := s)
        (k := k) (eps := S) hS A0 (fun _ => 1))
  calc
    connActAntiNormConst (Idx := Idx) r s k A0 T0
        <= connActAntiNormConst (Idx := Idx) r s k A0 (fun _ => S) := hmono
    _ = S * connActAntiStepConst (Idx := Idx) r s k A0 := hscale
    _ = connActAntiStepConst (Idx := Idx) r s k A0 * S := by ring

private theorem abs_inner_sum_le {r s : Nat}
    {A0 T0 : Real} (hA0 : 0 <= A0)
    {A : Idx -> Idx -> Idx -> Real}
    {T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall i j k : Idx, |A i j k| <= A0)
    (hT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T upper lower| <= T0)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) (a : Fin r) :
    |∑ k : Idx,
      A (upper a) (lower 0) k *
        T (Function.update upper a k) (connActLowerTail lower)| <=
      (Fintype.card Idx : Real) * (A0 * T0) := by
  have hterm (k : Idx) :
      |A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)| <=
        A0 * T0 := by
    rw [abs_mul]
    exact mul_le_mul
      (hA (upper a) (lower 0) k)
      (hT (Function.update upper a k) (connActLowerTail lower))
      (abs_nonneg _)
      hA0
  calc
    |∑ k : Idx,
      A (upper a) (lower 0) k *
        T (Function.update upper a k) (connActLowerTail lower)|
        <= ∑ k : Idx,
          |A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)| := by
          simpa using
            Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun k : Idx =>
                A (upper a) (lower 0) k *
                  T (Function.update upper a k) (connActLowerTail lower))
    _ <= ∑ _k : Idx, A0 * T0 := by
          exact Finset.sum_le_sum (fun k _ => hterm k)
    _ = (Fintype.card Idx : Real) * (A0 * T0) := by
          simp

private theorem abs_inner_sum_lower_le {r s : Nat}
    {A0 T0 : Real} (hA0 : 0 <= A0)
    {A : Idx -> Idx -> Idx -> Real}
    {T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall i j k : Idx, |A i j k| <= A0)
    (hT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T upper lower| <= T0)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) (b : Fin s) :
    |∑ k : Idx,
      A k (lower 0) (lower b.succ) *
        T upper (Function.update (connActLowerTail lower) b k)| <=
      (Fintype.card Idx : Real) * (A0 * T0) := by
  have hterm (k : Idx) :
      |A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)| <=
        A0 * T0 := by
    rw [abs_mul]
    exact mul_le_mul
      (hA k (lower 0) (lower b.succ))
      (hT upper (Function.update (connActLowerTail lower) b k))
      (abs_nonneg _)
      hA0
  calc
    |∑ k : Idx,
      A k (lower 0) (lower b.succ) *
        T upper (Function.update (connActLowerTail lower) b k)|
        <= ∑ k : Idx,
          |A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)| := by
          simpa using
            Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun k : Idx =>
                A k (lower 0) (lower b.succ) *
                  T upper (Function.update (connActLowerTail lower) b k))
    _ <= ∑ _k : Idx, A0 * T0 := by
          exact Finset.sum_le_sum (fun k _ => hterm k)
    _ = (Fintype.card Idx : Real) * (A0 * T0) := by
          simp

/-- Componentwise absolute-value estimate for the connection-difference
action.  It is deliberately coarse; the important point for F3 is that the
constant depends only on the tensor valence and model dimension. -/
theorem abs_connActComp_le {r s : Nat}
    {A0 T0 : Real} (hA0 : 0 <= A0)
    {A : Idx -> Idx -> Idx -> Real}
    {T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall i j k : Idx, |A i j k| <= A0)
    (hT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T upper lower| <= T0)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |connActComp A T upper lower| <= connActConst (Idx := Idx) r s A0 T0 := by
  let B : Real := (Fintype.card Idx : Real) * (A0 * T0)
  have hupper_term (a : Fin r) :
      |∑ k : Idx,
        A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)| <= B := by
    simpa [B] using
      abs_inner_sum_le (Idx := Idx) (r := r) (s := s)
        hA0 hA hT upper lower a
  have hlower_term (b : Fin s) :
      |∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)| <= B := by
    simpa [B] using
      abs_inner_sum_lower_le (Idx := Idx) (r := r) (s := s)
        hA0 hA hT upper lower b
  have hupper_sum :
      |∑ a : Fin r, ∑ k : Idx,
        A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)| <=
        (r : Real) * B := by
    calc
      |∑ a : Fin r, ∑ k : Idx,
        A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)|
          <= ∑ a : Fin r, |∑ k : Idx,
            A (upper a) (lower 0) k *
              T (Function.update upper a k) (connActLowerTail lower)| := by
            simpa using
              Finset.abs_sum_le_sum_abs
                (s := Finset.univ)
                (f := fun a : Fin r => ∑ k : Idx,
                  A (upper a) (lower 0) k *
                    T (Function.update upper a k) (connActLowerTail lower))
      _ <= ∑ _a : Fin r, B := by
            exact Finset.sum_le_sum (fun a _ => hupper_term a)
      _ = (r : Real) * B := by
            simp
  have hlower_sum :
      |∑ b : Fin s, ∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)| <=
        (s : Real) * B := by
    calc
      |∑ b : Fin s, ∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)|
          <= ∑ b : Fin s, |∑ k : Idx,
            A k (lower 0) (lower b.succ) *
              T upper (Function.update (connActLowerTail lower) b k)| := by
            simpa using
              Finset.abs_sum_le_sum_abs
                (s := Finset.univ)
                (f := fun b : Fin s => ∑ k : Idx,
                  A k (lower 0) (lower b.succ) *
                    T upper (Function.update (connActLowerTail lower) b k))
      _ <= ∑ _b : Fin s, B := by
            exact Finset.sum_le_sum (fun b _ => hlower_term b)
      _ = (s : Real) * B := by
            simp
  have htri :
      |(∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) -
        (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k))| <=
        (r : Real) * B + (s : Real) * B := by
    calc
      |(∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) -
        (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k))|
          <=
        |∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)| +
        |∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)| := by
            simpa [sub_eq_add_neg] using
              abs_add_le
                (∑ a : Fin r, ∑ k : Idx,
                  A (upper a) (lower 0) k *
                    T (Function.update upper a k) (connActLowerTail lower))
                (-(∑ b : Fin s, ∑ k : Idx,
                  A k (lower 0) (lower b.succ) *
                    T upper (Function.update (connActLowerTail lower) b k)))
      _ <= (r : Real) * B + (s : Real) * B :=
            add_le_add hupper_sum hlower_sum
  calc
    |connActComp A T upper lower| <= (r : Real) * B + (s : Real) * B := by
      simpa [connActComp, B] using htri
    _ = connActConst (Idx := Idx) r s A0 T0 := by
      simp [connActConst, B, Nat.cast_add]
      ring

/-- Component estimate for an antidiagonal Leibniz sum of connection-action
terms.  This is the finite-sum algebraic form expected from a future iterated
covariant product-rule producer. -/
theorem abs_connActAnti_le {r s : Nat} (k : Nat)
    {A0 T0 : Nat -> Real}
    (hA0 : forall a : Nat, 0 <= A0 a)
    {A : Nat -> Idx -> Idx -> Idx -> Real}
    {T : Nat -> (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall a : Nat, forall i j l : Idx, |A a i j l| <= A0 a)
    (hT : forall b : Nat, forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T b upper lower| <= T0 b)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |Finset.sum (Finset.antidiagonal k)
      (fun ab => (Nat.choose k ab.1 : Real) *
        connActComp (A ab.1) (T ab.2) upper lower)| <=
      Finset.sum (Finset.antidiagonal k) fun ab =>
        (Nat.choose k ab.1 : Real) *
          connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2) := by
  calc
    |Finset.sum (Finset.antidiagonal k)
      (fun ab => (Nat.choose k ab.1 : Real) *
        connActComp (A ab.1) (T ab.2) upper lower)|
        <= Finset.sum (Finset.antidiagonal k) fun ab =>
          |(Nat.choose k ab.1 : Real) *
            connActComp (A ab.1) (T ab.2) upper lower| := by
          exact Finset.abs_sum_le_sum_abs
            (s := Finset.antidiagonal k)
            (f := fun ab =>
              (Nat.choose k ab.1 : Real) *
                connActComp (A ab.1) (T ab.2) upper lower)
    _ <= Finset.sum (Finset.antidiagonal k) fun ab =>
        (Nat.choose k ab.1 : Real) *
          connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2) := by
          refine Finset.sum_le_sum ?_
          intro ab _hab
          have hchoose : 0 <= (Nat.choose k ab.1 : Real) := by positivity
          have hact :
              |connActComp (A ab.1) (T ab.2) upper lower| <=
                connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2) :=
            abs_connActComp_le (Idx := Idx) (hA0 ab.1)
              (hA ab.1) (hT ab.2) upper lower
          calc
            |(Nat.choose k ab.1 : Real) *
              connActComp (A ab.1) (T ab.2) upper lower|
                = (Nat.choose k ab.1 : Real) *
                    |connActComp (A ab.1) (T ab.2) upper lower| := by
                  rw [abs_mul, abs_of_nonneg hchoose]
            _ <= (Nat.choose k ab.1 : Real) *
                connActConst (Idx := Idx) r s (A0 ab.1) (T0 ab.2) := by
                  exact mul_le_mul_of_nonneg_left hact hchoose

theorem abs_connActAntiTensor_le
    [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) {r s : Nat} (k : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Nat -> TensorRSSpace 1 2 I x)
    (T : Nat -> TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |Finset.sum (Finset.antidiagonal k)
      (fun ab => (Nat.choose k ab.1 : Real) *
        connActComp
          (fun l i j =>
            componentRS (I := I) basis (A ab.1) (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            componentRS (I := I) basis (T ab.2) upper' lower')
          upper lower)| <=
      Finset.sum (Finset.antidiagonal k) fun ab =>
        (Nat.choose k ab.1 : Real) *
          connActConst (Idx := Idx) r s
            (Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 (A ab.1)))
            (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (T ab.2))) := by
  let A0 : Nat -> Real := fun a =>
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 (A a))
  let T0 : Nat -> Real := fun b =>
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (T b))
  let Acomp : Nat -> Idx -> Idx -> Idx -> Real :=
    fun a l i j =>
      componentRS (I := I) basis (A a) (fun _ : Fin 1 => l)
        (fun q : Fin 2 => if q = 0 then i else j)
  let Tcomp : Nat -> (Fin r -> Idx) -> (Fin s -> Idx) -> Real :=
    fun b upper' lower' => componentRS (I := I) basis (T b) upper' lower'
  have hA0 : forall a : Nat, 0 <= A0 a := by
    intro a
    exact Real.sqrt_nonneg _
  have hA :
      forall a : Nat, forall i j l : Idx, |Acomp a i j l| <= A0 a := by
    intro a i j l
    exact abs_componentRS_le_sqrt_normSqRS
      (I := I) g x 1 2 basis hinv (A a) (fun _ : Fin 1 => i)
      (fun q : Fin 2 => if q = 0 then j else l)
  have hT :
      forall b : Nat, forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
        |Tcomp b upper lower| <= T0 b := by
    intro b upper' lower'
    exact abs_componentRS_le_sqrt_normSqRS
      (I := I) g x r s basis hinv (T b) upper' lower'
  have hanti :=
    abs_connActAnti_le (Idx := Idx) (r := r) (s := s) k
      (A0 := A0) (T0 := T0) (A := Acomp) (T := Tcomp)
      hA0 hA hT upper lower
  simpa [A0, T0, Acomp, Tcomp] using hanti

theorem norm_connActAnti_le
    [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) {r s : Nat} (k : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Nat -> TensorRSSpace 1 2 I x)
    (T : Nat -> TensorRSSpace r s I x)
    (S : TensorRSSpace r (s + 1) I x)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      componentRS (I := I) basis S upper lower =
        Finset.sum (Finset.antidiagonal k)
          (fun ab => (Nat.choose k ab.1 : Real) *
            connActComp
              (fun l i j =>
                componentRS (I := I) basis (A ab.1) (fun _ : Fin 1 => l)
                  (fun q : Fin 2 => if q = 0 then i else j))
              (fun upper' lower' =>
                componentRS (I := I) basis (T ab.2) upper' lower')
              upper lower)) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r (s + 1) S) <=
      connActAntiNormConst (Idx := Idx) r s k
        (fun a => Real.sqrt
          (normSqRS (I := I) (g := g) (x := x) 1 2 (A a)))
        (fun b => Real.sqrt
          (normSqRS (I := I) (g := g) (x := x) r s (T b))) := by
  let B : Real :=
    Finset.sum (Finset.antidiagonal k) fun ab =>
      (Nat.choose k ab.1 : Real) *
        connActConst (Idx := Idx) r s
          (Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 (A ab.1)))
          (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (T ab.2)))
  have hB : 0 <= B := by
    unfold B
    refine Finset.sum_nonneg ?_
    intro ab _hab
    exact mul_nonneg (by positivity)
      (connActConst_nonneg (Idx := Idx) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  refine sqrt_normRS_le_comps (I := I) g x r (s + 1) basis hinv S hB ?_
  intro upper lower
  rw [hcomp upper lower]
  simpa [B, connActAntiNormConst] using
    abs_connActAntiTensor_le (I := I) g x k basis hinv A T upper lower

theorem norm_connActAnti_bound
    [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) {r s : Nat} (k : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Nat -> TensorRSSpace 1 2 I x)
    (T : Nat -> TensorRSSpace r s I x)
    (S : TensorRSSpace r (s + 1) I x)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      componentRS (I := I) basis S upper lower =
        Finset.sum (Finset.antidiagonal k)
          (fun ab => (Nat.choose k ab.1 : Real) *
            connActComp
              (fun l i j =>
                componentRS (I := I) basis (A ab.1) (fun _ : Fin 1 => l)
                  (fun q : Fin 2 => if q = 0 then i else j))
              (fun upper' lower' =>
                componentRS (I := I) basis (T ab.2) upper' lower')
              upper lower))
    {eps : Real} (B N : Nat -> Real) (heps : 0 <= eps)
    (hA : forall a : Nat,
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 (A a)) <= eps * B a)
    (hT : forall b : Nat,
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (T b)) <= N b) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r (s + 1) S) <=
      eps * connActAntiNormConst (Idx := Idx) r s k B N := by
  have hbase :=
    norm_connActAnti_le (I := I) g x k basis hinv A T S hcomp
  have hconst :
      connActAntiNormConst (Idx := Idx) r s k
          (fun a => Real.sqrt
            (normSqRS (I := I) (g := g) (x := x) 1 2 (A a)))
          (fun b => Real.sqrt
            (normSqRS (I := I) (g := g) (x := x) r s (T b))) <=
        eps * connActAntiNormConst (Idx := Idx) r s k B N :=
    connActAntiNormConst_le_mul_left (Idx := Idx) heps
      (fun a => Real.sqrt_nonneg _)
      (fun b => Real.sqrt_nonneg _)
      hA hT
  exact hbase.trans hconst

theorem norm_connActAnti_bound_step
    [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) {r s : Nat} (k : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Nat -> TensorRSSpace 1 2 I x)
    (T : Nat -> TensorRSSpace r s I x)
    (Santi : TensorRSSpace r (s + 1) I x)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      componentRS (I := I) basis Santi upper lower =
        Finset.sum (Finset.antidiagonal k)
          (fun ab => (Nat.choose k ab.1 : Real) *
            connActComp
              (fun l i j =>
                componentRS (I := I) basis (A ab.1) (fun _ : Fin 1 => l)
                  (fun q : Fin 2 => if q = 0 then i else j))
              (fun upper' lower' =>
                componentRS (I := I) basis (T ab.2) upper' lower')
              upper lower))
    {eps S : Real} (B : Nat -> Real)
    (heps : 0 <= eps) (hB : forall a : Nat, 0 <= B a) (hS : 0 <= S)
    (hA : forall a : Nat,
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 (A a)) <= eps * B a)
    (hT : forall b : Nat,
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (T b)) <= S) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r (s + 1) Santi) <=
      eps * connActAntiStepConst (Idx := Idx) r s k B * S := by
  let T0 : Nat -> Real := fun b =>
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (T b))
  have hbase :
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r (s + 1) Santi) <=
        eps * connActAntiNormConst (Idx := Idx) r s k B T0 :=
    norm_connActAnti_bound (I := I) g x k basis hinv A T Santi hcomp
      B T0 heps hA (fun b => le_rfl)
  have hconst :
      connActAntiNormConst (Idx := Idx) r s k B T0 <=
        connActAntiStepConst (Idx := Idx) r s k B * S :=
    connActAntiNormConst_le_step_mul (Idx := Idx)
      hB (fun b => Real.sqrt_nonneg _) hS hT
  have hscaled :
      eps * connActAntiNormConst (Idx := Idx) r s k B T0 <=
        eps * (connActAntiStepConst (Idx := Idx) r s k B * S) :=
    mul_le_mul_of_nonneg_left hconst heps
  calc
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r (s + 1) Santi)
        <= eps * connActAntiNormConst (Idx := Idx) r s k B T0 := hbase
    _ <= eps * (connActAntiStepConst (Idx := Idx) r s k B * S) := hscaled
    _ = eps * connActAntiStepConst (Idx := Idx) r s k B * S := by ring

theorem abs_connActComp_le_mul_left {r s : Nat}
    {A0 B T0 N eps : Real} (hA0 : 0 <= A0) (hT0 : 0 <= T0)
    {A : Idx -> Idx -> Idx -> Real}
    {T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall i j k : Idx, |A i j k| <= A0)
    (hT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T upper lower| <= T0)
    (hA_bound : A0 <= eps * B) (hT_bound : T0 <= N)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |connActComp A T upper lower| <=
      eps * connActConst (Idx := Idx) r s B N := by
  exact (abs_connActComp_le (Idx := Idx) hA0 hA hT upper lower).trans
    (connActConst_le_mul_left (Idx := Idx) hA0 hT0 hA_bound hT_bound)

/-- Tensor-norm version of `abs_connActComp_le`, obtained by bounding each
component of the connection-difference tensor and of `T` by their full
orthonormal-basis norms. -/
theorem abs_connActTensor_le
    [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) {r s : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace 1 2 I x) (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |connActComp
      (fun l i j =>
        componentRS (I := I) basis A (fun _ : Fin 1 => l)
          (fun q : Fin 2 => if q = 0 then i else j))
      (fun upper' lower' => componentRS (I := I) basis T upper' lower')
      upper lower| <=
      connActConst (Idx := Idx) r s
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 A))
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s T)) := by
  refine abs_connActComp_le (Idx := Idx)
    (A0 := Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 A))
    (T0 := Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s T))
    (r := r) (s := s) (Real.sqrt_nonneg _) ?_ ?_ upper lower
  · intro i j k
    exact abs_componentRS_le_sqrt_normSqRS
      (I := I) g x 1 2 basis hinv A (fun _ : Fin 1 => i)
      (fun q : Fin 2 => if q = 0 then j else k)
  · intro upper' lower'
    exact abs_componentRS_le_sqrt_normSqRS
      (I := I) g x r s basis hinv T upper' lower'

theorem abs_connActTensor_le_mul_left
    [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) {r s : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    {eps B N : Real}
    (A : TensorRSSpace 1 2 I x) (T : TensorRSSpace r s I x)
    (hA :
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 A) <= eps * B)
    (hT :
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s T) <= N)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |connActComp
      (fun l i j =>
        componentRS (I := I) basis A (fun _ : Fin 1 => l)
          (fun q : Fin 2 => if q = 0 then i else j))
      (fun upper' lower' => componentRS (I := I) basis T upper' lower')
      upper lower| <=
      eps * connActConst (Idx := Idx) r s B N := by
  exact (abs_connActTensor_le
    (I := I) g x basis hinv A T upper lower).trans
    (connActConst_le_mul_left (Idx := Idx)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hT)

end Components

end

end Tensor0SBundle
