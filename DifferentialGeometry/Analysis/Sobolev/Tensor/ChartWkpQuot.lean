import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpComplete
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

/-!
# Explicit algebra on the tensor chart-Sobolev quotient

The quotient already exists as `WkpTensorQuot`, but deliberately carries no
global algebraic, metric, normed-space, or complete-space instance.  This file
defines the underlying quotient operations as ordinary functions using
`Quotient.map` and `Quotient.map₂`.  It also proves the norm laws and the
separation theorem needed for a later local structure package.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Componentwise a.e. equality is preserved by addition on the genuine
tensor Sobolev carrier. -/
theorem qadd_rel
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} {hp : 1 ≤ p}
    {S₁ S₂ T₁ T₂ : WkpTensor (I := I) (M := M) g r s k p hp}
    (hS : TensorAEEq (I := I) (M := M) g S₁.1 S₂.1)
    (hT : TensorAEEq (I := I) (M := M) g T₁.1 T₂.1) :
    TensorAEEq (I := I) (M := M) g (S₁ + T₁).1 (S₂ + T₂).1 := by
  change TensorAEEq (I := I) (M := M) g (S₁.1 + T₁.1) (S₂.1 + T₂.1)
  exact hS.add hT

/-- Componentwise a.e. equality is preserved by negation. -/
theorem qneg_rel
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} {hp : 1 ≤ p}
    {S T : WkpTensor (I := I) (M := M) g r s k p hp}
    (h : TensorAEEq (I := I) (M := M) g S.1 T.1) :
    TensorAEEq (I := I) (M := M) g (-S).1 (-T).1 := by
  change TensorAEEq (I := I) (M := M) g (-S.1) (-T.1)
  exact h.neg

/-- Componentwise a.e. equality is preserved by real scalar multiplication. -/
theorem qsmul_rel
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} {hp : 1 ≤ p} (c : ℝ)
    {S T : WkpTensor (I := I) (M := M) g r s k p hp}
    (h : TensorAEEq (I := I) (M := M) g S.1 T.1) :
    TensorAEEq (I := I) (M := M) g (c • S).1 (c • T).1 := by
  change TensorAEEq (I := I) (M := M) g (c • S.1) (c • T.1)
  exact h.smul c

/-- Componentwise a.e. equality is preserved by subtraction. -/
theorem qsub_rel
    (g : SmoothRiemannianMetric I M) {r s k : ℕ}
    {p : ℝ≥0∞} {hp : 1 ≤ p}
    {S₁ S₂ T₁ T₂ : WkpTensor (I := I) (M := M) g r s k p hp}
    (hS : TensorAEEq (I := I) (M := M) g S₁.1 S₂.1)
    (hT : TensorAEEq (I := I) (M := M) g T₁.1 T₂.1) :
    TensorAEEq (I := I) (M := M) g (S₁ - T₁).1 (S₂ - T₂).1 := by
  change TensorAEEq (I := I) (M := M) g (S₁.1 - T₁.1) (S₂.1 - T₂.1)
  exact hS.sub hT

/-- The explicit zero class, without a global `Zero` instance. -/
def qzero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp :=
  Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
    (0 : WkpTensor (I := I) (M := M) g r s k p hp)

/-- Explicit quotient addition, defined by `Quotient.map₂`. -/
def qadd
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp →
      WkpTensorQuot (I := I) (M := M) g r s k p hp →
        WkpTensorQuot (I := I) (M := M) g r s k p hp :=
  Quotient.map₂ (fun S T => S + T) (by
    intro S₁ S₂ hS T₁ T₂ hT
    change TensorAEEq (I := I) (M := M) g S₁.1 S₂.1 at hS
    change TensorAEEq (I := I) (M := M) g T₁.1 T₂.1 at hT
    change TensorAEEq (I := I) (M := M) g
      (S₁.1 + T₁.1) (S₂.1 + T₂.1)
    exact hS.add hT)

/-- Explicit quotient negation, defined by `Quotient.map`. -/
def qneg
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp →
      WkpTensorQuot (I := I) (M := M) g r s k p hp :=
  Quotient.map (fun S => -S) (by
    intro S T h
    change TensorAEEq (I := I) (M := M) g S.1 T.1 at h
    change TensorAEEq (I := I) (M := M) g (-S.1) (-T.1)
    exact h.neg)

/-- Explicit quotient scalar multiplication, defined by `Quotient.map`. -/
def qsmul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (c : ℝ) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp →
      WkpTensorQuot (I := I) (M := M) g r s k p hp :=
  Quotient.map (fun S => c • S) (by
    intro S T h
    change TensorAEEq (I := I) (M := M) g S.1 T.1 at h
    change TensorAEEq (I := I) (M := M) g (c • S.1) (c • T.1)
    exact h.smul c)

/-- Explicit quotient subtraction, defined directly by `Quotient.map₂`. -/
def qsub
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp →
      WkpTensorQuot (I := I) (M := M) g r s k p hp →
        WkpTensorQuot (I := I) (M := M) g r s k p hp :=
  Quotient.map₂ (fun S T => S - T) (by
    intro S₁ S₂ hS T₁ T₂ hT
    change TensorAEEq (I := I) (M := M) g S₁.1 S₂.1 at hS
    change TensorAEEq (I := I) (M := M) g T₁.1 T₂.1 at hT
    change TensorAEEq (I := I) (M := M) g
      (S₁.1 - T₁.1) (S₂.1 - T₂.1)
    exact hS.sub hT)

/-- A chosen genuine tensor Sobolev representative of a quotient class. -/
noncomputable def qrep
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    WkpTensor (I := I) (M := M) g r s k p hp :=
  Quotient.out a

/-- The chosen representative maps back to its original quotient class. -/
theorem qmk_qrep
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
        (qrep (I := I) (M := M) g r s k p hp a) = a :=
  Quotient.out_eq a

@[simp] theorem qadd_mk
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (S T : WkpTensor (I := I) (M := M) g r s k p hp) :
    qadd (I := I) (M := M) g r s k p hp
        (Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S)
        (Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) T) =
      Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S + T) := rfl

@[simp] theorem qneg_mk
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (S : WkpTensor (I := I) (M := M) g r s k p hp) :
    qneg (I := I) (M := M) g r s k p hp
        (Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S) =
      Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (-S) := rfl

@[simp] theorem qsmul_mk
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (c : ℝ)
    (S : WkpTensor (I := I) (M := M) g r s k p hp) :
    qsmul (I := I) (M := M) g r s k p hp c
        (Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S) =
      Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (c • S) := rfl

@[simp] theorem qsub_mk
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (S T : WkpTensor (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp
        (Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S)
        (Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) T) =
      Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S - T) := rfl

/-- Right zero law for explicit quotient addition. -/
theorem qadd_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qadd (I := I) (M := M) g r s k p hp a
      (qzero (I := I) (M := M) g r s k p hp) = a := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S + 0) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S
  rw [add_zero]

/-- Left zero law for explicit quotient addition. -/
theorem qzero_add
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qadd (I := I) (M := M) g r s k p hp
      (qzero (I := I) (M := M) g r s k p hp) a = a := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (0 + S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S
  rw [zero_add]

/-- Associativity of explicit quotient addition. -/
theorem qadd_assoc
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b c : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qadd (I := I) (M := M) g r s k p hp
        (qadd (I := I) (M := M) g r s k p hp a b) c =
      qadd (I := I) (M := M) g r s k p hp a
        (qadd (I := I) (M := M) g r s k p hp b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro S T U
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) ((S + T) + U) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
      (S + (T + U))
  rw [add_assoc]

/-- Commutativity of explicit quotient addition. -/
theorem qadd_comm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qadd (I := I) (M := M) g r s k p hp a b =
      qadd (I := I) (M := M) g r s k p hp b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S + T) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (T + S)
  rw [add_comm]

/-- Negation preserves the explicit zero class. -/
theorem qneg_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    qneg (I := I) (M := M) g r s k p hp
      (qzero (I := I) (M := M) g r s k p hp) =
        qzero (I := I) (M := M) g r s k p hp := by
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp)
        (-(0 : WkpTensor (I := I) (M := M) g r s k p hp)) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) 0
  rw [neg_zero]

/-- Double explicit quotient negation is the identity. -/
theorem qneg_neg
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qneg (I := I) (M := M) g r s k p hp
      (qneg (I := I) (M := M) g r s k p hp a) = a := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (-(-S)) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S
  rw [neg_neg]

/-- A class plus its explicit negation is the zero class. -/
theorem qadd_neg_self
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qadd (I := I) (M := M) g r s k p hp a
      (qneg (I := I) (M := M) g r s k p hp a) =
        qzero (I := I) (M := M) g r s k p hp := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S + -S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) 0
  rw [add_neg_cancel]

/-- Explicit negation plus the original class is the zero class. -/
theorem qneg_add_self
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qadd (I := I) (M := M) g r s k p hp
      (qneg (I := I) (M := M) g r s k p hp a) a =
        qzero (I := I) (M := M) g r s k p hp := by
  rw [qadd_comm (I := I) (M := M) g r s k hp]
  exact qadd_neg_self (I := I) (M := M) g r s k hp a

/-- Explicit negation is scalar multiplication by `-1`. -/
theorem qneg_eq_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qneg (I := I) (M := M) g r s k p hp a =
      qsmul (I := I) (M := M) g r s k p hp (-1) a := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (-S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) ((-1) • S)
  rw [neg_one_smul]

/-- Explicit subtraction is addition with explicit negation. -/
theorem qsub_eq_add_neg
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp a b =
      qadd (I := I) (M := M) g r s k p hp a
        (qneg (I := I) (M := M) g r s k p hp b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S - T) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S + -T)
  rw [sub_eq_add_neg]

/-- Subtracting a class from itself gives the explicit zero class. -/
theorem qsub_self
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp a a =
      qzero (I := I) (M := M) g r s k p hp := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S - S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) 0
  rw [sub_self]

/-- Subtracting the explicit zero class is the identity. -/
theorem qsub_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp a
      (qzero (I := I) (M := M) g r s k p hp) = a := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S - 0) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S
  rw [sub_zero]

/-- The explicit zero class minus a class is its explicit negation. -/
theorem qzero_sub
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp
      (qzero (I := I) (M := M) g r s k p hp) a =
        qneg (I := I) (M := M) g r s k p hp a := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (0 - S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (-S)
  rw [zero_sub]

/-- Reversing an explicit difference negates it. -/
theorem qsub_rev
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp b a =
      qneg (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (T - S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) (-(S - T))
  rw [neg_sub]

/-- A long explicit difference is the sum of two consecutive differences. -/
theorem qsub_chain
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b c : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp a c =
      qadd (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp a b)
        (qsub (I := I) (M := M) g r s k p hp b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro S T U
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S - U) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
      ((S - T) + (T - U))
  have h : S - U = (S - T) + (T - U) := by abel
  rw [h]

/-- An explicit difference is zero exactly when its endpoints agree. -/
theorem qsub_eq_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsub (I := I) (M := M) g r s k p hp a b =
        qzero (I := I) (M := M) g r s k p hp ↔
      a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  constructor
  · intro hzero
    change Quotient.mk
        (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S - T) =
      Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) 0
        at hzero
    have hdiff : TensorAEEq (I := I) (M := M) g (S - T).1
        (0 : RSTensorSection I M r s) := Quotient.exact hzero
    have hST : TensorAEEq (I := I) (M := M) g S.1 T.1 := by
      intro α Idx Jdx
      have hcomp := hdiff α Idx Jdx
      rw [secChartComp_sub (I := I) (M := M),
        secChartComp_zero (I := I) (M := M)] at hcomp
      filter_upwards [hcomp] with y hy
      simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hy
    exact Quotient.sound hST
  · intro heq
    have hST : TensorAEEq (I := I) (M := M) g S.1 T.1 :=
      Quotient.exact heq
    have hdiff : TensorAEEq (I := I) (M := M) g (S - T).1
        (0 : RSTensorSection I M r s) := by
      intro α Idx Jdx
      rw [secChartComp_sub (I := I) (M := M),
        secChartComp_zero (I := I) (M := M)]
      filter_upwards [hST α Idx Jdx] with y hy
      simp only [Pi.sub_apply, Pi.zero_apply, hy, sub_self]
    change Quotient.mk
        (tensorChartSetoid (I := I) (M := M) g r s k p hp) (S - T) =
      Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) 0
    exact Quotient.sound hdiff

/-- The quotient norm vanishes on the explicit zero class. -/
theorem qnorm_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
      (qzero (I := I) (M := M) g r s k p hp) = 0 := by
  change wkpTensorNorm (I := I) (M := M) g k p
    (0 : RSTensorSection I M r s) = 0
  exact wkpTensorNorm_zero (I := I) (M := M) g r s k hp

/-- Triangle inequality for explicit quotient addition. -/
theorem qnorm_add_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qadd (I := I) (M := M) g r s k p hp a b) ≤
      wkpTensorQNorm (I := I) (M := M) g r s k p hp a +
        wkpTensorQNorm (I := I) (M := M) g r s k p hp b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change wkpTensorNorm (I := I) (M := M) g k p (S.1 + T.1) ≤
    wkpTensorNorm (I := I) (M := M) g k p S.1 +
      wkpTensorNorm (I := I) (M := M) g k p T.1
  exact wkpTensorNorm_add_le (I := I) (M := M) g hp S.2 T.2

/-- Homogeneity of the quotient norm for explicit scalar multiplication. -/
theorem qnorm_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (c : ℝ)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsmul (I := I) (M := M) g r s k p hp c a) =
      ‖c‖₊ * wkpTensorQNorm (I := I) (M := M) g r s k p hp a := by
  refine Quotient.inductionOn a ?_
  intro S
  change wkpTensorNorm (I := I) (M := M) g k p (c • S.1) =
    ‖c‖₊ * wkpTensorNorm (I := I) (M := M) g k p S.1
  exact wkpTensorNorm_smul (I := I) (M := M) g hp c S.2

/-- The quotient norm is finite on every quotient class. -/
theorem qnorm_lt_top
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp a < ⊤ := by
  refine Quotient.inductionOn a ?_
  intro S
  change wkpTensorNorm (I := I) (M := M) g k p S.1 < ⊤
  exact wkpTensorNorm_lt_top (I := I) (M := M) g hp S.2

/-- Zero quotient norm separates precisely the explicit zero class. -/
theorem qnorm_eq_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp a = 0 ↔
      a = qzero (I := I) (M := M) g r s k p hp := by
  refine Quotient.inductionOn a ?_
  intro S
  constructor
  · intro hzero
    change wkpTensorNorm (I := I) (M := M) g k p S.1 = 0 at hzero
    have hp_zero : p ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
    have hrel : TensorAEEq (I := I) (M := M) g S.1
        (0 : RSTensorSection I M r s) := by
      intro α Idx Jdx
      have hcomp_le := wkpNorm_secComp_le (I := I) (M := M) g k p
        S.1 α Idx Jdx
      rw [hzero] at hcomp_le
      have hcomp : wkpNorm (d := Module.finrank ℝ E) k p
          (secChartComp (I := I) (M := M) r s S.1 α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) = 0 :=
        le_antisymm hcomp_le (zero_le _)
      have heLp_le := eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) k p
        (chartTargetEuclid (I := I) (M := M) α)
        (secChartComp (I := I) (M := M) r s S.1 α Idx Jdx)
      rw [hcomp] at heLp_le
      have heLp : eLpNorm
          (secChartComp (I := I) (M := M) r s S.1 α Idx Jdx) p
          ((volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) = 0 :=
        le_antisymm heLp_le (zero_le _)
      have hae : secChartComp (I := I) (M := M) r s S.1 α Idx Jdx
          =ᵐ[(volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)] 0 :=
        (eLpNorm_eq_zero_iff
          ((S.2 α Idx Jdx).memLp.aestronglyMeasurable) hp_zero).mp heLp
      rw [secChartComp_zero (I := I) (M := M)]
      exact hae
    change Quotient.mk
        (tensorChartSetoid (I := I) (M := M) g r s k p hp) S =
      Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
        (0 : WkpTensor (I := I) (M := M) g r s k p hp)
    exact Quotient.sound hrel
  · intro heq
    rw [heq]
    exact qnorm_zero (I := I) (M := M) g r s k hp

/-- Explicit quotient negation preserves the quotient norm. -/
theorem qnorm_neg
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qneg (I := I) (M := M) g r s k p hp a) =
      wkpTensorQNorm (I := I) (M := M) g r s k p hp a := by
  rw [qneg_eq_smul (I := I) (M := M) g r s k hp,
    qnorm_smul (I := I) (M := M) g r s k hp]
  norm_num

/-- The norm of an explicit difference is symmetric in its endpoints. -/
theorem qnorm_sub_symm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp a b) =
      wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp b a) := by
  rw [qsub_rev (I := I) (M := M) g r s k hp a b,
    qnorm_neg (I := I) (M := M) g r s k hp]

/-- Triangle inequality for norms of consecutive explicit differences. -/
theorem qnorm_sub_triangle
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b c : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp a c) ≤
      wkpTensorQNorm (I := I) (M := M) g r s k p hp
          (qsub (I := I) (M := M) g r s k p hp a b) +
        wkpTensorQNorm (I := I) (M := M) g r s k p hp
          (qsub (I := I) (M := M) g r s k p hp b c) := by
  rw [qsub_chain (I := I) (M := M) g r s k hp a b c]
  exact qnorm_add_le (I := I) (M := M) g r s k hp _ _

/-- The norm of an explicit difference is zero exactly when its endpoints
agree. -/
theorem qnorm_sub_sep
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp a b) = 0 ↔
      a = b := by
  rw [qnorm_eq_zero (I := I) (M := M) g r s k hp,
    qsub_eq_zero (I := I) (M := M) g r s k hp]

/-- The ordinary real-valued distance function underlying a possible later
metric package.  It is kept as a plain function in this file. -/
def qdist
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) : ℝ :=
  (wkpTensorQNorm (I := I) (M := M) g r s k p hp
    (qsub (I := I) (M := M) g r s k p hp a b)).toReal

/-- The explicit real-valued quotient distance is nonnegative. -/
theorem qdist_nonneg
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    0 ≤ qdist (I := I) (M := M) g r s k p hp a b :=
  ENNReal.toReal_nonneg

/-- The explicit real-valued quotient distance is symmetric. -/
theorem qdist_symm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qdist (I := I) (M := M) g r s k p hp a b =
      qdist (I := I) (M := M) g r s k p hp b a := by
  unfold qdist
  rw [qnorm_sub_symm (I := I) (M := M) g r s k hp]

/-- The explicit real-valued quotient distance separates points. -/
theorem qdist_eq_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qdist (I := I) (M := M) g r s k p hp a b = 0 ↔ a = b := by
  unfold qdist
  constructor
  · intro hzero
    rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with hqzero | hqtop
    · exact (qnorm_sub_sep (I := I) (M := M) g r s k hp a b).mp hqzero
    · exact ((qnorm_lt_top (I := I) (M := M) g r s k hp
        (qsub (I := I) (M := M) g r s k p hp a b)).ne hqtop).elim
  · intro hab
    apply (ENNReal.toReal_eq_zero_iff _).mpr
    exact Or.inl ((qnorm_sub_sep (I := I) (M := M) g r s k hp a b).mpr hab)

/-- The explicit real-valued quotient distance vanishes on the diagonal. -/
theorem qdist_self
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qdist (I := I) (M := M) g r s k p hp a a = 0 :=
  (qdist_eq_zero (I := I) (M := M) g r s k hp a a).mpr rfl

/-- Triangle inequality for the explicit real-valued quotient distance. -/
theorem qdist_triangle
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a b c : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qdist (I := I) (M := M) g r s k p hp a c ≤
      qdist (I := I) (M := M) g r s k p hp a b +
        qdist (I := I) (M := M) g r s k p hp b c := by
  unfold qdist
  have hab_ne : wkpTensorQNorm (I := I) (M := M) g r s k p hp
      (qsub (I := I) (M := M) g r s k p hp a b) ≠ ⊤ :=
    (qnorm_lt_top (I := I) (M := M) g r s k hp
      (qsub (I := I) (M := M) g r s k p hp a b)).ne
  have hbc_ne : wkpTensorQNorm (I := I) (M := M) g r s k p hp
      (qsub (I := I) (M := M) g r s k p hp b c) ≠ ⊤ :=
    (qnorm_lt_top (I := I) (M := M) g r s k hp
      (qsub (I := I) (M := M) g r s k p hp b c)).ne
  have hq := qnorm_sub_triangle (I := I) (M := M) g r s k hp a b c
  exact (ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hab_ne, hbc_ne⟩) hq).trans
      ENNReal.toReal_add_le

/-- Explicit theorem-valued completeness on quotient sequences, stated only
with `qsub` and `wkpTensorQNorm`.  No metric or complete-space instance is
needed: every q-norm Cauchy sequence has a quotient class whose q-norm
differences tend to zero. -/
theorem qCauchy_limit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensorQuot (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp (u m) (u n)) ≤
          ENNReal.ofReal ε) :
    ∃ v : WkpTensorQuot (I := I) (M := M) g r s k p hp,
      Tendsto
        (fun n => wkpTensorQNorm (I := I) (M := M) g r s k p hp
          (qsub (I := I) (M := M) g r s k p hp (u n) v))
        atTop (𝒩 0) := by
  let rep : ℕ → WkpTensor (I := I) (M := M) g r s k p hp := fun n =>
    qrep (I := I) (M := M) g r s k p hp (u n)
  have hrep_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((rep m).1 - (rep n).1) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := h_cauchy ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hq := hN m n hm hn
    rw [← qmk_qrep (I := I) (M := M) g r s k p hp (u m),
      ← qmk_qrep (I := I) (M := M) g r s k p hp (u n)] at hq
    change wkpTensorNorm (I := I) (M := M) g k p
      ((rep m).1 - (rep n).1) ≤ ENNReal.ofReal ε at hq
    exact hq
  obtain ⟨v, hv⟩ :=
    wkpTensor_limit (I := I) (M := M) g r s k hp hp_top rep hrep_cauchy
  refine ⟨Quotient.mk
    (tensorChartSetoid (I := I) (M := M) g r s k p hp) v, ?_⟩
  have heq :
      (fun n => wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp (u n)
          (Quotient.mk
            (tensorChartSetoid (I := I) (M := M) g r s k p hp) v))) =
        (fun n => wkpTensorNorm (I := I) (M := M) g k p
          ((rep n).1 - v.1)) := by
    funext n
    rw [← qmk_qrep (I := I) (M := M) g r s k p hp (u n)]
    rfl
  rw [heq]
  exact hv

/-- Explicit metric-form completeness for the tensor chart-Sobolev quotient.
This is the consumer-facing version of `qCauchy_limit`: a sequence which is
Cauchy for the ordinary real-valued function `qdist` has a quotient limit in
that same distance.  No metric-space or complete-space instance is installed.
-/
theorem qdist_limit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensorQuot (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      qdist (I := I) (M := M) g r s k p hp (u m) (u n) < ε) :
    ∃ v : WkpTensorQuot (I := I) (M := M) g r s k p hp,
      Tendsto
        (fun n => qdist (I := I) (M := M) g r s k p hp (u n) v)
        atTop (𝓝 0) := by
  have hq_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp (u m) (u n)) ≤
          ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := h_cauchy ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hlt := hN m n hm hn
    have hfinite : wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsub (I := I) (M := M) g r s k p hp (u m) (u n)) ≠ ∞ :=
      (qnorm_lt_top (I := I) (M := M) g r s k hp
        (qsub (I := I) (M := M) g r s k p hp (u m) (u n))).ne
    apply (ENNReal.le_ofReal_iff_toReal_le hfinite hε.le).2
    simpa only [qdist] using hlt.le
  obtain ⟨v, hv⟩ :=
    qCauchy_limit (I := I) (M := M) g r s k hp hp_top u hq_cauchy
  refine ⟨v, ?_⟩
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hv
  simpa only [qdist, Function.comp_apply, ENNReal.toReal_zero] using hreal

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
