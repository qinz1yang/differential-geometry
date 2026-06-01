import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Integral.Connection.Tensor0SChartChristoffel
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian

/-!
# Chart-frame covariant derivative on `(0, s)`-tensor bundles

Given a smooth Riemannian manifold `(M, g)` and a chart center `α : M`, this
file constructs a *chart-frame* analog of the covariant derivative
`(∇_X T)(b) ∈ Tensor0SSpace s I b` for a `(0, s)`-tensor section `T` and a
tangent vector field `X`. The construction uses only chart-coordinate
ingredients (Fréchet derivative of the trivialised representation +
Christoffel correction), without invoking any abstract `CovariantDerivative`
typeclass on the tensor bundle.

For `s = 0`, the chart-frame covariant derivative acts as the directional
derivative of the scalar value. For `s = s' + 1`, it is the standard Leibniz
combination: the **intrinsic chart piece**
`tensor0SIntrinsicChartCLM (s+1) α T b (X b)` (from
`Tensor0SChartChristoffel.lean`) minus a **per-slot Christoffel correction**
obtained by composing the tensor `T b` with a slot-by-slot CLM substitution.

The slot CLM is the explicit linear formula
`v ↦ trivFromE α b (christoffelCorrection g α b (trivToE α b v) (X b))`,
which agrees with `chartLeviCivita g α (chartParallelExtend α b v) b (X b)`
on the chart Levi-Civita good set; that agreement is deferred to a later
file and is not required for the construction itself.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- The chart-α-parallel extension of a tangent vector at `b` across `M`,
defined via the chart-α trivialisation. -/
def chartParallelExtend (α b : M) (v : TangentSpace I b) (b' : M) :
    TangentSpace I b' :=
  trivFromE (I := I) α b' (trivToE (I := I) α b v)

/-- Pointwise unfolding of `chartParallelExtend`. -/
lemma chartParallelExtend_def (α b : M) (v : TangentSpace I b) (b' : M) :
    chartParallelExtend (I := I) α b v b' =
      trivFromE (I := I) α b' (trivToE (I := I) α b v) := rfl

/-- The chart-trivialised representation of the parallel extension equals the
constant `trivToE α b v` on the trivialisation base set. -/
lemma chartE_section_repr_chartParallelExtend
    (α b : M) (v : TangentSpace I b) {b' : M}
    (hb' : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v) b' =
      trivToE (I := I) α b v := by
  classical
  unfold chartParallelExtend
  change trivToE (I := I) α b' (trivFromE (I := I) α b' (trivToE (I := I) α b v))
      = trivToE (I := I) α b v
  exact trivToE_trivFromE (I := I) α hb' _

/-- The chart-α Levi-Civita-parallel CLM at `b`, applied along the vector
field `X`. On the chart Levi-Civita good set, this evaluates to the chart
Levi-Civita action on the parallel extension of its input. -/
def chartLeviCivitaParallelCLM
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') :
    TangentSpace I b →L[ℝ] TangentSpace I b :=
  (trivFromE (I := I) α b).comp
    (christoffelCorrection (I := I) g α b
      (trivToE (I := I) α b (X b)))

/-- Pointwise formula. -/
lemma chartLeviCivitaParallelCLM_apply
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') (v : TangentSpace I b) :
    chartLeviCivitaParallelCLM (I := I) g α b X v =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b)) v) := by
  classical
  unfold chartLeviCivitaParallelCLM
  rfl

/-- The slot-substitution function: identity on every coordinate except slot
`k`, where it places the given CLM `Φ`. -/
private def slotCLM (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin s) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

/-- Slot-substitution value at slot `k`. -/
private lemma slotCLM_self (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    slotCLM (I := I) s k Φ k = Φ := by
  unfold slotCLM
  simp

/-- Slot-substitution value at slot `i ≠ k`. -/
private lemma slotCLM_other (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin s} (h : i ≠ k) :
    slotCLM (I := I) s k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold slotCLM
  simp [h]

/-- The slot-`k` Christoffel correction term, as a `Tensor0SSpace s I b`.

This is the CMLM whose value at a tuple `(v₀, …, v_{s-1})` is
`T b (Fin.update m k (chartLeviCivitaParallelCLM g α b X (m k)))`. -/
def chartTensor0SSlotCorrection (s : ℕ) (g : SmoothRiemannianMetric I M)
    (α : M) (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    Tensor0SSpace s I b :=
  ContinuousMultilinearMap.compContinuousLinearMap
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from T b)
    (slotCLM (I := I) s k (chartLeviCivitaParallelCLM (I := I) g α b X))

/-- Pointwise formula for the slot-`k` Christoffel correction. -/
lemma chartTensor0SSlotCorrection_apply (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s)
    (m : Fin s → TangentSpace I b) :
    chartTensor0SSlotCorrection (I := I) s g α T X b k m =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from T b)
        (fun i =>
          slotCLM (I := I) s k
              (chartLeviCivitaParallelCLM (I := I) g α b X) i (m i)) := by
  classical
  unfold chartTensor0SSlotCorrection
  rfl

/-- The chart-frame covariant derivative of a `(0, s)`-tensor field along a
tangent vector field, returning a section of the `(0, s)`-tensor bundle. -/
def chartTensor0SCovariantDerivative :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) →
      (T : Π b : M, Tensor0SSpace s I b) →
      (X : Π b : M, TangentSpace I b) →
      (b : M) → Tensor0SSpace s I b
  | 0, _g, _α, T, X, b =>
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I b) ℝ from
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I b)
          (mfderiv I 𝓘(ℝ) (fun b' : M =>
              (show ContinuousMultilinearMap ℝ
                  (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
              (fun i => Fin.elim0 i)) b (X b)))
  | s + 1, g, α, T, X, b =>
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k

/-- Unfolding for `s = 0`. -/
lemma chartTensor0SCovariantDerivative_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensor0SCovariantDerivative (I := I) 0 g α T X b =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I b) ℝ from
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I b)
          (mfderiv I 𝓘(ℝ) (fun b' : M =>
              (show ContinuousMultilinearMap ℝ
                  (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
              (fun i => Fin.elim0 i)) b (X b))) := rfl

/-- Unfolding for `s = s' + 1`. -/
lemma chartTensor0SCovariantDerivative_succ (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b =
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := rfl

/-- Evaluation at the unique empty tuple in the `s = 0` case. -/
lemma chartTensor0SCovariantDerivative_zero_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (m : Fin 0 → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I b) ℝ from
      chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m =
      mfderiv I 𝓘(ℝ) (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
        (fun i => Fin.elim0 i)) b (X b) := by
  classical
  rw [chartTensor0SCovariantDerivative_zero]
  rfl

/-- Evaluation at a non-empty tuple in the `s = s' + 1` case. -/
lemma chartTensor0SCovariantDerivative_succ_apply (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (m : Fin (s + 1) → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)) m
      - ∑ k : Fin (s + 1),
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) m := by
  classical
  rw [chartTensor0SCovariantDerivative_succ]
  rw [show (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
          - ∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)) m
      - (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        ∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) m by
    rfl]
  congr 1
  set Y : Fin (s + 1) → Tensor0SSpace (s + 1) I b :=
    fun k => chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k
  have hY : (∑ k : Fin (s + 1), Y k) = ∑ k : Fin (s + 1), Y k := rfl
  change (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        ∑ k : Fin (s + 1), Y k) m = _
  rw [ContinuousMultilinearMap.sum_apply]

/-- **Additivity in `T` (`s = 0` case).** -/
lemma chartTensor0SCovariantDerivative_zero_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : MDiffAt
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T₁ b')
          (fun i => Fin.elim0 i)) b)
    (h₂ : MDiffAt
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T₂ b')
          (fun i => Fin.elim0 i)) b) :
    chartTensor0SCovariantDerivative (I := I) 0 g α (T₁ + T₂) X b =
      chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b
        + chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 0 => TangentSpace I b) ℝ from
        chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b
          + chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b) m =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b) m
          + (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b) ℝ from
            chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b) m := by
    rfl
  rw [hRHS]
  rw [chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply]
  have hpw :
      (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from (T₁ + T₂) b')
          (fun i => Fin.elim0 i)) =
        (fun b' : M =>
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin 0 => TangentSpace I b') ℝ from T₁ b')
            (fun i => Fin.elim0 i)) +
          (fun b' : M =>
              (show ContinuousMultilinearMap ℝ
                  (fun _ : Fin 0 => TangentSpace I b') ℝ from T₂ b')
              (fun i => Fin.elim0 i)) := by
    funext b'
    exact ContinuousMultilinearMap.add_apply
      (f := (T₁ b' : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ))
      (f' := (T₂ b' : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ))
      (fun i : Fin 0 => Fin.elim0 i)
  rw [hpw]
  rw [mfderiv_add h₁ h₂]
  rfl

/-- **Scalar homogeneity in `T` (`s = 0` case).** -/
lemma chartTensor0SCovariantDerivative_zero_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : MDiffAt
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i => Fin.elim0 i)) b) :
    chartTensor0SCovariantDerivative (I := I) 0 g α (c • T) X b =
      c • chartTensor0SCovariantDerivative (I := I) 0 g α T X b := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 0 => TangentSpace I b) ℝ from
        c • chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m =
        c • (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m := by
    rfl
  rw [hRHS]
  rw [chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply]
  have hpw :
      (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from (c • T) b')
          (fun i => Fin.elim0 i)) =
        c • (fun b' : M =>
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
            (fun i => Fin.elim0 i)) := by
    funext b'
    exact ContinuousMultilinearMap.smul_apply
      (f := (T b' : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ)) c
      (fun i : Fin 0 => Fin.elim0 i)
  rw [hpw]
  rw [const_smul_mfderiv hT c]
  rfl

/-- The slot-`k` correction is additive in `T`. -/
lemma chartTensor0SSlotCorrection_add (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α (T₁ + T₂) X b k =
      chartTensor0SSlotCorrection (I := I) s g α T₁ X b k
        + chartTensor0SSlotCorrection (I := I) s g α T₂ X b k := by
  classical
  unfold chartTensor0SSlotCorrection
  have hT_add : ((T₁ + T₂) b
        : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) =
      (T₁ b : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ)
        + (T₂ b : ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ) := by
    rfl
  rw [hT_add]
  apply ContinuousMultilinearMap.ext
  intro m
  rfl

/-- The slot-`k` correction is `ℝ`-linear in `T`. -/
lemma chartTensor0SSlotCorrection_smul (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α (c • T) X b k =
      c • chartTensor0SSlotCorrection (I := I) s g α T X b k := by
  classical
  unfold chartTensor0SSlotCorrection
  have hT_smul : ((c • T) b
        : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) =
      c • (T b : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) := by
    rfl
  rw [hT_smul]
  apply ContinuousMultilinearMap.ext
  intro m
  rfl

/-- **Additivity in `T` (`s = s' + 1` case).** -/
lemma chartTensor0SCovariantDerivative_succ_add (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α (T₁ + T₂) X b =
      chartTensor0SCovariantDerivative (I := I) (s + 1) g α T₁ X b
        + chartTensor0SCovariantDerivative (I := I) (s + 1) g α T₂ X b := by
  classical
  rw [chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ]
  have hsplit_intrinsic :
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α (T₁ + T₂) b (X b) =
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T₁ b (X b) +
          tensor0SIntrinsicChartCLM (I := I) (s + 1) α T₂ b (X b) := by
    have hCLM := tensor0SIntrinsicChartCLM_add_section
      (I := I) (s + 1) α T₁ T₂ b h₁ h₂
    have := congrArg (fun L : TangentSpace I b →L[ℝ] Tensor0SSpace (s + 1) I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_slot :
      (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (T₁ + T₂) X b k) =
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T₁ X b k) +
          (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T₂ X b k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact chartTensor0SSlotCorrection_add (I := I) (s + 1) g α T₁ T₂ X b k
  rw [hsplit_slot]
  abel

/-- **Scalar homogeneity in `T` (`s = s' + 1` case).** -/
lemma chartTensor0SCovariantDerivative_succ_smul (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α (c • T) X b =
      c • chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b := by
  classical
  rw [chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ]
  have hsplit_intrinsic :
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α (c • T) b (X b) =
        c • tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b) := by
    have hCLM := tensor0SIntrinsicChartCLM_smul_section
      (I := I) (s + 1) α c T b hT
    have := congrArg (fun L : TangentSpace I b →L[ℝ] Tensor0SSpace (s + 1) I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_slot :
      (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (c • T) X b k) =
        c • (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) := by
    have hterm :
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α (c • T) X b k) =
          ∑ k : Fin (s + 1),
            c • chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact chartTensor0SSlotCorrection_smul (I := I) (s + 1) g α c T X b k
    rw [hterm]
    classical
    have hmap :
        c • (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) =
          ∑ k : Fin (s + 1),
            c • chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := by
      have hLM := map_sum (LinearMap.lsmul ℝ (Tensor0SSpace (s + 1) I b) c)
          (fun k => chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k)
          Finset.univ
      exact hLM
    rw [hmap]
  rw [hsplit_slot]
  have hsub :
      c • (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b) (X b)
        - c • (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) =
      c • ((tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b) (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) :=
    ((LinearMap.lsmul ℝ (Tensor0SSpace (s + 1) I b) c).map_sub
        (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k)).symm
  exact hsub

end Connection
end Integral
end DifferentialGeometry
