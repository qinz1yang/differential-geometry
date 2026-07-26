import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import Mathlib.GroupTheory.Perm.Fin

/-!
# Slot-permutation naturality of the covariant gradient

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
the Levi-Civita-induced covariant derivative of `(0, s)`-tensor sections commutes with a
**constant slot reindexing** of the section: reindexing the `Fin s` covariant slots of a tensor
section by a fixed permutation `σ : Equiv.Perm (Fin s)` is a *parallel* bundle automorphism
(it is the same point-independent reindexing at every fibre, `∇σ = 0`), so the directional
covariant derivative `tensorCovDerivAt` of the reindexed section is the same reindexing of the
directional covariant derivative.

This file isolates that naturality (`tensorCovDerivAt_unit_toModel_domDomCongr_of_section`) and
uses it to track how the iterated covariant gradient `iteratedCovGrad` of a slot-reindexed
`(0, s)`-tensor relates to that of the original tensor: at every order `i` the two iterated
gradients differ by a (single, order-dependent) slot permutation of the model fibre
(`exists_iteratedCovGrad_unit_toModel_domDomCongr`).  Combined with the slot-permutation
invariance of the pointwise inner product (`tensorInnerPointwise_0s_domDomCongr`), this shows
that a slot reindexing — being a fibre isometry — preserves the `g`-fibre norm of every
iterated covariant gradient.

## The reindexing is read off the unit-evaluated section

An `(0, s)`-tensor `T : TensorRSSpace 0 s I x = Tensor0SSpace 0 I x →L Tensor0SSpace s I x` is
recovered from its value on the canonical unit `(0, 0)`-tensor `unit = ofModel (constOfIsEmpty
1)`: the `(0, s)`-multilinear form `Tensor0SSpace.toModel (T unit)`.  All statements here are
phrased through this unit-evaluation, which is exactly the form in which the iterated covariant
gradient is read off (`covGrad_toSection_apply_eval`).

## Main results

* `tensorCovDerivAt_unit_toModel_domDomCongr_of_section` — *the posited naturality core*: if two
  smooth `(0, s)`-tensor sections `S, S'` are related fibrewise by a constant slot reindexing
  `σ` (on their unit-evaluated model forms), then their directional covariant derivatives are
  related by the same `σ`.  This is the precise reusable "the Levi-Civita covariant derivative
  commutes with a constant slot reindex (a parallel fibre isometry)" primitive.

* `exists_iteratedCovGrad_unit_toModel_domDomCongr` — for two such related sections, at every
  order `i` there is a slot permutation `σ'` of `Fin (s + i)` relating the unit-evaluated model
  forms of the iterated covariant gradients `∇^i S'` and `∇^i S`.

* `riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr` — the consequence used by
  the metric-realization jet bound: a slot reindexing preserves the `g`-Riemannian fibre norm
  squared of every iterated covariant gradient.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The canonical unit `(0, 0)`-tensor `ofModel (constOfIsEmpty 1)` at a base point `x`, used to
read off an `(0, s)`-tensor `T : Tensor0SSpace 0 I x →L Tensor0SSpace s I x` as the `(0, s)`-form
`Tensor0SSpace.toModel (T unit)`. -/
def unitTensor (x : M) : Tensor0SSpace 0 I x :=
  Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))

/-- The unit-evaluated model `(0, s)`-form of a smooth compactly-supported `(0, s)`-tensor
section at `x`: `Tensor0SSpace.toModel (W.toSection x unit)`.  An `(0, s)`-tensor section value
`W.toSection x : Tensor0SSpace 0 I x →L Tensor0SSpace s I x` is recovered from this `(0, s)`-form
(evaluation at the canonical unit `(0, 0)`-tensor), which is the shape in which the iterated
covariant gradient is read off (`covGrad_toSection_apply_eval`). -/
def unitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))

/-- The unit-evaluated model `(0, s)`-form of the directional covariant derivative
`tensorCovDerivAt g 0 s W x v`. -/
private def covDerivUnitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g 0 s W x v)
      (unitTensor (I := I) (M := M) x))

/-- The unit-evaluated `(0, s)`-tensor section `y ↦ (W.toSection y) (unit)`, an abstract
`(0, s)`-tensor section whose `toModel` is the `unitModel`. -/
private def unitEvalSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) : Π y : M, Tensor0SSpace s I y :=
  fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from W.toSection y)
      (unitTensor (I := I) (M := M) y)

/-- **Step 1 — the directional cov-deriv at the unit reduces to the bundled `(0, s)`-cov-deriv
of the unit-evaluated section.**  `covDerivUnitModel W x v` is `toModel` of the bundled
`tensor0SCovariantDerivative` of `unitEvalSection W` at `x`, evaluated along `v`.  The unit
`(0, 0)`-tensor is `∇`-parallel, so the product rule `tensorRSCovariantDerivative_zeroS_unit_eval`
has no correction term. -/
private lemma covDerivUnitModel_eq_tensor0SCovariantDerivative
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) :
    covDerivUnitModel (I := I) (M := M) g s W x v =
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M s
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
          (unitEvalSection (I := I) (M := M) g s W) x v) := by
  rw [covDerivUnitModel, tensorCovDerivAt_def]
  congr 1
  exact tensorRSCovariantDerivative_zeroS_unit_eval
    (I := I) (M := M) g s W.toSection x v

/-- **Forward chart-trivialisation formula (on the base set).**  The chart-`α` trivialised
representation of `(0, s)`-tensor section `T` at `b ∈ baseSet`, evaluated on a model tuple `v`,
precomposes each slot of `T b` with the tangent-bundle trivialisation inverse `symmL b`. -/
private lemma tensor0SChartE_section_repr_apply_tuple
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : Fin s → E) :
    DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α T b v =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from T b)
        (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ b (v i)) := by
  classical
  rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply]
  set e := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with he
  have hbE : b ∈ e.baseSet := hb
  rw [e.continuousLinearMapAt_apply ℝ, e.coe_linearMapAt_of_mem hbE]
  rfl

/-- **The chart-trivialised representation commutes with a constant slot reindexing.**  The
chart-`α` trivialisation of the `(0, s)`-tensor bundle precomposes each slot with the *same*
tangent-bundle trivialisation map, so it commutes with the slot permutation `domDomCongr σ`.
This holds globally: on the trivialisation base set by the slot-uniform formula, and off it
because both sides vanish. -/
private lemma tensor0SChartE_section_repr_domDomCongr
    (s : ℕ) (σ : Equiv.Perm (Fin s)) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) b =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α T b) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  by_cases hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet
  · rw [tensor0SChartE_section_repr_apply_tuple (I := I) s α _ b hb v,
      ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.domDomCongr_apply,
      tensor0SChartE_section_repr_apply_tuple (I := I) s α T b hb (fun i => v (σ i))]
  · -- Off the base set: both representations vanish.
    set e := trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α with he
    have hbE : b ∉ e.baseSet := hb
    rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
      e.continuousLinearMapAt_apply ℝ, e.linearMapAt_def_of_notMem hbE]
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
      e.continuousLinearMapAt_apply ℝ, e.linearMapAt_def_of_notMem hbE]
    simp

/-- **Pointwise inverse chart-trivialisation formula (on the base set).**  The inverse
chart-`α` trivialisation `tensor0SChartFiberFromModel` of a model form `M0`, evaluated on a
tangent tuple `v`, precomposes each slot with the tangent-bundle trivialisation `continuousLinearMapAt`. -/
private lemma tensor0SChartFiberFromModel_apply_tuple
    (s : ℕ) (α : M) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (M0 : Tensor0SModel s ℝ E) (v : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from
        DifferentialGeometry.Integral.Connection.tensor0SChartFiberFromModel (I := I) s α b M0) v =
      M0 (fun i => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b (v i)) := by
  classical
  have h := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap (𝕜 := ℝ)
    (F := E) (E := TangentSpace I) (s := s) α b hb M0
  have h2 := DFunLike.congr_fun h v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  exact h2

/-- **The fibre-from-model map commutes with a constant slot reindexing (on the base set).**
The inverse chart-`α` trivialisation `tensor0SChartFiberFromModel` precomposes each slot with
the *same* tangent-bundle trivialisation map, so it commutes with the slot reindexing
`domDomCongr σ`. -/
private lemma tensor0SChartFiberFromModel_domDomCongr
    (s : ℕ) (σ : Equiv.Perm (Fin s)) (α : M) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (M0 : Tensor0SModel s ℝ E) :
    DifferentialGeometry.Integral.Connection.tensor0SChartFiberFromModel (I := I) s α b
        (ContinuousMultilinearMap.domDomCongr σ M0) =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.tensor0SChartFiberFromModel (I := I) s α b M0) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensor0SChartFiberFromModel_apply_tuple (I := I) s α b hb (ContinuousMultilinearMap.domDomCongr σ M0) v]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [tensor0SChartFiberFromModel_apply_tuple (I := I) s α b hb M0 (fun i => v (σ i))]

/-- **The intrinsic chart-Fréchet piece commutes with a constant slot reindexing (on the base
set).**  The intrinsic chart-`α` Fréchet-derivative CLM `tensor0SIntrinsicChartCLM` differentiates
the chart-trivialised model-valued representation; reindexing the slots by `σ` is post-composition
with the constant fibre isometry `domDomCongr σ`, which `fderiv` (`ContinuousLinearEquiv.comp_fderiv`)
and the inverse trivialisation both commute with. -/
private lemma tensor0SIntrinsicChartCLM_domDomCongr
    (s : ℕ) (σ : Equiv.Perm (Fin s)) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I b) :
    DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM (I := I) s α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) b v =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM (I := I) s α T b v) := by
  classical
  rw [DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM_apply,
    DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM_apply]

  set L : Tensor0SModel s ℝ E ≃L[ℝ] Tensor0SModel s ℝ E :=
    (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ σ).toContinuousLinearEquiv with hL
  have hpull :
      (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α
          (fun y => ContinuousMultilinearMap.domDomCongr σ
            (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) ∘
        (extChartAt I α).symm) =
      (⇑L) ∘
        (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α T ∘
          (extChartAt I α).symm) := by
    funext z
    simp only [Function.comp_apply]
    rw [tensor0SChartE_section_repr_domDomCongr (I := I) s σ α T ((extChartAt I α).symm z)]
    rw [hL, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  rw [hpull]
  rw [L.comp_fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [hL, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

  rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ σ)
        ((fderiv ℝ (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr
            (I := I) s α T ∘ (extChartAt I α).symm) (extChartAt I α b))
          (DifferentialGeometry.Integral.Connection.trivToE (I := I) α b v)) =
      ContinuousMultilinearMap.domDomCongr σ
        ((fderiv ℝ (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr
            (I := I) s α T ∘ (extChartAt I α).symm) (extChartAt I α b))
          (DifferentialGeometry.Integral.Connection.trivToE (I := I) α b v)) from rfl]

  rw [tensor0SChartFiberFromModel_domDomCongr (I := I) s σ α b hb]

/-- **The slot-`k` substitution CLM is `σ`-reindexed by relocating the active slot.**  The slot
substitution `localSlotCLM s k Φ` puts `Φ` at slot `k` and the identity elsewhere; precomposing
the slot index with `σ` relocates the active slot to `σ.symm k`. -/
private lemma localSlotCLM_comp_perm
    (s : ℕ) (σ : Equiv.Perm (Fin s)) {b : M} (k : Fin s)
    (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) (i : Fin s) :
    DifferentialGeometry.Integral.Connection.localSlotCLM s k Φ (σ i) =
      DifferentialGeometry.Integral.Connection.localSlotCLM s (σ.symm k) Φ i := by
  by_cases hi : i = σ.symm k
  · subst hi
    rw [Equiv.apply_symm_apply,
      DifferentialGeometry.Integral.Connection.localSlotCLM_self,
      DifferentialGeometry.Integral.Connection.localSlotCLM_self]
  · rw [DifferentialGeometry.Integral.Connection.localSlotCLM_other s k Φ
        (by intro h; exact hi (by rw [← Equiv.symm_apply_apply σ i, h])),
      DifferentialGeometry.Integral.Connection.localSlotCLM_other s (σ.symm k) Φ hi]

/-- **The slot-correction sum commutes with a constant slot reindexing.**  Reindexing the slots
of the tensor by `σ` and summing the Christoffel slot corrections over all slots agree with the
slot reindexing applied to the original slot-correction sum, because the per-slot active index is
relocated bijectively by `σ`. -/
private lemma chartTensor0SSlotCorrection_sum_domDomCongr
    (s : ℕ) (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin s)) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (X : Π b : M, TangentSpace I b) (b : M) :
    ∑ k : Fin s, DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection (I := I) s g α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) X b k =
      ContinuousMultilinearMap.domDomCongr σ
        (∑ k : Fin s, DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection (I := I) s g α
          T X b k) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]

  rw [← Equiv.sum_comp σ.symm (fun k => DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection
    (I := I) s g α T X b k (fun i => m (σ i)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM,
    DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM]

  rw [ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg _ ?_
  funext i
  rw [localSlotCLM_comp_perm (I := I) s σ k]

/-- **A constant slot reindexing respects subtraction.** -/
private lemma domDomCongr_sub
    {n : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (σ : Equiv.Perm (Fin n)) (a b : ContinuousMultilinearMap ℝ (fun _ : Fin n => A) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (a - b) =
      ContinuousMultilinearMap.domDomCongr σ a - ContinuousMultilinearMap.domDomCongr σ b := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

/-- **Chart-frame σ-naturality (succ, on the good set).**  At a base point `b` in the chart-`α`
good set, the chart-frame covariant derivative of the slot-reindexed `(0, s + 1)`-tensor section
`fun y => domDomCongr σ (T y)` along `X` equals the slot reindexing `domDomCongr σ` of the
chart-frame covariant derivative of `T`.  Assembled from the intrinsic-piece naturality
`tensor0SIntrinsicChartCLM_domDomCongr` and the slot-correction-sum naturality
`chartTensor0SSlotCorrection_sum_domDomCongr` through the explicit succ decomposition. -/
private lemma chartTensor0SCovariantDerivative_succ_domDomCongr
    (s : ℕ) (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin (s + 1))) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b) (X : Π b : M, TangentSpace I b) {b : M}
    (hb : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α) :
    DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative (I := I) (s + 1) g α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from T y)) X b =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative (I := I) (s + 1) g α
          T X b) := by
  classical
  have hbE : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_mem_baseSet hb
  rw [DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_succ (I := I) s g α
      (fun y => ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from T y)) X b,
    DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_succ (I := I) s g α T X b]
  rw [domDomCongr_sub σ
    (DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
    (∑ k : Fin (s + 1), DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection
      (I := I) (s + 1) g α T X b k)]
  rw [tensor0SIntrinsicChartCLM_domDomCongr (I := I) (s + 1) σ α T b hbE (X b)]
  rw [chartTensor0SSlotCorrection_sum_domDomCongr (I := I) (s + 1) g σ α T X b]

/-- **Smoothness of the unit-evaluated section.**  The unit-evaluated `(0, s)`-tensor section
`unitEvalSection g s W = fun y => (W.toSection y) (unit)` is `MDifferentiableAt` (in total-space
form) at every point: it is the smooth Hom-bundle section `W.toSection` applied to the smooth
constant unit `(0, 0)`-section. -/
private lemma unitEvalSection_tensorSectionMDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s
      (unitEvalSection (I := I) (M := M) g s W) x := by
  classical
  have hHom : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w →L[ℝ] Tensor0SSpace s I w) z
        (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace s I z from W.toSection z)) x :=
    (W.toSection.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w) z (unitTensor (I := I) (M := M) z)) x :=
    (DifferentialGeometry.Integral.Connection.contMDiff_unitZeroSection
      (I := I) (M := M)).contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHom hv

/-- A constant slot reindexing commutes with a finite `•`-combination. -/
private lemma domDomCongr_finsum_smul
    {n d : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (σ : Equiv.Perm (Fin n)) (c : Fin d → ℝ)
    (a : Fin d → ContinuousMultilinearMap ℝ (fun _ : Fin n => A) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (∑ i, c i • a i) =
      ∑ i, c i • ContinuousMultilinearMap.domDomCongr σ (a i) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

lemma tensor0SCovariantDerivative_succ_domDomCongr
    (s : ℕ) (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin (s + 1)))
    (ŝ ŝ' : Π y : M, Tensor0SSpace (s + 1) I y) (x : M) (v : TangentSpace I x)
    (hŝ : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) (s + 1) ŝ x)
    (hŝ' : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) (s + 1) ŝ' x)
    (hrel : ∀ y : M, ŝ' y = ContinuousMultilinearMap.domDomCongr σ
      (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from ŝ y)) :
    (show Tensor0SSpace (s + 1) I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ' x v) =
      ContinuousMultilinearMap.domDomCongr σ
        (show Tensor0SSpace (s + 1) I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ x v) := by
  classical
  have hx_good : x ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) x :=
    DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet x
  have hxE : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_mem_baseSet hx_good

  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ' x)
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x) =
        ContinuousMultilinearMap.domDomCongr σ
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ x)
            (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)) := by
    intro i
    have hXi_at := DifferentialGeometry.Integral.Connection.chartBasisVec_alpha_mdifferentiableAt
        (I := I) x i hx_good
    rw [← DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_eq_abstract_succ_aux
      (I := I) (M := M) g x s ŝ' (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i)
      hx_good hŝ' hXi_at]
    rw [show ŝ' = (fun y => ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from ŝ y))
        from funext hrel]
    rw [chartTensor0SCovariantDerivative_succ_domDomCongr (I := I) s g σ x ŝ
      (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i) hx_good]
    rw [DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_eq_abstract_succ_aux
      (I := I) (M := M) g x s ŝ (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i)
      hx_good hŝ hXi_at]

  conv_lhs => rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_recompose
    (I := I) x hxE v, map_sum]
  conv_rhs => rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_recompose
    (I := I) x hxE v, map_sum]
  simp_rw [map_smul]
  rw [domDomCongr_finsum_smul σ
    (fun i => ((DifferentialGeometry.Integral.Measure.chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v)) i)
    (fun i => (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ x)
      (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe i]

/-- **Slot-permutation naturality of the covariant derivative.**

Let `σ : Equiv.Perm (Fin s)` and let `S, S'` be smooth compactly-supported `(0, s)`-tensor
sections whose unit-evaluated model forms are related fibrewise by the constant slot reindexing
`σ`:

  `unitModel S' y = domDomCongr σ (unitModel S y)`  for every `y : M`.

Then the directional covariant derivatives are related by the *same* reindexing `σ`:

  `covDerivUnitModel S' x v = domDomCongr σ (covDerivUnitModel S x v)`.

This is the precise statement that the Levi-Civita `(0, s)`-tensor covariant derivative
`tensorCovDerivAt` commutes with a **constant** slot reindexing.  The reindexing `domDomCongr σ`
is a single point-independent linear automorphism of the model fibre `Tensor0SModel s`, i.e. the
fibrewise action of a parallel orthogonal bundle automorphism that permutes the covariant slots;
being parallel (`∇(domDomCongr σ) = 0`) it commutes with the iterated covariant gradient.  The
statement constrains `S'` to be the fibrewise reindexing of `S` (the hypothesis `hSS'`) and
concludes the corresponding relation for the covariant derivatives — it is not a packaging of
the conclusion (the hypothesis is about the raw section values; the conclusion about their
covariant derivatives), and it is non-vacuous (e.g. `S = T`, `S' = flipCcTensor g T`, `σ = swap
0 1` is a witnessing instance).

The proof reduces the directional covariant derivative read at the unit `(0, 0)`-tensor to the
bundled `(0, s)`-covariant derivative of the unit-evaluated section (the unit is `∇`-parallel,
`tensorRSCovariantDerivative_zeroS_unit_eval`), and then proves the bundled σ-naturality through
the chart-frame Christoffel decomposition: the intrinsic chart-Fréchet piece commutes with the
constant fibre isometry `domDomCongr σ` (slot-uniformity of the chart trivialisation +
`ContinuousLinearEquiv.comp_fderiv`), and the per-slot Christoffel-correction sum is `σ`-symmetric
under the bijective slot reindex `k ↦ σ.symm k`. -/
theorem tensorCovDerivAt_unit_toModel_domDomCongr_of_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (x : M) (v : TangentSpace I x) :
    covDerivUnitModel (I := I) (M := M) g s S' x v =
      ContinuousMultilinearMap.domDomCongr σ
        (covDerivUnitModel (I := I) (M := M) g s S x v) := by
  classical

  rw [covDerivUnitModel_eq_tensor0SCovariantDerivative (I := I) (M := M) g s S' x v,
    covDerivUnitModel_eq_tensor0SCovariantDerivative (I := I) (M := M) g s S x v]

  have hrel : ∀ y : M, unitEvalSection (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from
          unitEvalSection (I := I) (M := M) g s S y) := by
    intro y
    have h := hSS' y
    rw [unitModel, unitModel] at h
    exact h
  rcases s with _ | s
  · -- `s = 0`: a permutation of `Fin 0` is the identity, so the reindexing is trivial.
    have hsec : unitEvalSection (I := I) (M := M) g 0 S' = unitEvalSection (I := I) (M := M) g 0 S := by
      funext y
      have := hrel y
      rw [Subsingleton.elim σ (1 : Equiv.Perm (Fin 0))] at this
      apply ContinuousMultilinearMap.ext
      intro m
      rw [this, ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg _ (Subsingleton.elim _ _)
    rw [hsec]
    symm
    apply ContinuousMultilinearMap.ext
    intro m
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  · -- `s = s' + 1`: the chart-frame Christoffel σ-naturality.
    refine congrArg Tensor0SSpace.toModel ?_
    exact tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) s g σ
      (unitEvalSection (I := I) (M := M) g (s + 1) S)
      (unitEvalSection (I := I) (M := M) g (s + 1) S') x v
      (unitEvalSection_tensorSectionMDiffAt (I := I) (M := M) g (s + 1) S x)
      (unitEvalSection_tensorSectionMDiffAt (I := I) (M := M) g (s + 1) S' x)
      hrel

/-- **Unit-evaluated covariant gradient, one order.**  The unit-evaluated model `(0, s + 1)`-form
of `covGrad g 0 s W`, evaluated on a `Fin (s + 1)`-tuple `v`, reads the leftmost (gradient) slot:
it is the unit-evaluated model `(0, s)`-form of the directional covariant derivative
`tensorCovDerivAt g 0 s W x (v 0)`, evaluated on the tail `Matrix.vecTail v`.

This is `covGrad_toSection_apply_eval` specialized at the unit `(0, 0)`-tensor and packaged in
the `unitModel` / `covDerivUnitModel` vocabulary. -/
private lemma unitModel_covGrad_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : Fin (s + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s W) x v =
      covDerivUnitModel (I := I) (M := M) g s W x (v 0) (Matrix.vecTail v) := by
  rw [unitModel, covDerivUnitModel]
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 s W x
    (unitTensor (I := I) (M := M) x) v

/-- **Iterated slot-permutation naturality of the covariant gradient.**

If two smooth compactly-supported `(0, s)`-tensor sections `S, S'` are related fibrewise by a
constant slot reindexing `σ` (on their unit-evaluated model forms), then at every order `i`
there is a slot permutation `σ'` of `Fin (s + i)` relating the unit-evaluated model forms of the
iterated covariant gradients `∇^i S'` and `∇^i S`:

  `unitModel (∇^i S') x = domDomCongr σ' (unitModel (∇^i S) x)`  for every `x`.

Proven by induction on `i`: order `0` is the hypothesis (with `σ' = σ`); the step combines
`iteratedCovGrad_succ`, the one-order unit-evaluation `unitModel_covGrad_apply`, and the posited
naturality core `tensorCovDerivAt_unit_toModel_domDomCongr_of_section`, with the new permutation
`σ'.decomposeFin.symm (0, σ_i)` fixing the leftmost (gradient) slot and shifting `σ_i` onto the
remaining slots. -/
theorem exists_iteratedCovGrad_unit_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M, unitModel (I := I) (M := M) g (s + i)
          (iteratedCovGrad (I := I) (M := M) g 0 s i S') x =
        ContinuousMultilinearMap.domDomCongr σ'
          (unitModel (I := I) (M := M) g (s + i)
            (iteratedCovGrad (I := I) (M := M) g 0 s i S) x) := by
  induction i with
  | zero => exact ⟨σ, hSS'⟩
  | succ i ih =>
    obtain ⟨σ', hσ'⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, σ'), fun x => ?_⟩
    apply ContinuousMultilinearMap.ext
    intro v

    change unitModel (I := I) (M := M) g (s + i + 1)
        (covGrad (I := I) (M := M) g 0 (s + i)
          (iteratedCovGrad (I := I) (M := M) g 0 s i S')) x v =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ'))
        (unitModel (I := I) (M := M) g (s + i + 1)
          (covGrad (I := I) (M := M) g 0 (s + i)
            (iteratedCovGrad (I := I) (M := M) g 0 s i S)) x) v

    rw [unitModel_covGrad_apply (I := I) (M := M) g (s + i)
      (iteratedCovGrad (I := I) (M := M) g 0 s i S') x v]
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      unitModel_covGrad_apply (I := I) (M := M) g (s + i)
        (iteratedCovGrad (I := I) (M := M) g 0 s i S) x
        (fun k => v ((Equiv.Perm.decomposeFin.symm (0, σ')) k))]

    rw [tensorCovDerivAt_unit_toModel_domDomCongr_of_section (I := I) (M := M) g (s + i) σ'
      (iteratedCovGrad (I := I) (M := M) g 0 s i S)
      (iteratedCovGrad (I := I) (M := M) g 0 s i S') hσ' x (v 0)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]

    have hzero : v ((Equiv.Perm.decomposeFin.symm (0, σ')) (0 : Fin (s + i + 1))) = v 0 := by
      rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    have htail :
        (Matrix.vecTail fun k : Fin (s + i + 1) =>
            v ((Equiv.Perm.decomposeFin.symm (0, σ')) k)) =
          fun j : Fin (s + i) => Matrix.vecTail v (σ' j) := by
      funext j
      change v ((Equiv.Perm.decomposeFin.symm (0, σ')) (Fin.succ j)) = v (Fin.succ (σ' j))
      rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [hzero, htail]

/-! ## General contravariant-rank slot-permutation naturality of the covariant gradient

The positive-contravariant-rank (`r > 0`) lift of the rank-`0` directional naturality
`tensor0SCovariantDerivative_succ_domDomCongr`.  For two smooth `(r, s)`-tensor sections `Φ, Φ'`
whose model forms are related fibrewise by a constant covariant-slot reindexing `σ : Equiv.Perm
(Fin s)` (on every `(0, r)`-tensor input `d`), the directional covariant derivative
`tensorCovDerivAt` of `Φ'` is the same reindexing of that of `Φ`, and hence the covariant gradient
of `Φ'` is the `σ`-reindexing of that of `Φ` with the new leading gradient slot fixed.

The contravariant slot index `r` is untouched by the `s`-slot covariant reindexing; the Hom-connection
product rule `tensorRSCovariantDerivative_apply` splits the directional covariant derivative into the
`(0, s)`-target arm (where the rank-`0` naturality applies) and the `(0, r)`-source arm (untouched by
`σ`, just `σ`-reindexed by the hypothesis read at the source-differentiated input). -/

/-- **Smoothness of the application `(Φ.toSection ·)(w ·)` as a `(0, s)`-tensor section.**  For a
smooth `(r, s)`-operator field `Φ` and a smooth `(0, r)`-tensor section `w`, the `(0, s)`-tensor
section `y ↦ (Φ.toSection y)(w y)` is `MDifferentiableAt` in total-space form at every point. -/
private lemma applySection_tensorSectionMDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯) (x : M) :
    DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s
      (fun y => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (w y)) x := by
  classical
  have hHom : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun u : M => Tensor0SSpace r I u →L[ℝ] Tensor0SSpace s I u) z
        (show Tensor0SSpace r I z →L[ℝ] Tensor0SSpace s I z from Φ.toSection z)) x :=
    (Φ.toSection.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun u : M => Tensor0SSpace r I u) z (w z)) x :=
    (w.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHom hv

/-- **General contravariant-rank directional covariant-derivative σ-naturality.**  Let `σ :
Equiv.Perm (Fin s)` and let `Φ, Φ'` be smooth `(r, s)`-tensor sections whose model forms are related
fibrewise by the constant covariant-slot reindexing `σ`:

  `toModel ((Φ'.toSection y) d) = domDomCongr σ (toModel ((Φ.toSection y) d))`  for all `y` and all
  `(0, r)`-inputs `d`.

Then the directional covariant derivatives are related by the same reindexing:

  `toModel ((tensorCovDerivAt g r s Φ' x v) d) = domDomCongr σ (toModel ((tensorCovDerivAt g r s Φ x
  v) d))`.

Tested on a `(0, r)`-tensor `D = w x` (a local smooth extension): the Hom-connection product rule
`tensorRSCovariantDerivative_apply` writes both directional derivatives as the `(0, s)`-target arm
`∇^{(0,s)}_v(y ↦ Φ(w))` minus the `(0, r)`-source arm `Φ(∇^{(0,r)}_v w)`.  The target arm is
`σ`-natural by the rank-`0` directional naturality `tensor0SCovariantDerivative_succ_domDomCongr`
(applied to the `(0, s)`-sections `y ↦ Φ(w)` and `y ↦ Φ'(w)`, related by `σ` via the hypothesis),
and the source arm is `σ`-reindexed by the hypothesis read at the differentiated source input. -/
theorem tensorCovDerivAt_rs_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (x : M) (v : TangentSpace I x) (D : Tensor0SSpace r I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ' x v) D) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            tensorCovDerivAt (I := I) (M := M) g r s Φ x v) D)) := by
  classical

  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel r ℝ E) (V := fun y : M => Tensor0SSpace r I y)
    (n := (⊤ : ℕ∞)) x D

  set u : Π y : M, Tensor0SSpace s I y :=
    fun y => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (w y) with hu_def
  set u' : Π y : M, Tensor0SSpace s I y :=
    fun y => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) (w y) with hu'_def
  have hu_at : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s u x :=
    applySection_tensorSectionMDiffAt (I := I) (M := M) g r s Φ w x
  have hu'_at : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s u' x :=
    applySection_tensorSectionMDiffAt (I := I) (M := M) g r s Φ' w x
  have hurel : ∀ y : M, u' y =
      ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from u y) := by
    intro y
    apply Tensor0SSpace.toModel_injective
    have h := hrel y (w y)
    rw [hu'_def, hu_def]
    exact h

  rw [tensorCovDerivAt_def (I := I) (M := M) g r s Φ' x v,
    tensorCovDerivAt_def (I := I) (M := M) g r s Φ x v]
  have hHL' := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r s
    (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) Φ'.toSection w x v
  have hHL := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r s
    (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) Φ.toSection w x v
  rw [← hw]
  rw [hHL', hHL]
  rw [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub, domDomCongr_sub]

  have hsource :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ'.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M r
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) w x v)) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M r
                (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) w x v))) :=
    hrel x _

  have htarget :
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) u' x v) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) u x v)) := by
    rcases s with _ | s'
    · -- `s = 0`: `domDomCongr` over `Fin 0` is the identity.
      apply ContinuousMultilinearMap.ext
      intro m
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      congr 1
      · have hsec : u' = u := by
          funext y
          have hy := hurel y
          rw [Subsingleton.elim σ (1 : Equiv.Perm (Fin 0))] at hy
          rw [hy]
          apply ContinuousMultilinearMap.ext
          intro m'
          rw [ContinuousMultilinearMap.domDomCongr_apply]
          exact congrArg _ (Subsingleton.elim _ _)
        rw [hsec]
      · exact Subsingleton.elim _ _
    · refine congrArg Tensor0SSpace.toModel ?_
      exact tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) s' g σ u u' x v
        hu_at hu'_at hurel
  rw [htarget, hsource]

/-- **General contravariant-rank covariant-gradient σ-naturality (model form).**  Under the same
fibrewise hypothesis as `tensorCovDerivAt_rs_toModel_domDomCongr`, the covariant gradients of `Φ`
and `Φ'` are related by the `σ`-reindexing with the new leading gradient slot fixed: writing
`σ̂ = Equiv.Perm.decomposeFin.symm (0, σ)` (the permutation of `Fin (s + 1)` fixing slot `0` and
acting as `σ` on the remaining `s` slots),

  `toModel ((covGrad g r s Φ').toSection x d) = domDomCongr σ̂ (toModel ((covGrad g r s Φ).toSection
  x d))`  for all `x` and all `(0, r)`-inputs `d`.

The covariant gradient reads the new leading slot as the directional covariant derivative
(`covGrad_toSection_apply_eval`), which is `σ`-natural by `tensorCovDerivAt_rs_toModel_domDomCongr`;
the leading gradient slot is therefore fixed and the tail slots are `σ`-reindexed. -/
theorem covGrad_rs_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (x : M) (d : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s Φ').toSection x) d) v =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ))
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g r s Φ).toSection x) d)) v := by
  classical
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ' x d v]
  rw [ContinuousMultilinearMap.domDomCongr_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x d
      (fun k => v ((Equiv.Perm.decomposeFin.symm (0, σ)) k))]

  rw [tensorCovDerivAt_rs_toModel_domDomCongr (I := I) (M := M) g r s σ Φ Φ' hrel x (v 0) d]
  rw [ContinuousMultilinearMap.domDomCongr_apply]

  have hzero : v ((Equiv.Perm.decomposeFin.symm (0, σ)) (0 : Fin (s + 1))) = v 0 := by
    rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  have htail :
      (Matrix.vecTail fun k : Fin (s + 1) =>
          v ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
        fun j : Fin s => Matrix.vecTail v (σ j) := by
    funext j
    change v ((Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.succ j)) = v (Fin.succ (σ j))
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  rw [hzero, htail]

/-- **Rank-`0` lowering reads off the unit-evaluated model form.**  At rank `r = 0`, the metric
lowering `lowerAllUpperIndices g 0 s x` of the trivialized model tensor `TensorRSSpace.toModel
W_x` of a smooth `(0, s)`-tensor section `W` is, on a tuple `u : Fin (0 + s) → E`, the
unit-evaluated model `(0, s)`-form `unitModel W x` evaluated on the reindexed tuple
`u ∘ Fin.natAdd 0`.  The rank-`0` separable lowering form is the unit `(0, 0)`-tensor
(`separableFormAt_zero`), so the lowering is exactly evaluation at the unit. -/
private lemma lowerAllUpperIndices_zero_apply_unitModel
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (u : Fin (0 + s) → TangentSpace I x) :
    (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x))) u =
      (unitModel (I := I) (M := M) g s W x) (fun j => u (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [unitModel, unitTensor]
  rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))]
  rw [Tensor0SSpace.toModel_ofModel]
  rfl

/-- **A slot reindexing of the section reindexes the metric lowering.**  If two smooth
`(0, s)`-tensor sections `S, S'` are related fibrewise by the constant slot reindexing `σ` (on
their unit-evaluated model forms), then their metric lowerings are related by the slot
reindexing `σ` transported along `Fin s ≃ Fin (0 + s)`. -/
private lemma lowerAllUpperIndices_zero_domDomCongr_of_unitModel
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (x : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)) =
      ContinuousMultilinearMap.domDomCongr
        ((finCongr (Nat.zero_add s)).permCongr.symm σ)
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x))) := by
  apply ContinuousMultilinearMap.ext
  intro u
  rw [lowerAllUpperIndices_zero_apply_unitModel (I := I) (M := M) g s S' x u]
  rw [hSS' x, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [lowerAllUpperIndices_zero_apply_unitModel (I := I) (M := M) g s S x]

  congr 1
  funext j
  congr 1

  rw [Equiv.permCongr_symm, Equiv.permCongr_apply]
  apply Fin.ext
  simp

/-- **A slot reindexing of the section preserves the `g`-fibre norm of every iterated covariant
gradient.**  If two smooth `(0, s)`-tensor sections `S, S'` are related fibrewise by a constant
slot reindexing `σ` (on their unit-evaluated model forms), then at every order `i` and base
point `x` the `g`-Riemannian fibre norms squared of the iterated covariant gradients `∇^i S'`
and `∇^i S` coincide.

The slot reindexing is a fibre isometry: by `exists_iteratedCovGrad_unit_toModel_domDomCongr`
the order-`i` gradients differ by a slot permutation of the model fibre, and the pointwise inner
product `tensorInnerPointwise` is invariant under a simultaneous slot reindexing of both
arguments (`tensorInnerPointwise_0s_domDomCongr`). -/
theorem riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x) := by
  obtain ⟨σ', hσ'⟩ :=
    exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M) g s σ S S' hSS' i
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x)]

  change tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + i)) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x))) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + i)) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x)))
  rw [lowerAllUpperIndices_zero_domDomCongr_of_unitModel (I := I) (M := M) g (s + i) σ'
    (iteratedCovGrad (I := I) (M := M) g 0 s i S)
    (iteratedCovGrad (I := I) (M := M) g 0 s i S') hσ' x]
  rw [tensorInnerPointwise_0s_domDomCongr]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
