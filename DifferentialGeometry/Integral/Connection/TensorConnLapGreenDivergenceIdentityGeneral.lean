import DifferentialGeometry.Integral.Connection.TensorConnLapSecondOrderIBP
import DifferentialGeometry.Integral.Connection.TensorConnLapGreenDivergenceIdentity
import DifferentialGeometry.Integral.Connection.TensorConnLapGreenIdentity
import DifferentialGeometry.Integral.Connection.TensorCovGradL2InnerDirichletBridge
import DifferentialGeometry.Integral.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.TensorRSMetricCompatible
import DifferentialGeometry.Integral.Connection.TensorRicciCommutator
import DifferentialGeometry.Integral.Connection.TensorLoweringParallel
import DifferentialGeometry.Integral.Connection.CovariantIntegrationByParts
import DifferentialGeometry.Integral.Connection.Bochner
import DifferentialGeometry.Integral.Connection.RicciIdentitySmoothFrame
import DifferentialGeometry.Integral.Connection.ChartBridge.Hessian
import DifferentialGeometry.Integral.DivergenceTheorem.Proper
import DifferentialGeometry.Geometry.MetricSharpSmooth
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure

/-!
# The intrinsic `(0, s)` connection-Laplacian Green identity via the Dirichlet current

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file proves the integrated Green identity for the
rough (connection) Laplacian on `(0, s)`-tensor fields,

```
tensorL2Inner g 0 (s + 1) (covGrad g 0 s T).toFun (covGrad g 0 s v).toFun
  = − tensorL2Inner g 0 s (rawTensorConnLapSmooth g 0 s T).toFun v.toFun,
```

through a single **Dirichlet current** vector field and a single application of
the divergence theorem on the closed manifold.

This generalizes the rank-`(0, 2)` headline
`green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed`.  The proof structure is
identical: the whole Dirichlet-current chain — the current `1`-form, its musical
sharp, the Bochner divergence identity, and the divergence theorem — is
**rank-generic**.

## The rank-`0` metric-lowering intertwiner

The single genuinely rank-dependent ingredient is the rank-`0` connection
intertwiner: at every direction `v` and point `x`, the metric-lowering of the
genuine `(0, s)`-covariant derivative of a section `S` equals the directional
covariant derivative of the metric-lowered section,

```
toModel (loweredCovDerivAt g 0 s S x v)
  = lowerAllUpperIndices g 0 s x (toModel (∇^{(0,s)}_v S)).
```

This is the statement that metric-lowering commutes with `∇` (the metric is
`∇`-parallel).  The committed development proves it at rank `(0, 2)`
(`loweredCovDerivAt_eq_lower_tensorCovDerivAt`), where the lowered index
`0 + 2` reduces *definitionally* to `2`.  Every Dirichlet-current lemma below is
stated for an arbitrary covariant rank `s` together with an *explicit
intertwiner witness* `hint` at that rank; the rank-`(0, 3)` headline supplies the
witness by the same definitional-reduction proof (`0 + 3 ≡ 3`).

## Main definitions

* `dirichletFormGen g s T v b` — the `1`-form `X ↦ ⟨∇_X T, v⟩_g` at `b`.
* `dirichletVFGen g s T v b` — its metric-musical sharp, a tangent vector at `b`.
* `dirichletVFSectionGen g s T v` — `dirichletVFGen` packaged as a smooth
  tangent-bundle section.

## Main results

* `loweredCovDerivAt_eq_lower_tensorCovDerivAt_three` — the rank-`(0, 3)`
  metric-lowering intertwiner.
* `divergence_dirichletVFGen_eq` — the pointwise Bochner divergence identity at
  rank `(0, s)` (given the intertwiner witness).
* `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general` — the headline
  Green identity at rank `(0, s)` (given the intertwiner witness).
* `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three` — the
  unconditional rank-`(0, 3)` instance (the one consumed by the order-`2` `∇²T`
  Gårding bound).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The rank-`0` metric-lowering intertwiner at rank `s`: for every smooth
`(0, s)`-tensor section `S`, point `x` and direction `v`, the model coercion of
the lowered directional covariant derivative equals the index-lowering of the
genuine `(0, s)`-covariant derivative. -/
def LoweringIntertwiner (g : SmoothRiemannianMetric I M) (s : ℕ) : Prop :=
  ∀ (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (x : M) (v : TangentSpace I x),
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s S x v) =
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v))

/-- The rank-`(0, 2)` intertwiner witness (committed). -/
lemma loweringIntertwiner_two (g : SmoothRiemannianMetric I M) :
    LoweringIntertwiner (I := I) (M := M) g 2 :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g S x v

/-- **The rank-`(0, 3)` metric-lowering intertwiner.** Proved by the same
definitional-reduction argument as the committed `(0, 2)` case: the genuine
`(0, 3)`-covariant derivative, lowered, equals its evaluation at the unit
`(0, 0)`-tensor (`0 + 3` reduces to `3`), which by the product rule — the
covariant derivative of the constant unit `(0, 0)`-section vanishes — is the
covariant derivative of the lifted `(0, 0 + 3)`-tensor section, i.e.
`loweredCovDerivAt g 0 3 S x v`. -/
theorem loweredCovDerivAt_eq_lower_tensorCovDerivAt_three
    (g : SmoothRiemannianMetric I M)
    (S : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun x : M => TensorRSSpace 0 3 I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 3 S x v) =
      lowerAllUpperIndices (I := I) (M := M) g 0 3 x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v)) := by
  classical
  let unitSec : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
    ⟨fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
      contMDiff_unitZeroSection (I := I) (M := M)⟩
  have hcoe : (fun y : M => unitSec y) =
      fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl
  have hunit_model : Tensor0SSpace.toModel (unitSec x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    change Tensor0SSpace.toModel (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = _
    rw [Tensor0SSpace.toModel_ofModel]
  have hlowerA :
      lowerAllUpperIndices (I := I) (M := M) g 0 3 x
          (TensorRSSpace.toModel
            (tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 3) I x from
              tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v)
            (unitSec x)) := by
    rw [toModel_tensorRS_apply (I := I) (M := M) 0 3 x
      (tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v) (unitSec x)]
    rw [hunit_model]
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [lowerAllUpperIndices_apply, separableFormAt_zero]
    congr 1
    funext j
    exact congrArg u (Fin.ext (by simp))
  rw [hlowerA]
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 3
    (LeviCivita (I := I) g) S unitSec x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitSec y) x v) = 0 from by
    rw [hcoe]
    exact tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]
  rw [loweredCovDerivAt_def]
  have hsec : (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (0 + 3) I y from S y) (unitSec y)) =
      liftedTensorSection (I := I) (M := M) g 0 3 S := by
    funext y
    refine Tensor0SSpace.toModel_injective ?_
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [toModel_liftedTensorSection_zero_eq_apply_unit_reindex (I := I) (M := M) g 3 S y u]
    congr 1
    funext j
    exact congrArg u (Fin.ext (by simp))
  rw [hsec]

/-- The rank-`(0, 3)` intertwiner witness (unconditional). -/
lemma loweringIntertwiner_three (g : SmoothRiemannianMetric I M) :
    LoweringIntertwiner (I := I) (M := M) g 3 :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_three (I := I) (M := M) g S x v

/-- The un-lowered first directional covariant derivative `y ↦ ∇_{B y} T y` of a
smooth `(0, s)`-tensor section `T` along a smooth tangent vector field `B`, as a
raw `(0, s)`-tensor section. -/
def covDerivAlongVFrawGen
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, TensorRSSpace 0 s I y :=
  covApply (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g))
    (fun y : M => B y) (fun y : M => T y)

@[simp] lemma covDerivAlongVFrawGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFrawGen (I := I) (M := M) g s T B y =
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

/-- **Smoothness of the un-lowered first directional covariant derivative.** -/
lemma covDerivAlongVFrawGen_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covDerivAlongVFrawGen (I := I) (M := M) g s T B y)) := by
  classical
  set cov := tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) with hcov_def
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from rfl]
    exact T.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (B y)) :=
    B.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply cov (fun y : M => B y) (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT
  rw [← contMDiffOn_univ]
  exact hOn

/-- The un-lowered first directional covariant derivative, bundled as a smooth
section, at rank `(0, s)`. -/
def covDerivAlongVFSectionGen
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covDerivAlongVFrawGen (I := I) (M := M) g s T B y)
    (covDerivAlongVFrawGen_contMDiff (I := I) (M := M) g s T B)

@[simp] lemma covDerivAlongVFSectionGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionGen (I := I) (M := M) g s T B y =
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

/-- **The lowering of the un-lowered first directional derivative is the lowered
directional derivative**, at rank `(0, s)`, given the intertwiner witness. -/
lemma covDerivAlongVFSectionGen_lowered_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s y
        (TensorRSSpace.toModel (covDerivAlongVFSectionGen (I := I) (M := M) g s T B y)) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s T y (B y)) := by
  rw [hint T y (B y)]
  rfl

/-- The lifted `(0, 0 + s)`-tensor section of the first directional derivative
coincides, after model coercion, with the lowered directional derivative, at rank
`(0, s)`, given the intertwiner witness. -/
lemma toModel_liftedTensorSection_covDerivAlongVFSectionGen
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g 0 s
          (covDerivAlongVFSectionGen (I := I) (M := M) g s T B) y) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s T y (B y)) := by
  rw [toModel_liftedTensorSection]
  exact covDerivAlongVFSectionGen_lowered_eq (I := I) (M := M) g s hint T B y

/-- **The second directional derivative is the Hessian plus the frame
correction**, at rank `(0, s)`. -/
lemma covDerivAlongGen_covDerivAlongVFSectionGen_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionGen (I := I) (M := M) g s
        (covDerivAlongVFSectionGen (I := I) (M := M) g s T B) B y =
      tensorSecondCovDeriv (I := I) g 0 s
          (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) y +
        (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun b : M => T b) y
          ((LeviCivita (I := I) g).toFun (fun b : M => B b) y (B y)) := by
  rw [tensorSecondCovDeriv_def]
  change (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
      (covApply (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g))
        (fun b : M => B b) (fun b : M => T b)) y (B y) = _
  rw [show tensorCov (I := I) g 0 s =
      tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) from rfl]
  abel

/-- **The Dirichlet `1`-form** at rank `(0, s)`. -/
def dirichletFormGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g 0 s b
    (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 s T b X))
    (TensorRSSpace.toModel (v.toSection b))
  map_add' X Y := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 s T b (X + Y) =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b X +
          tensorCovDerivAt (I := I) (M := M) g 0 s T b Y := by
      change (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (X + Y) = _
      rw [ContinuousLinearMap.map_add]
      rfl
    rw [hcov, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  map_smul' c X := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 s T b (c • X) =
        c • tensorCovDerivAt (I := I) (M := M) g 0 s T b X := by
      change (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (c • X) = _
      rw [ContinuousLinearMap.map_smul]
      rfl
    rw [hcov, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
    rfl

@[simp] lemma dirichletFormGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M)
    (X : TangentSpace I b) :
    dirichletFormGen (I := I) (M := M) g s T v b X =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 s T b X))
        (TensorRSSpace.toModel (v.toSection b)) := rfl

/-- **The Dirichlet current vector field, pointwise** at rank `(0, s)`. -/
def dirichletVFGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (dirichletFormGen (I := I) (M := M) g s T v b)

/-- **The defining Riesz identity for the Dirichlet current** at rank `(0, s)`. -/
lemma inner_dirichletVFGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M)
    (X : TangentSpace I b) :
    g.inner b (dirichletVFGen (I := I) (M := M) g s T v b) X =
      dirichletFormGen (I := I) (M := M) g s T v b X := by
  rw [dirichletVFGen]
  exact inner_metricSharp (I := I) g b (dirichletFormGen (I := I) (M := M) g s T v b) X

/-- **Chart-local smoothness of the Dirichlet-form chart-basis component** at rank
`(0, s)`. -/
private lemma dirichletFormGen_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => dirichletFormGen (I := I) (M := M) g s T v b
        (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  have hcov_section : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun y : M => TensorRSSpace 0 s I y) b
        (tensorCovDerivAt (I := I) (M := M) g 0 s T b
          (chartBasisVecFiber (I := I) α j b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g 0 s T α j
  have hcov_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 s T b
            (chartBasisVecFiber (I := I) α j b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g 0 s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 s T b
        (chartBasisVecFiber (I := I) α j b)) α hcov_section
  have hv_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g 0 s v.toSection α
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (chartBasisVecFiber (I := I) α j b)))
          (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g 0 s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 s T b
        (chartBasisVecFiber (I := I) α j b))
      (fun b : M => v.toSection b) α hcov_lowered hv_lowered
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [dirichletFormGen_apply]

/-- **Smoothness of the Dirichlet current as a tangent-bundle section** at rank
`(0, s)`. -/
lemma dirichletVFGen_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (dirichletVFGen (I := I) (M := M) g s T v b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => dirichletFormGen (I := I) (M := M) g s T v b)
    (fun α j => dirichletFormGen_chartBasis_component_contMDiffOn
      (I := I) (M := M) g s T v α j)

/-- **The Dirichlet current packaged as a smooth tangent-bundle section** at rank
`(0, s)`. -/
def dirichletVFSectionGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => dirichletVFGen (I := I) (M := M) g s T v b)
    (dirichletVFGen_contMDiff (I := I) (M := M) g s T v)

@[simp] lemma dirichletVFSectionGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    dirichletVFSectionGen (I := I) (M := M) g s T v b =
      dirichletVFGen (I := I) (M := M) g s T v b := rfl

/-- **Per-direction Bochner expansion of the divergence summand** at rank
`(0, s)`, given the intertwiner witness. -/
private lemma divergence_dirichletVFGen_summand_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (dirichletVFSectionGen (I := I) (M := M) g s T v).toFun b
          (smoothOrthoFrame (I := I) g b i b))
        (smoothOrthoFrame (I := I) g b i b) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
              (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g b i y,
      smoothOrthoFrame_smooth (I := I) g b i⟩ with hB_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionGen (I := I) (M := M) g s T v with hZ_def
  have hBb : (B : ∀ y, TangentSpace I y) b = smoothOrthoFrame (I := I) g b i b := rfl
  have hleib := leibniz_inner (I := I) g
    (V := fun y : M => Z y) (W := fun y : M => B y)
    Z.contMDiff B.contMDiff
    (x := b) ((B : ∀ y, TangentSpace I y) b)
  have hfun : (fun y : M => g.inner y (Z y) (B y)) =
      tensorInnerScalar (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B) v.toSection := by
    funext y
    rw [hZ_def, dirichletVFSectionGen_apply, inner_dirichletVFGen, dirichletFormGen_apply,
      tensorInnerScalar_apply, covDerivAlongVFSectionGen_apply]
    rfl
  have hprod : tangentSectionAction (I := I) B
        (fun y : M => g.inner y (Z y) (B y)) b =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionGen (I := I) (M := M) g s
              (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B) B b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionGen (I := I) (M := M) g s v.toSection B b)) := by
    rw [show tangentSectionAction (I := I) B
            (fun y : M => g.inner y (Z y) (B y)) =
          tangentSectionAction (I := I) B
            (tensorInnerScalar (I := I) (M := M) g 0 s
              (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B) v.toSection) from by
      rw [hfun]]
    rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g 0 s
      (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B) v.toSection B b]
    congr 1
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionGen (I := I) (M := M) g s
          (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B) B)
        v.toSection b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionGen (I := I) (M := M) g s hint
        (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B) B b]
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B)
        (covDerivAlongVFSectionGen (I := I) (M := M) g s v.toSection B) b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionGen (I := I) (M := M) g s hint T.toSection B b,
        toModel_liftedTensorSection_covDerivAlongVFSectionGen (I := I) (M := M) g s hint v.toSection B b]
  have haccel : g.inner b (Z b)
        ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
          ((B : ∀ y, TangentSpace I y) b)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 s T b
            ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
              ((B : ∀ y, TangentSpace I y) b))))
        (TensorRSSpace.toModel (v.toSection b)) := by
    rw [hZ_def, dirichletVFSectionGen_apply, inner_dirichletVFGen, dirichletFormGen_apply]
  have hsecond := covDerivAlongGen_covDerivAlongVFSectionGen_eq (I := I) (M := M) g s T.toSection B b
  have hsummand : g.inner b
        ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
          ((B : ∀ y, TangentSpace I y) b))
        ((B : ∀ y, TangentSpace I y) b) =
      tangentSectionAction (I := I) B (fun y : M => g.inner y (Z y) (B y)) b
        - g.inner b (Z b)
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := by
    rw [tangentSectionAction_def]
    rw [hleib]; ring
  change g.inner b
      ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
        ((B : ∀ y, TangentSpace I y) b))
      ((B : ∀ y, TangentSpace I y) b) = _
  rw [hsummand, hprod, haccel]
  rw [hsecond, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have haccel_eq :
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := rfl
  rw [haccel_eq]
  rw [show covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b ((B : ∀ y, TangentSpace I y) b) from rfl,
    show covDerivAlongVFSectionGen (I := I) (M := M) g s v.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 s v b ((B : ∀ y, TangentSpace I y) b) from rfl]
  rw [hBb]
  rw [show (fun y : M => (B : ∀ z : M, TangentSpace I z) y) =
        (fun y : M => smoothOrthoFrame (I := I) g b i y) from rfl]
  ring

/-- **Dirichlet integrand = smooth-orthonormal-frame diagonal sum** at rank
`(0, s)`. -/
private lemma tensorCovDerivPointwiseInnerGen_eq_smoothOrthoFrame_diag
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hframe_def
  have hframe_eq : ∀ i, frame i = smoothOrthoFrame (I := I) g b i b := by
    intro i
    rw [hframe_def]
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → E) i = smoothOrthoFrame (I := I) g b i b
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hframe_eq i, hframe_eq j]
    exact hB_orth i j
  rw [tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (I := I) (M := M) g 0 s T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i]

/-- **The pointwise Bochner divergence identity** at rank `(0, s)`, given the
intertwiner witness. -/
lemma divergence_dirichletVFGen_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) (b : M) :
    divergence_g (I := I) g (dirichletVFSectionGen (I := I) (M := M) g s T v) b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
  classical
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g
    (dirichletVFSectionGen (I := I) (M := M) g s T v) b]
  rw [Finset.sum_congr rfl (fun i _ =>
    divergence_dirichletVFGen_summand_eq (I := I) (M := M) g s hint T v b i)]
  rw [Finset.sum_add_distrib]
  rw [← tensorCovDerivPointwiseInnerGen_eq_smoothOrthoFrame_diag (I := I) (M := M) g s T v b]
  rw [add_comm]
  congr 1
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 s
    (fun y : M => T.toSection y) b]
  rw [show TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) from ?_]
  · rw [show (∑ i : Fin (Module.finrank ℝ E),
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b)) =
          ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
    rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 s b Finset.univ _ _ _]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul]
  · exact map_sum (tensorRSSpace_continuousLinearEquiv (I := I) 0 s b)
      (fun i => tensorSecondCovDeriv (I := I) g 0 s
        (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
        (fun y : M => T.toSection y) b) Finset.univ

/-- **The headline intrinsic `(0, s)` connection-Laplacian Green identity**, given
the intertwiner witness. -/
theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun
        (covGrad (I := I) (M := M) g 0 s v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionGen (I := I) (M := M) g s T v with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hdiv_zero : ∫ b, divergence_g (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergence_g (I := I) g Z b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
    intro b; rw [hZ_def]; exact divergence_dirichletVFGen_eq (I := I) (M := M) g s hint T v b
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_cont : Continuous
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b) := by
    rw [show (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b) =
          fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
            (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
            (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s v).toSection b)) from by
      funext b
      exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
        (I := I) (M := M) g 0 s T v b)]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s T).toSection
      (covGrad (I := I) (M := M) g 0 s v).toSection).continuous
  have hsecond_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) := by
    rw [show (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b))) =
          fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel
              ((rawTensorConnLapSmooth (I := I) g 0 s T).toSection b))
            (TensorRSSpace.toModel (v.toSection b)) from by
      funext b
      rw [rawTensorConnLapSmooth_toSection_apply (I := I) g 0 s T b]]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 s
      (rawTensorConnLapSmooth (I := I) g 0 s T).toSection v.toSection).continuous
  have hcross_int : Integrable
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hcross_cont (HasCompactSupport.of_compactSpace _)
  have hsecond_int : Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hsecond_cont (HasCompactSupport.of_compactSpace _)
  rw [integral_add hcross_int hsecond_int] at hdiv_zero
  rw [tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
    (I := I) (M := M) g 0 s T v, ← hμ_def]
  rw [show tensorL2Inner (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b)) ∂μ from ?_]
  · linarith [hdiv_zero]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply]

/-- **The rank-`(0, 3)` instance of the connection-Laplacian Green identity**
(unconditional). This is the special case consumed by the order-`2` `∇²T` Gårding
bound. -/
theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 3) :
    tensorL2Inner (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3 T).toFun
        (covGrad (I := I) (M := M) g 0 3 v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3 T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general
    (I := I) (M := M) g 3 (loweringIntertwiner_three (I := I) (M := M) g) T v

/-- **The rank-`(0, 2)` instance of the connection-Laplacian Green identity**,
re-derived through the rank-generic Dirichlet-current chain with the committed
`(0, 2)` intertwiner witness. -/
theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun
        (covGrad (I := I) (M := M) g 0 2 v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general
    (I := I) (M := M) g 2 (loweringIntertwiner_two (I := I) (M := M) g) T v

end Connection
end Integral
end DifferentialGeometry

end
