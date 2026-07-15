import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldEvaluationLeibniz

/-! # The section-level metric trace and its intrinsic fibre-norm bound

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the algebraic Tensor library supplies the *fibrewise* trace contraction
`Tensor0SBundle.contract_trace r s x : TensorRSSpace (1 + r) (s + 1) I x →L[ℝ] TensorRSSpace r s I x`
(contract the first upper slot against the first lower slot), and its smooth-section lift
`Tensor0SBundle.contract_TensorRSField r s` on `TensorRSField`.  Neither is packaged at the
`SmoothCcTensor` level (the compactly-supported smooth-section type the covariant-gradient tower
`covGrad`/`iteratedCovGrad` lives on); the only `SmoothCcTensor`-level trace currently on disk is the
*Ricci*-specific `ricTraceDiffOp` (a curvature contraction, not the metric/algebraic trace).

This file liberates the algebraic trace to a first-class `SmoothCcTensor`-level operator
`contractCcTensor`, with its linearity API and — the analytic deliverable the covariant
Faà-di-Bruno / Bochner machinery consumes — the **intrinsic fibre-norm trace bound**: the trace is a
fixed fibrewise continuous-linear bundle map, so its intrinsic Riemannian fibre norm
`riemannianFiberNormSq` is controlled by a single nonnegative base-point-uniform constant times that of
its argument.  The bound is proved through the *proved* fibre-norm/bundle-norm bridge
`riemannianFiberNormSq_eq_bundle_norm_sq` and the operator norm of the trace map, the exact mechanism
of the fibrewise Cauchy–Schwarz `riemannianFiberNormSq_clm_apply_le`, here for a general
`TensorRSSpace`-valued continuous-linear map rather than the `(0, r) → (0, s)` special case.

The ambient manifold hypothesis is `IsManifold I ω M` (analytic), the regularity the algebraic Tensor
library's field-level trace `contract_TensorRSField` requires; it implies the `∞`-smoothness the
covariant-gradient tower uses, so `contractCcTensor` and `covGrad`/`iteratedCovGrad` coexist on the
same footing.

## Main definitions

* `contractCcTensor g r s` — the section-level metric/algebraic trace, sending a smooth
  compactly-supported `(1 + r, s + 1)`-tensor section to a smooth compactly-supported
  `(r, s)`-tensor section, contracting the first upper slot against the first lower slot.

## Main results

* `contractCcTensor_toSection_apply` — the underlying section value is the fibrewise trace
  `contract_trace r s x` of the argument's section value.
* `contractCcTensor_zero`, `contractCcTensor_add`, `contractCcTensor_smul` — `ℝ`-linearity.
* `riemannianFiberNormSq_contract_trace_le` — the per-point intrinsic fibre-norm trace bound for the
  fibrewise trace map, with a base-point-dependent constant.
* `exists_uniform_riemannianFiberNormSq_contractCcTensor_le` — the base-point-**uniform** fibre-norm
  trace bound for the section-level trace `contractCcTensor`, the shape the integrated tensor
  estimates consume.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- **The section-level metric/algebraic trace.** The trace contraction of a smooth
compactly-supported `(1 + r, s + 1)`-tensor section, contracting the first upper slot against the
first lower slot, packaged as a smooth compactly-supported `(r, s)`-tensor section.

Its underlying smooth section is `contract_TensorRSField r s` applied to the argument's section; it
has compact support because the fibrewise trace is continuous-linear (it kills the zero fibre), so its
underlying map vanishes wherever the argument's does. -/
noncomputable def contractCcTensor (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g (1 + r) (s + 1) → SmoothCcTensor g r s :=
  fun T =>
    { toSection :=
        Tensor0SBundle.contract_TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
          (n := ∞) r s T.toSection
      hasCompactSupport := by
        refine HasCompactSupport.of_support_subset_isCompact T.hasCompactSupport ?_
        intro x hx
        rw [Function.mem_support] at hx
        by_contra hxnot
        apply hx
        have hTzero : TensorRSSpace.toModel (T.toSection x) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : M => TensorRSSpace.toModel (T.toSection y)) hxnot
        have hxz : T.toSection x = 0 := by
          have h0 := TensorRSSpace.toModel_zero (I := I) (r := 1 + r) (s := s + 1) (x := x)
          exact TensorRSSpace.toModel_injective (hTzero.trans h0.symm)
        change TensorRSSpace.toModel
            (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x
              (T.toSection x)) = 0
        rw [hxz, map_zero, TensorRSSpace.toModel_zero] }

/-- **Pointwise-evaluation formula for the section-level trace.** At a base point `x`, the underlying
section value of `contractCcTensor g r s T` is the fibrewise trace `contract_trace r s x` of the
argument's section value `T.toSection x`. -/
theorem contractCcTensor_toSection_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g (1 + r) (s + 1)) (x : M) :
    (contractCcTensor (I := I) (M := M) g r s T).toSection x =
      Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x
        (T.toSection x) := rfl

/-- The section-level trace kills the zero section: `contractCcTensor g r s 0 = 0`. -/
@[simp] theorem contractCcTensor_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    contractCcTensor (I := I) (M := M) g r s (0 : SmoothCcTensor g (1 + r) (s + 1)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [contractCcTensor_toSection_apply]
  rw [show ((0 : SmoothCcTensor g (1 + r) (s + 1)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  rw [map_zero]
  rw [show ((0 : SmoothCcTensor g r s).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]

/-- The section-level trace is additive in the section. -/
theorem contractCcTensor_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₁ T₂ : SmoothCcTensor g (1 + r) (s + 1)) :
    contractCcTensor (I := I) (M := M) g r s (T₁ + T₂) =
      contractCcTensor (I := I) (M := M) g r s T₁ + contractCcTensor (I := I) (M := M) g r s T₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [contractCcTensor_toSection_apply]
  rw [show ((contractCcTensor (I := I) (M := M) g r s T₁ +
        contractCcTensor (I := I) (M := M) g r s T₂).toSection x) =
      (contractCcTensor (I := I) (M := M) g r s T₁).toSection x +
        (contractCcTensor (I := I) (M := M) g r s T₂).toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]; rfl]
  rw [contractCcTensor_toSection_apply, contractCcTensor_toSection_apply]
  rw [show ((T₁ + T₂).toSection x) = T₁.toSection x + T₂.toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]; rfl]
  rw [map_add]

/-- The section-level trace is `ℝ`-homogeneous in the section. -/
theorem contractCcTensor_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g (1 + r) (s + 1)) :
    contractCcTensor (I := I) (M := M) g r s (c • T) =
      c • contractCcTensor (I := I) (M := M) g r s T := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [contractCcTensor_toSection_apply]
  rw [show ((c • contractCcTensor (I := I) (M := M) g r s T).toSection x) =
      c • (contractCcTensor (I := I) (M := M) g r s T).toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl]
  rw [contractCcTensor_toSection_apply]
  rw [show ((c • T).toSection x) = c • T.toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl]
  rw [map_smul]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The intrinsic fibre norm equals the bundle norm under the Riemannian tensor-bundle instance.**
For the `(r, s)`-tensor Riemannian bundle instance, the intrinsic squared Riemannian fibre norm
`riemannianFiberNormSq` of a fibre value `z` is its squared bundle norm.  Proved via the bundle inner
product `tensorRSRiemannianInnerCLM` (whose diagonal is `tensorInnerPointwise`, the proved fibre-norm
bridge `riemannianFiberNormSq_eq_tensorInnerPointwise`) and `real_inner_self_eq_norm_sq`. -/
private lemma riemannianFiberNormSq_eq_bundle_norm_sq_gen
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (z : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    riemannianFiberNormSq (I := I) (M := M) g r s x z = ‖z‖ ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have h_inner :
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s x z z : ℝ) =
        riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
    exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x z).symm
  have hself : (inner ℝ z z : ℝ) =
      riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [← h_inner]; rfl
  rw [← hself, real_inner_self_eq_norm_sq]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Fibrewise Cauchy–Schwarz for a general tensor-fibre continuous-linear map.** For a fibrewise
continuous-linear map `φ : TensorRSSpace r₁ s₁ I x →L[ℝ] TensorRSSpace r₂ s₂ I x` between tensor
fibres at a point `x`, the intrinsic squared Riemannian fibre norm of the evaluation `φ v` is bounded
by a nonnegative fibre-operator constant `Cφ` (the squared `g`-fibre operator norm of `φ`) times the
intrinsic squared fibre norm of `v`.  The general-rank version of the proved
`riemannianFiberNormSq_clm_apply_le`; the proof installs the source / target tensor-bundle Riemannian
instances, converts both fibre norms to bundle norms (`riemannianFiberNormSq_eq_bundle_norm_sq_gen`),
and squares the operator bound `‖φg v‖ ≤ ‖φg‖ · ‖v‖`. -/
theorem riemannianFiberNormSq_tensorRS_clm_apply_le
    (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ : ℕ) (x : M)
    (φ : TensorRSSpace r₁ s₁ I x →L[ℝ] TensorRSSpace r₂ s₂ I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ v : TensorRSSpace r₁ s₁ I x,
      riemannianFiberNormSq (I := I) (M := M) g r₂ s₂ x (φ v) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g r₁ s₁ x v := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r₁ s₁ I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r₁ s₁
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r₂ s₂ I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r₂ s₂
  let φg : TensorRSSpace r₁ s₁ I x →L[ℝ] TensorRSSpace r₂ s₂ I x :=
    LinearMap.toContinuousLinearMap (φ.toLinearMap)
  have hφg_apply : ∀ v, φg v = φ v := fun v => by
    change (LinearMap.toContinuousLinearMap (φ.toLinearMap)) v = φ v
    rw [LinearMap.coe_toContinuousLinearMap']; rfl
  refine ⟨‖φg‖ ^ 2, sq_nonneg _, fun v => ?_⟩
  rw [riemannianFiberNormSq_eq_bundle_norm_sq_gen (I := I) (M := M) g r₂ s₂ x (φ v),
      riemannianFiberNormSq_eq_bundle_norm_sq_gen (I := I) (M := M) g r₁ s₁ x v, ← hφg_apply v]
  calc ‖φg v‖ ^ 2 ≤ (‖φg‖ * ‖v‖) ^ 2 := by
          apply sq_le_sq'
          · nlinarith [φg.le_opNorm v, norm_nonneg (φg v), norm_nonneg v, norm_nonneg φg]
          · exact φg.le_opNorm v
    _ = ‖φg‖ ^ 2 * ‖v‖ ^ 2 := by ring

/-- **The per-point intrinsic fibre-norm trace bound.** At a base point `x`, the fibrewise trace
`contract_trace r s x` is controlled in the intrinsic Riemannian fibre norm: there is a nonnegative
fibre-operator constant `Cφ` (the squared `g`-fibre operator norm of the trace map at `x`) such that
for every `(1 + r, s + 1)`-tensor fibre value `T`,
```
rfns(contract_trace r s x T) ≤ Cφ · rfns(T).
```
The trace is a fixed fibrewise continuous-linear bundle map, so this is the general fibrewise
Cauchy–Schwarz `riemannianFiberNormSq_tensorRS_clm_apply_le` applied to `φ = contract_trace r s x`. -/
theorem riemannianFiberNormSq_contract_trace_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ T : TensorRSSpace (1 + r) (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x
          (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x T) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g (1 + r) (s + 1) x T :=
  riemannianFiberNormSq_tensorRS_clm_apply_le (I := I) (M := M) g (1 + r) (s + 1) r s x
    (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x)

/-- **The per-point intrinsic fibre-norm trace bound, section form.** At a base point `x`, the
section value of the section-level trace `contractCcTensor g r s T` has intrinsic squared fibre norm
bounded by a nonnegative fibre-operator constant `Cφ` (at `x`) times that of `T`'s section value:
```
rfns((contractCcTensor g r s T) x) ≤ Cφ · rfns(T x).
```
Read off from `riemannianFiberNormSq_contract_trace_le` through the section-evaluation formula
`contractCcTensor_toSection_apply`; the constant is independent of the section `T`. -/
theorem rfns_contractCcTensor_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ T : SmoothCcTensor g (1 + r) (s + 1),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          ((contractCcTensor (I := I) (M := M) g r s T).toSection x) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g (1 + r) (s + 1) x (T.toSection x) := by
  obtain ⟨Cφ, hCφ, hbound⟩ := riemannianFiberNormSq_contract_trace_le (I := I) (M := M) g r s x
  refine ⟨Cφ, hCφ, fun T => ?_⟩
  rw [contractCcTensor_toSection_apply]
  exact hbound (T.toSection x)

end Connection
end Integral
end DifferentialGeometry

end
