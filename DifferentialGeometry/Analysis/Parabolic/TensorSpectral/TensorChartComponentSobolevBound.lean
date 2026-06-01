import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentWkpNormBoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientEpNormPerAlpha
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# `α`-uniform `L²` bound for chart-frame scalar components

Consolidated `α`-uniform bounds on the chart-frame scalar components of
smooth compactly-supported `H¹` tensor sections on a closed Riemannian
manifold `(M, g)`:

1. **`α`-uniform `L²` bound for `tensorChartComponentScalar`** —
   `tensorChartComponentScalar_eLpNorm_le` (and the equivalent functional
   packaging `tensorChartComponentScalar_eLpNorm_le_forall`).

The constant in the headline is independent of the chart base point `α`,
the multi-index pair `(Idx, Jdx)`, and the section `S`. The strategy uses
local finiteness of the chart-atlas partition of unity, packaged via the
**active finset** `chartAtlasPOU_activeFinset I M`, on which the
partition-of-unity centres are finite in number, so summing per-`α`
constants over the active finset produces a single `α`-uniform constant.
On inactive centres the scalar component vanishes identically.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart

section ScalarUniform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- On a compact manifold, only finitely many partition-of-unity centres
have non-empty support. We package the set of such centres as a `Finset M`. -/
noncomputable def chartAtlasPOU_activeFinset
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] : Finset M :=
  ((chartAtlasPOU I M).locallyFinite.finite_nonempty_of_compact).toFinset

/-- An index `α : M` belongs to the active finset iff its partition-of-unity
support is non-empty. -/
lemma mem_chartAtlasPOU_activeFinset_iff (α : M) :
    α ∈ chartAtlasPOU_activeFinset I M ↔
      (Function.support (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).Nonempty := by
  classical
  unfold chartAtlasPOU_activeFinset
  exact Set.Finite.mem_toFinset _

/-- If `α : M` is NOT in the active finset, then `POU_α` is identically zero. -/
lemma chartAtlasPOU_eq_zero_of_notMem_activeFinset
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M) :
    ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
  classical
  intro x
  have h_empty :
      ¬ (Function.support (fun y : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y)).Nonempty := by
    intro h
    exact hα ((mem_chartAtlasPOU_activeFinset_iff (I := I) (M := M) α).mpr h)
  rw [Set.not_nonempty_iff_eq_empty, Function.support_eq_empty_iff] at h_empty
  have := congrFun h_empty x
  simpa using this

lemma tensorChartComponentScalar_eq_zero_of_pou_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (h_zero : ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx = 0 := by
  classical
  funext x
  change (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x =
    (0 : M → ℝ) x
  rw [h_zero x, zero_mul]; rfl

/-- For an inactive centre `α`, the `eLpNorm` of the scalar component is `0`. -/
private lemma eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  rw [h_scalar_zero]
  exact eLpNorm_zero

private noncomputable def perAlphaConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)

private lemma perAlphaConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaConstant (I := I) (M := M) g r s α :=
  (Classical.choose_spec (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)).1

private lemma perAlphaConstant_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
  (Classical.choose_spec (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)).2 S Idx Jdx

private noncomputable def totalActiveConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    perAlphaConstant (I := I) (M := M) g r s α

private lemma totalActiveConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaConstant_nonneg (I := I) (M := M) g r s α)

private lemma perAlphaConstant_le_totalActiveConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOU_activeFinset I M) :
    perAlphaConstant (I := I) (M := M) g r s α ≤
      totalActiveConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveConstant
  have h_split :
      ∑ β ∈ chartAtlasPOU_activeFinset I M,
        perAlphaConstant (I := I) (M := M) g r s β =
        perAlphaConstant (I := I) (M := M) g r s α +
        ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
          perAlphaConstant (I := I) (M := M) g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
            perAlphaConstant (I := I) (M := M) g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaConstant_nonneg (I := I) (M := M) g r s β)
  linarith

private theorem tensorChartComponentScalar_eLpNorm_le_smoothCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensor g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  refine ⟨totalActiveConstant (I := I) (M := M) g r s,
    totalActiveConstant_nonneg (I := I) (M := M) g r s, ?_⟩
  intro S α Idx Jdx
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · have h_per :
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
      perAlphaConstant_bound (I := I) (M := M) g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) ≤
          ENNReal.ofReal (totalActiveConstant (I := I) (M := M) g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaConstant_le_totalActiveConstant
          (I := I) (M := M) g r s hα)
    have h_envelope_le :
        ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) ≤
          ENNReal.ofReal (totalActiveConstant (I := I) (M := M) g r s) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le _)
    exact h_per.trans h_envelope_le
  · rw [eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive
      (I := I) (M := M) g r s hα S Idx Jdx]
    exact zero_le _

private lemma tensorL2Norm_eq_norm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
      ‖S.toCcTensor‖ := by
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S.toCcTensor
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
        S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have h_norm_nn : 0 ≤ ‖S.toCcTensor‖ := norm_nonneg _
  have h_lhs :
      tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := rfl
  rw [h_lhs]
  have h_rhs :
      ‖S.toCcTensor‖ = Real.sqrt
        (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := by
    rw [← Real.sqrt_sq h_norm_nn, h_sq]
  rw [h_rhs]

private lemma coe_nnnorm_eq_ofReal_norm_scalar {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

private lemma ofReal_tensorL2Norm_le_norm_ennreal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal
        (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
      (‖S‖₊ : ℝ≥0∞) := by
  rw [tensorL2Norm_eq_norm_toCcTensor (I := I) (M := M) g r s S]
  have h_l2_le_h1 :
      ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm_scalar S]
  exact ENNReal.ofReal_le_ofReal h_l2_le_h1

/-- **Headline theorem (α-uniform L² bound for chart-frame scalar
components).** -/
theorem tensorChartComponentScalar_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₀, hC₀_nn, h_smoothCc⟩ :=
    tensorChartComponentScalar_eLpNorm_le_smoothCcTensor
      (I := I) (M := M) g r s
  refine ⟨C₀, hC₀_nn, ?_⟩
  intro S α Idx Jdx
  have h_smoothCc' :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₀ *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s
              S.toCcTensor.toFun) :=
    h_smoothCc S.toCcTensor α Idx Jdx
  have h_rhs_le :
      ENNReal.ofReal C₀ *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
        ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) :=
    mul_le_mul_of_nonneg_left
      (ofReal_tensorL2Norm_le_norm_ennreal (I := I) (M := M) g r s S)
      (by exact zero_le _)
  exact h_smoothCc'.trans h_rhs_le

/-- Functional packaging of the headline `α`-uniform bound. -/
theorem tensorChartComponentScalar_eLpNorm_le_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) :=
  tensorChartComponentScalar_eLpNorm_le
    (I := I) (M := M) g r s

end ScalarUniform

section GradUniform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma sqrt_g_inner_gradFun_eq_zero_of_scalar_zero
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (h_u_zero : u = 0) :
    (fun b : M => Real.sqrt
        (g.inner b (gradFun (I := I) g u b)
          (gradFun (I := I) g u b))) = 0 := by
  funext b
  have h_ev : u =ᶠ[𝓝 b] (fun _ : M => (0 : ℝ)) := by
    rw [h_u_zero]; rfl
  have h_grad_zero :
      gradFun (I := I) g u b = (0 : TangentSpace I b) :=
    gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
  rw [h_grad_zero]
  have h_map : g.inner b (0 : TangentSpace I b) =
      (0 : TangentSpace I b →L[ℝ] ℝ) := map_zero _
  rw [h_map]
  change Real.sqrt ((0 : TangentSpace I b →L[ℝ] ℝ) (0 : TangentSpace I b)) =
    (0 : M → ℝ) b
  simp

private lemma eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (fun b : M => Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  have h_integrand_zero :
      (fun b : M => Real.sqrt
          (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b))) = 0 :=
    sqrt_g_inner_gradFun_eq_zero_of_scalar_zero
      (I := I) (M := M) g h_scalar_zero
  rw [h_integrand_zero]
  exact eLpNorm_zero

end GradUniform

section ChartSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) g 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  rw [h_scalar_zero]
  exact wkpNormChart_zero_fun (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)

end ChartSobolev

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
