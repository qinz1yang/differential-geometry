import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.IntrinsicL2Bridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBound
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Uniform bound on the chart-pushed `L^2` norm of the chart-frame scalar
component from the H^1 norm of the underlying tensor section

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a smooth
compactly-supported H^1 tensor section `S : SmoothCcTensorH1 g r s`, a chart
point `α : M`, and a multi-index pair `(Idx, Jdx)`, the chart-pushed image of
the chart-frame scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`, viewed as a
function on the Euclidean chart target via the canonical chart-push
construction, has its `L^2(Ω)`-seminorm controlled by a single non-negative
constant times the H^1 seminorm of `S`, where the constant depends only on
`(g, r, s, α, β)` and is independent of `S`, `Idx`, and `Jdx`.

This is the `L^2` component of the chart Sobolev norm decomposition

```
wkpNormChart g 1 2 u = eLpNorm u 2 (volume.restrict Ω)
                       + Σ_k eLpNorm (chosenWeakPartial' 2 k u Ω) 2 (volume.restrict Ω)
```

evaluated on the chart-pushed scalar component. The `L^2` piece is the first
summand and is the deliverable here. The order-one partial sum is delivered
in companion modules; that work requires bridging the chosen weak partial of
the chart-pushed scalar component to a chart-pulled-back classical Frechet
partial, then applying the Layer E decomposition together with the gradient
norm comparison at index `(r, s + 1)` and the uniform Christoffel sup bound.

## Strategy

The chart-pushed image and the manifold-side scalar component are linked by

```
eLpNorm (chartPushed (chartAtlasPOU I M) β u) 2 (volume.restrict (chartTargetEuclid β))
  ≤ ENNReal.ofReal C₁(g, β) * eLpNorm u 2 (riemannianVolumeMeasure g)
```

(provided as a uniform-in-`u` reverse bridge below). Combined with the
manifold-side `L^2` uniform-in-`(Idx, Jdx)` bound

```
eLpNorm (tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx) 2
    (riemannianVolumeMeasure g)
  ≤ ENNReal.ofReal C₂(g, r, s, α) *
      ENNReal.ofReal (tensorL2Norm g r s S.toCcTensor.toFun)
```

(from `ComponentL2BoundUniform`), and the embedding `‖S.toCcTensor‖ ≤ ‖S‖`
on smooth sections (from `H1Compl`), the chart-pushed `L^2` seminorm of the
component scalar is bounded by `ENNReal.ofReal (C₁ * C₂) * ‖S‖₊`, uniformly
in `(S, Idx, Jdx)`.

## Public theorems

* `eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform`
  — uniform-in-`u` chart-pushed `L^2` reverse bridge.

* `eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm`
  — the chart-pushed `L^2` seminorm of the scalar component is bounded by
  `ENNReal.ofReal C * ‖S‖₊`, with `C` independent of `S`, `Idx`, `Jdx`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma abs_pou_mul_le_abs_local
    (β : M) (u : M → ℝ) (x : M) :
    |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| ≤ |u x| := by
  rw [abs_mul]
  have hρ_nn : 0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg β x
  have hρ_le : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one β x
  have hρ_abs_le_one : |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| ≤ 1 := by
    rw [abs_of_nonneg hρ_nn]; exact hρ_le
  calc |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| * |u x|
      ≤ 1 * |u x| := by gcongr
    _ = |u x| := one_mul _

theorem eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform
    (g : SmoothRiemannianMetric I M) (β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : M → ℝ) (_hu_meas : Measurable u),
        eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C *
            eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β with hρ_def
  set Kβ : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKβ_def
  have hKβ_compact : IsCompact Kβ := (isClosed_tsupport _).isCompact
  have hKβ_sub : Kβ ⊆ (chartAt H β).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g β hKβ_compact hKβ_sub hp_one hp_top
  refine ⟨C, hC_pos.le, ?_⟩
  intro u hu_meas
  set f : M → ℝ := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x with hf_def
  have hρ_cont : Continuous ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (ρ.contMDiff).continuous
  have hf_meas : Measurable f := hρ_cont.measurable.mul hu_meas
  have hf_supp : tsupport f ⊆ Kβ := by
    have h_eq : f = (fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • u x) := by
      funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_raw_bound := hC_bound (u := f) hf_meas hf_supp
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g from rfl]
    at h_raw_bound
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
      (I := I) (M := M)
      (ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      β u
  rw [eLpNorm_congr_ae h_ae]
  refine h_raw_bound.trans ?_
  gcongr
  refine eLpNorm_mono (f := f) (g := u) ?_
  intro x
  have h_norm_f : ‖f x‖ = |((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| := Real.norm_eq_abs _
  have h_norm_u : ‖u x‖ = |u x| := Real.norm_eq_abs _
  rw [h_norm_f, h_norm_u]
  exact abs_pou_mul_le_abs_local (I := I) (M := M) β u x

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

private lemma ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
      (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
  have h_norm_eq :
      ‖S.toCcTensor‖ = tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) S.toCcTensor
  rw [← h_norm_eq, ← coe_nnnorm_eq_ofReal_norm]

private lemma nnnorm_toCcTensor_le_nnnorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) := by
  have h_real : ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm, coe_nnnorm_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h_real

/-- **Headline `L^2`-piece bound (uniform in `S` and in multi-indices, fixed
charts `α, β`).**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart point
`α : M` for the chart-frame coordinates of the scalar component, and a chart
point `β : M` along which the manifold-side scalar field is pushed forward
to the Euclidean chart target, there is a single non-negative real constant
`C` (depending only on `(g, r, s, α, β)`) such that for every smooth
compactly-supported H^1 tensor section `S : SmoothCcTensorH1 g r s` and every
multi-index pair `(Idx, Jdx)`, the `L^2(volume.restrict (chartTargetEuclid β))`
seminorm of the chart-pushed image of the manifold-side scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is bounded by
`ENNReal.ofReal C * ‖S‖₊`.

The constant `C` is independent of `S`, `Idx`, and `Jdx`.

The proof chains three existing uniform bounds:

1. **Chart-pushed `L^2` reverse bridge**, uniform-in-`u` form delivered
   above: `eLpNorm (chartPushed β u) 2 (volume.restrict ChTE_β)
       ≤ ENNReal.ofReal C₁ * eLpNorm u 2 (riemannianVolumeMeasure g)`
   for measurable `u : M → ℝ`, with `C₁ ≥ 0` depending only on `(g, β)`.

2. **Manifold `L^2` bound for the scalar component**
   (`ComponentL2BoundUniform`):
   `eLpNorm (tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx) 2
       (riemannianVolumeMeasure g)
       ≤ ENNReal.ofReal C₂ * ENNReal.ofReal (tensorL2Norm g r s S.toCcTensor.toFun)`
   with `C₂ ≥ 0` depending only on `(g, r, s, α)`, uniformly in `(S, Idx, Jdx)`.

3. **`L^2 ≤ H^1`** (`H1Compl`): `‖S.toCcTensor‖ ≤ ‖S‖`, equivalently
   `ENNReal.ofReal (tensorL2Norm g r s S.toCcTensor.toFun) ≤ (‖S‖₊ : ℝ≥0∞)`. -/
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁_uniform⟩ :=
    eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform
      (I := I) (M := M) g β
  obtain ⟨C₂, hC₂_nn, h_man⟩ :=
    tensorChartComponentScalar_eLpNorm_le_uniform
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C₁ * C₂, mul_nonneg hC₁_nn hC₂_nn, ?_⟩
  intro S Idx Jdx
  set u : M → ℝ :=
    tensorChartComponentScalar (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
    with hu_def
  have hu_meas : Measurable u :=
    (tensorChartComponentScalar_contMDiff (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx).continuous.measurable
  have hA :
      eLpNorm
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
          ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C₁ *
          eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hC₁_uniform u hu_meas
  have hB :
      eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₂ *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) := by
    rw [hu_def]
    exact h_man S.toCcTensor Idx Jdx
  have hAB :
      eLpNorm
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
          ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun)) := by
    calc eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) := hA
      _ ≤ ENNReal.ofReal C₁ *
            (ENNReal.ofReal C₂ *
              ENNReal.ofReal
                (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun)) :=
          mul_le_mul_of_nonneg_left hB (by exact zero_le _)
  have h_eq :
      ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
        (‖S.toCcTensor‖₊ : ℝ≥0∞) :=
    ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor
      (I := I) (M := M) g r s S
  have h_le :
      (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) :=
    nnnorm_toCcTensor_le_nnnorm (I := I) (M := M) g r s S
  refine hAB.trans ?_
  rw [h_eq]
  calc ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ * (‖S.toCcTensor‖₊ : ℝ≥0∞))
      = (ENNReal.ofReal C₁ * ENNReal.ofReal C₂) *
            (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (C₁ * C₂) * (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
        rw [(ENNReal.ofReal_mul hC₁_nn).symm]
    _ ≤ ENNReal.ofReal (C₁ * C₂) * (‖S‖₊ : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_left h_le (by exact zero_le _)

/-- Functional packaging: for fixed `(g, r, s, α, β)`, the chart-pushed
`L²` seminorm of the scalar component is uniformly controlled across the
multi-index family by a single constant times the H¹ seminorm of `S`. -/
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          eLpNorm
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)) 2
              ((volume :
                  Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (I := I) (M := M) g r s α β

/-- Single-chart specialisation: `α = β`. The chart used for component
extraction is the same as the chart used to push the manifold-side scalar
field forward to the Euclidean target. -/
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (I := I) (M := M) g r s α α

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
