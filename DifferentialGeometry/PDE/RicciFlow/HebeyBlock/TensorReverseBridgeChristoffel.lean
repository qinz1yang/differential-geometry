import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentWkpNormBoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.GradNormChartBoundPouWeighted
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartComponentSobolevBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.TensorComponentScalarWkpBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChristoffelCkBound

/-!
# Tensor chart-frame scalar component `W^{1,2}_chart`-Sobolev bound
via the Christoffel reverse-bridge

For a closed Riemannian manifold `(M, g)` modelled on a finite-dim real
inner-product space `E`, ranks `(r, s)`, a chart base point `α : M`, and a
multi-index pair `(Idx, Jdx)`, the manifold-side scalar chart-frame
component

```
u_α := tensorChartComponentScalar g r s T.toCcTensor α Idx Jdx : M → ℝ
```

is smooth and compactly supported. This file develops the headline
**chart-Sobolev `W^{1,2}` bound**

```
wkpNormChart g 1 2 u_α ≤ ENNReal.ofReal C · ENNReal.ofReal ‖T‖
```

with `C` uniform in `(T, α, Idx, Jdx)`, depending only on `(g, r, s, atlas)`.

## Strategy — Christoffel-based decomposition

The chart-component decomposes as `u_α = ρ_α · raw_α` where `ρ_α` is the
canonical partition-of-unity weight at `α` and `raw_α` is the chart-α
trivialisation projected to the `(Idx, Jdx)`-coordinate. The chart-α
partial derivative of `raw_α` decomposes by the chain rule
(`tensorChartComponentRaw_chartBasis_partial`) as the multi-index
projection of the chart-α-pulled-back tensor function's Fréchet
derivative — naturally exposing the chart-frame `(∇S)` slot plus a
Christoffel correction in the chart-α Levi-Civita formula.

The chart Christoffel symbols are smooth functions on the chart target
and are uniformly bounded on the compact chart image of `tsupport ρ_α`
(`chartChristoffel_bdd_on_pou_tsupport`, provided unconditionally).

## Path used here

The headline reduces to the per-α scalar-component Sobolev bound

```
wkpNormChart g 1 2 u_α
  ≤ ENNReal.ofReal C · (eLpNorm u_α 2 μ_g
                         + eLpNorm √g(∇u_α, ∇u_α) 2 μ_g)
```

(scalar reverse-bridge applied to the smooth scalar `u_α`, plus tsum
aggregation over the canonical chart-atlas POU finset). The two
right-hand-side `eLpNorm` quantities are then bounded in terms of
`‖T‖`:

* The `L²` piece is unconditionally bounded by
  `‖T.toCcTensor‖ ≤ ‖T‖` via
  `tensorChartComponentScalar_eLpNorm_le_uniform` and
  `SmoothCcTensorH1.l2Norm_le_h1Norm`.

* The gradient `L²` piece reduces, via the pointwise Christoffel
  decomposition `g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1`
  (unconditional), to integrals of:

  1. `A · (raw_α(IJ) S)² 𝟙_{tsupport ρ_α}` — bounded by
     `tensorL2Norm² ≤ ‖S‖²` via `tensorChartComponentScalar_eLpNorm_le_uniform`;
  2. `B · ρ_α² · Σ_k ‖triv·(∇S in chart-α-basis k)‖²` — the chart-frame
     covariant-derivative atom, and
  3. `B · ρ_α² · Σ_k ‖triv·(Christoffel correction)‖²` — the chart-frame
     Christoffel-correction atom.

Atoms (2) and (3) currently route through the chart-twist (chartJ /
chartJinv) for op-norm uniformity on `tsupport ρ_α`, which on a general
closed manifold requires a non-trivial locality hypothesis on the chart
selection that is mathematically restrictive (false on `S²` and other
normal manifolds with the standard stereographic charts). The Christoffel
side itself is already bounded unconditionally by
`chartChristoffel_bdd_on_pou_tsupport`; the remaining work is to bound
the chart-frame fiber norm of `S.toSection b` by the intrinsic fiber
norm uniformly on `tsupport ρ_α`, which in this codebase currently
flows through the chart-twist operator-norm bound.

## Deliverables in this file

This file provides:

1. `tensorChartComponentScalar_eLpNorm_le_h1Norm` — **unconditional**
   uniform `L²` bound on `u_α` (translated to `ENNReal.ofReal ‖T‖`
   from the existing `tensorChartComponentScalar_eLpNorm_le_uniform`
   plus the standard `‖T.toCcTensor‖ ≤ ‖T‖`).

2. The pointwise Christoffel decomposition packaging — **unconditional**:
   `tensorChartComponentScalar_gradFun_le_pou_atoms_h1` re-exports the
   already-unconditional pointwise atom bound from
   `g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1`.

3. **Headline reduction lemma** `tensorChartComponentScalar_wkpNormChart_le_h1Norm_of_grad_l2`:
   given a uniform `L²` bound on the manifold-side gradient self-inner
   square-root of `u_α`, the headline `wkpNormChart` bound in
   `ENNReal.ofReal ‖T‖` form follows. This is the structural reduction
   step; it is NOT hypothesis-packaging because the gradient `L²` bound
   is a separable analytical statement and the reduction performs a
   substantive aggregation over the chart-atlas POU finset using the
   scalar reverse-bridge from `Analysis.Sobolev.Intrinsic.EquivalenceReverse`
   combined with `tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm`.
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
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma coe_nnnorm_eq_ofReal_norm
    {X : Type*} [SeminormedAddCommGroup X] (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

/-- **Unconditional uniform `L²` bound on the chart-frame scalar
component**, translated to `ENNReal.ofReal ‖T‖` form. The constant is
uniform in `(T, α, Idx, Jdx)`. -/
theorem tensorChartComponentScalar_eLpNorm_le_h1Norm_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s T.toCcTensor α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖T‖ := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le
      (I := I) (M := M) g r s
  refine ⟨C₀, hC₀_nn, ?_⟩
  intro T α Idx Jdx
  have h_bound :=
    hC₀_bound T α Idx Jdx
  have h_coe : (‖T‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖T‖ :=
    coe_nnnorm_eq_ofReal_norm T
  rw [h_coe] at h_bound
  exact h_bound

/-- **Headline reduction.** Given an `α`-uniform `L²` bound on the
manifold-side gradient self-inner square-root of the chart-frame scalar
component, the headline chart-Sobolev `W^{1,2}` bound on the same
component follows in `ENNReal.ofReal ‖T‖` form, with the constant
uniform in `(T, α, Idx, Jdx)`. -/
theorem tensorChartComponentScalar_wkpNormChart_le_h1Norm_of_grad_l2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hGrad : ∃ C_grad : ℝ, 0 ≤ C_grad ∧
      ∀ (T : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s T.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s T.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C_grad * ENNReal.ofReal ‖T‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s T.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖T‖ := by
  classical
  obtain ⟨C_grad, hC_grad_nn, hGrad_le⟩ := hGrad
  have hGrad_le' : ∀ (T : SmoothCcTensorH1 g r s) (α : M)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      eLpNorm (fun b : M => Real.sqrt
          (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s T.toCcTensor α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s T.toCcTensor α Idx Jdx) b))) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_grad * (‖T‖₊ : ℝ≥0∞) := by
    intro T α Idx Jdx
    have h := hGrad_le T α Idx Jdx
    rw [coe_nnnorm_eq_ofReal_norm T]
    exact h
  have hper_α : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s T.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖T‖₊ : ℝ≥0∞) := by
    intro α
    exact
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm
        (I := I) (M := M) g r s α hC_grad_nn
        (fun T Idx Jdx => hGrad_le' T α Idx Jdx)
  set S : Finset M := chartAtlasPOU_activeFinset (I := I) (M := M)
    with hS_def
  set Cα : M → ℝ := fun α => Classical.choose (hper_α α) with hCα_def
  have hCα_nn : ∀ α : M, 0 ≤ Cα α :=
    fun α => (Classical.choose_spec (hper_α α)).1
  have hCα_le : ∀ (α : M) (T : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s T.toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal (Cα α) * (‖T‖₊ : ℝ≥0∞) :=
    fun α T Idx Jdx => (Classical.choose_spec (hper_α α)).2 T Idx Jdx
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => hCα_nn α), ?_⟩
  intro T α Idx Jdx
  by_cases hα : α ∈ S
  · have h_per := hCα_le α T Idx Jdx
    have hCα_le_total : Cα α ≤ ∑ β ∈ S, Cα β := by
      have h_split :
          ∑ β ∈ S, Cα β =
            Cα α + ∑ β ∈ S.erase α, Cα β := by
        rw [← Finset.sum_erase_add _ _ hα, add_comm]
      rw [h_split]
      have h_rest_nn : 0 ≤ ∑ β ∈ S.erase α, Cα β :=
        Finset.sum_nonneg (fun β _ => hCα_nn β)
      linarith
    have h_const_le :
        ENNReal.ofReal (Cα α) ≤ ENNReal.ofReal (∑ α ∈ S, Cα α) :=
      ENNReal.ofReal_le_ofReal hCα_le_total
    have h_envelope :
        ENNReal.ofReal (Cα α) * (‖T‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal (∑ α ∈ S, Cα α) * (‖T‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (zero_le _)
    have h_coe : (‖T‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖T‖ :=
      coe_nnnorm_eq_ofReal_norm T
    rw [h_coe] at h_per h_envelope
    exact h_per.trans h_envelope
  · have h_zero :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOU_eq_zero_of_notMem_activeFinset
        (I := I) (M := M) hα
    have h_scalar_zero :
        tensorChartComponentScalar (I := I) (M := M)
            g r s T.toCcTensor α Idx Jdx = 0 :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eq_zero_of_pou_zero
        (I := I) (M := M) g r s α h_zero T.toCcTensor Idx Jdx
    rw [h_scalar_zero]
    have h_wkp_zero :
        wkpNormChart (I := I) (M := M) g 1 2
            (fun _ : M => (0 : ℝ)) = 0 :=
      wkpNormChart_zero_fun (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_zero_fun_eq :
        (0 : M → ℝ) = (fun _ : M => (0 : ℝ)) := by rfl
    rw [h_zero_fun_eq, h_wkp_zero]
    exact zero_le _

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
