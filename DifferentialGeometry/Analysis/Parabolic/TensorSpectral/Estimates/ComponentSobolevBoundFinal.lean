import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBoundDerivBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.PartialL2Transfer
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.IntrinsicL2Bridge

/-!
# Per-section chart-Sobolev bound for tensor scalar components, uniform in
multi-indices

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart point
`α : M`, and a smooth compactly-supported H¹ tensor section
`S : SmoothCcTensorH1 g r s`, this file delivers the per-section chart-Sobolev
norm bound

  `wkpNormChart g 1 2 (tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx)
      ≤ ENNReal.ofReal C * (‖S‖₊ + 1)`

with a single non-negative constant `C` (depending on `(g, r, s, α, S)`) that
is **uniform across the finite multi-index pair `(Idx, Jdx)`**.

The bound is a strengthening of `tensorChartComponent_wkpNormChart_le_per_section`
in `ComponentSobolevBound.lean`, which produces a constant that may vary with
`(Idx, Jdx)`. The improvement is obtained by summing the per-multi-index
constants over the (finite) multi-index Finset.

This is the headline existential `wkpNormChart` bound consumed by the
downstream spectral pipeline when an `(Idx, Jdx)`-uniform constant is
required for the per-section assembly.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

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

/-- For a finite indexed family of non-negative reals, the sum dominates each
individual element. -/
private lemma le_sum_of_mem_finset_nonneg
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf_nn : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ ∑ j, f j := by
  classical
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have h_split :
      ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := by
    rw [← Finset.sum_erase_add _ _ hmem, add_comm]
  have h_rest_nn :
      0 ≤ ∑ j ∈ Finset.univ.erase i, f j :=
    Finset.sum_nonneg (fun j _ => hf_nn j)
  linarith

/-- **Headline per-section bound (uniform in multi-indices).** For each
chart point `α : M`, ranks `(r, s)`, and smooth compactly-supported H¹ tensor
section `S : SmoothCcTensorH1 g r s`, there is a single non-negative real
constant `C` (depending on `(g, r, s, α, S)`) such that for every multi-index
pair `(Idx, Jdx)`, the chart-Sobolev `W^{1,2}` norm of the chart-frame scalar
component `tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is
bounded by `ENNReal.ofReal C * (‖S‖₊ + 1)`.

The constant `C` is uniform across the (finite) multi-index family
`(Fin r → Fin d) × (Fin s → Fin d)` with `d = Module.finrank ℝ E`. -/
theorem tensorChartComponentScalar_wkpNormChart_le_per_section_improved
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E))),
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α IJ.1 IJ.2) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun IJ =>
    tensorChartComponent_wkpNormChart_le_per_section
      (I := I) (M := M) g r s S α IJ.1 IJ.2
  choose CIJ hCIJ_nn hCIJ_le using hper
  set Csum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                          (Fin s → Fin (Module.finrank ℝ E)),
    CIJ IJ with hCsum_def
  have hCsum_nn : 0 ≤ Csum :=
    Finset.sum_nonneg (fun IJ _ => hCIJ_nn IJ)
  refine ⟨Csum, hCsum_nn, ?_⟩
  intro Idx Jdx
  have hsmd : CIJ (Idx, Jdx) ≤ Csum :=
    le_sum_of_mem_finset_nonneg
      (f := fun IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E)) => CIJ IJ)
      (fun IJ => hCIJ_nn IJ) (Idx, Jdx)
  have h_ofReal_le : ENNReal.ofReal (CIJ (Idx, Jdx)) ≤
      ENNReal.ofReal Csum := ENNReal.ofReal_le_ofReal hsmd
  have h_envelope_le :
      ENNReal.ofReal (CIJ (Idx, Jdx)) * (‖S‖₊ + 1) ≤
        ENNReal.ofReal Csum * (‖S‖₊ + 1) :=
    mul_le_mul_of_nonneg_right h_ofReal_le (by exact zero_le _)
  exact (hCIJ_le (Idx, Jdx)).trans h_envelope_le

/-- Functional packaging of the headline bound: for each `(g, r, s, α)` the
per-section, uniform-in-multi-index bound holds for every
`S : SmoothCcTensorH1 g r s`. -/
theorem tensorChartComponentScalar_wkpNormChart_le_per_section_improved_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          wkpNormChart (I := I) (M := M) g 1 2
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  tensorChartComponentScalar_wkpNormChart_le_per_section_improved
    (I := I) (M := M) g r s α S

/-- Sum across the (finite) multi-index family of the chart-Sobolev norms,
bounded by a single non-negative constant times `(‖S‖₊ + 1)`. -/
theorem sum_tensorChartComponentScalar_wkpNormChart_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α IJ.1 IJ.2) ≤
        ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  obtain ⟨C, hC_nn, hC_le⟩ :=
    tensorChartComponentScalar_wkpNormChart_le_per_section_improved
      (I := I) (M := M) g r s α S
  set N : ℕ := Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                              (Fin s → Fin (Module.finrank ℝ E))) with hN_def
  refine ⟨(N : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC_nn, ?_⟩
  have h_sum_le :
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α IJ.1 IJ.2) ≤
      ∑ _IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
        ENNReal.ofReal C * (‖S‖₊ + 1) :=
    Finset.sum_le_sum (fun IJ _ => hC_le IJ.1 IJ.2)
  refine h_sum_le.trans ?_
  rw [Finset.sum_const, Finset.card_univ]
  change (N : ℕ) • (ENNReal.ofReal C * (‖S‖₊ + 1)) ≤
      ENNReal.ofReal ((N : ℝ) * C) * (‖S‖₊ + 1)
  rw [nsmul_eq_mul]
  have hN_ofReal : (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  rw [hN_ofReal]
  rw [show ENNReal.ofReal (N : ℝ) * (ENNReal.ofReal C * (‖S‖₊ + 1)) =
        (ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C) * (‖S‖₊ + 1) from
      (mul_assoc _ _ _).symm]
  rw [show ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C =
        ENNReal.ofReal ((N : ℝ) * C) from
      (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
