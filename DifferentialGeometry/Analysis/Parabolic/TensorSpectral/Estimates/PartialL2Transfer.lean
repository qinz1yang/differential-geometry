import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevPointwise
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBoundDerivBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.IntrinsicL2Bridge

/-!
# Partial `L^2` transfer: uniform-in-multi-index bound on the chart-pushed
chosen weak partial of the scalar component

For a closed Riemannian manifold `(M, g)` and a smooth compactly-supported
`(r, s)`-tensor section `S : SmoothCcTensorH1 g r s`, the chart-pushed
scalar component
`chartPushed (chartAtlasPOU I M) β (tensorChartComponentScalar g r s S α Idx Jdx)`
on the Euclidean chart target `chartTargetEuclid β` admits a chosen weak
partial `chosenWeakPartial' 2 k _ Ω` in each coordinate direction `k`. The
parent module `ComponentSobolevBoundDerivBridge` produces a per-section
finite-`L^2` bound

```
eLpNorm (chosenWeakPartial' 2 k ...) ≤ ENNReal.ofReal C(S, Idx, Jdx) *
  (‖S‖₊ + 1)
```

where the real constant `C(S, Idx, Jdx)` is built by taking
`(eLpNorm ...).toReal + 1` of the same quantity (so it is genuinely
per-section, and varies with the multi-index pair).

This file packages a sequence of polished consequences obtained from the
parent bound combined with `ComponentSobolevPointwise`'s uniform-in-
multi-index pointwise estimate
`exists_const_fderiv_tensorChartComponentRaw_pullback_norm_sq_le`.

## Headline results

* `exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices`
  — for fixed `(g, r, s, α, β, k)`, there is a single non-negative real
  constant `C` such that for every smooth compactly-supported section `S`
  and every multi-index pair `(Idx, Jdx)`, the chart-pushed chosen weak
  partial of the scalar component has `eLpNorm` bounded by
  `ENNReal.ofReal C * (‖S‖₊ + 1)`. The constant is uniform across the
  finite multi-index family but still depends on `S` via the
  per-section assembly.

* `exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices`
  — the sum-over-`k` consolidation, again with a single constant
  uniform across multi-index pairs and across coordinate directions
  (depending on `S`, `α`, `β`, but not on `Idx`, `Jdx`).

* `exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_S`
  — packaged existential form combining the multi-index sum and the
  envelope `(‖S‖₊ + 1)` factor, mirroring the polished signature style of
  the parent F.1.a bound.

The constants here are uniform in the multi-index pair `(Idx, Jdx)`; they
remain per-section (depending on `S`). A truly uniform-in-`S` constant
requires the full chain through the chart-pushed gradient operator-norm
bound and the Christoffel decomposition, which is built up in adjacent
modules.
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

/-- For a finite indexed family of non-negative reals, the sum dominates
each element. -/
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

/-- **Uniform-in-multi-index per-section `L^2` bound for the chosen weak
partial of the chart-pushed scalar component.** For each chart pair
`(α, β)`, ranks `(r, s)`, direction `k`, and smooth compactly-supported
section `S`, there is a single non-negative real constant `C` such that
for every multi-index pair `(Idx, Jdx)`, the `L^2` norm of
`chosenWeakPartial' 2 k (chartPushed ... (tensorChartComponentScalar S α Idx Jdx))`
on `chartTargetEuclid β` is bounded by `ENNReal.ofReal C * (‖S‖₊ + 1)`.

The constant `C` depends on `(g, r, s, S, α, β, k)` but is independent of
`(Idx, Jdx)`. -/
theorem exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E))),
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α IJ.1 IJ.2))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun IJ =>
    eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_per_section
      (I := I) (M := M) g r s S α β IJ.1 IJ.2 k
  choose CIJ hCIJ_nn hCIJ_le using hper
  set Csum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                          (Fin s → Fin (Module.finrank ℝ E)),
    CIJ IJ with hCsum_def
  refine ⟨Csum, Finset.sum_nonneg (fun IJ _ => hCIJ_nn IJ), ?_⟩
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

/-- **Uniform-in-multi-index sum-over-coordinate-directions per-section
`L^2` bound.** For each chart pair `(α, β)`, ranks `(r, s)`, and smooth
compactly-supported section `S`, there is a single non-negative real
constant `C` such that for every multi-index pair `(Idx, Jdx)`, the sum
over coordinate directions of the `L^2` norms of
`chosenWeakPartial' 2 k (chartPushed ... (tensorChartComponentScalar S α Idx Jdx))`
on `chartTargetEuclid β` is bounded by `ENNReal.ofReal C * (‖S‖₊ + 1)`. -/
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ k : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun k =>
    exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
      (I := I) (M := M) g r s S α β k
  choose Ck hCk_nn hCk_le using hper
  set Ctot : ℝ := ∑ k : Fin (Module.finrank ℝ E), Ck k with hCtot_def
  refine ⟨Ctot, Finset.sum_nonneg (fun k _ => hCk_nn k), ?_⟩
  intro Idx Jdx
  have h_sum_le :
      ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
        ∑ k : Fin (Module.finrank ℝ E),
          ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) :=
    Finset.sum_le_sum (fun k _ => hCk_le k Idx Jdx)
  refine h_sum_le.trans ?_
  rw [show
        ∑ k : Fin (Module.finrank ℝ E),
          ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) =
        (∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k)) *
          (‖S‖₊ + 1) from
      (Finset.sum_mul (s := Finset.univ)
        (f := fun k : Fin (Module.finrank ℝ E) => ENNReal.ofReal (Ck k))
        (a := (‖S‖₊ + 1))).symm]
  have h_ofReal_sum :
      ∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k) ≤
        ENNReal.ofReal (∑ k : Fin (Module.finrank ℝ E), Ck k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hCk_nn k)]
  exact mul_le_mul_of_nonneg_right h_ofReal_sum (by exact zero_le _)

/-- Per-direction packaged form: a single non-negative constant works
uniformly in `(Idx, Jdx)` for fixed `(g, r, s, S, α, β, k)`. This is the
polished signature shape exposed for downstream consumption. -/
theorem exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_S
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α β k

/-- Sum-over-directions packaged form: a single non-negative constant
controls the sum over coordinate directions, uniformly in `(Idx, Jdx)`
for fixed `(g, r, s, S, α, β)`. -/
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_S
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm
                (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                  (d := Module.finrank ℝ E) 2 k
                  (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                    (tensorChartComponentScalar (I := I) (M := M)
                      g r s S.toCcTensor α Idx Jdx))
                  (chartTargetEuclid (I := I) (M := M) β)) 2
                (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α β

/-- Single-chart specialisation of the per-direction bound: `α = β`. -/
theorem exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) :=
  exists_const_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α α k

/-- Single-chart specialisation of the sum-over-directions bound. -/
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) α)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) :=
  exists_const_sum_eLpNorm_chosenWeakPartial'_chartPushed_le_uniform_indices
    (I := I) (M := M) g r s S α α

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
