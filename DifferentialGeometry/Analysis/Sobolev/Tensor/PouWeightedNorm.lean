import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A partition-of-unity-weighted chart-Sobolev norm for tensor sections

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner product space `E`, and a smooth compactly-supported `(r, s)`-tensor
section `T`, this file defines an alternative aggregated Sobolev-type norm
`tensorPouSobolevNorm g k T`. The norm collects, on every chart, the squared
norms of the iterated Fréchet derivatives (orders `0, 1, …, 2k`) of the **raw**
chart-frame scalar components (no partition-of-unity multiplier inside the
function being differentiated), and integrates each squared norm against the
chart's Lebesgue measure weighted, externally, by the canonical chart-atlas
partition of unity. The square root of the resulting `tsum` of finite sums is
then taken.

Schematically, with `n = finrank ℝ E`, `IJ = (Idx, Jdx)` the component
multi-index pair, and writing `ρ_α := chartAtlasPOU I M α` for the chart-`α`
partition-of-unity weight,
`tensorPouSobolevNorm g k T` is

`(∑'α, ∑_{IJ} ∑_{j ≤ 2k} ∫ ρ_α(p(y)) · ‖D^j (Tᵅ_{IJ} ∘ φᵅ⁻¹)(p(y))‖² dy)^{1/2}`,

where `p` shorthand for `(extChartAt I α).symm ∘ toEuclidean.symm` (the Euclidean
representation map), `φᵅ := extChartAt I α`, and `Tᵅ_{IJ}` is the raw chart-`α`
`(Idx, Jdx)`-component of `T` (no partition-of-unity multiplier).

The contrast with the existing `wtwokTwoNorm g k T` from
`Analysis/Sobolev/Tensor/Defs.lean` is that there each chart component carries
the partition-of-unity weight inside the function before differentiation (via
`tensorChartComponent` = `chartPushedRaw α (tensorChartComponentPou α …)`),
producing residual partition-of-unity derivatives upon iteration. Here the
partition of unity appears as a measure weight, so the Leibniz expansion of
`iteratedFDeriv` does not produce partition-of-unity-free residual terms — the
partition of unity is never differentiated. The two norms are equivalent (up to
bounded constants) to the intrinsic Sobolev norm of order `2k`, but they are not
identical; both are useful, on different occasions.

## Main definitions

* `tensorPouSobolevNorm g k T` — the partition-of-unity-weighted chart-Sobolev
  norm of `T` at regularity order `2k`.

## Main results

* `tensorPouSobolevNorm_nonneg`, `tensorPouSobolevNorm_zero_section` — basic
  non-negativity and vanishing-at-zero.
* `tensorPouSobolevNorm_le_succ` — monotonicity in `k`:
  `tensorPouSobolevNorm g k T ≤ tensorPouSobolevNorm g (k + 1) T`.

## Implementation

The norm is built directly from `tensorChartComponentRaw` (the
partition-of-unity-free chart-frame scalar component on `M`) composed with
`(extChartAt I α).symm` to reach the Euclidean model, integrated against
`(volume : Measure (EuclideanSpace ℝ (Fin n)))` with the partition of unity
appearing as an `ENNReal.ofReal` multiplicative weight on the integrand.

The `α`-`tsum` ranges over all of `M`; outside the finite set of charts where
the partition of unity has nonempty support the integrand vanishes
identically, so the sum is well-defined regardless of the chart-`α`
contributions outside the support.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The partition-of-unity-weighted chart-Sobolev norm of a smooth
compactly-supported `(r, s)`-tensor section `T` at regularity order `2k`.

Concretely, a square root of a `tsum` over chart base points `α : M` of the
finite sum, over component multi-indices `IJ` and over Fréchet-derivative
orders `j ≤ 2k`, of the integral, against the volume measure of the chart
target in `EuclideanSpace ℝ (Fin n)` (where `n = finrank ℝ E`), of the
partition-of-unity weight at `α` (composed with the Euclidean representation
map back to `M`) times the squared norm of the `j`-th Fréchet derivative of the
raw chart-frame `(Idx, Jdx)`-component composed with `(extChartAt I α).symm`,
evaluated at the corresponding point of `E`.

The partition of unity appears as a measure weight, not as a function multiplier
inside the function being differentiated, so the iterated derivative never
produces partition-of-unity-free residual terms. -/
noncomputable def tensorPouSobolevNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  (∑' α : M,
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ)

/-- Unfolding lemma for `tensorPouSobolevNorm`. -/
theorem tensorPouSobolevNorm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T =
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ) := rfl

/-- The partition-of-unity-weighted chart-Sobolev norm is non-negative.
(It is valued in `ℝ≥0∞`, so this is the trivial `0 ≤ ·` fact, recorded for
downstream convenience.) -/
theorem tensorPouSobolevNorm_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ tensorPouSobolevNorm (I := I) (M := M) g k T :=
  zero_le _

/-- The raw chart-frame scalar component of the zero tensor section is the
zero function on `M`. Follows from `tensorChartComponentRaw_smul` applied with
the zero scalar. -/
private lemma tensorChartComponentRaw_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx = (fun _ : M => 0) := by
  classical
  funext x
  have h := tensorChartComponent_smul (I := I) (M := M) g r s (0 : ℝ)
    (0 : SmoothCcTensor g r s) α Idx Jdx
  unfold tensorChartComponentRaw
  have h0 : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
          ((0 : SmoothCcTensor g r s).toSection x) = 0 := by
    have hsec : (0 : SmoothCcTensor g r s).toSection x = 0 := by rfl
    rw [hsec]
    exact map_zero _
  change tensorChartComponentProjection (E := E) r s Idx Jdx
      (tensorTrivProj (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α x) = 0
  unfold tensorTrivProj
  rw [h0]
  exact map_zero _

/-- The composite `(tensorChartComponentRaw α Idx Jdx) ∘ (extChartAt I α).symm`
of the raw chart-frame component of the zero tensor section vanishes identically
on `E`. -/
private lemma tensorChartComponentRaw_comp_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx ∘ (extChartAt I α).symm) =
      (fun _ : E => (0 : ℝ)) := by
  funext x
  change tensorChartComponentRaw (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α Idx Jdx ((extChartAt I α).symm x) = 0
  rw [tensorChartComponentRaw_zero_section (I := I) (M := M) g r s α Idx Jdx]

/-- The partition-of-unity-weighted chart-Sobolev norm of the zero tensor
section is zero. -/
theorem tensorPouSobolevNorm_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    tensorPouSobolevNorm (I := I) (M := M) g k
        (0 : SmoothCcTensor g r s) = 0 := by
  classical
  rw [tensorPouSobolevNorm_eq]
  have htsum :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
        0 := by
    have hpt : ∀ α : M,
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) = 0 := by
      intro α
      refine Finset.sum_eq_zero ?_
      intro IJ _
      refine Finset.sum_eq_zero ?_
      intro j _
      have hraw := tensorChartComponentRaw_comp_zero_section
        (I := I) (M := M) g r s α IJ.1 IJ.2
      have hiter : iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s
              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
            ∘ (extChartAt I α).symm) = 0 := by
        rw [hraw]
        exact iteratedFDeriv_fun_zero
      have hintegrand_zero :
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                        (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)) =
            (fun _ => 0) := by
        funext y
        rw [hiter]
        simp
      rw [hintegrand_zero]
      simp
    rw [tsum_congr hpt]
    exact tsum_zero
  rw [htsum]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

/-- The partition-of-unity-weighted chart-Sobolev norm is monotone in the
regularity order: passing from order `2k` to order `2(k+1)` cannot decrease the
norm, because the additional iterated-derivative orders contribute non-negative
summands to the inner finite sum. -/
theorem tensorPouSobolevNorm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T ≤
      tensorPouSobolevNorm (I := I) (M := M) g (k + 1) T := by
  classical
  rw [tensorPouSobolevNorm_eq, tensorPouSobolevNorm_eq]
  have hrange : Finset.range (2 * k + 1) ⊆ Finset.range (2 * (k + 1) + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hper_chart : ∀ α : M,
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E))))) ≤
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (k + 1) + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E))))) := by
    intro α
    refine Finset.sum_le_sum ?_
    intro IJ _
    exact Finset.sum_le_sum_of_subset_of_nonneg hrange
      (by intro j _ _; exact zero_le _)
  have htsum_le :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ≤
        (∑' α : M,
          ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * (k + 1) + 1),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) := by
    exact ENNReal.tsum_le_tsum hper_chart
  exact ENNReal.rpow_le_rpow htsum_le (by norm_num)

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
