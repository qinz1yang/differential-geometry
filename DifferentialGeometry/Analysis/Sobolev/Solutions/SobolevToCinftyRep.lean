import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding

/-!
# A.e. continuous representative of a chart-`W^{k,p}` function

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
modelled on a finite-dimensional real inner-product space `E` of positive
dimension `n`, this file delivers a clean wrapper around the headline
iterated Sobolev embedding theorem from
`IteratedSobolevEmbedding.lean`. Concretely, we expose the *existence of an
a.e.-continuous representative*:

  if `u : M → ℝ` is a measurable function in `MemWkpChart g k 2` with
  `2k > n`, then there is a continuous function `ũ : M → ℝ` with
  `ũ =ᵐ[μ_g] u`, where `μ_g` is the canonical Riemannian volume measure.

The literal statement "every `u ∈ MemWkpChart g k p` is `ContMDiff` of some
positive order" is *false* — `MemWkpChart` is an a.e. condition and is
indifferent to modification on null sets, whereas `ContMDiff` is a
pointwise predicate. The mathematically correct statement on closed
manifolds at supercritical exponent is the existence of a representative
with the desired regularity.

The conclusion delivered here is at the `C^0` (continuity) level, which is
what the existing infrastructure supports. The stronger `C^l` (`l ≥ 1`)
case — i.e., extracting a `ContMDiff` (or even a `Continuous` derivative)
representative when `(k - l)·p > n` — requires substantially more
infrastructure than is available in this project: it would need a bridge
between weak partial derivatives in charts and classical (pointwise)
higher derivatives, plus a global gluing argument for higher derivatives
across the partition of unity. That bridge is a separate, standalone
project, and is left to future work.

Even at the `C^0` level the result is genuinely useful downstream: any
eigenfunction of the variational Laplacian on a closed Riemannian
manifold lies (on iteration) in `MemWkpChart g k 2` for arbitrarily large
`k`, and one therefore obtains a continuous representative of every
eigenfunction.

## Main results

* `exists_continuous_representative_of_memWkpChart_isRegular` — the
  faithful wrapper around `sobolev_embedding_chart_C0_Hk`,
  retaining the technical regularity hypothesis
  `RegularExponent.IsRegular (Module.finrank ℝ E : ℝ) 2 k` (i.e., for the
  Hilbert exponent `p = 2`, the iteration ladder
  `n / m` for `m ∈ {1, …, k}` does not coincide with `2`).

* `exists_continuous_representative_of_memWkpChart` — the unconditional
  variant: every measurable `u ∈ MemWkpChart g k 2` with `2k > n` admits a
  continuous a.e.-representative. Internally uses
  `iterated_sobolev_embedding_chart_C0_unconditional` to lift the
  regularity assumption (the side condition `2 ≤ n ∨ 1 < p` is vacuously
  true for `p = 2`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure

/-- **Continuous representative of a chart-`H^k` function (regularity
ladder hypothesis kept).**
For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
modelled on a finite-dimensional real inner-product space `E` of positive
dimension `n = Module.finrank ℝ E`, every measurable
`u : M → ℝ` in `MemWkpChart g k 2` with `2k > n` and the regularity
condition `RegularExponent.IsRegular n 2 k` admits a continuous function
`ũ : M → ℝ` with `ũ =ᵐ[μ_g] u`, where
`μ_g = riemannianVolumeMeasure I M g`.

Faithful wrapper for `sobolev_embedding_chart_C0_Hk`. -/
theorem exists_continuous_representative_of_memWkpChart_isRegular
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    {k : ℕ} (hk : Module.finrank ℝ E < 2 * k)
    (hreg : RegularExponent.IsRegular (Module.finrank ℝ E : ℝ) 2 k)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g k 2 u) :
    ∃ ũ : M → ℝ, Continuous ũ ∧
      ũ =ᵐ[riemannianVolumeMeasure I M g] u := by
  obtain ⟨ũ, _C, hũ_cont, _hC_nn, hũ_ae, _hũ_bound⟩ :=
    sobolev_embedding_chart_C0_Hk (I := I) (M := M) g hk hreg
      hu_meas hu
  refine ⟨ũ, hũ_cont, ?_⟩
  have hμ_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure I M g :=
    (riemannianVolumeMeasure_def (I := I) (M := M) g).symm
  rw [hμ_eq] at hũ_ae
  exact hũ_ae

/-- **Continuous representative of a chart-`H^k` function (unconditional
in the regularity ladder).**
For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
modelled on a finite-dimensional real inner-product space `E` of positive
dimension `n = Module.finrank ℝ E`, every measurable
`u : M → ℝ` in `MemWkpChart g k 2` with `2k > n` admits a continuous
function `ũ : M → ℝ` with `ũ =ᵐ[μ_g] u`, where
`μ_g = riemannianVolumeMeasure I M g`.

This is a wrapper around `iterated_sobolev_embedding_chart_C0_unconditional`
specialized to `p = 2`. The side condition `2 ≤ n ∨ 1 < p` of the
unconditional embedding is vacuously satisfied at `p = 2`, and the
regularity ladder hypothesis is removed by the perturbation argument
internal to that theorem. -/
theorem exists_continuous_representative_of_memWkpChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    {k : ℕ} (hk : Module.finrank ℝ E < 2 * k)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g k 2 u) :
    ∃ ũ : M → ℝ, Continuous ũ ∧
      ũ =ᵐ[riemannianVolumeMeasure I M g] u := by
  have hd_pos : 0 < Module.finrank ℝ E := NeZero.pos _
  have hk_pos : 1 ≤ k := by
    by_contra h_not
    have hk_zero : k = 0 := by omega
    rw [hk_zero] at hk
    omega
  have hp_one : (1 : ℝ) ≤ 2 := by norm_num
  have hkp_real : (Module.finrank ℝ E : ℝ) < (k : ℝ) * 2 := by
    have h_real : (Module.finrank ℝ E : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast hk
    have h2k : ((2 * k : ℕ) : ℝ) = (k : ℝ) * 2 := by push_cast; ring
    rw [h2k] at h_real
    exact h_real
  have h_side : 2 ≤ Module.finrank ℝ E ∨ (1 : ℝ) < 2 := Or.inr (by norm_num)
  have h_two_eq : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) from by norm_num]
    rw [ENNReal.ofReal_natCast]
    rfl
  have hu' : MemWkpChart (I := I) (M := M) g k (ENNReal.ofReal 2) u := by
    rw [← h_two_eq]; exact hu
  obtain ⟨ũ, _C, hũ_cont, _hC_nn, hũ_ae, _hũ_bound⟩ :=
    iterated_sobolev_embedding_chart_C0_unconditional (I := I) (M := M) g hk_pos
      hp_one hkp_real h_side hu_meas hu'
  refine ⟨ũ, hũ_cont, ?_⟩
  have hμ_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure I M g :=
    (riemannianVolumeMeasure_def (I := I) (M := M) g).symm
  rw [hμ_eq] at hũ_ae
  exact hũ_ae

end Chart
end Sobolev
end Analysis
end DifferentialGeometry

end
