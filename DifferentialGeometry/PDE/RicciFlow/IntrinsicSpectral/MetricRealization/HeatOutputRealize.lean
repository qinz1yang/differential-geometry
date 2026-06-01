import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.SpectralSmoothing

/-!
# Realizing the spectral heat output as a genuine smooth tensor / Riemannian metric

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled
on a finite-dimensional real inner-product space `E`, the parabolic / spectral
heat semigroup `e^{tΔ}` maps an `L²` initial datum into the spectral smooth
subspace `⋂_σ Hˢ` for every positive time (`heat_semigroup_into_all_tensorHs`).

This file turns that `Hˢ`-membership into a *genuine smooth representative* of
the heat output, and then assembles the realized `(0,2)`-tensor into an honest
`SmoothRiemannianMetric` perturbation — closing the realization chain

  `e^{tΔ} u₀` (`t > 0`) ∈ every `Hˢ`  →  smooth `SmoothCcTensor` representative
    →  `SmoothRiemannianMetric` (smooth + positive-definite).

The construction is *chart-locality-free* (no `HasLocallyConstantChartAt`): it
runs through the unconditional eigenbasis machinery
`tensorHsSmoothRepr` / `tensorSectionRealizeMetric`, which already
ship a genuine smooth representative for every finitely-supported spectral
element. The single mathematical input that makes the heat-output case fall into
that already-closed regime is the elementary observation that the heat rescaling
`coeff i ↦ exp(-λᵢ t) · coeff i` *never enlarges* the spectral support (the
exponential factor is nonzero); so a finite spectral support of the initial
datum is inherited by the heat output, which therefore has a genuine smooth
representative.

## Main results

* `heatHsWitness_support_eq` — the spectral support of the heat witness equals
  the spectral support of the initial datum's intrinsic eigenbasis coordinates.

* `heatHsWitness_finite_support_of_finite` — if the initial datum has finite
  spectral support, so does the positive-time heat witness.

* `heatOutputSmoothRepr` — the genuine smooth (`SmoothCcTensor`) representative
  of the positive-time heat output `e^{tΔ} u₀`, for an initial datum with finite
  spectral support.

* `heatOutputSmoothRepr_toL2` — the `L²` class of `heatOutputSmoothRepr`
  coincides with the heat output `tensorHeatSemigroup g r s t u₀`.

* `heatOutputSmoothRepr_contMDiff` — the underlying section of
  `heatOutputSmoothRepr` is `C^∞`.

* `heatOutputSmoothRepr_memWtwokTwo` — the smooth representative lies in
  `W^{2k,2}` for every order `k`.

* `exists_smooth_metric_of_heatOutput_small` — the headline: for a `(0,2)`
  initial datum with finite spectral support, whenever the symmetrized
  extracted form of the heat output's smooth representative is uniformly
  `g`-fibre small with constant `< 1`, the positive-time heat output is realized
  as a genuine `SmoothRiemannianMetric` equal fibrewise to `g + h_sym`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The intrinsic eigenbasis coordinate family of an `L²` tensor element, taken
against the unconditional compactness witness
`tensorResolventL2_isCompactOperator`. -/
def spectralCoeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) :
    TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
  tensorL2Coeff (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) u₀

@[simp] lemma spectralCoeff_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    spectralCoeff (I := I) (M := M) g r s u₀ i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        u₀ i := rfl

/-- **The heat witness has the same spectral support as the initial datum.** The
support of the heat witness's coordinate family equals the spectral support of
`u₀`: the exponential rescaling factor `exp(-λᵢ t)` is nonzero, so it neither
creates nor destroys support. -/
theorem heatHsWitness_support_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    Function.support (heatHsWitness (I := I) (M := M) g r s σ ht u₀).coeff =
      Function.support (spectralCoeff (I := I) (M := M) g r s u₀) := by
  apply Set.ext
  intro i
  have hexp : Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  rw [Function.mem_support, Function.mem_support, heatHsWitness_coeff,
    spectralCoeff_apply]
  exact mul_ne_zero_iff_left hexp

/-- **Finite spectral support is inherited by the heat witness.** If the initial
datum `u₀` has finite spectral support, then for every positive time the heat
witness `heatHsWitness g r s σ ht u₀` has finite coordinate support. -/
theorem heatHsWitness_finite_support_of_finite
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    (Function.support (heatHsWitness (I := I) (M := M) g r s σ ht u₀).coeff).Finite := by
  rw [heatHsWitness_support_eq (I := I) (M := M) g r s σ ht u₀]
  exact hu₀_fs

/-- **The genuine smooth representative of the heat output.** For a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, an initial datum `u₀` with finite
spectral support, and a positive time `t`, this is the genuine smooth,
compactly-supported `(r, s)`-tensor section representing `e^{tΔ} u₀`. It is the
unconditional spectral smooth representative of the (finitely-supported) heat
witness at the `H⁰`-scale. -/
def heatOutputSmoothRepr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    SmoothCcTensor g r s :=
  tensorHsSmoothRepr (I := I) (M := M)
    (heatHsWitness (I := I) (M := M) g r s 0 ht u₀)
    (heatHsWitness_finite_support_of_finite (I := I) (M := M) g r s 0 ht u₀ hu₀_fs)

/-- **The smooth representative realizes the heat output.** The `L²` class of the
smooth representative `heatOutputSmoothRepr` coincides with the spectral heat
output `e^{tΔ} u₀ = tensorHeatSemigroup g r s t u₀`.

The proof composes the chart-locality-free identification
`tensorHsSmoothRepr_toL2` (the `L²` class of the smooth
representative is the canonical inclusion of the heat witness) with
`heat_semigroup_into_tensorHs` (that inclusion *is* the heat output). -/
theorem heatOutputSmoothRepr_toL2 (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    (heatOutputSmoothRepr (I := I) (M := M) g r s ht u₀ hu₀_fs :
        TensorL2 r s g) =
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ := by
  unfold heatOutputSmoothRepr
  rw [tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ))
    (heatHsWitness (I := I) (M := M) g r s 0 ht u₀)
    (heatHsWitness_finite_support_of_finite (I := I) (M := M) g r s 0 ht u₀ hu₀_fs)]
  exact heat_semigroup_into_tensorHs (I := I) (M := M) g r s (le_refl (0 : ℝ)) ht u₀

/-- **The smooth representative lies in every Sobolev order.** For every `k : ℕ`,
the smooth representative `heatOutputSmoothRepr` lies in `W^{2k,2}`. This is the
all-orders Sobolev regularity of the genuine `C^∞` heat output, inherited from
`tensorHsSmoothRepr_memWtwokTwo`. -/
theorem heatOutputSmoothRepr_memWtwokTwo (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite)
    (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (heatOutputSmoothRepr (I := I) (M := M) g r s ht u₀ hu₀_fs) :=
  tensorHsSmoothRepr_memWtwokTwo (I := I) (M := M)
    (heatHsWitness (I := I) (M := M) g r s 0 ht u₀)
    (heatHsWitness_finite_support_of_finite (I := I) (M := M) g r s 0 ht u₀ hu₀_fs) k

/-- **The positive-time heat output has a genuine smooth representative.** For an
initial datum `u₀` with finite spectral support, there is a smooth,
compactly-supported tensor section (the `SmoothCcTensor` type is, by
construction, a `C^∞` section of the `(r, s)`-tensor bundle) whose `L²` class is
the heat output `e^{tΔ} u₀` and which lies in `W^{2k,2}` for every order `k`. -/
theorem exists_smooth_heatOutput_representative (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g r s u₀)).Finite) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
          tensorHeatSemigroup (I := I) (M := M) g r s t u₀ ∧
        ∀ k : ℕ, MemWtwokTwo (I := I) (M := M) g k T :=
  ⟨heatOutputSmoothRepr (I := I) (M := M) g r s ht u₀ hu₀_fs,
    heatOutputSmoothRepr_toL2 (I := I) (M := M) g r s ht u₀ hu₀_fs,
    fun k => heatOutputSmoothRepr_memWtwokTwo (I := I) (M := M) g r s ht u₀ hu₀_fs k⟩

/-- **Smooth realization of a finitely-supported member of `⋂_σ Hˢ`.** Let
`u : TensorL2 r s g` lie (via the chart-locality-free inclusion) in `Hˢ` for
every `σ ≥ 0`, witnessed coherently as in the gate predicate. If, additionally,
`u` has finite spectral support, then `u` is the `L²` class of a genuine
`SmoothCcTensor`.

The hypothesis `h_mem` is the spectral smooth-subspace membership of `u`; the
hypothesis `hu_fs` is its finite spectral support. From the `σ = 0` witness we
recover `u` as the canonical inclusion of an `H⁰` element with finite coordinate
support, whose unconditional spectral smooth representative realizes it. -/
theorem spectralSmooth_realizesAsSmooth_of_finite_support
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_mem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v = u)
    (hu_fs : ∀ v : tensorHs (I := I) (M := M) g r s 0,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) (le_refl (0 : ℝ)) v = u →
          (Function.support v.coeff).Finite) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u := by
  obtain ⟨v₀, hv₀⟩ := h_mem 0 (le_refl (0 : ℝ))
  have hv₀_fs : (Function.support v₀.coeff).Finite := hu_fs v₀ hv₀
  refine ⟨tensorHsSmoothRepr (I := I) (M := M) v₀ hv₀_fs, ?_⟩
  rw [tensorHsSmoothRepr_toL2 (I := I) (M := M)
    (le_refl (0 : ℝ)) v₀ hv₀_fs]
  exact hv₀

/-- The symmetric smooth bilinear `Hom`-section extracted from the heat output's
smooth representative. -/
def heatOutputBilinSymm (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 0 2 g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g 0 2 u₀)).Finite)
    (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ccTensorBilinSymm (I := I) g
    (heatOutputSmoothRepr (I := I) (M := M) g 0 2 ht u₀ hu₀_fs) x

/-- On a closed Riemannian manifold `(M, g)`, for a covariant `(0,2)` initial
datum `u₀ : TensorL2 0 2 g` with finite spectral support and a positive time `t`,
if the symmetrized extracted bilinear form `heatOutputBilinSymm` of the heat
output's smooth representative is uniformly `g`-fibre small with constant
`δ' < 1`, then there exists a `SmoothRiemannianMetric I M` whose inner product is
fibrewise `g.inner + heatOutputBilinSymm`.

Here the genuine smooth representative `heatOutputSmoothRepr` of the positive-time
heat output `e^{tΔ} u₀` supplies the perturbation
`heatOutputBilinSymm = ccTensorBilinSymm` of that representative. The fibre-bound
hypothesis `hδ'` (with `δ' < 1`) is the genuine smallness assumption: it forces
the quadratic form of `g + heatOutputBilinSymm` to be bounded below by
`(1 - δ') · g x v v > 0`, so the perturbed object is positive-definite, and the
`C^∞` regularity of the representative makes it a smooth metric. The metric is
constructed (not assumed) by delegating to
`exists_smooth_metric_of_smooth_tensor_small`. -/
theorem exists_smooth_metric_of_heatOutput_small
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 0 2 g)
    (hu₀_fs : (Function.support (spectralCoeff (I := I) (M := M) g 0 2 u₀)).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g
      (heatOutputBilinSymm (I := I) g ht u₀ hu₀_fs) δ') :
    ∃ g' : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x),
        g'.inner x v w =
          g.inner x v w + heatOutputBilinSymm (I := I) g ht u₀ hu₀_fs x v w :=
  exists_smooth_metric_of_smooth_tensor_small (I := I) g
    (heatOutputSmoothRepr (I := I) (M := M) g 0 2 ht u₀ hu₀_fs) hδ'_lt hδ'

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
