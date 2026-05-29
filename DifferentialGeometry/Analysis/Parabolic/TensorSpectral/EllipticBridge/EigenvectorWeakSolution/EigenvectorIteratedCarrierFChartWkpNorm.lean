import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSDiffWkpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedNirenbergWeakenedQuant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedCarrier
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartWeightedMemLp

/-!
# The weighted-`L²` bound for the iterated carrier's effective source field

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, and a
component multi-index `P₀`, the interior elliptic-regularity bootstrap packages
the `m`-fold-differentiated chart `P₀`-component of a resolvent eigenvector by
the iterated divergence-form carrier
`eigenvectorIteratedTensorChartBilinearData g r s h_atlas i α P₀ m`.

The quantitative interior `W^{2,2}` headline
`eigenvectorChartIteratedPartial_wkpNorm_two_two_le` bounds the `W^{2,2}`-norm of
the `m`-fold mixed weak partial by its `W^{1,2}`-norm plus the `L²`-norm of the
carrier's effective source `f_chart`, measured in the chart-pulled weighted
measure `μw := (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

This module supplies the standalone control of that weighted `L²`-norm: for a
level-`m` carrier `D_m` whose effective source field `fChartEff` equals the
level-`m` differentiated chart right-hand side `eigenvectorChartRHSDiff g r s
h_atlas i α P₀ m directions` — exactly the carrier produced by
`exists_eigenvectorIteratedCarrier` — the weighted `L²`-norm of the carrier's
`f_chart` is bounded by `ENNReal.ofReal (μ⁻¹ · C)` times the finite order-`0`
aggregate `diffRHSAggregate g r s h_atlas i α P₀ m 0 directions`.

## Strategy

The bound composes three facts:

* the carrier identity `f_chart = D_m.fChartEff = eigenvectorChartRHSDiff …
  m directions` (`(eigenvectorIteratedTensorChartBilinearData_toData …).f_chart`
  is `D_m.fChartEff` definitionally);
* the weighted-versus-volume `eLpNorm` comparison restricted to the support: the
  level-`m` differentiated right-hand side vanishes almost everywhere off the
  compact partition-of-unity kernel `chartPouKernel α`, on which the chart
  density `densityOnEuclid g α` is bounded above, so its weighted `L²`-norm is a
  multiple of its plain-volume `L²`-norm;
* the weighted-`eLpNorm` bound `eigenvectorChartRHSDiff_eLpNorm_le` for the
  differentiated chart right-hand side against the plain Lebesgue volume.

## Main results

* `eigenvectorIteratedCarrier_fChartEff_eLpNorm_le` — the weighted-`L²` bound for
  the iterated carrier's effective source field.
* `diffRHSAggregate_ne_top` — the finiteness of the order-`K` aggregate
  `diffRHSAggregate` of primitive regularity data.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The chart-pulled weighted measure dominated on the partition-of-unity kernel

On the compact partition-of-unity kernel `chartPouKernel α ⊆ chartTargetEuclid α`
the chart density `densityOnEuclid g α` is bounded above, so the chart-pulled
weighted measure restricted to the kernel is dominated by a positive scalar
multiple of `volume` restricted to the kernel. -/

/-- On the compact partition-of-unity kernel `chartPouKernel α`, the chart-pulled
weighted measure restricted to the kernel is dominated by a nonnegative scalar
multiple of `volume` restricted to the kernel. -/
private lemma chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ c : ℝ, 0 ≤ c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartPouKernel (I := I) (M := M) α) ≤
        ENNReal.ofReal c •
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The density is bounded above by a positive constant on the compact kernel.
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, le_of_lt (lt_of_lt_of_le hc_min_pos hc_le), ?_⟩
  -- Compare the two measures by evaluating on measurable sets.
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  -- The density is `≤ c_max` pointwise on `A ∩ K`.
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_mono_ae' (hA.inter hK_meas) ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact ENNReal.ofReal_le_ofReal (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) :=
    MeasureTheory.setLIntegral_const _ _
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

/-! ## The weighted-versus-volume `eLpNorm` comparison

For a function vanishing almost everywhere off the compact partition-of-unity
kernel `chartPouKernel α`, the weighted `L²`-norm against the chart-pulled
weighted measure restricted to the chart target is bounded by a nonnegative
constant times the plain-volume `L²`-norm restricted to the chart target. -/

omit [CompleteSpace E] in
/-- **Weighted-versus-volume `eLpNorm` comparison on the kernel.** Let
`f : EuclN → ℝ` vanish almost everywhere — with respect to the plain Lebesgue
volume restricted to `chartTargetEuclid α \ chartPouKernel α` — off the compact
partition-of-unity kernel `chartPouKernel α`. Then there is a nonnegative
constant `C` with `eLpNorm f 2 (μw.restrict (chartTargetEuclid α)) ≤
ENNReal.ofReal C · eLpNorm f 2 (volume.restrict (chartTargetEuclid α))`, where
`μw = chartPulledWeightedMeasure g α`.

On the compact partition-of-unity kernel the chart density is bounded above, so
the weighted measure restricted there is dominated by a multiple of `volume`; off
the kernel `f` vanishes almost everywhere, and the weighted restricted measure is
absolutely continuous with respect to the plain restricted volume, so the
a.e.-vanishing transfers. -/
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (α : M) {f : EuclN → ℝ}
    (hf : f =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm f 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          eLpNorm f 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ Ω := chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_meas : MeasurableSet (Ω \ K) := hΩ_open.measurableSet.diff hK_meas
  -- Recast the off-kernel a.e.-vanishing as a pointwise implication on `Ω`.
  have hf' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ K → f y = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at hf
    rw [ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
  -- Domination of the weighted measure on `K`.
  obtain ⟨c, hc_nn, hc_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
      (I := I) (M := M) g α
  refine ⟨Real.sqrt c, Real.sqrt_nonneg _, ?_⟩
  -- The weighted measure restricted to `Ω` is absolutely continuous w.r.t. the
  -- plain volume restricted to `Ω`.
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (volume : Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (withDensity_absolutelyContinuous (volume : Measure EuclN) _).restrict Ω
  -- `f` vanishes a.e. off `K` for the weighted restricted measure too.
  have hf_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → f y = 0 := h_abs.ae_le hf'
  -- `f` agrees a.e. with `K.indicator f` for both measures.
  have h_ind_w : f =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator f := by
    filter_upwards [hf_w] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  have h_ind_v : f =ᵐ[(volume : Measure EuclN).restrict Ω] K.indicator f := by
    filter_upwards [hf'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  -- Rewrite both `eLpNorm`s through the indicator.
  rw [eLpNorm_congr_ae h_ind_w, eLpNorm_congr_ae h_ind_v,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas]
  -- `(μ.restrict Ω).restrict K = μ.restrict K` because `K ⊆ Ω`.
  rw [Measure.restrict_restrict_of_subset hK_in,
    Measure.restrict_restrict_of_subset hK_in]
  -- Dominate the weighted measure on `K`, then split the scalar.
  have h_mono :
      eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ eLpNorm f 2
            (ENNReal.ofReal c • ((volume : Measure EuclN).restrict K)) :=
    eLpNorm_mono_measure f hc_le
  refine h_mono.trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  -- `(1 / 2 : ℝ≥0∞).toReal = 1 / 2`.
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  -- `ENNReal.ofReal c ^ (1 / 2) = ENNReal.ofReal (√c)`.
  have h_pow_eq : ENNReal.ofReal c ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hc_nn (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

omit [CompleteSpace E] in
/-- **Eigenbasis-uniform weighted-versus-volume `eLpNorm` comparison on the
kernel.** The constant-uniform twin of
`eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel`: given a family of
functions `f i : EuclN → ℝ`, indexed by an arbitrary type `ι`, each vanishing
almost everywhere — with respect to the plain Lebesgue volume restricted to
`chartTargetEuclid α \ chartPouKernel α` — off the compact partition-of-unity
kernel `chartPouKernel α`, there is a *single* nonnegative constant `C` such that
`eLpNorm (f i) 2 (μw.restrict (chartTargetEuclid α)) ≤ ENNReal.ofReal C ·
eLpNorm (f i) 2 (volume.restrict (chartTargetEuclid α))` holds for *every* index
`i`, where `μw = chartPulledWeightedMeasure g α`.

The comparison constant is the square root of the kernel-domination constant `c`
from `chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel`, which
depends only on `g` and `α`, not on the function. Hoisting that constant before
the index, the per-index comparison proof is exactly the per-function proof of
`eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel` for `f i`. -/
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
    {ι : Type*} (g : SmoothRiemannianMetric I M) (α : M) {f : ι → EuclN → ℝ}
    (hf : ∀ i, f i =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : ι,
        eLpNorm (f i) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm (f i) 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ Ω := chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_meas : MeasurableSet (Ω \ K) := hΩ_open.measurableSet.diff hK_meas
  -- Domination of the weighted measure on `K`: the constant `c` is `i`-free,
  -- so the witness `√c` can be hoisted before the index.
  obtain ⟨c, hc_nn, hc_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
      (I := I) (M := M) g α
  refine ⟨Real.sqrt c, Real.sqrt_nonneg _, fun i => ?_⟩
  -- Recast the off-kernel a.e.-vanishing of `f i` as a pointwise implication
  -- on `Ω`.
  have hf' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ K → f i y = 0 := by
    have hf_i := hf i
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at hf_i
    rw [ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf_i] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
  -- The weighted measure restricted to `Ω` is absolutely continuous w.r.t. the
  -- plain volume restricted to `Ω`.
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (volume : Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (withDensity_absolutelyContinuous (volume : Measure EuclN) _).restrict Ω
  -- `f i` vanishes a.e. off `K` for the weighted restricted measure too.
  have hf_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → f i y = 0 := h_abs.ae_le hf'
  -- `f i` agrees a.e. with `K.indicator (f i)` for both measures.
  have h_ind_w : f i =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator (f i) := by
    filter_upwards [hf_w] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  have h_ind_v : f i =ᵐ[(volume : Measure EuclN).restrict Ω] K.indicator (f i) := by
    filter_upwards [hf'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  -- Rewrite both `eLpNorm`s through the indicator.
  rw [eLpNorm_congr_ae h_ind_w, eLpNorm_congr_ae h_ind_v,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas]
  -- `(μ.restrict Ω).restrict K = μ.restrict K` because `K ⊆ Ω`.
  rw [Measure.restrict_restrict_of_subset hK_in,
    Measure.restrict_restrict_of_subset hK_in]
  -- Dominate the weighted measure on `K`, then split the scalar.
  have h_mono :
      eLpNorm (f i) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ eLpNorm (f i) 2
            (ENNReal.ofReal c • ((volume : Measure EuclN).restrict K)) :=
    eLpNorm_mono_measure (f i) hc_le
  refine h_mono.trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  -- `(1 / 2 : ℝ≥0∞).toReal = 1 / 2`.
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  -- `ENNReal.ofReal c ^ (1 / 2) = ENNReal.ofReal (√c)`.
  have h_pow_eq : ENNReal.ofReal c ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hc_nn (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

/-! ## The weighted-`L²` bound for the iterated carrier's effective source field -/

section MainBound

/-- **The weighted-`L²` bound for the iterated carrier's effective source
field.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, a
component multi-index `P₀`, a level `m`, a direction multi-index `directions`, a
level-`m` iterated carrier `D_m` whose effective source field `fChartEff` is the
level-`m` differentiated chart right-hand side `eigenvectorChartRHSDiff g r s
h_atlas i α P₀ m directions` (exactly the carrier produced by
`exists_eigenvectorIteratedCarrier`), chart-`H^{m+1}` regularity `h_parent` of
the eigenvector chart component, and the order-`(m + 1)` partition-of-unity
regularity input `h_pou`, there is a nonnegative constant `C` such that the
`L²`-norm of the carrier's effective source `f_chart` against the chart-pulled
weighted measure restricted to the chart-`α` target is bounded by
`ENNReal.ofReal (μ⁻¹ · C)` times the order-`0` aggregate
`diffRHSAggregate g r s h_atlas i α P₀ m 0 directions`.

The bound composes the carrier identity
`(eigenvectorIteratedTensorChartBilinearData_toData …).f_chart = D_m.fChartEff =
eigenvectorChartRHSDiff … m directions`, the weighted-versus-volume `eLpNorm`
comparison `eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel` (the
level-`m` right-hand side vanishes a.e. off the compact partition-of-unity
kernel), and the weighted-`eLpNorm` bound `eigenvectorChartRHSDiff_eLpNorm_le`
for the differentiated chart right-hand side against the plain Lebesgue
volume. -/
theorem eigenvectorIteratedCarrier_fChartEff_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m)
    (h_fChartEff : D_m.fChartEff =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ m directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
          ((eigenvectorIteratedTensorChartBilinearData_toData
              (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent).f_chart)
          2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m 0 directions := by
  classical
  -- The carrier's `f_chart` is, definitionally, `D_m.fChartEff`.
  have h_f_chart_eq :
      (eigenvectorIteratedTensorChartBilinearData_toData
          (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent).f_chart =
        eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m directions := by
    change D_m.fChartEff =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ m directions
    exact h_fChartEff
  rw [h_f_chart_eq]
  -- The level-`m` right-hand side vanishes a.e. off the compact kernel.
  have h_ae_zero :
      eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m directions
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s h_atlas i α P₀ m directions
  -- The weighted-versus-volume `eLpNorm` comparison.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
      (I := I) (M := M) g α h_ae_zero
  -- The plain-volume weighted-`eLpNorm` bound for the differentiated right-hand
  -- side: `eigenvectorChartRHSDiff_eLpNorm_le` needs `h_pou` at order `m + 1`.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le (I := I) (M := M)
      g r s h_atlas i α P₀ m directions h_pou
  -- Assemble: the headline constant is `Ccmp · Cvol`.
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  -- Chain the comparison through the plain-volume bound.
  calc
    eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ m directions) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) hCvol_bd
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

/-- **The eigenbasis-uniform weighted-`L²` bound for the iterated carrier's
effective source field.**

The constant-uniform twin of `eigenvectorIteratedCarrier_fChartEff_eLpNorm_le`:
for a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P₀`, a level `m`, and a direction multi-index
`directions`, with the order-`(m + 1)` partition-of-unity regularity input
`h_pou` phrased uniformly over the eigenbasis index, there is a *single*
nonnegative constant `C` such that, for *every* eigenbasis index `i` with
resolvent eigenvalue `μ := i.fst.val`, every level-`m` iterated carrier `D_m`
whose effective source field `fChartEff` is the level-`m` differentiated chart
right-hand side `eigenvectorChartRHSDiff g r s h_atlas i α P₀ m directions`, and
every chart-`H^{m+1}` regularity witness `h_parent` of the eigenvector chart
component, the `L²`-norm of the carrier's effective source `f_chart` against the
chart-pulled weighted measure restricted to the chart-`α` target is bounded by
`ENNReal.ofReal (μ⁻¹ · C)` times the order-`0` aggregate
`diffRHSAggregate g r s h_atlas i α P₀ m 0 directions`.

A `_uniform` statement cannot be derived from its per-`i` original (one cannot
get `∃ C, ∀ i` from `∀ i, ∃ C`); this carries its own proof. The comparison
constant is hoisted by the eigenbasis-uniform comparison
`eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform` (its
constant depends only on `g` and `α`), and the plain-volume constant is hoisted
by the eigenbasis-uniform weighted-`eLpNorm` bound
`eigenvectorChartRHSDiff_eLpNorm_le_uniform`. The per-`i` carrier identity, the
per-`i` off-kernel a.e.-vanishing, and the resolvent-eigenvalue reciprocity stay
inside the `∀ i`. -/
theorem eigenvectorIteratedCarrier_fChartEff_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
          g r s h_atlas i α P₀ m)
        (_h_fChartEff : D_m.fChartEff =
          eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m directions)
        (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)),
        eLpNorm
            ((eigenvectorIteratedTensorChartBilinearData_toData
                (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent).f_chart)
            2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m 0 directions := by
  classical
  -- The level-`m` right-hand side vanishes a.e. off the compact kernel — this
  -- holds for every eigenbasis index, so it furnishes the function family fed
  -- to the eigenbasis-uniform comparison.
  have h_ae_zero :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m directions
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    fun i => rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s h_atlas i α P₀ m directions
  -- The eigenbasis-uniform weighted-versus-volume `eLpNorm` comparison — its
  -- constant depends only on `g` and `α`, so it is hoisted before `intro i`.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
      (I := I) (M := M)
      (ι := TensorEigenIdx (I := I) (M := M) g r s) g α h_ae_zero
  -- The eigenbasis-uniform plain-volume weighted-`eLpNorm` bound for the
  -- differentiated right-hand side — its constant is likewise `i`-free.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform (I := I) (M := M)
      g r s h_atlas α P₀ m directions h_pou
  -- Assemble: the headline constant is `Ccmp · Cvol`.
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  intro i D_m h_fChartEff h_parent
  -- The carrier's `f_chart` is, definitionally, `D_m.fChartEff`.
  have h_f_chart_eq :
      (eigenvectorIteratedTensorChartBilinearData_toData
          (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent).f_chart =
        eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m directions := by
    change D_m.fChartEff =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ m directions
    exact h_fChartEff
  rw [h_f_chart_eq]
  -- Chain the eigenbasis-uniform comparison through the eigenbasis-uniform
  -- plain-volume bound, both specialised at `i`.
  calc
    eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ m directions) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd i
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) (hCvol_bd i)
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

end MainBound

/-! ## Finiteness of the order-`K` aggregate

The order-`K` aggregate `diffRHSAggregate g r s h_atlas i α P₀ m K l` is an
honest finite `ℝ≥0∞`-valued sum of `wkpNorm`s of `W^{k,2}` functions, hence
finite. Each `wkpNorm` summand is finite by `wkpNorm_lt_top_of_memWkp`; the
finite-sum structure folds the per-summand finiteness into the aggregate. -/

omit [CompleteSpace E] in
/-- **Unconditional order-`N` regularity of every iterated weak partial.** Every
`j`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s h_atlas i α P₀
j idx` lies in `MemWkp N 2` on the chart-`α` target — the eigenvector chart
component lies in `MemWkp (N + j) 2` for every `j` and `N`
(`eigenvector_chartComponent_memWkp_arbitrary`), and the polymorphic bridge
`eigenvectorChartIteratedPartial_memWkp_of_memWkp` transfers it. -/
private lemma iteratedPartial_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (N j : ℕ)
    (idx : Fin j → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ j idx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_comp : MemWkp (d := Module.finrank ℝ E) (N + j) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s h_atlas i (N + j) α P₀
  exact eigenvectorChartIteratedPartial_memWkp_of_memWkp (I := I) (M := M)
    g r s h_atlas i α P₀ j N h_comp idx

omit [CompleteSpace E] in
/-- The level-`(m + 1)` head `diffRHSHead` of `diffRHSAggregate` is finite: each
of its two pieces is a `wkpNorm` of an iterated weak partial, a `W^{k,2}`
function. -/
private lemma diffRHSHead_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  rw [diffRHSHead]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · -- The first piece is a finite sum of `wkpNorm`s of iterated weak partials.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun a _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (iteratedPartial_memWkp_unconditional (I := I) (M := M)
        g r s h_atlas i α P₀ (2 + K) (m + 1) (Fin.cons a (Fin.init l)))
  · -- The second piece is a single `wkpNorm` of an iterated weak partial.
    exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (iteratedPartial_memWkp_unconditional (I := I) (M := M)
        g r s h_atlas i α P₀ (2 + K) m (Fin.init l)))

/-- The level-`0` aggregate `rhsZeroAggregate` of `diffRHSAggregate` is finite:
each of its seven summands is a `wkpNorm` (or a finite sum of `wkpNorm`s) of a
`W^{k,2}` function. The first summand uses the unconditional arbitrary-order
interior regularity of the eigenvector chart component; the remaining six use the
order-`(K + 1)` partition-of-unity regularity input. -/
private lemma rhsZeroAggregate_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  rw [rhsZeroAggregate]
  -- Discharge the seven-term sum piece by piece.
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- Summand 1: the eigenvector chart component at order `K` — unconditional.
    exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
        g r s h_atlas i K α P₀))
  · -- Summand 2: the transport double-sum of resolvent-coercion chart components
    -- at order `K + 1`, each finite directly from `h_pou`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr (fun Q _ => ?_),
        ENNReal.sum_lt_top.mpr (fun β' _ =>
          ENNReal.sum_lt_top.mpr (fun Q _ => ?_))⟩))
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β Q)
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β' Q)
  · -- Summand 3: the transport sum of resolvent-coercion chart components at
    -- order `K`, each obtained from `h_pou` by dropping the order.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.sum_lt_top.mpr (fun Q _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (MemWkp.le_of_le (d := Module.finrank ℝ E)
        (by omega : K ≤ K + 1) (h_pou β Q))
  · -- Summand 4: the chart-partial atoms `partialLpLimit` at order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun k _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (partialLpLimit_memWkp (I := I) (M := M) g r s h_atlas i α P k K h_pou)
  · -- Summand 5: the chart-component atoms `componentLpLimit` at order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (componentLpLimit_memWkp (I := I) (M := M) g r s h_atlas i α p K h_pou)
  · -- Summand 6: the cutoff cross-right limit objects `crossRightLimitComponent`
    -- at order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s h_atlas i α P K h_pou)
  · -- Summand 7: the cutoff chart-partial atoms `cutoffPartialLpLimit` at
    -- order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun l _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (cutoffPartialLpLimit_memWkp (I := I) (M := M)
        g r s h_atlas i α P l K h_pou)

/-- **Finiteness of the order-`K` aggregate.** For a closed Riemannian manifold
`(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a chart center `α : M`, a
component multi-index `P₀`, a level `m`, a regularity order `K`, a direction
multi-index `l`, and the order-`(m + 1 + K)` partition-of-unity regularity input
`h_pou`, the order-`K` aggregate of primitive regularity data
`diffRHSAggregate g r s h_atlas i α P₀ m K l` is finite.

The proof is induction on `m`, with `K` universally quantified:

* level `0` is `rhsZeroAggregate`, finite by `rhsZeroAggregate_ne_top` fed
  `h_pou` at order `0 + 1 + K = K + 1`;
* level `m + 1` is `diffRHSHead` — finite by `diffRHSHead_ne_top` — added to the
  level-`m` aggregate at order `K + 1`, finite by the inductive hypothesis fed
  `h_pou` at order `m + 1 + (K + 1)`. -/
theorem diffRHSAggregate_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  induction m generalizing K with
  | zero =>
      -- Level `0`: the order-`K` seven-term aggregate `rhsZeroAggregate`.
      rw [show diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ 0 K l =
        rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K from rfl]
      -- `rhsZeroAggregate_ne_top` needs `h_pou` at order `K + 1`; this theorem's
      -- `h_pou` is at order `0 + 1 + K = K + 1`.
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      exact rhsZeroAggregate_ne_top (I := I) (M := M)
        g r s h_atlas i α P₀ K h_pou'
  | succ m ih =>
      -- Level `m + 1`: `diffRHSHead` plus the level-`m` aggregate at order
      -- `K + 1`.
      rw [show diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) K l =
          diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m K l +
            diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m (K + 1) (Fin.init l) from rfl]
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · exact diffRHSHead_ne_top (I := I) (M := M) g r s h_atlas i α P₀ m K l
      · -- The inductive hypothesis at order `K + 1` needs `h_pou` at order
        -- `m + 1 + (K + 1) = m + 1 + 1 + K`, supplied by this theorem's `h_pou`.
        have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
            MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
          intro β Q
          have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
          rw [h_idx]
          exact h_pou β Q
        exact ih (K + 1) (Fin.init l) h_pou_prev

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The headline produces, from the carrier identity and the order-`(m + 1)`
partition-of-unity regularity input, the weighted-`L²` bound for the iterated
carrier's effective source field. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m)
    (h_fChartEff : D_m.fChartEff =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ m directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
          ((eigenvectorIteratedTensorChartBilinearData_toData
              (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent).f_chart)
          2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m 0 directions :=
  eigenvectorIteratedCarrier_fChartEff_eLpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ directions D_m h_fChartEff h_parent h_pou

/-- The eigenbasis-uniform headline produces, from the uniformly-phrased
order-`(m + 1)` partition-of-unity regularity input, a single nonnegative
constant serving the weighted-`L²` bound for the iterated carrier's effective
source field of *every* eigenbasis index. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
          g r s h_atlas i α P₀ m)
        (_h_fChartEff : D_m.fChartEff =
          eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m directions)
        (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)),
        eLpNorm
            ((eigenvectorIteratedTensorChartBilinearData_toData
                (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent).f_chart)
            2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m 0 directions :=
  eigenvectorIteratedCarrier_fChartEff_eLpNorm_le_uniform (I := I) (M := M)
    g r s h_atlas α P₀ directions h_pou

/-- The finiteness lemma certifies the order-`K` aggregate is finite. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) :=
  diffRHSAggregate_ne_top (I := I) (M := M) g r s h_atlas i α P₀ m K l h_pou

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations below re-key the chart-locality-conditional results above onto
the intrinsic compact-operator eigenbasis, eliminating the
`HasLocallyConstantChartAt` hypothesis. Each twin is a faithful re-keying of its
original: the eigenbasis vector is supplied by
`tensorResolventEigenbasisVec_ofCompact` fed the intrinsic compactness witness
`tensorResolventL2_isCompactOperator_intrinsic g r s`, and every chart-locality
dependency is replaced by its previously-established `_unconditional` twin. -/

section MainBoundUnconditional

/-- Chart-locality-free twin of
`eigenvectorIteratedCarrier_fChartEff_eLpNorm_le`. -/
theorem eigenvectorIteratedCarrier_fChartEff_eLpNorm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
      g r s i α P₀ m)
    (h_fChartEff : D_m.fChartEff =
      eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
        g r s i α P₀ m directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
          ((eigenvectorIteratedTensorChartBilinearData_toData_unconditional
              (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart)
          2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
  classical
  -- The carrier's `f_chart` is, definitionally, `D_m.fChartEff`.
  have h_f_chart_eq :
      (eigenvectorIteratedTensorChartBilinearData_toData_unconditional
          (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart =
        eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m directions := by
    change D_m.fChartEff =
      eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
        g r s i α P₀ m directions
    exact h_fChartEff
  rw [h_f_chart_eq]
  -- The level-`m` right-hand side vanishes a.e. off the compact kernel.
  have h_ae_zero :
      eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m directions
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    rhsDiff_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
      g r s i α P₀ m directions
  -- The weighted-versus-volume `eLpNorm` comparison.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
      (I := I) (M := M) g α h_ae_zero
  -- The plain-volume weighted-`eLpNorm` bound for the differentiated right-hand
  -- side: `eigenvectorChartRHSDiff_eLpNorm_le_unconditional` needs `h_pou` at
  -- order `m + 1`.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_unconditional (I := I) (M := M)
      g r s i α P₀ m directions h_pou
  -- Assemble: the headline constant is `Ccmp · Cvol`.
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  -- Chain the comparison through the plain-volume bound.
  calc
    eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m directions) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) hCvol_bd
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

/-- Chart-locality-free twin of
`eigenvectorIteratedCarrier_fChartEff_eLpNorm_le_uniform`. -/
theorem eigenvectorIteratedCarrier_fChartEff_eLpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (D_m : eigenvectorIteratedTensorChartBilinearData_unconditional
          (I := I) (M := M) g r s i α P₀ m)
        (_h_fChartEff : D_m.fChartEff =
          eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m directions)
        (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)),
        eLpNorm
            ((eigenvectorIteratedTensorChartBilinearData_toData_unconditional
                (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart)
            2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ m 0 directions := by
  classical
  -- The level-`m` right-hand side vanishes a.e. off the compact kernel — this
  -- holds for every eigenbasis index, so it furnishes the function family fed
  -- to the eigenbasis-uniform comparison.
  have h_ae_zero :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m directions
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    fun i => rhsDiff_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
      g r s i α P₀ m directions
  -- The eigenbasis-uniform weighted-versus-volume `eLpNorm` comparison — its
  -- constant depends only on `g` and `α`, so it is hoisted before `intro i`.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
      (I := I) (M := M)
      (ι := TensorEigenIdx (I := I) (M := M) g r s) g α h_ae_zero
  -- The eigenbasis-uniform plain-volume weighted-`eLpNorm` bound for the
  -- differentiated right-hand side — its constant is likewise `i`-free.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform_unconditional (I := I) (M := M)
      g r s α P₀ m directions h_pou
  -- Assemble: the headline constant is `Ccmp · Cvol`.
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  intro i D_m h_fChartEff h_parent
  -- The carrier's `f_chart` is, definitionally, `D_m.fChartEff`.
  have h_f_chart_eq :
      (eigenvectorIteratedTensorChartBilinearData_toData_unconditional
          (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart =
        eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m directions := by
    change D_m.fChartEff =
      eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
        g r s i α P₀ m directions
    exact h_fChartEff
  rw [h_f_chart_eq]
  -- Chain the eigenbasis-uniform comparison through the eigenbasis-uniform
  -- plain-volume bound, both specialised at `i`.
  calc
    eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m directions) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd i
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) (hCvol_bd i)
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

end MainBoundUnconditional

/-! ## Chart-locality-free finiteness of the order-`K` aggregate -/

/-- Chart-locality-free twin of `diffRHSHead_ne_top`. -/
private lemma diffRHSHead_ne_top_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  -- Chart-locality-free order-`N` regularity of every iterated weak partial:
  -- the eigenvector chart component lies in `MemWkp (N + j) 2` for every `j`
  -- and `N`, and the polymorphic bridge transfers it.
  have h_iter : ∀ (N j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) N 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro N j idx
    have h_comp : MemWkp (d := Module.finrank ℝ E) (N + j) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
      eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
        g r s i (N + j) α P₀
    exact eigenvectorChartIteratedPartial_unconditional_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ j N h_comp idx
  rw [diffRHSHead_unconditional]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · -- The first piece is a finite sum of `wkpNorm`s of iterated weak partials.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun a _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (h_iter (2 + K) (m + 1) (Fin.cons a (Fin.init l)))
  · -- The second piece is a single `wkpNorm` of an iterated weak partial.
    exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (h_iter (2 + K) m (Fin.init l)))

/-- Chart-locality-free twin of `rhsZeroAggregate_ne_top`. -/
private lemma rhsZeroAggregate_ne_top_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  rw [rhsZeroAggregate_unconditional]
  -- Discharge the seven-term sum piece by piece.
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- Summand 1: the eigenvector chart component at order `K` — unconditional.
    exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
        g r s i K α P₀))
  · -- Summand 2: the transport double-sum of resolvent-coercion chart components
    -- at order `K + 1`, each finite directly from `h_pou`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr (fun Q _ => ?_),
        ENNReal.sum_lt_top.mpr (fun β' _ =>
          ENNReal.sum_lt_top.mpr (fun Q _ => ?_))⟩))
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β Q)
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β' Q)
  · -- Summand 3: the transport sum of resolvent-coercion chart components at
    -- order `K`, each obtained from `h_pou` by dropping the order.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.sum_lt_top.mpr (fun Q _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (MemWkp.le_of_le (d := Module.finrank ℝ E)
        (by omega : K ≤ K + 1) (h_pou β Q))
  · -- Summand 4: the chart-partial atoms `partialLpLimit_unconditional` at
    -- order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun k _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (partialLpLimit_memWkp_unconditional (I := I) (M := M)
        g r s i α P k K h_pou)
  · -- Summand 5: the chart-component atoms `componentLpLimit_unconditional` at
    -- order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (componentLpLimit_memWkp_unconditional (I := I) (M := M)
        g r s i α p K h_pou)
  · -- Summand 6: the cutoff cross-right limit objects
    -- `crossRightLimitComponent_unconditional` at order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (crossRightLimitComponent_memWkp_unconditional (I := I) (M := M)
        g r s i α P K h_pou)
  · -- Summand 7: the cutoff chart-partial atoms `cutoffPartialLpLimit_unconditional`
    -- at order `K`.
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun l _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (cutoffPartialLpLimit_memWkp_unconditional (I := I) (M := M)
        g r s i α P l K h_pou)

/-- Chart-locality-free twin of `diffRHSAggregate_ne_top`. -/
theorem diffRHSAggregate_ne_top_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  induction m generalizing K with
  | zero =>
      -- Level `0`: the order-`K` seven-term aggregate `rhsZeroAggregate_unconditional`.
      rw [show diffRHSAggregate_unconditional (I := I) (M := M)
          g r s i α P₀ 0 K l =
        rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K from rfl]
      -- `rhsZeroAggregate_ne_top_unconditional` needs `h_pou` at order `K + 1`;
      -- this theorem's `h_pou` is at order `0 + 1 + K = K + 1`.
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      exact rhsZeroAggregate_ne_top_unconditional (I := I) (M := M)
        g r s i α P₀ K h_pou'
  | succ m ih =>
      -- Level `m + 1`: `diffRHSHead_unconditional` plus the level-`m` aggregate
      -- at order `K + 1`.
      rw [show diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) K l =
          diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m K l +
            diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ m (K + 1) (Fin.init l) from rfl]
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · exact diffRHSHead_ne_top_unconditional (I := I) (M := M)
          g r s i α P₀ m K l
      · -- The inductive hypothesis at order `K + 1` needs `h_pou` at order
        -- `m + 1 + (K + 1) = m + 1 + 1 + K`, supplied by this theorem's `h_pou`.
        have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
            MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
          intro β Q
          have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
          rw [h_idx]
          exact h_pou β Q
        exact ih (K + 1) (Fin.init l) h_pou_prev

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
