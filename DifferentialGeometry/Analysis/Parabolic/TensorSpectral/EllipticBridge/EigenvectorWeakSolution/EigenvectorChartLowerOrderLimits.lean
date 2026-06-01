import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolutionGlobal
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartPartialL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.PouComponentBridge

/-!
# The `n → ∞` `L²`-limits of the three lower-order coefficient terms

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`,
and a component multi-index `P₀`, the per-approximant chart bilinear identity of
the connection Laplacian carries three lower-order coefficient terms on its
right-hand side, evaluated at the partition-of-unity-weighted smooth approximant
`Tₙ := pouSmul g r s α (eigenvectorSmoothApprox g r s i n)`:

* the principal rotation coefficient `covPrincipalRotationCoeff g r s Tₙ α P₀`;
* the lower-order rotation value coefficient
  `covLowerOrderRotationValueCoeff g r s Tₙ α P₀`;
* the chart-density-weighted lower-order gradient coefficient
  `weightedGradCoeff g r s Tₙ α P₀ l`, together with its chart-Euclidean
  divergence `euclidPartial l (weightedGradCoeff g r s Tₙ α P₀ l)`.

This file produces, for each of these, the `n → ∞` `L²`-limit in
`Lp ℝ 2 (chartL2Measure α)`.

## The tracing identity

With `wₙ := eigenvectorSmoothApprox g r s i n` and
`Tₙ := pouSmul g r s α wₙ.toCcTensor`, the raw chart component of `Tₙ` is the
partition-of-unity-weighted chart component of `wₙ.toCcTensor`
(`tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou`), whose Euclidean
push-forward is the canonical Euclidean chart component
`tensorChartComponent g r s wₙ.toCcTensor α P`. Consequently each of the three
coefficients, evaluated at `Tₙ` and restricted to the chart target, is a finite
`C^∞`-coefficient-weighted sum of the two `T`-dependent atoms

* `tensorChartComponent g r s wₙ.toCcTensor α P` (the bare chart component);
* `euclidPartial k (tensorChartComponent g r s wₙ.toCcTensor α P)` (its
  chart-Euclidean partial).

The `L²`-limits of those two atoms are supplied by the companion files:
`eigenvectorChartComponentL2_tendsto` (chart component) and
`eigenvectorChartPartialLp_tendsto` (chart partial). Multiplication by a `C^∞`
coefficient — bounded on the compact partition-of-unity kernel, off which every
atom vanishes — preserves `L²`-convergence, and a finite sum of `L²`-convergent
sequences converges.

## Main definitions

* `covPrincipalRotationCoeffLimit g r s i α P₀` — the explicit
  `L²`-limit function of `covPrincipalRotationCoeff g r s Tₙ α P₀`.
* `covLowerOrderRotationValueCoeffLimit g r s i α P₀` — the
  explicit `L²`-limit function of `covLowerOrderRotationValueCoeff g r s Tₙ α P₀`.
* `weightedGradCoeffLimit g r s i α P₀ l` — the explicit `L²`-limit
  function of `weightedGradCoeff g r s Tₙ α P₀ l`.
* `weightedGradCoeffDivLimit g r s i α P₀ l` — the explicit
  `L²`-limit function of `euclidPartial l (weightedGradCoeff g r s Tₙ α P₀ l)`.

## Main results

* `covPrincipalRotationCoeff_tendsto`,
  `covLowerOrderRotationValueCoeff_tendsto`,
  `weightedGradCoeff_tendsto`,
  `weightedGradCoeffDiv_tendsto` — the four
  `n → ∞` `L²`-convergence headlines.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The compact partition-of-unity kernel of the chart at `α`, transferred to
the Euclidean model space: the `toEuclidean`-image of the chart image of the
closed support of the chart-atlas partition-of-unity weight. -/
def chartPouKernel (α : M) : Set EuclN :=
  toEuclidean '' ((extChartAt I α) ''
    (tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)))

/-- The partition-of-unity kernel is compact. -/
lemma chartPouKernel_isCompact (α : M) :
    IsCompact (chartPouKernel (I := I) (M := M) α) :=
  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_isCompact
    (I := I) (M := M) α).image (toEuclidean (E := E)).continuous

/-- The partition-of-unity kernel is a measurable set. -/
lemma chartPouKernel_measurableSet (α : M) :
    MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
  (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.measurableSet

/-- The partition-of-unity kernel is contained in the Euclidean chart target. -/
lemma chartPouKernel_subset_chartTargetEuclid (α : M) :
    chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  rw [chartPouKernel, chartTargetEuclid]
  refine Set.image_mono ?_
  exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_subset_target
    (I := I) (M := M) α

/-- If a Euclidean point lies outside the partition-of-unity kernel, then its
chart-Euclidean preimage lies outside the closed support of the chart-atlas
partition-of-unity weight. -/
private lemma notMem_pouTsupport_of_notMem_chartPouKernel
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hker : y ∉ chartPouKernel (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
  classical
  intro hb
  apply hker
  refine ⟨(toEuclidean (E := E)).symm y, ⟨_, hb, ?_⟩, ?_⟩
  · have hmem : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
        (I := I) (M := M) hy
    exact (extChartAt I α).right_inv hmem
  · exact toEuclidean.apply_symm_apply y

/-- The Euclidean chart component vanishes outside the partition-of-unity
kernel. -/
lemma tensorChartComponent_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  classical
  by_cases htar : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) htar]
    have hb := notMem_pouTsupport_of_notMem_chartPouKernel
      (I := I) (M := M) α htar hy
    have hb_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
        Function.support
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      fun hc => hb (subset_tsupport _ hc)
    have hρ : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      by_contra hc; exact hb_supp hc
    change tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0
    unfold tensorChartComponentPou
    rw [hρ, zero_mul]
  · rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ htar]

/-- The chart-Euclidean partial of the Euclidean chart component vanishes
outside the partition-of-unity kernel. -/
lemma euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y = 0 := by
  classical
  have hsupp : Function.support
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx hzk)
  have htsupp : tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α :=
    (closure_minimal hsupp
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed)
  have hy_compl : y ∈ (tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx))ᶜ :=
    fun hc => hy (htsupp hc)
  have hopen : IsOpen (tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have hevt : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx
      =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy_compl) (fun z hz => ?_)
    exact image_eq_zero_of_notMem_tsupport hz
  rw [euclidPartial_def, hevt.fderiv_eq]
  simp

/-- A `C^∞`-on-the-chart-target function is bounded on the compact
partition-of-unity kernel: there is a non-negative constant `C` with
`‖c y‖ ≤ C` for every `y` in the kernel. -/
lemma exists_bound_on_chartPouKernel
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ chartPouKernel (I := I) (M := M) α, ‖c y‖ ≤ C := by
  classical
  have hcont : ContinuousOn (fun y => ‖c y‖)
      (chartPouKernel (I := I) (M := M) α) :=
    (hc.continuousOn.mono
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).norm
  obtain ⟨C, hC⟩ := (chartPouKernel_isCompact (I := I) (M := M) α).bddAbove_image
    hcont
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  exact (hC ⟨y, hy, rfl⟩).trans (le_max_left _ _)

/-- The indicator of the partition-of-unity kernel times a `C^∞`-on-the-chart-
target function is `AEStronglyMeasurable` with respect to the chart `L²`
measure. -/
lemma aestronglyMeasurable_indicator_mul
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    AEStronglyMeasurable
      (Set.indicator (chartPouKernel (I := I) (M := M) α) c)
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcont : ContinuousOn c (chartPouKernel (I := I) (M := M) α) :=
    hc.continuousOn.mono
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  have hmeas : AEStronglyMeasurable c
      ((chartL2Measure (I := I) (M := M) α).restrict
        (chartPouKernel (I := I) (M := M) α)) :=
    hcont.aestronglyMeasurable
      (chartPouKernel_measurableSet (I := I) (M := M) α)
  exact (aestronglyMeasurable_indicator_iff
    (chartPouKernel_measurableSet (I := I) (M := M) α)).mpr hmeas

/-- The product of a bounded `AEStronglyMeasurable` function with an `L²`
function is `L²`, with the `L²` norm of the product controlled by the bound. -/
lemma memLp_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : AEStronglyMeasurable c (chartL2Measure (I := I) (M := M) α))
    {f : EuclN → ℝ}
    (hf : MemLp f 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine ⟨hc_meas.mul hf.1, ?_⟩
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  have hmono := eLpNorm_mono (μ := chartL2Measure (I := I) (M := M) α)
    (p := 2) hpt
  calc eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α)
      ≤ eLpNorm ((C : ℝ) • f) 2 (chartL2Measure (I := I) (M := M) α) := hmono
    _ = ‖(C : ℝ)‖ₑ * eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_const_smul (C : ℝ) f 2 _
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hf.2

/-- The `L²` norm of the product of a bounded `AEStronglyMeasurable` function
`c` with an `L²` function is bounded by the sup bound times the `L²` norm. -/
lemma eLpNorm_bdd_mul_le
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (f : EuclN → ℝ) :
    eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  calc eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α)
      ≤ eLpNorm ((C : ℝ) • f) 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_mono hpt
    _ = ‖(C : ℝ)‖ₑ * eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_const_smul (C : ℝ) f 2 _
    _ = ENNReal.ofReal C *
          eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
        rw [Real.enorm_eq_ofReal hC]

/-- **Multiplication by a bounded measurable factor preserves `L²`-convergence.**
If a sequence `Fₙ` of `Lp` classes converges to `F` in `Lp ℝ 2 (chartL2Measure α)`,
and `c` is a globally bounded `AEStronglyMeasurable` function, then the sequence
of `L²` classes of `c · Fₙ` converges to the `L²` class of `c · F`. -/
lemma tendsto_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : AEStronglyMeasurable c (chartL2Measure (I := I) (M := M) α))
    {F : ℕ → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)}
    {Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)}
    (hF : Filter.Tendsto F atTop (𝓝 Flim)) :
    Filter.Tendsto
      (fun n => (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
      atTop
      (𝓝 ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y))) := by
  classical
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hCpos : (0 : ℝ) < C + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hF (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdist_eq :
      dist
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y)) =
      (eLpNorm
        (fun y => c y * (F n : EuclN → ℝ) y -
          c y * (Flim : EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [Lp.dist_def]
    refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
    filter_upwards [MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC
        hc_bd hc_meas (Lp.memLp (F n))),
      MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim))] with y hy₁ hy₂
    rw [Pi.sub_apply, hy₁, hy₂]
  rw [hdist_eq]
  have hsub_eq :
      (fun y => c y * (F n : EuclN → ℝ) y - c y * (Flim : EuclN → ℝ) y) =
        (fun y => c y * ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) := by
    funext y; ring
  rw [hsub_eq]
  have hle := eLpNorm_bdd_mul_le (I := I) (M := M) α hC hc_bd
    (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
  have hsub_ae :
      (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (((F n) - Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ) :=
    (Lp.coeFn_sub (F n) Flim).symm
  have hdist_F :
      eLpNorm (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y) 2
          (chartL2Measure (I := I) (M := M) α) =
        ENNReal.ofReal (dist (F n) Flim) := by
    have hfin : eLpNorm
        (((F n) - Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) ≠ ⊤ :=
      (Lp.memLp ((F n) - Flim)).2.ne
    rw [eLpNorm_congr_ae hsub_ae, Lp.dist_def,
      ENNReal.ofReal_toReal ((eLpNorm_congr_ae hsub_ae) ▸ hfin)]
    exact (eLpNorm_congr_ae hsub_ae).symm
  rw [hdist_F] at hle
  have hfin : (ENNReal.ofReal C * ENNReal.ofReal (dist (F n) Flim)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have hreal :
      (eLpNorm (fun y => c y *
          ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) 2
        (chartL2Measure (I := I) (M := M) α)).toReal ≤
        C * dist (F n) Flim := by
    refine (ENNReal.toReal_mono hfin hle).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ENNReal.toReal_ofReal dist_nonneg]
  refine lt_of_le_of_lt hreal ?_
  have hd : dist (F n) Flim < ε / (C + 1) := hN n hn
  calc C * dist (F n) Flim
      ≤ (C + 1) * dist (F n) Flim :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_left hd hCpos
    _ = ε := by field_simp

/-- The Euclidean chart component is globally `C^∞`: a restatement of
`tensorChartComponent_contMDiff` via the model-space `ContMDiff ↔ ContDiff`
correspondence. -/
lemma tensorChartComponent_contDiff'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mp
    (tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx)

/-- The topological support of the Euclidean chart component is contained in the
partition-of-unity kernel, hence in the chart target. -/
lemma tensorChartComponent_tsupport_subset_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
  classical
  have hsupp : Function.support
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx hzk)
  exact closure_minimal hsupp
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed

/-- The chosen weak `k`-th chart partial of the Euclidean chart component agrees,
almost everywhere on the chart `L²` measure, with the classical chart-Euclidean
partial. -/
lemma chosenWeakPartial'_tensorChartComponent_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorChartComponent_contDiff' (I := I) (M := M) g r s S α Idx Jdx
  have hu_cpt : HasCompactSupport u :=
    tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (tensorChartComponent_tsupport_subset_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx).trans
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : MemWkp (d := Module.finrank ℝ E) 1 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      hu_smooth hu_cpt hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := Module.finrank ℝ E)
    hp_one hΩ_open hu_smooth hu_W1p k
  rw [chartL2Measure]
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y; rw [euclidPartial_def]

/-- The function underlying a finite sum of `L²` classes agrees almost
everywhere with the finite sum of the underlying functions. -/
lemma coeFn_finsetSum_lp
    (α : M) {ι : Type*} (s : Finset ι)
    (G : ι → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, G a) : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, ((G a : EuclN → ℝ) y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add (G a) (∑ b ∈ t, G b)).trans ?_
      filter_upwards [ih] with y hy
      rw [Pi.add_apply, hy, Finset.sum_insert ha]

/-- The function underlying a finite sum of `L²` classes of `MemLp` functions
agrees almost everywhere with the finite sum of those functions. -/
lemma coeFn_finsetSum_toLp
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, MemLp (f a) 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, (hf a).toLp (f a)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y := by
  classical
  refine (coeFn_finsetSum_lp (I := I) (M := M) α s
    (fun a => (hf a).toLp (f a))).trans ?_
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      filter_upwards [ih, MemLp.coeFn_toLp (hf a)] with y hy hya
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hya, hy]

/-- The `L²` class of a function equal almost everywhere to a finite sum of `L²`
functions is the finite sum of the `L²` classes of the summands. -/
lemma toLp_finsetSum_congr
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, MemLp (f a) 2 (chartL2Measure (I := I) (M := M) α))
    {F : EuclN → ℝ}
    (hF : MemLp F 2 (chartL2Measure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y) :
    hF.toLp F = ∑ a ∈ s, (hf a).toLp (f a) := by
  classical
  apply Lp.ext
  exact (MemLp.coeFn_toLp hF).trans
    (hFeq.trans (coeFn_finsetSum_toLp (I := I) (M := M) α s hf).symm)

/-- **Finite-sum `L²`-convergence assembly.** If, for each index `a` in a finite
set, the `L²` classes `(hf a n).toLp (f a n)` converge to `(hflim a).toLp
(flim a)`, and `Fₙ` agrees almost everywhere with `∑ a, f a n` while `Flim`
agrees almost everywhere with `∑ a, flim a`, then the `L²` class of `Fₙ`
converges to the `L²` class of `Flim`. -/
lemma tendsto_toLp_finsetSum
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ a : ι, MemLp (flim a) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) atTop
        (𝓝 ((hflim a).toLp (flim a))))
    {Fn : ℕ → EuclN → ℝ} {Flim : EuclN → ℝ}
    (hFn : ∀ n : ℕ, MemLp (Fn n) 2 (chartL2Measure (I := I) (M := M) α))
    (hFlim : MemLp Flim 2 (chartL2Measure (I := I) (M := M) α))
    (hFn_eq : ∀ n : ℕ, Fn n =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a n y)
    (hFlim_eq : Flim =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, flim a y) :
    Filter.Tendsto (fun n => (hFn n).toLp (Fn n)) atTop
      (𝓝 (hFlim.toLp Flim)) := by
  classical
  have h_n : ∀ n : ℕ,
      (hFn n).toLp (Fn n) =
        ∑ a ∈ s, (hf a n).toLp (f a n) :=
    fun n => toLp_finsetSum_congr (I := I) (M := M) α s
      (fun a => hf a n) (hFn n) (hFn_eq n)
  have h_lim :
      hFlim.toLp Flim = ∑ a ∈ s, (hflim a).toLp (flim a) :=
    toLp_finsetSum_congr (I := I) (M := M) α s hflim hFlim hFlim_eq
  rw [show (fun n => (hFn n).toLp (Fn n)) =
      (fun n => ∑ a ∈ s, (hf a n).toLp (f a n)) from funext h_n, h_lim]
  exact tendsto_finset_sum s (fun a _ => h_tendsto a)

/-- A `C^∞`-on-the-chart-target factor, indicator-cut to the partition-of-unity
kernel, times an arbitrary `L²` limit class, is `L²`. -/
lemma memLp_indicatorFactor_mul_lp
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (G : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (G : EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc) (Lp.memLp G)

/-- The chart push-forward of the raw chart component of the partition-of-unity-
weighted section equals the canonical Euclidean chart component. -/
private lemma chartPushedRaw_tensorChartComponentRaw_pouSmul_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx) =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := by
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S Idx Jdx, tensorChartComponent_def]

/-- The `T`-independent `C^∞` factor of the `(P, Q, k, l)`-summand of the
principal rotation coefficient: the chart-frame tensor-metric Gram, the
unweighted inverse Gram, and the chart-Euclidean partial of the inverse-Gram
column entry. -/
def principalRotationFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
        chartInvGramEuclid (I := I) g α k l y *
      euclidPartial (E := E) l (gramInvEntry (I := I) (M := M) g r s α Q P₀) y

/-- The `T`-independent factor of the principal rotation coefficient is `C^∞` on
the Euclidean chart target. -/
lemma principalRotationFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (euclidPartial_contDiffOn_target (I := I) (M := M) α l
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀))

/-- On the Euclidean chart target, the zeroth-order Christoffel correction of the
partition-of-unity-weighted approximant is the finite linear combination, over
component multi-index pairs, of the lower-order correction coefficient times the
canonical Euclidean chart component. -/
private lemma covDerivLowerOrderTerm_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivLowerOrderTerm_def]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S p.1 p.2,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α p.1 p.2) hy]

/-- The `T`-independent `C^∞` factor of the `(P, Q, k, p)`-summand of the
chart-density-weighted lower-order gradient coefficient. -/
def weightedGradFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          chartInvGramEuclid (I := I) g α k l y *
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2 y *
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀

/-- The `T`-independent factor of the chart-density-weighted lower-order gradient
coefficient is `C^∞` on the Euclidean chart target. -/
lemma weightedGradFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((((densityOnEuclid_contDiffOn (I := I) g α).mul
        (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q)).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
      g r s α k P.1 p.1 P.2 p.2)).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)

/-- On the chart target, the chart-density-weighted lower-order gradient
coefficient at the partition-of-unity weight of a smooth section `S` equals the
four-fold finite sum of `weightedGradFactor` times the bare chart-component atom
of `S`. -/
private lemma weightedGradCoeff_pouSmul_eqOn_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (S : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀ l y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                tensorChartComponent (I := I) (M := M) g r s
                  S α p.1 p.2 y := by
  classical
  simp only [weightedGradCoeff, covLowerOrderRotationGradCoeff_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
    S k P.1 P.2 hy]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [weightedGradFactor]
  ring

/-- **One nesting level of finite-sum `L²`-convergence.** If, for every index `a`
in a finite type, the `L²` classes `(hf a n).toLp (f a n)` converge to
`(hflim a).toLp (flim a)`, then the `L²` class of the finite sum `∑ a, f a n`
converges to the `L²` class of `∑ a, flim a`. The summed `L²` classes are built
from `memLp_finset_sum`, so the conclusion composes with itself across nesting
levels. -/
lemma tendsto_sumToLp
    (α : M) {ι : Type*} [Fintype ι]
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ a : ι, MemLp (flim a) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) atTop
        (𝓝 ((hflim a).toLp (flim a)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
        Finset.univ (fun a _ => hf a n)).toLp (fun y => ∑ a, f a n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
        Finset.univ (fun a _ => hflim a)).toLp (fun y => ∑ a, flim a y))) :=
  tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ hf hflim h_tendsto
    (fun n => memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      Finset.univ (fun a _ => hf a n))
    (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      Finset.univ (fun a _ => hflim a))
    (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl

/-- **The chart-Euclidean partial distributes across a finite sum.** For a
finite family of functions all differentiable at `y`, the `l`-th chart-Euclidean
partial of the sum is the sum of the chart-Euclidean partials. -/
lemma euclidPartial_finsetSum
    (l : Fin (Module.finrank ℝ E)) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ} {y : EuclN}
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) y) :
    euclidPartial (E := E) l (fun z => ∑ a ∈ s, f a z) y =
      ∑ a ∈ s, euclidPartial (E := E) l (f a) y := by
  classical
  rw [euclidPartial_def, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => by rw [euclidPartial_def])

/-- **Four-fold nested finite-sum `L²`-convergence.** Per-`(a, b, c, d)`-leaf
`L²`-convergence assembles into the `L²`-convergence of the four-fold nested
finite sum. -/
private lemma tendsto_sum4
    (α : M) {κ₁ κ₂ κ₃ κ₄ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (n : ℕ),
      MemLp (f a b c d n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      MemLp (flim a b c d) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      Filter.Tendsto (fun n => (hf a b c d n).toLp (f a b c d n)) atTop
        (𝓝 ((hflim a b c d).toLp (flim a b c d)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => hf a b c d n))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, f a b c d n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => hflim a b c d))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, flim a b c d y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, f a b c d n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, flim a b c d y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n))))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d))))
    (fun a => tendsto_sumToLp (I := I) (M := M) α
      (f := fun b => fun n y => ∑ c, ∑ d, f a b c d n y)
      (flim := fun b => fun y => ∑ c, ∑ d, flim a b c d y)
      (fun b n => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n)))
      (fun b => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d)))
      (fun b => tendsto_sumToLp (I := I) (M := M) α
        (f := fun c => fun n y => ∑ d, f a b c d n y)
        (flim := fun c => fun y => ∑ d, flim a b c d y)
        (fun c n => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n))
        (fun c => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d))
        (fun c => tendsto_sumToLp (I := I) (M := M) α
          (hf := fun d n => hf a b c d n) (hflim := fun d => hflim a b c d)
          (h_tendsto a b c))))

/-- **Five-fold nested finite-sum `L²`-convergence.** Per-`(a, b, c, d, e)`-leaf
`L²`-convergence assembles into the `L²`-convergence of the five-fold nested
finite sum. -/
private lemma tendsto_sum5
    (α : M) {κ₁ κ₂ κ₃ κ₄ κ₅ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄] [Fintype κ₅]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅) (n : ℕ),
      MemLp (f a b c d e n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      MemLp (flim a b c d e) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      Filter.Tendsto (fun n => (hf a b c d e n).toLp (f a b c d e n)) atTop
        (𝓝 ((hflim a b c d e).toLp (flim a b c d e)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => memLp_finset_sum Finset.univ
                  (fun e _ => hf a b c d e n)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => memLp_finset_sum Finset.univ
                  (fun e _ => hflim a b c d e)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ
          (fun d _ => memLp_finset_sum Finset.univ
            (fun e _ => hf a b c d e n)))))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ
          (fun d _ => memLp_finset_sum Finset.univ
            (fun e _ => hflim a b c d e)))))
    (fun a => tendsto_sum4 (I := I) (M := M) α
      (f := fun b c d e n => f a b c d e n)
      (flim := fun b c d e => flim a b c d e)
      (fun b c d e n => hf a b c d e n)
      (fun b c d e => hflim a b c d e)
      (fun b c d e => h_tendsto a b c d e))

/-- A function `C^∞` on the open Euclidean chart target is differentiable at
every point of the chart target. -/
lemma differentiableAt_of_contDiffOn_chartTarget
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ c y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  exact (hc.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)

/-- The bare Euclidean chart component of a smooth section is differentiable at
every point. -/
lemma differentiableAt_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN) :
    DifferentiableAt ℝ
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y :=
  ((tensorChartComponent_contDiff' (I := I) (M := M) g r s S α Idx Jdx).differentiable
    (by simp)).differentiableAt

/-- On the chart target, the `l`-th chart-Euclidean partial of the
chart-density-weighted lower-order gradient coefficient at the
partition-of-unity-weighted approximant equals the four-fold finite sum of the
Leibniz contributions: the chart-Euclidean partial of `weightedGradFactor` times
the bare chart-component atom, plus `weightedGradFactor` times the
chart-Euclidean partial of the bare chart-component atom. -/
private lemma euclidPartial_weightedGradCoeff_pouSmul_eqOn_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (S : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α P₀ l) y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                euclidPartial (E := E) l
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
                  tensorChartComponent (I := I) (M := M) g r s
                    S α p.1 p.2 y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                    euclidPartial (E := E) l
                      (tensorChartComponent (I := I) (M := M) g r s
                        S α p.1 p.2) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  set wₙ : SmoothCcTensor g r s := S with hwₙ_def
  set Sum4 : EuclN → ℝ := fun z =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p z *
              tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 z
    with hSum4_def
  have hcoeff_evt :
      weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α wₙ) α P₀ l =ᶠ[𝓝 y] Sum4 := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy) (fun z hz => ?_)
    rw [hSum4_def]
    exact weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀ l wₙ hz
  rw [euclidPartial_def, hcoeff_evt.fderiv_eq, ← euclidPartial_def]
  have hleaf_diff : ∀ P Q : TensorCompIdx (E := E) r s,
      ∀ k : Fin (Module.finrank ℝ E), ∀ p : TensorCompIdx (E := E) r s,
      DifferentiableAt ℝ
        (fun z => weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p z *
          tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 z) y :=
    fun P Q k p =>
      (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        hy).mul
      (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
        p.1 p.2 y)
  rw [hSum4_def, euclidPartial_finsetSum (E := E) l Finset.univ
    (fun P _ => DifferentiableAt.fun_sum (fun Q _ =>
      DifferentiableAt.fun_sum (fun k _ =>
        DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p))))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun Q _ => DifferentiableAt.fun_sum (fun k _ =>
      DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p)))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun k _ => DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun p _ => hleaf_diff P Q k p)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact euclidPartial_mul (E := E) l
    (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p) hy)
    (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
      p.1 p.2 y)

/-- The chart-Euclidean partial of the `T`-independent `C^∞` factor
`weightedGradFactor` is `C^∞` on the Euclidean chart target. -/
lemma euclidPartial_weightedGradFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p))
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_target (I := I) (M := M) α l
    (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)

/-- The `L²` class of a function equal almost everywhere to a sum of two `L²`
functions is the sum of the `L²` classes of the summands. -/
lemma toLp_add_eq
    (α : M) {f₁ f₂ F : EuclN → ℝ}
    (hf₁ : MemLp f₁ 2 (chartL2Measure (I := I) (M := M) α))
    (hf₂ : MemLp f₂ 2 (chartL2Measure (I := I) (M := M) α))
    (hF : MemLp F 2 (chartL2Measure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => f₁ y + f₂ y) :
    hF.toLp F = hf₁.toLp f₁ + hf₂.toLp f₂ := by
  classical
  apply Lp.ext
  refine (MemLp.coeFn_toLp hF).trans (hFeq.trans ?_)
  refine Filter.EventuallyEq.symm ?_
  refine (Lp.coeFn_add (hf₁.toLp f₁) (hf₂.toLp f₂)).trans ?_
  filter_upwards [MemLp.coeFn_toLp hf₁, MemLp.coeFn_toLp hf₂] with y hy₁ hy₂
  rw [Pi.add_apply, hy₁, hy₂]

/-- The `T`-independent `C^∞` factor of the chart-partial-atom summand of the
lower-order rotation value coefficient: the chart-frame tensor-metric Gram, the
unweighted inverse Gram, and the collapsed Christoffel coefficient. -/
def valuePartialFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
        chartInvGramEuclid (I := I) g α k l y *
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y

/-- The `T`-independent `C^∞` factor of the chart-partial-atom summand is `C^∞`
on the Euclidean chart target. -/
lemma valuePartialFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M) g r s α P₀ l Q)

/-- The `T`-independent `C^∞` factor of the component-atom summand of the
lower-order rotation value coefficient: the chart-frame tensor-metric Gram, the
unweighted inverse Gram, the sum of the chart-Euclidean partial of the
inverse-Gram entry and the collapsed Christoffel coefficient, and the lower-order
correction coefficient. -/
def valueComponentFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
          chartInvGramEuclid (I := I) g α k l y *
        (euclidPartial (E := E) l
              (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y) *
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2 y

/-- The `T`-independent `C^∞` factor of the component-atom summand is `C^∞` on
the Euclidean chart target. -/
lemma valueComponentFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
      ((euclidPartial_contDiffOn_target (I := I) (M := M) α l
          (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)).add
        (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M)
          g r s α P₀ l Q))).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2)

/-- On the chart target, the lower-order rotation value coefficient at the
partition-of-unity-weighted approximant equals the four-fold nested
chart-partial-atom sum (`valuePartialFactor` against the chart-Euclidean partial
of the bare chart-component atom) plus the five-fold nested component-atom sum
(`valueComponentFactor` against the bare chart-component atom). -/
private lemma covLowerOrderRotationValueCoeff_pouSmul_eqOn_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (S : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀ y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                  euclidPartial (E := E) k
                    (tensorChartComponent (I := I) (M := M) g r s
                      S α P.1 P.2) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p y *
                      tensorChartComponent (I := I) (M := M) g r s
                        S α p.1 p.2 y := by
  classical
  set wₙ : SmoothCcTensor g r s := S with hwₙ_def
  rw [covLowerOrderRotationValueCoeff_def]
  have hbody : ∀ P Q : TensorCompIdx (E := E) r s,
      ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α k l y *
          (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s (pouSmul (I := I) (M := M) g r s α wₙ) α P.1 P.2)) y *
              lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (pouSmul (I := I) (M := M) g r s α wₙ) α k P.1 P.2 y *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (pouSmul (I := I) (M := M) g r s α wₙ) α k P.1 P.2 y *
                lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y) =
        chartInvGramEuclid (I := I) g α k l y *
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y *
            euclidPartial (E := E) k
              (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y
          + ∑ p : TensorCompIdx (E := E) r s,
              chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) *
                  covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s α k P.1 p.1 P.2 p.2 y *
                tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 y := by
    intro P Q k l
    rw [show euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                (pouSmul (I := I) (M := M) g r s α wₙ) α P.1 P.2)) y =
          euclidPartial (E := E) k
            (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y from
        congrArg (fun u : EuclN → ℝ => euclidPartial (E := E) k u y)
          (chartPushedRaw_tensorChartComponentRaw_pouSmul_eq (I := I) (M := M)
            g r s α wₙ P.1 P.2)]
    rw [covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α wₙ
      k P.1 P.2 hy]
    rw [show (∑ p : TensorCompIdx (E := E) r s,
              chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) *
                  covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s α k P.1 p.1 P.2 p.2 y *
                tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 y) =
          chartInvGramEuclid (I := I) g α k l y *
              ((∑ p : TensorCompIdx (E := E) r s,
                  covDerivLowerOrderCoeff (I := I) (M := M)
                      g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y) +
            chartInvGramEuclid (I := I) g α k l y *
              ((∑ p : TensorCompIdx (E := E) r s,
                  covDerivLowerOrderCoeff (I := I) (M := M)
                      g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) *
                lowerOrderRotationLOCoeff (I := I) (M := M)
                  g r s α P₀ l Q y) from by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_); ring]
    ring
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
      (fun l _ => hbody P Q k l))]))]
  have hsplit : ∀ P Q : TensorCompIdx (E := E) r s,
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
          (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (chartInvGramEuclid (I := I) g α k l y *
                  lowerOrderRotationLOCoeff (I := I) (M := M)
                    g r s α P₀ l Q y *
                  euclidPartial (E := E) k
                    (tensorChartComponent (I := I) (M := M)
                      g r s wₙ α P.1 P.2) y
              + ∑ p : TensorCompIdx (E := E) r s,
                  chartInvGramEuclid (I := I) g α k l y *
                      (euclidPartial (E := E) l
                          (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y) *
                      covDerivLowerOrderCoeff (I := I) (M := M)
                        g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
              euclidPartial (E := E) k
                (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y)
          + ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
                  tensorChartComponent (I := I) (M := M)
                    g r s wₙ α p.1 p.2 y := by
    intro P Q
    rw [Finset.mul_sum]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                ∑ l : Fin (Module.finrank ℝ E),
                  (chartInvGramEuclid (I := I) g α k l y *
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y *
                        euclidPartial (E := E) k
                          (tensorChartComponent (I := I) (M := M)
                            g r s wₙ α P.1 P.2) y
                    + ∑ p : TensorCompIdx (E := E) r s,
                        chartInvGramEuclid (I := I) g α k l y *
                            (euclidPartial (E := E) l
                                (gramInvEntry (I := I) (M := M)
                                  g r s α Q P₀) y +
                              lowerOrderRotationLOCoeff (I := I) (M := M)
                                g r s α P₀ l Q y) *
                            covDerivLowerOrderCoeff (I := I) (M := M)
                              g r s α k P.1 p.1 P.2 p.2 y *
                          tensorChartComponent (I := I) (M := M)
                            g r s wₙ α p.1 p.2 y)) =
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M)
                    g r s wₙ α P.1 P.2) y
              + ∑ p : TensorCompIdx (E := E) r s,
                  valueComponentFactor (I := I) (M := M)
                      g r s α P₀ P Q k l p y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [mul_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · rw [valuePartialFactor]; ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [valueComponentFactor]; ring]
    rw [Finset.sum_congr rfl (fun k _ =>
        Finset.sum_add_distrib
          (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))),
      Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
    (fun Q _ => hsplit P Q))]
  rw [Finset.sum_congr rfl (fun P _ =>
      Finset.sum_add_distrib (s := (Finset.univ : Finset (TensorCompIdx (E := E) r s)))),
    Finset.sum_add_distrib]

/-- Chart-locality-free twin of `approxComponentLp`. -/
def approxComponentLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (n : ℕ) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (tensorChartComponent_memLp (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P.1 P.2).toLp
    (tensorChartComponent (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `componentLpLimit`. -/
def componentLpLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  i.fst.val •
    tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      α P

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `approxComponentLp_tendsto`. -/
lemma approxComponentLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => approxComponentLp (I := I) (M := M) g r s i α P n)
      atTop
      (𝓝 (componentLpLimit (I := I) (M := M) g r s i α P)) := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_tendsto :=
    (eigenvectorChartComponentL2_tendsto (I := I) (M := M)
      g r s i α P).const_smul i.fst.val
  have h_term : ∀ n : ℕ,
      i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)) α P =
        approxComponentLp (I := I) (M := M) g r s i α P n := by
    intro n
    rw [eigenvectorChartComponentL2_approx_eq (I := I) (M := M)
      g r s i α P n, smul_smul, mul_inv_cancel₀ i.fst.val_ne_zero,
      one_smul]
    rfl
  rw [show (fun n => i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)) α P) =
      (fun n => approxComponentLp (I := I) (M := M)
        g r s i α P n) from funext h_term] at h_tendsto
  exact h_tendsto

/-- Chart-locality-free twin of `approxPartialLp`. -/
def approxPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
    α P.1 P.2 k).toLp
    (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
      (tensorChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P.1 P.2)
      (chartTargetEuclid (I := I) (M := M) α))

/-- Chart-locality-free twin of `partialLpLimit`. -/
def partialLpLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  i.fst.val •
    eigenvectorChartPartialLp (I := I) (M := M) g r s i α P k

/-- Chart-locality-free twin of `approxPartialLp_tendsto`. -/
lemma approxPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => approxPartialLp (I := I) (M := M) g r s i α P k n)
      atTop
      (𝓝 (partialLpLimit (I := I) (M := M) g r s i α P k)) := by
  classical
  have h_tendsto :=
    (eigenvectorChartPartialLp_tendsto (I := I) (M := M)
      g r s i α P k).const_smul i.fst.val
  have h_term : ∀ n : ℕ,
      i.fst.val •
        ((i.fst.val)⁻¹ •
          eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n))) =
        approxPartialLp (I := I) (M := M) g r s i α P k n := by
    intro n
    rw [eigenvectorChartPartialLp_approx_eq (I := I) (M := M)
      g r s i α P k n, smul_smul, mul_inv_cancel₀ i.fst.val_ne_zero,
      one_smul]
    rfl
  rw [show (fun n => i.fst.val •
        ((i.fst.val)⁻¹ •
          eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n)))) =
      (fun n => approxPartialLp (I := I) (M := M)
        g r s i α P k n) from funext h_term] at h_tendsto
  exact h_tendsto

/-- Chart-locality-free twin of `tendsto_componentSummand`. -/
lemma tendsto_componentSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (componentLpLimit (I := I) (M := M) g r s i α P :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    (approxComponentLp_tendsto (I := I) (M := M) g r s i α P)
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxComponentLp (I := I) (M := M)
          g r s i α P n))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    have hcomp : (approxComponentLp (I := I) (M := M)
        g r s i α P n : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 := by
      rw [approxComponentLp]; exact MemLp.coeFn_toLp _
    filter_upwards [hcomp] with y hy
    rw [hy]
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hker]
    · rw [hci_def, Set.indicator_of_notMem hker, zero_mul,
        tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 hker, mul_zero]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (componentLpLimit (I := I) (M := M)
          g r s i α P))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxComponentLp (I := I) (M := M)
          g r s i α P n))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

/-- Chart-locality-free twin of `tendsto_partialSummand`. -/
lemma tendsto_partialSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (partialLpLimit (I := I) (M := M) g r s i α P k :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    (approxPartialLp_tendsto (I := I) (M := M) g r s i α P k)
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxPartialLp (I := I) (M := M)
          g r s i α P k n))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    have hpart : (approxPartialLp (I := I) (M := M)
        g r s i α P k n : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) := by
      refine (MemLp.coeFn_toLp _).trans ?_
      exact chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P.1 P.2 k
    filter_upwards [hpart] with y hy
    rw [hy]
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hker]
    · rw [hci_def, Set.indicator_of_notMem hker, zero_mul,
        euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 k hker, mul_zero]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (partialLpLimit (I := I) (M := M)
          g r s i α P k))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxPartialLp (I := I) (M := M)
          g r s i α P k n))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

/-- Chart-locality-free twin of
`euclidPartial_tensorChartComponent_approx_memLp`. -/
lemma euclidPartial_tensorChartComponent_approx_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2)) 2
      (chartL2Measure (I := I) (M := M) α) :=
  MemLp.ae_eq
    (chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2 k)
    (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      α P.1 P.2 k)

/-- Chart-locality-free twin of `memLp_factor_mul_componentAtom`. -/
lemma memLp_factor_mul_componentAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    MemLp
      (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2 y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, zero_mul,
        tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 hker, mul_zero]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (tensorChartComponent_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2)

/-- Chart-locality-free twin of `memLp_factor_mul_partialAtom`. -/
lemma memLp_factor_mul_partialAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    MemLp
      (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          euclidPartial (E := E) k
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P.1 P.2) y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, zero_mul,
        euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 k hker, mul_zero]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (euclidPartial_tensorChartComponent_approx_memLp (I := I) (M := M)
      g r s i α P k n)

/-- Chart-locality-free twin of `covPrincipalRotationCoeffLimit`. -/
noncomputable def covPrincipalRotationCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              (partialLpLimit (I := I) (M := M) g r s i α P k :
                EuclN → ℝ) y

/-- Chart-locality-free twin of `covPrincipalRotationCoeff_pouSmul_eq_sum`. -/
private lemma covPrincipalRotationCoeff_pouSmul_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) (y : EuclN) :
    covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α P.1 P.2) y := by
  classical
  rw [covPrincipalRotationCoeff_def]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [chartPushedRaw_tensorChartComponentRaw_pouSmul_eq (I := I) (M := M)
    g r s α (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor P.1 P.2]
  rw [principalRotationFactor]
  ring

/-- Chart-locality-free twin of `covPrincipalRotationCoeff_pouSmul_memLp`. -/
theorem covPrincipalRotationCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ =>
            memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α P k n
              (principalRotationFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))).ae_eq ?_
  exact Filter.EventuallyEq.symm (Filter.Eventually.of_forall (fun y =>
    covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s i α P₀ n y))

/-- Chart-locality-free twin of `covPrincipalRotationCoeffLimit_memLp`. -/
theorem covPrincipalRotationCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covPrincipalRotationCoeffLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (principalRotationFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ P Q k l)
            (partialLpLimit (I := I) (M := M) g r s i α P k)))))

/-- **The `n → ∞` `L²`-limit of the principal rotation coefficient
(chart-locality-free).** Chart-locality-free twin of
`covPrincipalRotationCoeff_tendsto`. -/
theorem covPrincipalRotationCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covPrincipalRotationCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _)
      atTop
      (𝓝 ((covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _)) := by
  classical
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (n : ℕ),
      MemLp (fun y => principalRotationFactor (I := I) (M := M)
            g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          euclidPartial (E := E) a.2.2.1
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α a.1.1 a.1.2) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_partialAtom (I := I) (M := M) g r s i α a.1
      a.2.2.1 n (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (partialLpLimit (I := I) (M := M) g r s i α a.1 a.2.2.1 :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (partialLpLimit (I := I) (M := M) g r s i α a.1 a.2.2.1)
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      Filter.Tendsto (fun n => (hf a n).toLp _) atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_partialSummand (I := I) (M := M) g r s i α a.1 a.2.2.1
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  have hFn_eq : ∀ n : ℕ,
      covPrincipalRotationCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            euclidPartial (E := E) a.2.2.1
              (tensorChartComponent (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α a.1.1 a.1.2) y := by
    intro n
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s i α P₀ n y]
    simp only [Fintype.sum_prod_type]
  have hFlim_eq :
      covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (partialLpLimit (I := I) (M := M)
              g r s i α a.1 a.2.2.1 : EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ n)
    (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀)
    hFn_eq hFlim_eq

/-- Chart-locality-free twin of `weightedGradCoeffLimit`. -/
noncomputable def weightedGradCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              (componentLpLimit (I := I) (M := M) g r s i α p :
                EuclN → ℝ) y

/-- Chart-locality-free twin of `weightedGradCoeff_pouSmul_eqOn`. -/
private lemma weightedGradCoeff_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ l y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α p.1 p.2 y := by
  classical
  simp only [weightedGradCoeff, covLowerOrderRotationGradCoeff_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
    (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor k P.1 P.2 hy]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [weightedGradFactor]
  ring

/-- Chart-locality-free twin of `weightedGradCoeff_pouSmul_memLp`. -/
theorem weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ =>
            memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s i α p n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s i α P₀ l n hy)

/-- Chart-locality-free twin of `weightedGradCoeffLimit_memLp`. -/
theorem weightedGradCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffLimit (I := I) (M := M)
        g r s i α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (weightedGradFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q k p)
            (componentLpLimit (I := I) (M := M) g r s i α p)))))

/-- **The `n → ∞` `L²`-limit of the chart-density-weighted lower-order gradient
coefficient (chart-locality-free).** Chart-locality-free twin of
`weightedGradCoeff_tendsto`. -/
theorem weightedGradCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _)
      atTop
      (𝓝 ((weightedGradCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _)) := by
  classical
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) (n : ℕ),
      MemLp (fun y => weightedGradFactor (I := I) (M := M)
            g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_componentAtom (I := I) (M := M) g r s i α
      a.2.2.2 n (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (componentLpLimit (I := I) (M := M) g r s i α a.2.2.2 :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (componentLpLimit (I := I) (M := M) g r s i α a.2.2.2)
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      Filter.Tendsto (fun n => (hf a n).toLp _) atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_componentSummand (I := I) (M := M) g r s i α a.2.2.2
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  have hFn_eq : ∀ n : ℕ,
      weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀ l
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y := by
    intro n
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s i α P₀ l n hy]
    simp only [Fintype.sum_prod_type]
  have hFlim_eq :
      weightedGradCoeffLimit (I := I) (M := M) g r s i α P₀ l
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M)
                g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (componentLpLimit (I := I) (M := M)
              g r s i α a.2.2.2 : EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ l n)
    (weightedGradCoeffLimit_memLp (I := I) (M := M) g r s i α P₀ l)
    hFn_eq hFlim_eq

/-- Chart-locality-free twin of `weightedGradCoeffDivLimit`. -/
noncomputable def weightedGradCoeffDivLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p))
                  y *
                (componentLpLimit (I := I) (M := M) g r s i α p :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)
                    y *
                  (partialLpLimit (I := I) (M := M) g r s i α p l :
                    EuclN → ℝ) y

/-- Chart-locality-free twin of `euclidPartial_weightedGradCoeff_pouSmul_memLp`. -/
theorem euclidPartial_weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α P₀ l)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcomp : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α p.1 p.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s i α p n
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  have hpart : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                euclidPartial (E := E) l
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α p.1 p.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α p l n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  refine (hcomp.add hpart).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    euclidPartial_weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀ l
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
      hy)

/-- Chart-locality-free twin of `weightedGradCoeffDivLimit_memLp`. -/
theorem weightedGradCoeffDivLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffDivLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (componentLpLimit (I := I) (M := M) g r s i α p)))))
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (partialLpLimit (I := I) (M := M) g r s i α p l)))))

/-- **The `n → ∞` `L²`-limit of the chart-Euclidean divergence of the
chart-density-weighted lower-order gradient coefficient (chart-locality-free).**
Chart-locality-free twin of `weightedGradCoeffDiv_tendsto`. -/
theorem weightedGradCoeffDiv_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n).toLp _)
      atTop
      (𝓝 ((weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _)) := by
  classical
  have h_comp := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      euclidPartial (E := E) l
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s i α p n
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (componentLpLimit (I := I) (M := M) g r s i α p))
    (fun P Q k p => tendsto_componentSummand (I := I) (M := M)
      g r s i α p
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s i α p n
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p)
        (componentLpLimit (I := I) (M := M) g r s i α p)))
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
        euclidPartial (E := E) l
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α p.1 p.2) y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        (partialLpLimit (I := I) (M := M) g r s i α p l :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s i α p l n
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (partialLpLimit (I := I) (M := M) g r s i α p l))
    (fun P Q k p => tendsto_partialSummand (I := I) (M := M)
      g r s i α p l
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s i α p l n
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        (partialLpLimit (I := I) (M := M) g r s i α p l)))
  have h_add := h_comp.add h_part
  have h_termN : ∀ n : ℕ,
      (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom
                  (I := I) (M := M) g r s i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      euclidPartial_weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
        g r s α P₀ l
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
        hy)
  have h_termLim :
      (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (componentLpLimit (I := I) (M := M)
                    g r s i α p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (partialLpLimit (I := I) (M := M)
                    g r s i α p l)))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffDivLimit]
  rw [show (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom
                  (I := I) (M := M) g r s i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

/-- **The `n → ∞` `L²`-limit of the total chart-Euclidean divergence
(chart-locality-free).** Chart-locality-free twin of
`weightedGradCoeffDivSum_tendsto`. -/
theorem weightedGradCoeffDivSum_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => ∑ l : Fin (Module.finrank ℝ E),
        (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
          g r s i α P₀ l n).toLp _)
      atTop
      (𝓝 (∑ l : Fin (Module.finrank ℝ E),
        (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
          g r s i α P₀ l).toLp _)) :=
  tendsto_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => weightedGradCoeffDiv_tendsto (I := I) (M := M)
      g r s i α P₀ l)

/-- Chart-locality-free twin of `covLowerOrderRotationValueCoeffLimit`. -/
noncomputable def covLowerOrderRotationValueCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
                (partialLpLimit (I := I) (M := M) g r s i α P k :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M)
                      g r s i α p : EuclN → ℝ) y

/-- Chart-locality-free twin of `covLowerOrderRotationValueCoeff_pouSmul_memLp`. -/
theorem covLowerOrderRotationValueCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hpart : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s i α P k n
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))
  have hcomp : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
                  tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor α p.1 p.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_finset_sum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                g r s i α p n
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p))))))
  refine (hpart.add hcomp).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    covLowerOrderRotationValueCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
      hy)

/-- Chart-locality-free twin of `covLowerOrderRotationValueCoeffLimit_memLp`. -/
theorem covLowerOrderRotationValueCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationValueCoeffLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)
              (partialLpLimit (I := I) (M := M) g r s i α P k)))))
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_finset_sum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p)
                (componentLpLimit (I := I) (M := M)
                  g r s i α p))))))

/-- **The `n → ∞` `L²`-limit of the lower-order rotation value coefficient
(chart-locality-free).** Chart-locality-free twin of
`covLowerOrderRotationValueCoeff_tendsto`. -/
theorem covLowerOrderRotationValueCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _)
      atTop
      (𝓝 ((covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _)) := by
  classical
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k l n y =>
      valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y)
    (flim := fun P Q k l y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
        (partialLpLimit (I := I) (M := M) g r s i α P k :
          EuclN → ℝ) y)
    (fun P Q k l n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s i α P k n
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
    (fun P Q k l => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (partialLpLimit (I := I) (M := M) g r s i α P k))
    (fun P Q k l => tendsto_partialSummand (I := I) (M := M)
      g r s i α P k
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s i α P k n
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
        (partialLpLimit (I := I) (M := M) g r s i α P k)))
  have h_comp := tendsto_sum5 (I := I) (M := M) α
    (f := fun P Q k l p n y =>
      valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k l p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
    (fun P Q k l p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s i α p n
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p))
    (fun P Q k l p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (componentLpLimit (I := I) (M := M) g r s i α p))
    (fun P Q k l p => tendsto_componentSummand (I := I) (M := M)
      g r s i α p
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s i α p n
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ P Q k l p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
        (componentLpLimit (I := I) (M := M) g r s i α p)))
  have h_add := h_part.add h_comp
  have h_termN : ∀ n : ℕ,
      (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom
                    (I := I) (M := M) g r s i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      covLowerOrderRotationValueCoeff_pouSmul_eqOn_section (I := I) (M := M)
        g r s α P₀
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
        hy)
  have h_termLim :
      (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s i α P₀).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)
                  (partialLpLimit (I := I) (M := M)
                    g r s i α P k)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p)
                    (componentLpLimit (I := I) (M := M)
                      g r s i α p))))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covLowerOrderRotationValueCoeffLimit]
  rw [show (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom
                  (I := I) (M := M) g r s i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom
                    (I := I) (M := M) g r s i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
