import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.ChartPartialUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelBound
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivChartFormLowerOrder
import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothFChartResidual.BilinearBound

/-!
# A uniform `L²` bound for the chosen weak chart-partials of the cutoff chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)` and a chart center
`α : M`, the cutoff-weighted Euclidean chart component
`cutoffComponentEuclid g r s S α Idx Jdx` is the chart push-forward of the
manifold scalar field `chartKernelCutoff α · tensorChartComponentRaw …`. The
cutoff `chartKernelCutoff α` is a fixed smooth `[0, 1]`-valued bump compactly
supported inside the chart-`α` source. The cutoff chart component is therefore
globally `C^∞` on the Euclidean model space with compact support inside the
Euclidean chart target, so each of its chosen weak chart-partials is
`L²`-finite.

This file assembles the headline uniform-in-`S` `L²` bound on those chosen weak
chart-partials, summed over the chart-coordinate directions. It is the
cutoff-weight analogue of
`exists_const_sum_eLpNorm_chosenWeakPartial'_tensorChartComponent_le_uniform`
(the partition-of-unity-weighted version of `ChartPartialUniformBound.lean`),
obtained by the same Leibniz factorisation: the classical `k`-th partial of the
cutoff component splits, on the chart target, into the cutoff-weighted
covariant component, the cutoff-weighted lower-order term, and the Leibniz
cross-term carrying the derivative of the pushed cutoff. The three contributions
are bounded by, respectively, the generic chart-supported-weight covariant
`L²` bound `exists_eLpNorm_chartWeight_mul_sqrt_sum_…`, the Christoffel-uniform
lower-order argument over the (compact) cutoff support, and the reverse
chart-push `L²` bridge applied to the cutoff scalar component.

## Main result

* `exists_const_sum_eLpNorm_chosenWeakPartial'_cutoffComponentEuclid_le_uniform`
  — the headline unconditional uniform `L²` bound for the cutoff chart
  component.
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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

/-- For three almost-everywhere strongly measurable functions, the `L²`
seminorm of `a + b − c` is bounded by the sum of the three `L²` seminorms. -/
private lemma eLpNorm_add_add_sub_le
    {β : Type*} [MeasurableSpace β] {ν : Measure β} {a b c : β → ℝ}
    (ha : AEStronglyMeasurable a ν) (hb : AEStronglyMeasurable b ν)
    (hc : AEStronglyMeasurable c ν) :
    eLpNorm (fun y => a y + b y - c y) 2 ν ≤
      eLpNorm a 2 ν + eLpNorm b 2 ν + eLpNorm c 2 ν := by
  have h_ab : eLpNorm (fun y => a y + b y) 2 ν ≤
      eLpNorm a 2 ν + eLpNorm b 2 ν :=
    eLpNorm_add_le ha hb (by norm_num)
  have h_full : eLpNorm (fun y => (a y + b y) - c y) 2 ν ≤
      eLpNorm (fun y => a y + b y) 2 ν + eLpNorm c 2 ν :=
    eLpNorm_sub_le (ha.add hb) hc (by norm_num)
  exact h_full.trans (by gcongr)

/-- A product of Kronecker deltas has absolute value at most `1`. -/
private lemma abs_prod_kronecker_le_one'
    {ι : Type*} (t : Finset ι) (f : ι → Prop) [DecidablePred f] :
    |∏ i ∈ t, (if f i then (1 : ℝ) else 0)| ≤ 1 := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, abs_mul]
      by_cases hf : f i
      · rw [if_pos hf, abs_one, one_mul]; exact ih
      · rw [if_neg hf, abs_zero, zero_mul]; exact zero_le_one

/-- A Kronecker delta has absolute value at most `1`. -/
private lemma abs_kronecker_le_one' {P : Prop} [Decidable P] :
    |if P then (1 : ℝ) else 0| ≤ 1 := by
  by_cases h : P
  · rw [if_pos h, abs_one]
  · rw [if_neg h, abs_zero]; exact zero_le_one

/-- The absolute value of a finite sum of `coefficient · Kronecker-delta`
products, with each coefficient bounded by `Cχ` in absolute value, is at most
`card · Cχ`. -/
private lemma abs_sum_coeff_kronecker_le'
    {ι : Type*} (t : Finset ι) (f : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ) (hf : ∀ i ∈ t, |f i| ≤ Cχ) :
    |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)| ≤ t.card * Cχ := by
  classical
  have hbound : ∀ i ∈ t,
      |f i * (if P i then (1 : ℝ) else 0)| ≤ Cχ := by
    intro i hi
    rw [abs_mul]
    calc |f i| * |if P i then (1 : ℝ) else 0|
        ≤ Cχ * 1 :=
          mul_le_mul (hf i hi) abs_kronecker_le_one' (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  calc |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)|
      ≤ ∑ i ∈ t, |f i * (if P i then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ t, Cχ := Finset.sum_le_sum hbound
    _ = t.card * Cχ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The closed support of the chart-kernel cutoff at `α`. -/
private def cutoffKernelM (α : M) : Set M :=
  tsupport (fun x : M => ((chartKernelCutoff (I := I) (M := M) α
    : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

private lemma cutoffKernelM_isCompact (α : M) :
    IsCompact (cutoffKernelM (I := I) (M := M) α) :=
  chartKernelCutoff_hasCompactSupport (I := I) (M := M) α

private lemma cutoffKernelM_isClosed (α : M) :
    IsClosed (cutoffKernelM (I := I) (M := M) α) :=
  isClosed_tsupport _

private lemma cutoffKernelM_subset_chart_source (α : M) :
    cutoffKernelM (I := I) (M := M) α ⊆ (chartAt H α).source := by
  refine Subset.trans ?_ (chartKernelCutoff_tsupport_subset_source
    (I := I) (M := M) α)
  exact subset_rfl

/-- The cutoff kernel is contained in the tangent-bundle trivialisation base
set at `α`. -/
private lemma cutoffKernelM_subset_baseSet (α : M) :
    cutoffKernelM (I := I) (M := M) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
  exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx

/-- The chart-kernel cutoff at `α` is `C^∞` as a function on `M`. -/
private lemma chartKernelCutoff_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
  (chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯).contMDiff

/-- The pushed chart-kernel cutoff `chartPushedRaw I α (⇑(chartKernelCutoff I M
α))` is `C^∞` on all of the Euclidean model space. -/
private lemma chartPushedRaw_cutoff_contDiff (α : M) :
    ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) :=
  DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M)
    (chartKernelCutoff_contMDiff (I := I) (M := M) α)
    (cutoffKernelM_subset_chart_source (I := I) (M := M) α)

/-- The `k`-th Euclidean partial derivative of a globally `C^∞` function is
again `C^∞`. -/
private lemma euclidPartial_contDiff_of_contDiff'
    {u : EuclN → ℝ} (hu : ContDiff ℝ ∞ u) (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k u) := by
  have hfd : ContDiff ℝ ∞ (fun z => fderiv ℝ u z) :=
    hu.fderiv_right (m := (∞ : WithTop ℕ∞))
      (by rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl])
  have hcomp : euclidPartial (E := E) k u =
      (fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) ∘
        (fun z => fderiv ℝ u z) := by
    funext z; rw [euclidPartial_def]; rfl
  rw [hcomp]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single k 1)).contDiff.comp hfd

/-- The cutoff Euclidean chart component is globally `C^∞` on the Euclidean
model space. -/
private lemma cutoffComponentEuclid_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M)
    (cutoffComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

/-- The cutoff Euclidean chart component has compact support. -/
private lemma cutoffComponentEuclid_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

/-- The topological support of the cutoff Euclidean chart component is contained
in the Euclidean chart target. -/
private lemma cutoffComponentEuclid_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

/-- **Step 1.** For a smooth compactly-supported tensor section `S`, the chosen
weak `k`-th partial of the cutoff Euclidean chart component agrees almost
everywhere, on the Euclidean volume restricted to the chart target, with the
classical Euclidean partial derivative `euclidPartial k`. -/
private lemma chosenWeakPartial'_cutoffComponentEuclid_ae_eq_euclidPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    cutoffComponentEuclid_contDiff (I := I) (M := M) g r s S α Idx Jdx
  have hu_cpt : HasCompactSupport u :=
    cutoffComponentEuclid_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    cutoffComponentEuclid_tsupport_subset (I := I) (M := M) g r s S α Idx Jdx
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2 u (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩ_open hu_smooth hu_cpt hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial_smooth_ae_eq
      (d := Module.finrank ℝ E) hp_one hΩ_open hu_smooth hu_W1p k
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [euclidPartial_def]

/-- On the chart target the cutoff chart component is the pushed chart-kernel
cutoff times the pushed raw chart component. -/
private lemma cutoffComponentEuclid_eq_cutoff_mul_rawPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y =
      chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
        chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
  rfl

/-- **Leibniz factorisation of the cutoff-component partial.** For a chart-target
point `y`, the classical `k`-th Euclidean partial of the cutoff chart component
is the pushed chart-kernel cutoff times the `k`-th partial of the pushed raw
component, plus the `k`-th partial of the pushed cutoff times the pushed raw
component. -/
private lemma euclidPartial_cutoffComponentEuclid_eq_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) y =
      chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
          euclidPartial (E := E) k
            (chartPushedRaw (I := I) (M := M) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + euclidPartial (E := E) k
            (chartPushedRaw (I := I) (M := M) α
              (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y *
          chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  set χ : EuclN → ℝ :=
    chartPushedRaw (I := I) (M := M) α
      (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) with hχ_def
  set w : EuclN → ℝ :=
    chartPushedRaw (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) with hw_def
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_nhds : chartTargetEuclid (I := I) (M := M) α ∈ 𝓝 y :=
    hΩ_open.mem_nhds hy
  have h_eqf : cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx
      =ᶠ[𝓝 y] (fun z : EuclN => χ z * w z) := by
    filter_upwards [hΩ_nhds] with z hz
    rw [hχ_def, hw_def]
    exact cutoffComponentEuclid_eq_cutoff_mul_rawPushed
      (I := I) (M := M) g r s S α Idx Jdx hz
  have hχ_diff : DifferentiableAt ℝ χ y :=
    ((chartPushedRaw_cutoff_contDiff (I := I) (M := M) α).differentiable
      (by simp)).differentiableAt
  have hw_diffOn : DifferentiableOn ℝ w
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartPushedRaw_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s S α Idx Jdx).differentiableOn (by simp)
  have hw_diff : DifferentiableAt ℝ w y :=
    (hw_diffOn y hy).differentiableAt hΩ_nhds
  have h_fderiv :
      fderiv ℝ (cutoffComponentEuclid (I := I) (M := M)
          g r s S α Idx Jdx) y =
        χ y • fderiv ℝ w y + w y • fderiv ℝ χ y := by
    rw [h_eqf.fderiv_eq]
    exact fderiv_mul hχ_diff hw_diff
  rw [euclidPartial_def, h_fderiv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    euclidPartial_def, euclidPartial_def]
  ring

/-- **The covariant-component substitution.** For a chart-target point `y`, the
`k`-th Euclidean partial of the pushed raw chart component equals the chart
covariant-derivative component minus the lower-order correction term. -/
private lemma euclidPartial_rawPushed_eq_covDerivComponent_sub'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y =
      tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
              (chartBasisVecFiber (I := I) α k)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
        - covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y := by
  have h := covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s S α k Idx Jdx hy
  linarith [h]

/-- The Leibniz cross-term: the `k`-th partial of the pushed chart-kernel cutoff
times the pushed raw chart component. -/
private def cutoffLeibnizCrossTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y *
      chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y

/-- The cutoff-weighted chart covariant-derivative component. -/
private def cutoffCovDerivComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α k)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))

/-- The cutoff-weighted lower-order correction term. -/
private def cutoffLowerOrderTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
      covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y

/-- **The three-term identity.** For a chart-target point `y`, the classical
`k`-th Euclidean partial of the cutoff chart component is the cutoff-weighted
covariant component, plus the Leibniz cross-term, minus the cutoff-weighted
lower-order term. -/
private lemma euclidPartial_cutoffComponentEuclid_eq_three_terms
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) y =
      cutoffCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx y
        + cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y
        - cutoffLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y := by
  classical
  rw [euclidPartial_cutoffComponentEuclid_eq_leibniz
    (I := I) (M := M) g r s S α k Idx Jdx hy,
    euclidPartial_rawPushed_eq_covDerivComponent_sub'
      (I := I) (M := M) g r s S α k Idx Jdx hy]
  unfold cutoffCovDerivComponent cutoffLeibnizCrossTerm cutoffLowerOrderTerm
  ring

private lemma chartPushedRaw_cutoff_continuousOn (α : M) :
    ContinuousOn
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedRaw_cutoff_contDiff (I := I) (M := M) α).continuous.continuousOn

private lemma euclidPartial_chartPushedRaw_cutoff_continuousOn
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (euclidPartial_contDiff_of_contDiff' (E := E)
    (chartPushedRaw_cutoff_contDiff (I := I) (M := M) α) k).continuous.continuousOn

private lemma chartPushedRaw_rawComponent_continuousOn'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (I := I) (M := M) g r s S α Idx Jdx).continuousOn

private lemma euclidPartial_chartPushedRaw_rawComponent_continuousOn'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (euclidPartial_chartPushedRaw_contDiffOn
    (I := I) (M := M) g r s S α k Idx Jdx).continuousOn

private lemma cutoffCovDerivComponent_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (cutoffCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set galt : EuclN → ℝ := fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
      (euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y)
    with hgalt_def
  have hgalt_cont : ContinuousOn galt
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartPushedRaw_cutoff_continuousOn (I := I) (M := M) α).mul
      ((euclidPartial_chartPushedRaw_rawComponent_continuousOn'
        (I := I) (M := M) g r s S α k Idx Jdx).add
      (covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α
        k Idx Jdx
        (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
          (I := I) (M := M) g r s S α Idx' Jdx')).continuousOn)
  refine hgalt_cont.congr (fun y hy => ?_)
  have h := euclidPartial_rawPushed_eq_covDerivComponent_sub'
    (I := I) (M := M) g r s S α k Idx Jdx hy
  unfold cutoffCovDerivComponent
  rw [hgalt_def, show
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α k)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y
      from by linarith [h]]

private lemma cutoffLowerOrderTerm_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (cutoffLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold cutoffLowerOrderTerm
  exact (chartPushedRaw_cutoff_continuousOn (I := I) (M := M) α).mul
    (covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α
      k Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S α Idx' Jdx')).continuousOn

private lemma cutoffLeibnizCrossTerm_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold cutoffLeibnizCrossTerm
  exact (euclidPartial_chartPushedRaw_cutoff_continuousOn
      (I := I) (M := M) α k).mul
    (chartPushedRaw_rawComponent_continuousOn' (I := I) (M := M)
      g r s S α Idx Jdx)

/-- The `k`-th partial of the pushed chart-kernel cutoff has topological support
inside the chart image of the closed support of the chart-kernel cutoff. -/
private lemma euclidPartial_chartPushedRaw_cutoff_tsupport_subset
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    tsupport
        (euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) := by
  classical
  have h1 : tsupport
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))) ⊆
      tsupport (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) := by
    have h := tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))
      (EuclideanSpace.single k (1 : ℝ))
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport _)) h
    intro y hy
    refine subset_tsupport _ ?_
    simpa [euclidPartial_def] using hy
  have h2 : tsupport (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) := by
    have hK_compact : IsCompact ((extChartAt I α) ''
        (cutoffKernelM (I := I) (M := M) α)) :=
      (cutoffKernelM_isCompact (I := I) (M := M) α).image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx
          rw [extChartAt_source]
          exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx))
    have hKE_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α))) :=
      hK_compact.image (toEuclidean (E := E)).continuous
    refine closure_minimal ?_ hKE_compact.isClosed
    intro y hy
    rw [Function.mem_support] at hy
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      by_contra hy_off
      exact hy (chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy_off)
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_src : b ∈ (chartAt H α).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy_target
    have hb_cut : b ∈ cutoffKernelM (I := I) (M := M) α := by
      refine subset_tsupport _ ?_
      rw [Function.mem_support]
      intro hb_zero
      apply hy
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy_target]
      exact hb_zero
    have hb_ext : b ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hb_src
    have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have h_extChartAt_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
      rw [hb_def]
      exact (extChartAt I α).right_inv hy_symm
    refine ⟨extChartAt I α b, ⟨b, hb_cut, rfl⟩, ?_⟩
    rw [h_extChartAt_b]
    exact (toEuclidean (E := E)).apply_symm_apply y
  exact h1.trans h2

/-- The Leibniz cross-term vanishes off the chart image of the closed support of
the chart-kernel cutoff. -/
private lemma cutoffLeibnizCrossTerm_eq_zero_off_cutoff_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∉ (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α))) :
    cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y = 0 := by
  classical
  unfold cutoffLeibnizCrossTerm
  have hχ_zero : euclidPartial (E := E) k
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y = 0 := by
    by_contra hne
    exact hy (euclidPartial_chartPushedRaw_cutoff_tsupport_subset
      (I := I) (M := M) α k (subset_tsupport _ (Function.mem_support.mpr hne)))
  rw [hχ_zero, zero_mul]

/-- The manifold-side raw-component cutoff: the raw chart component on the
closed support of the chart-kernel cutoff at `α`, zero elsewhere. -/
private def rawComponentCutoffM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : M → ℝ :=
  (cutoffKernelM (I := I) (M := M) α).indicator
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)

/-- The raw-component cutoff has topological support inside the closed support
of the chart-kernel cutoff at `α`. -/
private lemma rawComponentCutoffM_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) ⊆
      cutoffKernelM (I := I) (M := M) α := by
  classical
  refine closure_minimal ?_ (cutoffKernelM_isClosed (I := I) (M := M) α)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_off
  exact hx (by rw [rawComponentCutoffM, Set.indicator_of_notMem hx_off])

/-- The raw-component cutoff is Borel measurable. -/
private lemma rawComponentCutoffM_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  unfold rawComponentCutoffM
  rw [show (cutoffKernelM (I := I) (M := M) α).indicator
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) =
      (cutoffKernelM (I := I) (M := M) α).piecewise
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (fun _ : M => (0 : ℝ)) from by
    funext x
    by_cases hx : x ∈ cutoffKernelM (I := I) (M := M) α
    · simp [Set.indicator_of_mem hx, Set.piecewise_eq_of_mem _ _ _ hx]
    · simp [Set.indicator_of_notMem hx, Set.piecewise_eq_of_notMem _ _ _ hx]]
  have hraw_cont : ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (cutoffKernelM (I := I) (M := M) α) :=
    ((tensorChartComponentRaw_contMDiffOn_chart_source
        (I := I) (M := M) g r s S α Idx Jdx).continuousOn).mono
      (cutoffKernelM_subset_chart_source (I := I) (M := M) α)
  exact ContinuousOn.measurable_piecewise hraw_cont
    (continuousOn_const) (cutoffKernelM_isClosed (I := I) (M := M) α).measurableSet

/-- **Uniform pointwise quadratic bound for the raw-component cutoff.** There is
a single non-negative constant `C` such that for every section, every component
multi-index pair, and every base point, the square of the raw-component cutoff
is bounded by `C` times the pointwise tensor inner product. -/
private lemma exists_const_rawComponentCutoffM_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    sq_norm_le_const_mul_chartTensorInner_on_compact
      (I := I) (M := M) (E := E) g r s α
      (cutoffKernelM_isCompact (I := I) (M := M) α)
      (cutoffKernelM_subset_baseSet (I := I) (M := M) α)
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  by_cases hb : b ∈ cutoffKernelM (I := I) (M := M) α
  · have hcut_eq : rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx b =
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
      rw [rawComponentCutoffM, Set.indicator_of_mem hb]
    rw [hcut_eq, tensorChartComponentRaw_def]
    set T : TensorRSModel r s ℝ E :=
      tensorTrivProj (I := I) (M := M) g r s S α b with hT_def
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      cutoffKernelM_subset_baseSet (I := I) (M := M) α hb
    have h_proj_le :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx T‖ ≤
          C_proj * ‖T‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
          (norm_nonneg _))
    have h_proj_sq_le :
        (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2 ≤
          C_proj ^ 2 * ‖T‖ ^ 2 := by
      have h_abs : (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2 =
          ‖tensorChartComponentProjection (E := E) r s Idx Jdx T‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [h_abs]
      have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
      nlinarith [hsq, norm_nonneg (tensorChartComponentProjection (E := E)
        r s Idx Jdx T), norm_nonneg T, hC_proj_nn]
    have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      have h := h_norm b hb T
      rwa [hT_def, chartTensorInner_tensorTrivProj_eq_tensorInner
        (I := I) (M := M) g r s α S hb_base] at h
    calc (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2
        ≤ C_proj ^ 2 * ‖T‖ ^ 2 := h_proj_sq_le
      _ ≤ C_proj ^ 2 *
          (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
        mul_le_mul_of_nonneg_left h_triv_sq_le (sq_nonneg _)
      _ = C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  · have hcut_zero : rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx b
        = 0 := by
      rw [rawComponentCutoffM, Set.indicator_of_notMem hb]
    rw [hcut_zero]
    have h_rhs_nn : 0 ≤ C_proj ^ 2 * K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hK_nn) hQ_nn
    simpa using h_rhs_nn

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq'
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma le_sqrt_of_sq_le' {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt' {a : ℝ} (ha : 0 ≤ a) :
    (ENNReal.ofReal a) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt a) := by
  rw [show a = Real.sqrt a * Real.sqrt a from (Real.mul_self_sqrt ha).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt a)) * (ENNReal.ofReal (Real.sqrt a)) =
      (ENNReal.ofReal (Real.sqrt a)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- **Uniform `L²` bound for the raw-component cutoff.** There is a single
non-negative constant `C` such that for every smooth compactly-supported tensor
section and every component multi-index pair, the `L²` norm of the
raw-component cutoff against the Riemannian volume measure is bounded by `C`
times the `L²` norm of the section. -/
private lemma exists_const_eLpNorm_rawComponentCutoffM_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    exists_const_rawComponentCutoffM_sq_le (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx
    with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
          g r s b (S.toFun b) (S.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
  have h_inner_int := SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M) (g := g) (r := r) (s := s) S S
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_sq :
      (eLpNorm f 2 μ) ^ 2 ≤
        ENNReal.ofReal (C *
          tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq' μ f]
    have h_lint_le :
        ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
          ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
            (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards with b using h_pt_enn b
    have h_lint_eq :
        ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ =
          ENNReal.ofReal (∫ b, C * tensorInnerPointwise
            (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) ∂μ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        h_C_smul_int h_C_smul_nn).symm
    have h_int_const_mul :
        ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) ∂μ =
          C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
      unfold tensorL2Inner
      rw [integral_const_mul]
    rw [h_lint_eq, h_int_const_mul] at h_lint_le
    exact h_lint_le
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    refine integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  set Stotal : ℝ := C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun
    with hStotal_def
  have hStotal_nn : 0 ≤ Stotal := mul_nonneg hC_nn h_inner_nn
  have h_eLp_le : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt Stotal) := by
    have h_pow := le_sqrt_of_sq_le' h_sq
    rw [sqrt_ofReal_eq_ofReal_sqrt' hStotal_nn] at h_pow
    exact h_pow
  have h_sqrt_factor : Real.sqrt Stotal = Real.sqrt C * ‖S‖ := by
    rw [hStotal_def, h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self
        (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun),
      SmoothCcTensor.norm_def (I := I) (M := M)]
  rw [h_sqrt_factor, ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLp_le
  exact h_eLp_le

/-- A uniform supremum bound for the `k`-th partial of the pushed chart-kernel
cutoff: a single non-negative constant bounding the absolute value
everywhere. -/
private lemma exists_const_euclidPartial_chartPushedRaw_cutoff_le
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧
      ∀ y : EuclN,
        ‖euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y‖
            ≤ Cχ := by
  classical
  set χ : EuclN → ℝ :=
    euclidPartial (E := E) k
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) with hχ_def
  have hχ_cont : Continuous χ := by
    rw [hχ_def]
    exact (euclidPartial_contDiff_of_contDiff' (E := E)
      (chartPushedRaw_cutoff_contDiff (I := I) (M := M) α) k).continuous
  have hχ_cpt : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α))) ?_ ?_
    · exact ((cutoffKernelM_isCompact (I := I) (M := M) α).image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx
          rw [extChartAt_source]
          exact cutoffKernelM_subset_chart_source (I := I) (M := M)
            α hx))).image (toEuclidean (E := E)).continuous
    · refine subset_trans ?_
        (euclidPartial_chartPushedRaw_cutoff_tsupport_subset
          (I := I) (M := M) α k)
      exact subset_tsupport _
  by_cases hK_ne : (tsupport χ).Nonempty
  · obtain ⟨x₀, _, hx₀_max⟩ :=
      hχ_cpt.exists_isMaxOn hK_ne (hχ_cont.norm.continuousOn)
    refine ⟨max ‖χ x₀‖ 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : y ∈ tsupport χ
    · exact (hx₀_max hy).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact le_max_right _ _
  · refine ⟨0, le_refl 0, fun y => ?_⟩
    have hy : y ∉ tsupport χ := fun hy => hK_ne ⟨y, hy⟩
    rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]

/-- **The pointwise cross-term bound.** For every `y`, the absolute value of the
Leibniz cross-term is bounded by `Cχ` times the chart push-forward of the
raw-component cutoff. -/
private lemma cutoffLeibnizCrossTerm_le_const_mul_chartPushedRaw_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ)
    (hCχ : ∀ y : EuclN,
      ‖euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y‖ ≤ Cχ)
    (y : EuclN) :
    ‖cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y‖ ≤
      Cχ * ‖chartPushedRaw (I := I) (M := M) α
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) y‖ := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    by_cases hb : b ∈ cutoffKernelM (I := I) (M := M) α
    · have h_cut_eval : chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) y =
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) hy,
          rawComponentCutoffM, Set.indicator_of_mem hb]
      have h_raw_eval : chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y =
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
      unfold cutoffLeibnizCrossTerm
      rw [h_cut_eval, h_raw_eval, norm_mul]
      exact mul_le_mul_of_nonneg_right (hCχ y) (norm_nonneg _)
    · have h_cross_zero : cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α
          k Idx Jdx y = 0 := by
        refine cutoffLeibnizCrossTerm_eq_zero_off_cutoff_kernel
          (I := I) (M := M) g r s S α k Idx Jdx ?_
        rintro ⟨z, ⟨b', hb'_cut, hb'_eq⟩, hz_eq⟩
        apply hb
        have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
          rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
          exact hy
        have hb'_src : b' ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hb'_cut
        have h_symm_y : (toEuclidean (E := E)).symm y = z := by
          rw [← hz_eq]
          exact (toEuclidean (E := E)).symm_apply_apply z
        have hb_eq_b' : b = b' := by
          rw [hb_def, h_symm_y, ← hb'_eq, (extChartAt I α).left_inv hb'_src]
        rw [hb_eq_b']
        exact hb'_cut
      rw [h_cross_zero, norm_zero]
      exact mul_nonneg hCχ_nn (norm_nonneg _)
  · have h_cross_zero : cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α
        k Idx Jdx y = 0 := by
      unfold cutoffLeibnizCrossTerm
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy,
        mul_zero]
    have h_cut_zero : chartPushedRaw (I := I) (M := M) α
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) hy
    rw [h_cross_zero, norm_zero, h_cut_zero, norm_zero, mul_zero]

/-- **A uniform `L²` bound for the Leibniz cross-term.** For a closed Riemannian
manifold `(M, g)`, ranks `(r, s)`, a chart center `α : M`, and a chart-
coordinate direction `k`, there is a single non-negative real constant `C` —
depending only on `(g, r, s, α, k)` — such that for every smooth
compactly-supported `H¹` tensor section `S`, the `L²` norm of the Leibniz
cross-term against the Euclidean volume restricted to the chart target is
bounded by `ENNReal.ofReal C` times the `H¹` norm of `S`. -/
private theorem exists_const_eLpNorm_cutoffLeibnizCrossTerm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      eLpNorm
          (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
            k Idx Jdx) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨Cχ, hCχ_nn, hCχ⟩ :=
    exists_const_euclidPartial_chartPushedRaw_cutoff_le (I := I) (M := M) α k
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  obtain ⟨C_bridge, hC_bridge_pos, hC_bridge⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α (cutoffKernelM_isCompact (I := I) (M := M) α)
      (cutoffKernelM_subset_chart_source (I := I) (M := M) α) hp_one hp_top
  obtain ⟨C_cut, hC_cut_nn, hC_cut⟩ :=
    exists_const_eLpNorm_rawComponentCutoffM_le (I := I) (M := M) g r s α
  refine ⟨Cχ * (C_bridge * C_cut),
    mul_nonneg hCχ_nn (mul_nonneg hC_bridge_pos.le hC_cut_nn), ?_⟩
  intro S Idx Jdx
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  set normCut : EuclN → ℝ := fun y : EuclN =>
    ‖chartPushedRaw (I := I) (M := M) α
      (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) y‖
    with hnormCut_def
  have h_ptwise : ∀ y : EuclN,
      ‖cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx y‖ ≤
        (Cχ • normCut) y := by
    intro y
    rw [Pi.smul_apply, smul_eq_mul, hnormCut_def]
    exact cutoffLeibnizCrossTerm_le_const_mul_chartPushedRaw_cutoff
      (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx hCχ_nn hCχ y
  have h_mono :
      eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        eLpNorm (Cχ • normCut) 2 μ :=
    eLpNorm_mono_real h_ptwise
  have h_smul :
      eLpNorm (Cχ • normCut) 2 μ =
        ‖Cχ‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := by
    rw [eLpNorm_const_smul Cχ normCut 2 μ, hnormCut_def, eLpNorm_norm]
  have hCχ_enorm : ‖Cχ‖ₑ = ENNReal.ofReal Cχ := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hCχ_nn]
  have h_bridge :
      eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ ≤
        ENNReal.ofReal C_bridge *
          eLpNorm (rawComponentCutoffM (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx)
            2 (riemannianMeasure (I := I) g (chartAtlasPOU I M)) :=
    hC_bridge
      (rawComponentCutoffM_measurable (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx)
      (rawComponentCutoffM_tsupport_subset (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx)
  have h_meas_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure (I := I) (M := M) g := rfl
  rw [h_meas_eq] at h_bridge
  have h_cut_h1 :
      eLpNorm (rawComponentCutoffM (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_cut * (‖S‖₊ : ℝ≥0∞) := by
    have hb := hC_cut S.toCcTensor Idx Jdx
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (zero_le _))
    rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from by
      rw [show ((‖S‖₊ : ℝ≥0∞)) = ‖S‖ₑ from (enorm_eq_nnnorm S).symm,
        ← ofReal_norm_eq_enorm S]]
    exact ENNReal.ofReal_le_ofReal
      (SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S)
  calc eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ
      ≤ eLpNorm (Cχ • normCut) 2 μ := h_mono
    _ = ‖Cχ‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := h_smul
    _ = ENNReal.ofReal Cχ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := by rw [hCχ_enorm]
    _ ≤ ENNReal.ofReal Cχ *
          (ENNReal.ofReal C_bridge *
            eLpNorm (rawComponentCutoffM (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) 2
              (riemannianVolumeMeasure (I := I) (M := M) g)) :=
        mul_le_mul_of_nonneg_left h_bridge (by positivity)
    _ ≤ ENNReal.ofReal Cχ *
          (ENNReal.ofReal C_bridge *
            (ENNReal.ofReal C_cut * (‖S‖₊ : ℝ≥0∞))) := by gcongr
    _ = ENNReal.ofReal (Cχ * (C_bridge * C_cut)) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hCχ_nn, ENNReal.ofReal_mul hC_bridge_pos.le]
        ring

/-- The manifold-side weighted norm-sum function for the cutoff weight: the
chart-kernel cutoff at `α` times the square root of the sum, over chart
directions, of the squared inverse-twist norm of the abstract covariant
derivative of `S`. -/
private noncomputable def cutoffCovNormSumFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) : M → ℝ :=
  fun b : M =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)

/-- The base set of the `(r, s)`-tensor trivialisation at `α` equals the
chart-`α` source. -/
private lemma tensorRS_baseSet_eq_chart_source' (α : M) (r s : ℕ) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

/-- `C^∞` smoothness of the inverse-twisted covariant derivative on the chart
source. -/
private lemma chartRSTwistInv_tensorCovDeriv_contMDiffOn'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))))
      ((chartAt H α).source) := by
  classical
  have htriv := tensorCovDeriv_chartBasis_trivImage_contMDiffOn
    (I := I) (M := M) g r s S α i
  rw [show (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source from rfl] at htriv
  refine htriv.congr (fun b hb => ?_)
  rw [← triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (chartBasisVecFiber (I := I) α i b))]
  have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRS_baseSet_eq_chart_source' (I := I) (M := M) α r s]
    exact hb
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hb_base]

/-- The squared inverse-twist norm sum is `ContinuousOn` the chart-`α`
source. -/
private lemma cutoffCovNormSqSum_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (fun b : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)
      ((chartAt H α).source) := by
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  have hcov : ContinuousOn
      (fun b : M =>
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))))
      ((chartAt H α).source) :=
    (chartRSTwistInv_tensorCovDeriv_contMDiffOn' (I := I) (M := M)
      g r s S α i).continuousOn
  exact (hcov.norm).pow 2

/-- **Global continuity of the manifold-side cutoff weighted norm-sum
function.** -/
private lemma cutoffCovNormSumFun_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Continuous (cutoffCovNormSumFun (I := I) (M := M) g r s S α) := by
  classical
  set χ : C^∞⟮I, M; ℝ⟯ := chartKernelCutoff (I := I) (M := M) α with hχ_def
  set w : M → ℝ := fun b : M =>
    Real.sqrt
      (∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b
                (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) with hw_def
  have hfun_eq : cutoffCovNormSumFun (I := I) (M := M) g r s S α =
      fun b : M => ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b • w b := by
    funext b
    rw [cutoffCovNormSumFun]
    rfl
  rw [hfun_eq]
  refine continuous_of_tsupport (fun x hx => ?_)
  have hx_supp : x ∈ tsupport ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    tsupport_smul_subset_left
      (f := fun b : M => ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) (g := w) hx
  have hx_src : x ∈ (chartAt H α).source :=
    chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx_supp
  have hχ_contAt : ContinuousAt ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (χ.contMDiff.continuous).continuousAt
  have hw_contOn : ContinuousOn w ((chartAt H α).source) := by
    rw [hw_def]
    exact (cutoffCovNormSqSum_continuousOn_chart_source (I := I) (M := M)
      g r s S α).sqrt
  have hw_contAt : ContinuousAt w x :=
    hw_contOn.continuousAt ((chartAt H α).open_source.mem_nhds hx_src)
  exact hχ_contAt.smul hw_contAt

/-- The manifold-side cutoff weighted norm-sum function is measurable. -/
private lemma cutoffCovNormSumFun_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Measurable (cutoffCovNormSumFun (I := I) (M := M) g r s S α) :=
  (cutoffCovNormSumFun_continuous (I := I) (M := M) g r s S α).measurable

/-- The topological support of the cutoff weighted norm-sum function is
contained in the topological support of the chart-kernel cutoff at `α`. -/
private lemma cutoffCovNormSumFun_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tsupport (cutoffCovNormSumFun (I := I) (M := M) g r s S α) ⊆
      cutoffKernelM (I := I) (M := M) α := by
  classical
  have hfun_eq : cutoffCovNormSumFun (I := I) (M := M) g r s S α =
      fun b : M =>
        ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b •
          Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
    funext b
    rw [cutoffCovNormSumFun]
    rfl
  rw [hfun_eq]
  exact tsupport_smul_subset_left
    (f := fun b : M => ((chartKernelCutoff (I := I) (M := M) α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
    (g := fun b : M =>
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2))

/-- For `y` in the Euclidean chart target, the chart base point lies in the
chart-`α` Levi-Civita good set. -/
private lemma chartBasePoint_mem_goodSet'
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      chartLeviCivitaGoodSet (I := I) α := by
  have hsrc : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) α,
    extChartAt_source]
  exact hsrc

/-- **The pointwise bound on the chart target.** For every `y`, the absolute
value of the cutoff-weighted chart-frame component of the chart-coordinate
covariant derivative of `S` is bounded by `C_proj` times the chart push-forward
of the manifold-side cutoff weighted norm-sum function. -/
private lemma cutoffCovDerivComponent_le_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclN) :
    ‖cutoffCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx y‖ ≤
      (chartComponentProjectionUniformBound (E := E) r s •
        chartPushedRaw (I := I) (M := M) α
          (cutoffCovNormSumFun (I := I) (M := M) g r s S α)) y := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
      chartBasePoint_mem_goodSet' (I := I) (M := M) α hy
    have hb_src : b ∈ (chartAt H α).source := by
      have := symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
      rwa [← hb_def] at this
    have hχ_nn : 0 ≤ ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartKernelCutoff_mem_Icc (I := I) (M := M) α b).1
    have hcut_eval : chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy]
    have hcov_eval : chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y =
          cutoffCovNormSumFun (I := I) (M := M) g r s S α b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) hy]
    have hcomp_eq :
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
                (chartBasisVecFiber (I := I) α k) b)) =
          tensorChartComponentProjection (E := E) r s Idx Jdx
            (chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α k b)))) := by
      rw [← tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
        g r s S α k hb_good]
      rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
        r s α hb_src
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α k b))]
    set X : TensorRSModel r s ℝ E :=
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α k b))) with hX_def
    have h_proj_le :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ ≤
          C_proj * ‖X‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
          (norm_nonneg _))
    have h_norm_le_sqrt :
        ‖X‖ ≤
          Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
      have hsq_le :
          ‖X‖ ^ 2 ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun i : Fin (Module.finrank ℝ E) =>
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ k)
      have hX_eq : ‖X‖ = Real.sqrt (‖X‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      rw [hX_eq]
      exact Real.sqrt_le_sqrt hsq_le
    unfold cutoffCovDerivComponent
    rw [hcomp_eq, hcut_eval]
    have h_norm_prod :
        ‖((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            tensorChartComponentProjection (E := E) r s Idx Jdx X‖ =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ := by
      rw [norm_mul, Real.norm_of_nonneg hχ_nn]
    have hRHS_eq :
        (C_proj •
          chartPushedRaw (I := I) (M := M) α
            (cutoffCovNormSumFun (I := I) (M := M) g r s S α)) y =
          C_proj *
            (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
                : M → ℝ) b *
              Real.sqrt
                (∑ i : Fin (Module.finrank ℝ E),
                  ‖chartRSTwistInv (I := I) (M := M) α b r s
                      (TensorRSSpace.toModel
                        (tensorCovDerivAt (I := I) (M := M) g r s S b
                          (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)) := by
      change C_proj * chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y = _
      rw [hcov_eval]
      rfl
    rw [h_norm_prod, hRHS_eq]
    set w : ℝ :=
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) with hw_def
    have hw_nn : 0 ≤ w := Real.sqrt_nonneg _
    have h_proj_le_w :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ ≤
          C_proj * w :=
      h_proj_le.trans
        (mul_le_mul_of_nonneg_left h_norm_le_sqrt hC_proj_nn)
    calc ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖
        ≤ ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (C_proj * w) :=
          mul_le_mul_of_nonneg_left h_proj_le_w hχ_nn
      _ = C_proj *
            (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
                : M → ℝ) b * w) := by
          ring
  · have hcov_zero : chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) hy
    have hcomp_zero : cutoffCovDerivComponent (I := I) (M := M)
        g r s S α k Idx Jdx y = 0 := by
      unfold cutoffCovDerivComponent
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy,
        zero_mul]
    rw [hcomp_zero, norm_zero]
    change (0 : ℝ) ≤ C_proj * chartPushedRaw (I := I) (M := M) α
      (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y
    rw [hcov_zero, mul_zero]

/-- The per-direction Euclidean `L²` norm of the cutoff-weighted chart-frame
covariant-derivative component is bounded by a single non-negative constant
times the `H¹` seminorm of `S`. -/
private lemma exists_const_eLpNorm_cutoffCovDerivComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E))
      (m : Fin (Module.finrank ℝ E)),
      eLpNorm
        (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx)
        2 ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  set Kα : Set M := cutoffKernelM (I := I) (M := M) α with hKα_def
  have hKα_compact : IsCompact Kα := cutoffKernelM_isCompact (I := I) (M := M) α
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    cutoffKernelM_subset_chart_source (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C_bridge, hC_bridge_pos, hC_bridge⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  obtain ⟨C_cov, hC_cov_nn, hC_cov⟩ :=
    exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
      (fun x : M => ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      (fun x => (chartKernelCutoff_mem_Icc (I := I) (M := M) α x).1)
      (fun x => (chartKernelCutoff_mem_Icc (I := I) (M := M) α x).2)
      hKα_compact
      (cutoffKernelM_subset_baseSet (I := I) (M := M) α)
      (subset_rfl)
  refine ⟨C_proj * (C_bridge * C_cov),
    mul_nonneg hC_proj_nn (mul_nonneg hC_bridge_pos.le hC_cov_nn), ?_⟩
  intro S Idx Jdx m
  set v : M → ℝ := cutoffCovNormSumFun (I := I) (M := M) g r s S.toCcTensor α
    with hv_def
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have h_ptwise : ∀ y : EuclN,
      ‖cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx y‖ ≤
        (C_proj • chartPushedRaw (I := I) (M := M) α v) y := by
    intro y
    rw [hv_def, hC_proj_def]
    exact cutoffCovDerivComponent_le_chartPushedRaw (I := I) (M := M)
      g r s S.toCcTensor α m Idx Jdx y
  have h_mono :
      eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx) 2 μ ≤
        eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    eLpNorm_mono_real h_ptwise
  have h_smul :
      eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ =
        ‖C_proj‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    eLpNorm_const_smul C_proj (chartPushedRaw (I := I) (M := M) α v) 2 μ
  have hC_proj_enorm : ‖C_proj‖ₑ = ENNReal.ofReal C_proj := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_proj_nn]
  have hv_meas : Measurable v :=
    cutoffCovNormSumFun_measurable (I := I) (M := M) g r s S.toCcTensor α
  have hv_supp : tsupport v ⊆ Kα :=
    cutoffCovNormSumFun_tsupport_subset (I := I) (M := M) g r s S.toCcTensor α
  have h_bridge :
      eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ ≤
        ENNReal.ofReal C_bridge *
          eLpNorm v 2
            (riemannianMeasure (I := I) g (chartAtlasPOU I M)) :=
    hC_bridge hv_meas hv_supp
  have h_meas_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure (I := I) (M := M) g := rfl
  rw [h_meas_eq] at h_bridge
  have hv_eq : v = fun b : M =>
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s
                    S.toCcTensor b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
    rw [hv_def]
    funext b
    rw [cutoffCovNormSumFun]
  have h_cov :
      eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞) := by
    rw [hv_eq]
    exact hC_cov S
  calc eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx) 2 μ
      ≤ eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ := h_mono
    _ = ‖C_proj‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
        h_smul
    _ = ENNReal.ofReal C_proj *
          eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ := by
        rw [hC_proj_enorm]
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
        exact mul_le_mul_of_nonneg_left h_bridge (by positivity)
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            (ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞))) := by
        gcongr
    _ = ENNReal.ofReal (C_proj * (C_bridge * C_cov)) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hC_proj_nn,
          ENNReal.ofReal_mul hC_bridge_pos.le]
        ring

/-- On the chart target, the pushed chart-kernel cutoff times the raw chart
component (read at the chart-Euclidean preimage) equals the cutoff Euclidean
chart component `cutoffComponentEuclid`. -/
private lemma chartPushedRaw_cutoff_mul_raw_eq_cutoffComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy,
    cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy]
  rfl

/-- On the chart target, the cutoff-weighted lower-order term equals the finite
linear combination, over component multi-index pairs, of `covDerivLowerOrderCoeff`
times the cutoff Euclidean chart component `cutoffComponentEuclid`. -/
private lemma cutoffLowerOrderTerm_eq_linearCombination
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    cutoffLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          cutoffComponentEuclid (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  unfold cutoffLowerOrderTerm
  rw [covDerivComponent_lowerOrder_eq_linearCombination
    (I := I) (M := M) g r s S α m Idx Jdx y, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← mul_assoc, mul_comm (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y)
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y),
    mul_assoc,
    chartPushedRaw_cutoff_mul_raw_eq_cutoffComponent (I := I) (M := M)
      g r s S α p.1 p.2 hy]

/-- The cutoff Euclidean chart component is continuous on the Euclidean model
space. -/
private lemma cutoffComponentEuclid_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) :=
  (cutoffComponentEuclid_contDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

/-- If the cutoff Euclidean chart component is nonzero at `y`, then `y` lies in
the chart target and its chart-Euclidean preimage lies in the closed support of
the chart-kernel cutoff at `α`. -/
private lemma mem_cutoffKernelM_image_of_cutoffComponentEuclid_ne_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hne : cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y ≠ 0) :
    y ∈ chartTargetEuclid (I := I) (M := M) α ∧
      y ∈ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) := by
  classical
  have hy : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    by_contra hy
    exact hne (cutoffComponentEuclid_apply_of_notMem
      (I := I) (M := M) g r s S α Idx Jdx hy)
  refine ⟨hy, ?_⟩
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hval : cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y =
      cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx b :=
    cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy
  rw [hval] at hne
  have hχ_ne : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
      : M → ℝ) b ≠ 0 := by
    intro hχ_zero
    apply hne
    unfold cutoffComponentScalar
    rw [hχ_zero, zero_mul]
  have hb_cut : b ∈ cutoffKernelM (I := I) (M := M) α :=
    subset_tsupport _ (Function.mem_support.mpr hχ_ne)
  have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hb_cut
  have h_extChartAt_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]
    exact (extChartAt I α).right_inv hy_symm
  refine ⟨extChartAt I α b, ⟨b, hb_cut, rfl⟩, ?_⟩
  rw [h_extChartAt_b]
  exact (toEuclidean (E := E)).apply_symm_apply y

/-- **Uniform sup bound for `covDerivLowerOrderCoeff` on the cutoff kernel.**
There is a single non-negative constant `C` bounding the lower-order Christoffel
coefficient in absolute value at every chart-Euclidean point whose preimage lies
in the closed support of the chart-kernel cutoff at `α`. -/
private theorem exists_const_covDerivLowerOrderCoeff_bdd_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
        (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
        {y : EuclN},
        y ∈ chartTargetEuclid (I := I) (M := M) α →
        y ∈ (toEuclidean (E := E)) ''
          ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) →
        |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
          Jdx Jdx' y| ≤ C := by
  classical
  have hKE_compact : IsCompact ((extChartAt I α) ''
      (cutoffKernelM (I := I) (M := M) α)) :=
    (cutoffKernelM_isCompact (I := I) (M := M) α).image_of_continuousOn
      ((continuousOn_extChartAt α).mono (by
        intro x hx
        rw [extChartAt_source]
        exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx))
  have hKE_sub_interior : (extChartAt I α) ''
      (cutoffKernelM (I := I) (M := M) α) ⊆
      interior ((extChartAt I α).target : Set E) := by
    have h_open : IsOpen ((extChartAt I α).target : Set E) :=
      isOpen_extChartAt_target (I := I) α
    rw [h_open.interior_eq]
    rintro y ⟨x, hx, rfl⟩
    have hx_src : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx
    exact (extChartAt I α).map_source hx_src
  obtain ⟨Cχ, hCχ_nn, hCχ⟩ :=
    chartChristoffel_bdd_on_compact (I := I) (M := M) g α
      hKE_compact hKE_sub_interior
  refine ⟨(r + s) * Cχ, by positivity, ?_⟩
  intro m Idx Idx' Jdx Jdx' y hy hb
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have himg : extChartAt I α b ∈ (extChartAt I α) ''
      (cutoffKernelM (I := I) (M := M) α) := by
    obtain ⟨z, ⟨b', hb'_cut, hb'_eq⟩, hz_eq⟩ := hb
    have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have hb'_src : b' ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hb'_cut
    have h_symm_y : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]
      exact (toEuclidean (E := E)).symm_apply_apply z
    have hb_eq_b' : b = b' := by
      rw [hb_def, h_symm_y, ← hb'_eq, (extChartAt I α).left_inv hb'_src]
    rw [hb_eq_b']
    exact ⟨b', hb'_cut, rfl⟩
  have hinput : ∀ k : Fin r,
      |inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y| ≤ Cχ := by
    intro k
    rw [inputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g r α m k
      Idx Idx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Idx k) (Idx' k),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Idx' k) m (Idx k)
              (extChartAt I α b)| *
            |∏ i ∈ Finset.univ.erase k,
              (if Idx' i = Idx i then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one' _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  have houtput : ∀ l : Fin s,
      |outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y| ≤ Cχ := by
    intro l
    rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g s α m l
      Jdx Jdx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Jdx' l) (Jdx l),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Jdx l) m (Jdx' l)
              (extChartAt I α b)| *
            |∏ j ∈ Finset.univ.erase l,
              (if Jdx j = Jdx' j then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one' _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  have hsum_input :
      |∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0)| ≤ r * Cχ := by
    have h := abs_sum_coeff_kronecker_le' (Finset.univ : Finset (Fin r))
      (fun k => inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y)
      (fun _ => Jdx' = Jdx) hCχ_nn (fun k _ => hinput k)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hsum_output :
      |∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0)| ≤ s * Cχ := by
    have h := abs_sum_coeff_kronecker_le' (Finset.univ : Finset (Fin s))
      (fun l => outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y)
      (fun _ => Idx' = Idx) hCχ_nn (fun l _ => houtput l)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  rw [covDerivLowerOrderCoeff_def]
  have habs_sub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-b| := abs_add_le a (-b)
      _ = |a| + |b| := by rw [abs_neg]
  refine (habs_sub _ _).trans ?_
  have := add_le_add hsum_input hsum_output
  rw [add_mul]
  linarith

/-- **The `L²` bound for a single coefficient-cutoff-component product.** For a
fixed component multi-index pair `p` and chart-coordinate direction `m`, the
`L²` norm of `covDerivLowerOrderCoeff · cutoffComponentEuclid` against the
Euclidean volume restricted to the chart target is bounded by the
Christoffel-coefficient sup `Ccoeff` times the cutoff component `L²` norm. -/
private lemma eLpNorm_coeff_mul_cutoffComponent_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {Ccoeff : ℝ} (hCcoeff_nn : 0 ≤ Ccoeff)
    (hCcoeff : ∀ {y : EuclN},
      y ∈ chartTargetEuclid (I := I) (M := M) α →
      y ∈ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) →
      |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
        Jdx Jdx' y| ≤ Ccoeff) :
    eLpNorm
        (fun y : EuclN =>
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
              Jdx Jdx' y *
            cutoffComponentEuclid (I := I) (M := M) g r s S α Idx' Jdx' y) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal Ccoeff *
        eLpNorm (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx' Jdx') 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
  set comp : EuclN → ℝ :=
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx' Jdx' with hcomp_def
  have hpt : ∀ y : EuclN,
      ‖covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
            Jdx Jdx' y * comp y‖ ≤
        ‖(Ccoeff : ℝ) • comp y‖ := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, smul_eq_mul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg hCcoeff_nn]
    by_cases hcz : comp y = 0
    · rw [hcz, abs_zero, mul_zero, mul_zero]
    · obtain ⟨hy, hb⟩ :=
        mem_cutoffKernelM_image_of_cutoffComponentEuclid_ne_zero
          (I := I) (M := M) g r s S α Idx' Jdx' (by rw [← hcomp_def]; exact hcz)
      exact mul_le_mul_of_nonneg_right (hCcoeff hy hb) (abs_nonneg _)
  calc eLpNorm
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
                Jdx Jdx' y * comp y) 2 μ
      ≤ eLpNorm ((Ccoeff : ℝ) • comp) 2 μ := eLpNorm_mono hpt
    _ = ‖(Ccoeff : ℝ)‖ₑ * eLpNorm comp 2 μ :=
        eLpNorm_const_smul (Ccoeff : ℝ) comp 2 _
    _ = ENNReal.ofReal Ccoeff * eLpNorm comp 2 μ := by
        rw [Real.enorm_eq_ofReal hCcoeff_nn]

/-- **A uniform `L²` bound for the cutoff-weighted lower-order term.** For a
closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart center
`α : M`, there is a single non-negative real constant `C` — depending only on
`(g, r, s, α)` — such that for every smooth compactly-supported `H¹` tensor
section `S`, the `L²` norm (against the Euclidean volume restricted to the
chart target) of the cutoff-weighted lower-order term, summed over all
chart-coordinate directions, is bounded by `ENNReal.ofReal C` times the `H¹`
norm of `S`. -/
private theorem exists_const_sum_eLpNorm_cutoffLowerOrderTerm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ m : Fin (Module.finrank ℝ E),
        eLpNorm
          (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
            m Idx Jdx) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨Ccoeff, hCcoeff_nn, hCcoeff⟩ :=
    exists_const_covDerivLowerOrderCoeff_bdd_cutoff (I := I) (M := M) g r s α
  obtain ⟨Ccomp, hCcomp_nn, hCcomp⟩ :=
    cutoffComponentEuclid_eLpNorm_le_uniform (I := I) (M := M) g r s α
  set n : ℕ := Module.finrank ℝ E with hn_def
  set Npair : ℕ := Fintype.card ((Fin r → Fin n) × (Fin s → Fin n))
    with hNpair_def
  refine ⟨n * (Npair * (Ccoeff * Ccomp)), by positivity, ?_⟩
  intro S Idx Jdx
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have hμ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hdir : ∀ m : Fin n,
      eLpNorm
          (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
            m Idx Jdx) 2 μ ≤
        ENNReal.ofReal (Npair * (Ccoeff * Ccomp)) * (‖S‖₊ : ℝ≥0∞) := by
    intro m
    have hae :
        (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
            m Idx Jdx)
          =ᵐ[μ]
        ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) := by
      rw [hμ_def]
      refine (ae_restrict_iff' hμ_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Finset.sum_apply]
      exact cutoffLowerOrderTerm_eq_linearCombination
        (I := I) (M := M) g r s S.toCcTensor α m Idx Jdx hy
    rw [eLpNorm_congr_ae hae]
    have hmeas : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        AEStronglyMeasurable
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) μ := by
      intro p
      rw [hμ_def]
      have hcont_on : ContinuousOn
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y)
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine ContinuousOn.mul ?_ ?_
        · exact (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
            g r s α m Idx p.1 Jdx p.2).continuousOn
        · exact (cutoffComponentEuclid_continuous (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2).continuousOn
      exact hcont_on.aestronglyMeasurable hμ_meas
    have hcomp_h1 : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        eLpNorm (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2) 2 μ ≤
          ENNReal.ofReal Ccomp * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      rw [hμ_def]
      have hb := hCcomp S.toCcTensor p.1 p.2
      rw [chartL2Measure] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ (zero_le _))
      rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from by
        rw [show ((‖S‖₊ : ℝ≥0∞)) = ‖S‖ₑ from (enorm_eq_nnnorm S).symm,
          ← ofReal_norm_eq_enorm S]]
      exact ENNReal.ofReal_le_ofReal
        (SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S)
    have hsummand : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        eLpNorm
            (fun y : EuclN =>
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                  Jdx p.2 y *
                cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                  p.1 p.2 y) 2 μ ≤
          ENNReal.ofReal (Ccoeff * Ccomp) * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      have h1 :
          eLpNorm
              (fun y : EuclN =>
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                    Jdx p.2 y *
                  cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                    p.1 p.2 y) 2 μ ≤
            ENNReal.ofReal Ccoeff *
              eLpNorm (cutoffComponentEuclid (I := I) (M := M)
                g r s S.toCcTensor α p.1 p.2) 2 μ := by
        rw [hμ_def]
        exact eLpNorm_coeff_mul_cutoffComponent_le (I := I) (M := M) g r s
          S.toCcTensor α m Idx p.1 Jdx p.2 hCcoeff_nn
          (fun {y} hy hb => hCcoeff m Idx p.1 Jdx p.2 hy hb)
      refine (h1.trans
        (mul_le_mul_of_nonneg_left (hcomp_h1 p) (zero_le _))).trans_eq ?_
      rw [ENNReal.ofReal_mul hCcoeff_nn, mul_assoc]
    refine (eLpNorm_sum_le (fun p _ => hmeas p) (by norm_num)).trans ?_
    refine (Finset.sum_le_sum (fun p _ => hsummand p)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, ← hNpair_def, nsmul_eq_mul]
    rw [show ((Npair : ℝ≥0∞)) = ENNReal.ofReal (Npair : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine (Finset.sum_le_sum (fun m _ => hdir m)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) from by
    rw [ENNReal.ofReal_natCast]]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- **A uniform `L²` bound for the chosen weak chart-partials of the cutoff
chart component.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)` and
a chart center `α : M`, there is a single non-negative real constant `C` —
depending only on `(g, r, s, α)`, **independent of the section `S` and of the
component multi-indices `(Idx, Jdx)`** — such that for every smooth
compactly-supported `H¹` tensor section `S`, the `L²` norm (against the
Euclidean volume restricted to the chart target) of the chosen weak `k`-th
chart-partial of the cutoff Euclidean chart component
`cutoffComponentEuclid g r s S.toCcTensor α Idx Jdx`, summed over all
chart-coordinate directions `k`, is bounded by `ENNReal.ofReal C` times the
`H¹` norm of `S`.

The constant `C` is unconditional and uniform in `S`, `Idx`, `Jdx`. The cutoff
chart component is, by construction, the chart push-forward of a globally smooth
compactly-supported manifold scalar field confined to the Euclidean chart
target, so each of its chosen weak chart-partials is `L²`-finite. -/
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_cutoffComponentEuclid_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C_cov, hC_cov_nn, hC_cov⟩ :=
    exists_const_eLpNorm_cutoffCovDerivComponent_le_uniform
      (I := I) (M := M) g r s α
  obtain ⟨C_low, hC_low_nn, hC_low⟩ :=
    exists_const_sum_eLpNorm_cutoffLowerOrderTerm_le_uniform
      (I := I) (M := M) g r s α
  set n : ℕ := Module.finrank ℝ E with hn_def
  have h_cross_const : ∀ k : Fin n,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := fun k =>
    exists_const_eLpNorm_cutoffLeibnizCrossTerm_le_uniform
      (I := I) (M := M) g r s α k
  set C_cross : ℝ := ∑ k : Fin n, (h_cross_const k).choose with hC_cross_def
  have hC_cross_nn : 0 ≤ C_cross :=
    Finset.sum_nonneg (fun k _ => (h_cross_const k).choose_spec.1)
  refine ⟨(n : ℝ) * C_cov + C_low + C_cross,
    by positivity, ?_⟩
  intro S Idx Jdx
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have hμ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hdir : ∀ k : Fin n,
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) 2 μ ≤
        eLpNorm
            (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2 μ
          + eLpNorm
              (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
                k Idx Jdx) 2 μ
          + eLpNorm
              (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                k Idx Jdx) 2 μ := by
    intro k
    have h_step1 := chosenWeakPartial'_cutoffComponentEuclid_ae_eq_euclidPartial
      (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
    rw [hμ_def, eLpNorm_congr_ae h_step1]
    set tCov : EuclN → ℝ :=
      cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htCov_def
    set tCross : EuclN → ℝ :=
      cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htCross_def
    set tLow : EuclN → ℝ :=
      cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htLow_def
    have h_three :
        euclidPartial (E := E) k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx)
          =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
        (fun y : EuclN => tCov y + tCross y - tLow y) := by
      refine (ae_restrict_iff' hμ_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [htCov_def, htCross_def, htLow_def]
      exact euclidPartial_cutoffComponentEuclid_eq_three_terms
        (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx hy
    rw [eLpNorm_congr_ae h_three]
    have h_cov_meas : AEStronglyMeasurable tCov
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (cutoffCovDerivComponent_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    have h_cross_meas : AEStronglyMeasurable tCross
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (cutoffLeibnizCrossTerm_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    have h_low_meas : AEStronglyMeasurable tLow
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (cutoffLowerOrderTerm_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    exact eLpNorm_add_add_sub_le h_cov_meas h_cross_meas h_low_meas
  refine (Finset.sum_le_sum (fun k _ => hdir k)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h_cov_sum :
      ∑ k : Fin n,
        eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal ((n : ℝ) * C_cov) * (‖S‖₊ : ℝ≥0∞) := by
    have h_each : ∀ k : Fin n,
        eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
          ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞) := fun k => hC_cov S Idx Jdx k
    refine (Finset.sum_le_sum (fun k _ => h_each k)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have h_low_sum :
      ∑ k : Fin n,
        eLpNorm (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal C_low * (‖S‖₊ : ℝ≥0∞) := hC_low S Idx Jdx
  have h_cross_sum :
      ∑ k : Fin n,
        eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal C_cross * (‖S‖₊ : ℝ≥0∞) := by
    have h_each : ∀ k : Fin n,
        eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
          ENNReal.ofReal ((h_cross_const k).choose) * (‖S‖₊ : ℝ≥0∞) := by
      intro k
      exact (h_cross_const k).choose_spec.2 S Idx Jdx
    refine (Finset.sum_le_sum (fun k _ => h_each k)).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    rw [hC_cross_def]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => (h_cross_const k).choose_spec.1)]
  calc (∑ k : Fin n,
            eLpNorm (cutoffCovDerivComponent (I := I) (M := M)
              g r s S.toCcTensor α k Idx Jdx) 2 μ
          + ∑ k : Fin n,
            eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M)
              g r s S.toCcTensor α k Idx Jdx) 2 μ)
        + ∑ k : Fin n,
            eLpNorm (cutoffLowerOrderTerm (I := I) (M := M)
              g r s S.toCcTensor α k Idx Jdx) 2 μ
      ≤ (ENNReal.ofReal ((n : ℝ) * C_cov) * (‖S‖₊ : ℝ≥0∞)
            + ENNReal.ofReal C_cross * (‖S‖₊ : ℝ≥0∞))
          + ENNReal.ofReal C_low * (‖S‖₊ : ℝ≥0∞) := by
        gcongr
    _ = ENNReal.ofReal ((n : ℝ) * C_cov + C_low + C_cross) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (by positivity) hC_cross_nn,
          ENNReal.ofReal_add (by positivity) hC_low_nn]
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
