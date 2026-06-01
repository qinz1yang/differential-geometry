import DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanIteratedL2
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.ChartBanach
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.NullSubmodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# `L²`-convention chart-based Sobolev space `W^{k,2}_chart(M)` and its
Hilbert structure on a smooth manifold-with-boundary

This is the with-boundary parallel of `Analysis/Sobolev/ChartL2.lean`.
Given a smooth manifold `M` modelled on the canonical Euclidean
half-space `EuclideanHalfSpace n` (via
`modelWithCornersEuclideanHalfSpace n`), we mirror the boundaryless
chart-based `L²`-Sobolev norm and inner product, replacing the
underlying boundaryless `L²` quantities by the half-space-friendly
Dirichlet variants from `WithBoundary/EuclideanIteratedL2.lean`.

The `L²`-convention chart-based norm is

  `‖u‖_{W^{k,2}_chart(M)}² = ∑_α ‖chartPushed α u‖²_{W^{k,2}_0(chart-target)}`,

i.e., a `tsum` over chart points of squared per-chart Dirichlet
half-space `L²`-Sobolev norms, and the corresponding `L²`-Sobolev inner
product is

  `⟨u, v⟩_{W^{k,2}_chart(M)} = ∑_α ⟨chartPushed α u, chartPushed α v⟩_{W^{k,2}_0(chart-target)}`.

The resulting subtype `WkpChartL2 g k` carries:
* a `SeminormedAddCommGroup` structure;
* a `Module ℝ` structure;
* an `InnerProductSpace ℝ` structure.

The standard `SeparationQuotient`-based wrapper `WkpChartL2Quot` then
carries an honest `NormedAddCommGroup` and `InnerProductSpace ℝ`
structure.

Completeness is *not* developed here; it is left to a separate module.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

/-- The squared `L²`-convention chart-based Sobolev norm, as a `tsum`
over charts of squared per-chart half-space `L²`-Sobolev norms. -/
def wkpNormChartL2Sq [T2Space M] [SigmaCompactSpace M]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
      (d := n)
      k
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α)

/-- The `L²`-convention chart-based Sobolev norm. -/
def wkpNormChartL2 [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u : M → ℝ) : ℝ≥0∞ :=
  wkpNormChartL2Sq (n := n) (M := M) g k u ^ ((1 : ℝ) / 2)

theorem wkpNormChartL2_eq_rpow
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u : M → ℝ) :
    wkpNormChartL2 (n := n) (M := M) g k u =
      wkpNormChartL2Sq (n := n) (M := M) g k u ^ ((1 : ℝ) / 2) := rfl

theorem wkpNormChartL2Sq_eq_tsum
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u : M → ℝ) :
    wkpNormChartL2Sq (n := n) (M := M) g k u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := rfl

/-- `wkpNormChartL2 g k u = ENNReal.ofReal √((wkpNormChartL2Sq g k u).toReal)`
when the squared norm is finite. -/
private theorem wkpNormChartL2_eq_ofReal_sqrt_toReal
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {u : M → ℝ}
    (hSq : wkpNormChartL2Sq (n := n) (M := M) g k u ≠ (⊤ : ℝ≥0∞)) :
    wkpNormChartL2 (n := n) (M := M) g k u =
      ENNReal.ofReal (Real.sqrt
        (wkpNormChartL2Sq (n := n) (M := M) g k u).toReal) := by
  unfold wkpNormChartL2
  have h_toReal_pow :
      (wkpNormChartL2Sq (n := n) (M := M) g k u) ^ ((1 : ℝ) / 2) =
        ENNReal.ofReal
          ((wkpNormChartL2Sq (n := n) (M := M) g k u).toReal ^ ((1 : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_toReal hSq]
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [h_toReal_pow]
  rw [show (wkpNormChartL2Sq (n := n) (M := M) g k u).toReal ^ ((1 : ℝ) / 2) =
      Real.sqrt (wkpNormChartL2Sq (n := n) (M := M) g k u).toReal by
    rw [Real.sqrt_eq_rpow]]

/-- The squared `L²`-Sobolev chart-based norm of the zero function is zero. -/
theorem wkpNormChartL2Sq_zero_fun
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} :
    wkpNormChartL2Sq (n := n) (M := M) g k (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartL2Sq
  have hpt : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
        (d := n) k
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (fun _ : M => (0 : ℝ)))
        (chartTargetEuclid (n := n) (M := M) α) = 0 := by
    intro α
    rw [chartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_zero_fun_zero
      (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

/-- The `L²`-Sobolev chart-based norm of the zero function is zero. -/
theorem wkpNormChartL2_zero_fun
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} :
    wkpNormChartL2 (n := n) (M := M) g k (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartL2
  rw [wkpNormChartL2Sq_zero_fun (n := n) (M := M) g]
  exact ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)

/-- The squared `L²`-chart norm is finite for any function in
`MemWkpChart g k 2`, when `M` is compact. -/
theorem wkpNormChartL2Sq_lt_top_of_memWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k 2 u) :
    wkpNormChartL2Sq (n := n) (M := M) g k u < ⊤ := by
  classical
  unfold wkpNormChartL2Sq
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
      (d := n) k
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α) with hf_def
  have hPOU_locFin : LocallyFinite
      (fun α : M => Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU
      (modelWithCornersEuclideanHalfSpace n) M).locallyFinite
  have hSupport_finite : {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty}.Finite :=
    hPOU_locFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) := by
        rw [hα]; exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]; ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
      (d := n) k
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_zero_fun_zero
      (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  set S : Set M := {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have hf_supp_S : Function.support f ⊆ S := by
    intro α hα
    by_contra hαS
    apply hα
    have h_not_in_S : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne; exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α h_not_in_S
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := by
      intro hαS
      apply hα
      exact (Set.Finite.mem_toFinset _).mpr hαS
    have hempty : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne; exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_lt_top_of_memWkpHalfSpace
    (d := n) (hu α)

/-- The `L²`-Sobolev chart norm is finite for any function in
`MemWkpChart g k 2`, when `M` is compact. -/
theorem wkpNormChartL2_lt_top_of_memWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k 2 u) :
    wkpNormChartL2 (n := n) (M := M) g k u < ⊤ := by
  unfold wkpNormChartL2
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (wkpNormChartL2Sq_lt_top_of_memWkpChart (n := n) (M := M) g hu).ne

/-- The squared `L²`-chart norm is invariant under `ChartPushedAEEq`. -/
theorem wkpNormChartL2Sq_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {u v : M → ℝ}
    (huv : ChartPushedAEEq (n := n) (M := M) g u v) :
    wkpNormChartL2Sq (n := n) (M := M) g k u =
      wkpNormChartL2Sq (n := n) (M := M) g k v := by
  unfold wkpNormChartL2Sq
  refine tsum_congr ?_
  intro α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_congr_ae
    (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (huv α)

/-- The `L²`-chart norm is invariant under `ChartPushedAEEq`. -/
theorem wkpNormChartL2_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {u v : M → ℝ}
    (huv : ChartPushedAEEq (n := n) (M := M) g u v) :
    wkpNormChartL2 (n := n) (M := M) g k u =
      wkpNormChartL2 (n := n) (M := M) g k v := by
  unfold wkpNormChartL2
  rw [wkpNormChartL2Sq_congr_chartPushed_ae (n := n) (M := M) g huv]

/-- Scalar-multiplication identity for the squared `L²`-chart norm. -/
theorem wkpNormChartL2Sq_const_smul
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k 2 u) :
    wkpNormChartL2Sq (n := n) (M := M) g k (fun x => c * u x) =
      ‖c‖ₑ ^ (2 : ℕ) * wkpNormChartL2Sq (n := n) (M := M) g k u := by
  unfold wkpNormChartL2Sq
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_const_smul
    (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) c

/-- Scalar-multiplication identity for the `L²`-chart norm. -/
theorem wkpNormChartL2_const_smul
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k 2 u) :
    wkpNormChartL2 (n := n) (M := M) g k (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChartL2 (n := n) (M := M) g k u := by
  unfold wkpNormChartL2
  rw [wkpNormChartL2Sq_const_smul (n := n) (M := M) g c hu]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [show ((‖c‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) = ‖c‖ₑ ^ ((2 : ℕ) : ℝ) by
    rw [ENNReal.rpow_natCast]]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Auxiliary: pointwise per-chart triangle for the squared `L²`-norm
composes to the squared global. -/
private theorem wkpNormChartL2_add_le_aux
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ}
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k 2 u)
    (hv : MemWkpChart (n := n) (M := M) g k 2 v) :
    wkpNormChartL2 (n := n) (M := M) g k (fun x => u x + v x) ≤
      wkpNormChartL2 (n := n) (M := M) g k u +
        wkpNormChartL2 (n := n) (M := M) g k v := by
  classical
  have h_per_α : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
        (d := n) k
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (fun x => u x + v x))
        (chartTargetEuclid (n := n) (M := M) α) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) +
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α v)
          (chartTargetEuclid (n := n) (M := M) α) := by
    intro α
    rw [chartPushed_add]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_add_le
      (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
      (hu α) (hv α)
  set S : Set M := {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty}
      with hS_def
  have hPOU_locFin : LocallyFinite
      (fun α : M => Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU
      (modelWithCornersEuclideanHalfSpace n) M).locallyFinite
  have hS_finite : S.Finite := hPOU_locFin.finite_nonempty_of_compact
  set fU : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
      (d := n) k
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α) with hfU_def
  set fV : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
      (d := n) k
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α v)
      (chartTargetEuclid (n := n) (M := M) α) with hfV_def
  set fUV : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
      (d := n) k
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α
        (fun x => u x + v x))
      (chartTargetEuclid (n := n) (M := M) α) with hfUV_def
  have h_finiteness_fU : ∀ α : M, fU α < (⊤ : ℝ≥0∞) := by
    intro α
    rw [hfU_def]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_lt_top_of_memWkpHalfSpace
      (d := n) (hu α)
  have h_finiteness_fV : ∀ α : M, fV α < (⊤ : ℝ≥0∞) := by
    intro α
    rw [hfV_def]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_lt_top_of_memWkpHalfSpace
      (d := n) (hv α)
  have h_finiteness_fUV : ∀ α : M, fUV α < (⊤ : ℝ≥0∞) := by
    intro α
    have := h_per_α α
    have h_rhs_ne : fU α + fV α ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨(h_finiteness_fU α).ne, (h_finiteness_fV α).ne⟩
    change fUV α < (⊤ : ℝ≥0∞)
    exact lt_of_le_of_lt this (lt_of_le_of_ne le_top h_rhs_ne)
  let fUR : M → ℝ := fun α => (fU α).toReal
  let fVR : M → ℝ := fun α => (fV α).toReal
  let fUVR : M → ℝ := fun α => (fUV α).toReal
  have hUR_nonneg : ∀ α, 0 ≤ fUR α := fun α => ENNReal.toReal_nonneg
  have hVR_nonneg : ∀ α, 0 ≤ fVR α := fun α => ENNReal.toReal_nonneg
  have hUVR_nonneg : ∀ α, 0 ≤ fUVR α := fun α => ENNReal.toReal_nonneg
  have h_per_α_R : ∀ α : M, fUVR α ≤ fUR α + fVR α := by
    intro α
    have h_lhs := h_per_α α
    have h_rhs_ne : fU α + fV α ≠ (⊤ : ℝ≥0∞) :=
      ENNReal.add_ne_top.mpr ⟨(h_finiteness_fU α).ne, (h_finiteness_fV α).ne⟩
    have h_lhs_le := ENNReal.toReal_mono h_rhs_ne h_lhs
    rw [ENNReal.toReal_add (h_finiteness_fU α).ne (h_finiteness_fV α).ne] at h_lhs_le
    exact h_lhs_le
  have h_zero_outside_U : ∀ α : M, α ∉ S → fU α = 0 := by
    intro α hα
    have hempty : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      rw [hS_def] at hα
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne; exact hα hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) := by
        rw [hempty]; exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]; ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
      (d := n) k _ _ = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_zero_fun_zero
      (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  have h_zero_outside_V : ∀ α : M, α ∉ S → fV α = 0 := by
    intro α hα
    have hempty : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      rw [hS_def] at hα
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne; exact hα hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) := by
        rw [hempty]; exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α v =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]; ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
      (d := n) k _ _ = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_zero_fun_zero
      (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  have h_zero_outside_UV : ∀ α : M, α ∉ S → fUV α = 0 := by
    intro α hα
    have hempty : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      rw [hS_def] at hα
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne; exact hα hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) := by
        rw [hempty]; exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α
        (fun x => u x + v x) = (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]; ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace
      (d := n) k _ _ = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_zero_fun_zero
      (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  have htsum_eq_USq : ∑' α : M, (fU α) ^ (2 : ℕ) =
      ∑ α ∈ hS_finite.toFinset, (fU α) ^ (2 : ℕ) := by
    apply tsum_eq_sum
    intro α hα
    have hαS : α ∉ S := fun hαS => hα ((Set.Finite.mem_toFinset _).mpr hαS)
    rw [h_zero_outside_U α hαS]
    simp
  have htsum_eq_VSq : ∑' α : M, (fV α) ^ (2 : ℕ) =
      ∑ α ∈ hS_finite.toFinset, (fV α) ^ (2 : ℕ) := by
    apply tsum_eq_sum
    intro α hα
    have hαS : α ∉ S := fun hαS => hα ((Set.Finite.mem_toFinset _).mpr hαS)
    rw [h_zero_outside_V α hαS]
    simp
  have htsum_eq_UVSq : ∑' α : M, (fUV α) ^ (2 : ℕ) =
      ∑ α ∈ hS_finite.toFinset, (fUV α) ^ (2 : ℕ) := by
    apply tsum_eq_sum
    intro α hα
    have hαS : α ∉ S := fun hαS => hα ((Set.Finite.mem_toFinset _).mpr hαS)
    rw [h_zero_outside_UV α hαS]
    simp
  have h_chartL2Sq_U : wkpNormChartL2Sq (n := n) (M := M) g k u =
      ∑ α ∈ hS_finite.toFinset, (fU α) ^ (2 : ℕ) := by
    unfold wkpNormChartL2Sq
    rw [show (∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α)) =
        ∑' α : M, (fU α) ^ (2 : ℕ) from
      tsum_congr (fun α => by
        rw [hfU_def,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_sq_eq_wkpNormL2SqHalfSpace])]
    exact htsum_eq_USq
  have h_chartL2Sq_V : wkpNormChartL2Sq (n := n) (M := M) g k v =
      ∑ α ∈ hS_finite.toFinset, (fV α) ^ (2 : ℕ) := by
    unfold wkpNormChartL2Sq
    rw [show (∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α v)
          (chartTargetEuclid (n := n) (M := M) α)) =
        ∑' α : M, (fV α) ^ (2 : ℕ) from
      tsum_congr (fun α => by
        rw [hfV_def,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_sq_eq_wkpNormL2SqHalfSpace])]
    exact htsum_eq_VSq
  have h_chartL2Sq_UV : wkpNormChartL2Sq (n := n) (M := M) g k (fun x => u x + v x) =
      ∑ α ∈ hS_finite.toFinset, (fUV α) ^ (2 : ℕ) := by
    unfold wkpNormChartL2Sq
    rw [show (∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α
            (fun x => u x + v x))
          (chartTargetEuclid (n := n) (M := M) α)) =
        ∑' α : M, (fUV α) ^ (2 : ℕ) from
      tsum_congr (fun α => by
        rw [hfUV_def,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2HalfSpace_sq_eq_wkpNormL2SqHalfSpace])]
    exact htsum_eq_UVSq
  have h_chartL2Sq_U_finite :
      wkpNormChartL2Sq (n := n) (M := M) g k u ≠ (⊤ : ℝ≥0∞) := by
    rw [h_chartL2Sq_U]
    exact (ENNReal.sum_lt_top.mpr fun α _ =>
      ENNReal.pow_lt_top (h_finiteness_fU α)).ne
  have h_chartL2Sq_V_finite :
      wkpNormChartL2Sq (n := n) (M := M) g k v ≠ (⊤ : ℝ≥0∞) := by
    rw [h_chartL2Sq_V]
    exact (ENNReal.sum_lt_top.mpr fun α _ =>
      ENNReal.pow_lt_top (h_finiteness_fV α)).ne
  have h_chartL2Sq_UV_finite :
      wkpNormChartL2Sq (n := n) (M := M) g k (fun x => u x + v x) ≠ (⊤ : ℝ≥0∞) := by
    rw [h_chartL2Sq_UV]
    exact (ENNReal.sum_lt_top.mpr fun α _ =>
      ENNReal.pow_lt_top (h_finiteness_fUV α)).ne
  have h_chartL2Sq_U_toReal :
      (wkpNormChartL2Sq (n := n) (M := M) g k u).toReal =
        ∑ α ∈ hS_finite.toFinset, fUR α ^ 2 := by
    rw [h_chartL2Sq_U]
    rw [ENNReal.toReal_sum (fun α _ => (ENNReal.pow_lt_top (h_finiteness_fU α)).ne)]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [ENNReal.toReal_pow]
  have h_chartL2Sq_V_toReal :
      (wkpNormChartL2Sq (n := n) (M := M) g k v).toReal =
        ∑ α ∈ hS_finite.toFinset, fVR α ^ 2 := by
    rw [h_chartL2Sq_V]
    rw [ENNReal.toReal_sum (fun α _ => (ENNReal.pow_lt_top (h_finiteness_fV α)).ne)]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [ENNReal.toReal_pow]
  have h_chartL2Sq_UV_toReal :
      (wkpNormChartL2Sq (n := n) (M := M) g k (fun x => u x + v x)).toReal =
        ∑ α ∈ hS_finite.toFinset, fUVR α ^ 2 := by
    rw [h_chartL2Sq_UV]
    rw [ENNReal.toReal_sum (fun α _ => (ENNReal.pow_lt_top (h_finiteness_fUV α)).ne)]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [ENNReal.toReal_pow]
  have h_real_triangle :
      Real.sqrt (∑ α ∈ hS_finite.toFinset, fUVR α ^ 2) ≤
        Real.sqrt (∑ α ∈ hS_finite.toFinset, fUR α ^ 2) +
          Real.sqrt (∑ α ∈ hS_finite.toFinset, fVR α ^ 2) := by
    let A : Type _ := { α : M // α ∈ hS_finite.toFinset }
    let aR : A → ℝ := fun α => fUR α.val
    let bR : A → ℝ := fun α => fVR α.val
    let cR : A → ℝ := fun α => fUVR α.val
    have h_per_a : ∀ a : A, cR a ≤ aR a + bR a := fun a => h_per_α_R a.val
    have hcR_nn : ∀ a : A, 0 ≤ cR a := fun a => hUVR_nonneg a.val
    have haR_nn : ∀ a : A, 0 ≤ aR a := fun a => hUR_nonneg a.val
    have hbR_nn : ∀ a : A, 0 ≤ bR a := fun a => hVR_nonneg a.val
    have h_eq_a :
        ∑ α ∈ hS_finite.toFinset, fUR α ^ 2 =
          ∑ a ∈ hS_finite.toFinset.attach, aR a ^ 2 :=
      (Finset.sum_attach hS_finite.toFinset (fun α => fUR α ^ 2)).symm
    have h_eq_b :
        ∑ α ∈ hS_finite.toFinset, fVR α ^ 2 =
          ∑ a ∈ hS_finite.toFinset.attach, bR a ^ 2 :=
      (Finset.sum_attach hS_finite.toFinset (fun α => fVR α ^ 2)).symm
    have h_eq_c :
        ∑ α ∈ hS_finite.toFinset, fUVR α ^ 2 =
          ∑ a ∈ hS_finite.toFinset.attach, cR a ^ 2 :=
      (Finset.sum_attach hS_finite.toFinset (fun α => fUVR α ^ 2)).symm
    rw [h_eq_a, h_eq_b, h_eq_c]
    have h_compsq_le : ∀ a ∈ hS_finite.toFinset.attach,
        cR a ^ 2 ≤ (aR a + bR a) ^ 2 := by
      intro a _
      have hcR_nn' : 0 ≤ cR a := hcR_nn a
      have hsum_nn : 0 ≤ aR a + bR a := add_nonneg (haR_nn a) (hbR_nn a)
      nlinarith [h_per_a a, hcR_nn', hsum_nn,
        sq_nonneg (cR a - (aR a + bR a)), sq_nonneg (cR a + (aR a + bR a))]
    have h_sqrt_le_sum :
        Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, cR a ^ 2) ≤
          Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, (aR a + bR a) ^ 2) :=
      Real.sqrt_le_sqrt (Finset.sum_le_sum h_compsq_le)
    have h_minkowski :
        Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, (aR a + bR a) ^ 2) ≤
          Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, aR a ^ 2) +
          Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, bR a ^ 2) := by
      let FR : EuclideanSpace ℝ A := WithLp.toLp 2 aR
      let GR : EuclideanSpace ℝ A := WithLp.toLp 2 bR
      have hFR_apply : ∀ a, FR a = aR a := fun a => rfl
      have hGR_apply : ∀ a, GR a = bR a := fun a => rfl
      have h_norm_FR : ‖FR‖ = Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, aR a ^ 2) := by
        rw [EuclideanSpace.norm_eq]
        rw [show (∑ a : A, ‖FR a‖ ^ 2) =
            ∑ a ∈ hS_finite.toFinset.attach, ‖FR a‖ ^ 2 from rfl]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Real.norm_eq_abs, sq_abs, hFR_apply]
      have h_norm_GR : ‖GR‖ = Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, bR a ^ 2) := by
        rw [EuclideanSpace.norm_eq]
        rw [show (∑ a : A, ‖GR a‖ ^ 2) =
            ∑ a ∈ hS_finite.toFinset.attach, ‖GR a‖ ^ 2 from rfl]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Real.norm_eq_abs, sq_abs, hGR_apply]
      have h_norm_FRpGR :
          ‖FR + GR‖ = Real.sqrt (∑ a ∈ hS_finite.toFinset.attach, (aR a + bR a) ^ 2) := by
        rw [EuclideanSpace.norm_eq]
        rw [show (∑ a : A, ‖(FR + GR) a‖ ^ 2) =
            ∑ a ∈ hS_finite.toFinset.attach, ‖(FR + GR) a‖ ^ 2 from rfl]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Real.norm_eq_abs, sq_abs]
        change ((FR a + GR a) ^ 2 : ℝ) = _
        rw [hFR_apply, hGR_apply]
      have h_lp_triangle : ‖FR + GR‖ ≤ ‖FR‖ + ‖GR‖ := norm_add_le FR GR
      rw [← h_norm_FRpGR, ← h_norm_FR, ← h_norm_GR]
      exact h_lp_triangle
    linarith
  rw [wkpNormChartL2_eq_ofReal_sqrt_toReal h_chartL2Sq_UV_finite]
  rw [wkpNormChartL2_eq_ofReal_sqrt_toReal h_chartL2Sq_U_finite]
  rw [wkpNormChartL2_eq_ofReal_sqrt_toReal h_chartL2Sq_V_finite]
  rw [h_chartL2Sq_U_toReal, h_chartL2Sq_V_toReal, h_chartL2Sq_UV_toReal]
  rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h_real_triangle

/-- Triangle inequality for the chart-based `L²`-Sobolev norm
(compact `M`). -/
theorem wkpNormChartL2_add_le
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ}
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k 2 u)
    (hv : MemWkpChart (n := n) (M := M) g k 2 v) :
    wkpNormChartL2 (n := n) (M := M) g k (fun x => u x + v x) ≤
      wkpNormChartL2 (n := n) (M := M) g k u +
        wkpNormChartL2 (n := n) (M := M) g k v :=
  wkpNormChartL2_add_le_aux (n := n) (M := M) g hu hv

/-- The chart-based `L²`-Sobolev inner product, defined as the `tsum` of
the per-chart half-space `L²`-Sobolev inner products. -/
def wkpInnerChartL2
    [T2Space M] [SigmaCompactSpace M]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u v : M → ℝ) : ℝ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace
      (d := n)
      k
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α v)
      (chartTargetEuclid (n := n) (M := M) α)

theorem wkpInnerChartL2_eq_tsum
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u v : M → ℝ) :
    wkpInnerChartL2 (n := n) (M := M) g k u v =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace
          (d := n)
          k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α v)
          (chartTargetEuclid (n := n) (M := M) α) := rfl

/-- Symmetry of the chart-based `L²`-Sobolev inner product. -/
theorem wkpInnerChartL2_comm
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u v : M → ℝ) :
    wkpInnerChartL2 (n := n) (M := M) g k u v =
      wkpInnerChartL2 (n := n) (M := M) g k v u := by
  unfold wkpInnerChartL2
  refine tsum_congr ?_
  intro α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace_comm
    (d := n) k _ _ _

/-- The chart-based `L²`-Sobolev inner product is non-negative on the
diagonal. -/
theorem wkpInnerChartL2_self_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u : M → ℝ) :
    0 ≤ wkpInnerChartL2 (n := n) (M := M) g k u u := by
  unfold wkpInnerChartL2
  exact tsum_nonneg fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace_self_nonneg
      (d := n) k _ _

/-- The `L²`-convention chart-based Sobolev space, as a subtype of
`M → ℝ`, implemented as the underlying subtype of
`wkpChartSubmodule g k 2`. -/
def WkpChartL2
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) : Type _ :=
  ↥(wkpChartSubmodule (n := n) (M := M) g k 2 (by norm_num : (1 : ℝ≥0∞) ≤ 2))

instance instAddCommGroupWkpChartL2
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    AddCommGroup (WkpChartL2 (n := n) (M := M) g k) :=
  inferInstanceAs (AddCommGroup ↥(wkpChartSubmodule (n := n) (M := M) g k 2
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)))

instance instModuleRealWkpChartL2
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    Module ℝ (WkpChartL2 (n := n) (M := M) g k) :=
  inferInstanceAs (Module ℝ ↥(wkpChartSubmodule (n := n) (M := M) g k 2
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)))

/-- The underlying `M → ℝ` function of an element `u : WkpChartL2 g k`. -/
def wkpChartL2Fun
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ}
    (u : WkpChartL2 (n := n) (M := M) g k) : M → ℝ :=
  Subtype.val (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (n := n) (M := M) g k 2
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)) u

/-- The membership property of the underlying function of an element of
`WkpChartL2`. -/
lemma wkpChartL2Fun_memWkpChart
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ}
    (u : WkpChartL2 (n := n) (M := M) g k) :
    MemWkpChart (n := n) (M := M) g k 2 (wkpChartL2Fun u) :=
  Subtype.property
    (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (n := n) (M := M) g k 2
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)) u

@[simp]
lemma wkpChartL2Fun_add
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ}
    (u v : WkpChartL2 (n := n) (M := M) g k) :
    wkpChartL2Fun (u + v) = fun x => wkpChartL2Fun u x + wkpChartL2Fun v x := by
  ext x; rfl

@[simp]
lemma wkpChartL2Fun_smul
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ}
    (c : ℝ) (u : WkpChartL2 (n := n) (M := M) g k) :
    wkpChartL2Fun (c • u) = fun x => c * wkpChartL2Fun u x := by
  ext x; rfl

@[simp]
lemma wkpChartL2Fun_zero
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} :
    wkpChartL2Fun (0 : WkpChartL2 (n := n) (M := M) g k) = (fun _ => 0) := rfl

/-- `Norm` instance on `WkpChartL2 g k`, using the `L²`-convention chart
norm. -/
instance instNormWkpChartL2
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    Norm (WkpChartL2 (n := n) (M := M) g k) where
  norm u := (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)).toReal

@[simp]
lemma norm_wkpChartL2_def
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ}
    (u : WkpChartL2 (n := n) (M := M) g k) :
    ‖u‖ = (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)).toReal := rfl

/-- The `SeminormedSpace.Core` for `WkpChartL2 g k` (compact `M`). -/
lemma wkpChartL2_seminormedSpace_core
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    SeminormedSpace.Core ℝ (WkpChartL2 (n := n) (M := M) g k) where
  norm_nonneg u := ENNReal.toReal_nonneg
  norm_smul c u := by
    have hu_mem := wkpChartL2Fun_memWkpChart u
    change (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun (c • u))).toReal =
      ‖c‖ * (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)).toReal
    rw [wkpChartL2Fun_smul]
    rw [wkpNormChartL2_const_smul (n := n) (M := M) g c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]
  norm_triangle u v := by
    have hu_mem := wkpChartL2Fun_memWkpChart u
    have hv_mem := wkpChartL2Fun_memWkpChart v
    change (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun (u + v))).toReal ≤
      (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)).toReal +
        (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun v)).toReal
    rw [wkpChartL2Fun_add]
    have h_add_le := wkpNormChartL2_add_le (n := n) (M := M) g hu_mem hv_mem
    have hu_lt : wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) < ⊤ :=
      wkpNormChartL2_lt_top_of_memWkpChart (n := n) (M := M) g hu_mem
    have hv_lt : wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun v) < ⊤ :=
      wkpNormChartL2_lt_top_of_memWkpChart (n := n) (M := M) g hv_mem
    have hu_ne : wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) ≠ ⊤ := hu_lt.ne
    have hv_ne : wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun v) ≠ ⊤ := hv_lt.ne
    have hRHS_ne : wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) +
        wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun v) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
    have hToReal := ENNReal.toReal_mono hRHS_ne h_add_le
    rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
    exact hToReal

/-- `SeminormedAddCommGroup` instance on `WkpChartL2 g k` (compact `M`). -/
instance instSeminormedAddCommGroupWkpChartL2
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    SeminormedAddCommGroup (WkpChartL2 (n := n) (M := M) g k) :=
  SeminormedAddCommGroup.ofCore (wkpChartL2_seminormedSpace_core (n := n) (M := M) g k)

/-- `NormedSpace ℝ` instance on `WkpChartL2 g k` (compact `M`). -/
instance instNormedSpaceRealWkpChartL2
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    NormedSpace ℝ (WkpChartL2 (n := n) (M := M) g k) where
  norm_smul_le c u := by
    have hu_mem := wkpChartL2Fun_memWkpChart u
    change (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun (c • u))).toReal ≤
      ‖c‖ * (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)).toReal
    rw [wkpChartL2Fun_smul]
    rw [wkpNormChartL2_const_smul (n := n) (M := M) g c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]

/-- The `SeparationQuotient` of `WkpChartL2 g k` is a `NormedAddCommGroup`. -/
def WkpChartL2Quot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) : Type _ :=
  SeparationQuotient (WkpChartL2 (n := n) (M := M) g k)

instance instAddCommGroupWkpChartL2Quot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    AddCommGroup (WkpChartL2Quot (n := n) (M := M) g k) :=
  inferInstanceAs (AddCommGroup
    (SeparationQuotient (WkpChartL2 (n := n) (M := M) g k)))

instance instNormedAddCommGroupWkpChartL2Quot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    NormedAddCommGroup (WkpChartL2Quot (n := n) (M := M) g k) :=
  inferInstanceAs (NormedAddCommGroup
    (SeparationQuotient (WkpChartL2 (n := n) (M := M) g k)))

instance instModuleWkpChartL2Quot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    Module ℝ (WkpChartL2Quot (n := n) (M := M) g k) :=
  inferInstanceAs (Module ℝ
    (SeparationQuotient (WkpChartL2 (n := n) (M := M) g k)))

instance instNormedSpaceRealWkpChartL2Quot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    NormedSpace ℝ (WkpChartL2Quot (n := n) (M := M) g k) :=
  inferInstanceAs (NormedSpace ℝ
    (SeparationQuotient (WkpChartL2 (n := n) (M := M) g k)))

/-- The `Inner ℝ` instance on `WkpChartL2 g k`. -/
instance instInnerWkpChartL2
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    Inner ℝ (WkpChartL2 (n := n) (M := M) g k) where
  inner u v :=
    wkpInnerChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) (wkpChartL2Fun v)

@[simp]
lemma inner_wkpChartL2_def
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ}
    (u v : WkpChartL2 (n := n) (M := M) g k) :
    @inner ℝ _ _ u v =
      wkpInnerChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) (wkpChartL2Fun v) := rfl

/-- The set of "active" chart points: those for which the partition-of-unity
weight has nonempty support. This is finite when `M` is compact. -/
private def activeChartSupp
    [T2Space M] [SigmaCompactSpace M] : Set M :=
  { α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty }

private theorem activeChartSupp_finite
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] :
    (activeChartSupp (n := n) (M := M)).Finite :=
  ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
    (modelWithCornersEuclideanHalfSpace n) M).locallyFinite).finite_nonempty_of_compact

/-- Outside the active set, the chart-pushed function is identically zero. -/
private theorem chartPushed_eq_zero_off_activeChartSupp
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (hα : α ∉ activeChartSupp (n := n) (M := M)) (u : M → ℝ) :
    chartPushed (n := n) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M) α u =
      (fun _ => (0 : ℝ)) := by
  unfold activeChartSupp at hα
  have hempty : (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
    have h_not_nonempty : ¬ (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
      intro hne; exact hα hne
    exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
  have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
      (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) x = 0 := by
    intro x
    have : x ∉ Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) := by
      rw [hempty]; exact Set.notMem_empty x
    simpa [Function.mem_support] using this
  funext y
  unfold chartPushed
  rw [hρ_empty]; ring

/-- The chart-based inner product reduces to a finite sum over the active set. -/
private theorem wkpInnerChartL2_eq_finsum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u v : M → ℝ) :
    wkpInnerChartL2 (n := n) (M := M) g k u v =
      ∑ α ∈ (activeChartSupp_finite (n := n) (M := M)).toFinset,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α v)
          (chartTargetEuclid (n := n) (M := M) α) := by
  unfold wkpInnerChartL2
  apply tsum_eq_sum
  intro α hα
  have hα_off : α ∉ activeChartSupp (n := n) (M := M) := fun hαS =>
    hα ((Set.Finite.mem_toFinset _).mpr hαS)
  rw [chartPushed_eq_zero_off_activeChartSupp (n := n) (M := M) α hα_off u]
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2
  refine Finset.sum_eq_zero ?_
  intro j _
  refine Finset.sum_eq_zero ?_
  intro β _
  have hΩ_open : IsOpen
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  have h_iter_zero :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_ae_zero_of_input_ae_zero
      (d := n) (p := (2 : ℝ≥0∞)) (by norm_num) hΩ_open j β
      (Filter.Eventually.of_forall (fun _ => rfl))
  rw [show (∫ x in
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
        (d := n) (2 : ℝ≥0∞) j β
        (fun _ => (0 : ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) x *
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
        (d := n) (2 : ℝ≥0∞) j β
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α v)
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) x) =
      ∫ x in
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α), 0 by
    refine integral_congr_ae ?_
    filter_upwards [h_iter_zero] with x hx
    rw [hx]; ring]
  simp

/-- The chart-based norm-squared (real-valued) reduces to a finite sum
over the active set. -/
private theorem wkpNormChartL2Sq_toReal_eq_finsum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {u : M → ℝ} (hu : MemWkpChart (n := n) (M := M) g k 2 u) :
    (wkpNormChartL2Sq (n := n) (M := M) g k u).toReal =
      ∑ α ∈ (activeChartSupp_finite (n := n) (M := M)).toFinset,
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α)).toReal := by
  classical
  unfold wkpNormChartL2Sq
  have h_zero_outside : ∀ α : M,
      α ∉ (activeChartSupp_finite (n := n) (M := M)).toFinset →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
        (d := n) k
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u)
        (chartTargetEuclid (n := n) (M := M) α) = 0 := by
    intro α hα
    have hα_off : α ∉ activeChartSupp (n := n) (M := M) := fun hαS =>
      hα ((Set.Finite.mem_toFinset _).mpr hαS)
    rw [chartPushed_eq_zero_off_activeChartSupp (n := n) (M := M) α hα_off u]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_zero_fun_zero
      (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  have h_finiteness : ∀ α ∈ (activeChartSupp_finite (n := n) (M := M)).toFinset,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace
        (d := n) k
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u)
        (chartTargetEuclid (n := n) (M := M) α) ≠ ⊤ := by
    intro α _
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_lt_top_of_memWkpHalfSpace
      (d := n) (hu α)).ne
  rw [tsum_eq_sum h_zero_outside]
  rw [ENNReal.toReal_sum h_finiteness]

/-- The diagonal inner product reduces to a finite sum over the active set. -/
private theorem wkpInnerChartL2_self_eq_finsum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u : M → ℝ) :
    wkpInnerChartL2 (n := n) (M := M) g k u u =
      ∑ α ∈ (activeChartSupp_finite (n := n) (M := M)).toFinset,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace
          (d := n) k
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) :=
  wkpInnerChartL2_eq_finsum (n := n) (M := M) g k u u

/-- The norm-inner identity on `WkpChartL2`. -/
private theorem wkpChartL2_norm_sq_eq_inner
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u : WkpChartL2 (n := n) (M := M) g k) :
    ‖u‖ ^ 2 = wkpInnerChartL2 (n := n) (M := M) g k
      (wkpChartL2Fun u) (wkpChartL2Fun u) := by
  classical
  have hu_mem := wkpChartL2Fun_memWkpChart u
  have h_chartL2_sq :
      (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)) ^ (2 : ℕ) =
        wkpNormChartL2Sq (n := n) (M := M) g k (wkpChartL2Fun u) := by
    unfold wkpNormChartL2
    rw [show ((wkpNormChartL2Sq (n := n) (M := M) g k (wkpChartL2Fun u)) ^
        ((1 : ℝ) / 2)) ^ (2 : ℕ) =
        (wkpNormChartL2Sq (n := n) (M := M) g k (wkpChartL2Fun u)) ^
        (((1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) by
      rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]]
    rw [show ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 by norm_num]
    rw [ENNReal.rpow_one]
  have h_norm_sq :
      ‖u‖ ^ 2 = (wkpNormChartL2Sq (n := n) (M := M) g k (wkpChartL2Fun u)).toReal := by
    change (wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)).toReal ^ 2 = _
    rw [show ((wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)).toReal ^ 2 : ℝ) =
        ((wkpNormChartL2 (n := n) (M := M) g k (wkpChartL2Fun u)) ^ (2 : ℕ)).toReal from by
      rw [ENNReal.toReal_pow]]
    rw [h_chartL2_sq]
  rw [h_norm_sq]
  rw [wkpNormChartL2Sq_toReal_eq_finsum (n := n) (M := M) g hu_mem]
  rw [wkpInnerChartL2_self_eq_finsum (n := n) (M := M) g k (wkpChartL2Fun u)]
  refine Finset.sum_congr rfl ?_
  intro α _
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormL2SqHalfSpace_toReal_eq_wkpInnerL2HalfSpace_self
    (d := n) (hu_mem α)

/-- Inner product is symmetric. -/
private theorem wkpInnerChartL2_apply_comm
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u v : WkpChartL2 (n := n) (M := M) g k) :
    @inner ℝ _ _ v u = @inner ℝ _ _ u v := by
  change wkpInnerChartL2 (n := n) (M := M) g k _ _ = _
  rw [wkpInnerChartL2_comm (n := n) (M := M) g k (wkpChartL2Fun v) (wkpChartL2Fun u)]
  rfl

/-- Inner product is bilinear in the first slot (additivity). -/
private theorem wkpInnerChartL2_apply_add_left
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u v w : WkpChartL2 (n := n) (M := M) g k) :
    @inner ℝ _ _ (u + v) w = @inner ℝ _ _ u w + @inner ℝ _ _ v w := by
  classical
  have hu_mem := wkpChartL2Fun_memWkpChart u
  have hv_mem := wkpChartL2Fun_memWkpChart v
  have hw_mem := wkpChartL2Fun_memWkpChart w
  change wkpInnerChartL2 (n := n) (M := M) g k _ _ = _
  rw [wkpChartL2Fun_add]
  rw [wkpInnerChartL2_eq_finsum (n := n) (M := M) g k _ (wkpChartL2Fun w)]
  rw [show (@inner ℝ _ _ u w + @inner ℝ _ _ v w) =
      wkpInnerChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) (wkpChartL2Fun w) +
      wkpInnerChartL2 (n := n) (M := M) g k (wkpChartL2Fun v) (wkpChartL2Fun w) from rfl]
  rw [wkpInnerChartL2_eq_finsum (n := n) (M := M) g k (wkpChartL2Fun u) (wkpChartL2Fun w)]
  rw [wkpInnerChartL2_eq_finsum (n := n) (M := M) g k (wkpChartL2Fun v) (wkpChartL2Fun w)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro α _
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace_add_left
    (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu_mem α) (hv_mem α) (hw_mem α)

/-- Inner product is bilinear in the first slot (scalar multiplication). -/
private theorem wkpInnerChartL2_apply_smul_left
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (u v : WkpChartL2 (n := n) (M := M) g k) (r : ℝ) :
    @inner ℝ _ _ (r • u) v = r * @inner ℝ _ _ u v := by
  classical
  have hu_mem := wkpChartL2Fun_memWkpChart u
  change wkpInnerChartL2 (n := n) (M := M) g k _ _ = _
  rw [wkpChartL2Fun_smul]
  rw [show (r * @inner ℝ _ _ u v) =
      r * wkpInnerChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) (wkpChartL2Fun v) from rfl]
  rw [wkpInnerChartL2_eq_finsum (n := n) (M := M) g k _ (wkpChartL2Fun v)]
  rw [wkpInnerChartL2_eq_finsum (n := n) (M := M) g k (wkpChartL2Fun u) (wkpChartL2Fun v)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro α _
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpInnerL2HalfSpace_smul_left
    (d := n) (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    _ (hu_mem α) r

/-- The `InnerProductSpace ℝ` instance on `WkpChartL2 g k` (compact `M`). -/
instance instInnerProductSpaceRealWkpChartL2
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    InnerProductSpace ℝ (WkpChartL2 (n := n) (M := M) g k) where
  norm_sq_eq_re_inner u := by
    change ‖u‖ ^ 2 =
      wkpInnerChartL2 (n := n) (M := M) g k (wkpChartL2Fun u) (wkpChartL2Fun u)
    exact wkpChartL2_norm_sq_eq_inner (n := n) (M := M) g k u
  conj_inner_symm u v := by
    change (@inner ℝ _ _ v u) = (@inner ℝ _ _ u v)
    exact wkpInnerChartL2_apply_comm (n := n) (M := M) g k u v
  add_left u v w := wkpInnerChartL2_apply_add_left (n := n) (M := M) g k u v w
  smul_left u v r := by
    change @inner ℝ _ _ (r • u) v = r * @inner ℝ _ _ u v
    exact wkpInnerChartL2_apply_smul_left (n := n) (M := M) g k u v r

/-- The `InnerProductSpace ℝ` instance on `WkpChartL2Quot g k` (compact `M`),
inherited via `SeparationQuotient.instInnerProductSpace`. -/
instance instInnerProductSpaceRealWkpChartL2Quot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) :
    InnerProductSpace ℝ (WkpChartL2Quot (n := n) (M := M) g k) :=
  inferInstanceAs (InnerProductSpace ℝ
    (SeparationQuotient (WkpChartL2 (n := n) (M := M) g k)))

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
