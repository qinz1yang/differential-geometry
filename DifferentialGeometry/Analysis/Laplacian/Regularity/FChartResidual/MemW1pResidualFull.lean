import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplResidualMemW1p
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplResidual
import DifferentialGeometry.Analysis.Laplacian.Regularity.FChartResidual.MemW1pResidual
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifoldHigherOrder

/-!
# Smooth-density-based `MemW1p 2` discharge for `fChartResidual`

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, and an element
`u_h ∈ laplacianDomainPow g 2`, this file packages the chart-pulled residual
`MemW1p 2 chartTargetEuclid α` discharge into a form parametrized by the
smooth-approximator chart-W^{1,2}-Cauchy / identification hypothesis. The
smooth-density theorem `contMDiff_dense_in_WkpChart_k` supplies the
chart-W^{2,2}-converging smooth approximator sequence; the residual
chart-target W^{1,2}-Cauchy property is then a bilinear-continuity statement
of the smooth-residual operator from chart-W^{2,2} to chart-target W^{1,2}.

## Key infrastructure

* `contMDiff_dense_in_WkpChart_k` (from `Sobolev.Approximation`): for every
  `u : M → ℝ` in `MemWkpChart g k p`, the smooth functions are `wkpNormChart`-
  dense.
* `memW1p_fChartResidual_of_wkpNorm_cauchy_identification` (from
  `DiffChartBilinearH1ComplResidual`): for a smooth approximator
  sequence satisfying the chart-W^{1,2}-Cauchy + identification hypothesis,
  the residual is in `MemW1p 2 chartTargetEuclid α`.
* `memW1p_fChartResidual_smoothToH1Compl` (from
  `DiffChartBilinearH1ComplResidualMemW1p`): unconditional smooth-case
  discharge.

## Main results

* `exists_smoothApprox_chartW22` — for `u_h ∈ laplacianDomainPow g 2` and any
  `ε > 0`, there exists a smooth scalar `v` with `wkpNormChart g 2 2`-
  approximation level `ε` to the canonical function representative of `u_h`.
* `smoothApproxSeq` — the chosen smooth approximator sequence at level `1/(n+1)`.
* `smoothApproxSeq_wkpNormChart_le` — the per-`n` approximation bound.
* `smoothApproxSeq_wkpNormChart_diff_le` — the chart-W^{2,2}-Cauchy property
  of the approximating sequence.
* `fChartResidual_memW1p_unconditional` — the headline `MemW1p 2` discharge
  of `fChartResidual g α u_h` from the chart-target W^{1,2}-Cauchy +
  identification hypothesis on the smooth-residual sequence applied to
  `smoothApproxSeq`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace MemW1pFChartResidualFull

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For `u_h ∈ laplacianDomainPow g 2`, a smooth approximator at any `ε > 0`
in chart-W^{2,2} norm. -/
theorem exists_smoothApprox_chartW22
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : SmoothScalar g, wkpNormChart (I := I) (M := M) g 2 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        v.toFun x) ≤ ENNReal.ofReal ε := by
  classical
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  have h_u_mem : MemWkpChart (I := I) (M := M) g 2 2 u :=
    (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h).1.1
  obtain ⟨w, hw_smooth, hw_le⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_dense_in_WkpChart_k
      (I := I) (M := M) g 2 (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h_u_mem hε
  refine ⟨⟨w, hw_smooth⟩, ?_⟩
  exact hw_le

/-- For each `n : ℕ`, choose a smooth approximator at level `1/(n+1)`. -/
noncomputable def smoothApproxSeq
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) : SmoothScalar g :=
  (exists_smoothApprox_chartW22 (I := I) (M := M) g hu_h
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose

/-- The chart-W^{2,2}-norm approximation bound for the approximator sequence. -/
theorem smoothApproxSeq_wkpNormChart_le
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) :
    wkpNormChart (I := I) (M := M) g 2 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  (exists_smoothApprox_chartW22 (I := I) (M := M) g hu_h
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose_spec

/-- The chart-W^{2,2}-Cauchy property of the approximating sequence. -/
theorem smoothApproxSeq_wkpNormChart_diff_le
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m n : ℕ) :
    wkpNormChart (I := I) (M := M) g 2 2
      (fun x => (smoothApproxSeq (I := I) (M := M) g hu_h m).toFun x -
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) ≤
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  classical
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  set vm : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h m
  set vn : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h n
  have h_decomp : (fun x => vm.toFun x - vn.toFun x) =
      (fun x => (u x - vn.toFun x) - (u x - vm.toFun x)) := by
    funext x; ring
  rw [h_decomp]
  have h_u_mem : MemWkpChart (I := I) (M := M) g 2 2 u :=
    (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h).1.1
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_smooth_vm : MemWkpChart (I := I) (M := M) g 2 2 vm.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one 2 vm.smooth
  have h_smooth_vn : MemWkpChart (I := I) (M := M) g 2 2 vn.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one 2 vn.smooth
  have h_u_diff_vm : MemWkpChart (I := I) (M := M) g 2 2 (fun x => u x - vm.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g hp_one h_u_mem h_smooth_vm
  have h_u_diff_vn : MemWkpChart (I := I) (M := M) g 2 2 (fun x => u x - vn.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g hp_one h_u_mem h_smooth_vn
  have h_split : (fun x : M => (u x - vn.toFun x) - (u x - vm.toFun x)) =
      (fun x : M => (u x - vn.toFun x) + (-1 : ℝ) * (u x - vm.toFun x)) := by
    funext x; ring
  rw [h_split]
  have h_neg_smul :
      wkpNormChart (I := I) (M := M) g 2 2
        (fun x => (-1 : ℝ) * (u x - vm.toFun x)) =
      ‖(-1 : ℝ)‖ₑ * wkpNormChart (I := I) (M := M) g 2 2 (fun x => u x - vm.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_const_smul
      (I := I) (M := M) g hp_one (-1 : ℝ) h_u_diff_vm
  have h_neg_one_norm : ‖(-1 : ℝ)‖ₑ = 1 := by
    simp [enorm]
  rw [h_neg_one_norm, one_mul] at h_neg_smul
  have h_u_diff_vm_neg : MemWkpChart (I := I) (M := M) g 2 2
      (fun x => (-1 : ℝ) * (u x - vm.toFun x)) := by
    have h_eq : (fun x : M => (-1 : ℝ) * (u x - vm.toFun x)) =
        (fun x => -(u x - vm.toFun x)) := by funext x; ring
    rw [h_eq]
    exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_neg
      (I := I) (M := M) g hp_one h_u_diff_vm
  have h_add :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_add_le (I := I) (M := M)
      g (k := 2) (p := 2) hp_one h_u_diff_vn h_u_diff_vm_neg
  rw [h_neg_smul] at h_add
  have h_bound1 : wkpNormChart (I := I) (M := M) g 2 2 (fun x => u x - vn.toFun x) +
        wkpNormChart (I := I) (M := M) g 2 2 (fun x => u x - vm.toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
    add_le_add
      (smoothApproxSeq_wkpNormChart_le (I := I) (M := M) g hu_h n)
      (smoothApproxSeq_wkpNormChart_le (I := I) (M := M) g hu_h m)
  have h_comm : ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((m : ℝ) + 1)) =
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [add_comm]
  exact le_trans h_add (le_of_le_of_eq h_bound1 h_comm)

/-- **Headline discharge (from bilinear continuity hypothesis).**

For `u_h ∈ laplacianDomainPow g 2` and a chart-target W^{1,2} bilinear
continuity hypothesis on the smooth-residual operator applied to the
chart-W^{2,2} smooth-density approximator sequence `smoothApproxSeq`, the
chart-pulled residual `fChartResidual g α u_h` is in `MemW1p 2 chartTargetEuclid α`.

The bilinear continuity hypothesis (chart-target W^{1,2}-Cauchy + identification)
captures the elliptic regularity content via the smooth-density approximation. -/
theorem fChartResidual_memW1p_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y =>
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (smoothApproxSeq (I := I) (M := M) g hu_h m) y -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (smoothApproxSeq (I := I) (M := M) g hu_h n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y =>
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
              (I := I) (M := M) g α (smoothApproxSeq (I := I) (M := M) g hu_h n) y -
            F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.memW1p_fChartResidual_of_wkpNorm_cauchy_identification
    (I := I) (M := M) g α hu_h (smoothApproxSeq (I := I) (M := M) g hu_h)
    h_cauchy h_identification

end MemW1pFChartResidualFull
end Laplacian
end Analysis
end DifferentialGeometry

end
