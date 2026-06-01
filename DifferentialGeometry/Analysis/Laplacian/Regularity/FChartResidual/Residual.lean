import DifferentialGeometry.Analysis.Laplacian.Regularity.FChartResidual.MemW1pResidualFull

/-!
# Reformulations of the `MemW1p 2` discharge for `fChartResidual`

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, and an element
`u_h ∈ laplacianDomainPow g 2`, this module packages alternative
reformulations of the chart-target `MemW1p 2` discharge of `fChartResidual
g α u_h` from `MemW1pFChartResidualFull`.

The reformulations expose the chart-bilinear analytical content of the
discharge in a single packaged form, parametrized by the chart-W^{1,2}-
Cauchy / identification hypothesis on the smooth-approximator residuals.

## Main results

* `fChartResidual_memW1p_from_smoothApprox_cauchy_identification` — the
  packaged form of the `MemW1p 2` discharge from the chart-target
  W^{1,2}-Cauchy + identification hypothesis on the smooth-approximator
  residuals.

## Notes on the chart-bilinear analytical content

The chart-target W^{1,2}-Cauchy hypothesis on the smooth-approximator
residuals captures the standard PDE chart-bilinear continuity:

```
‖smoothFChartResidual g α v‖_{W^{1,2}(chartTarget)}
  ≤ C(g, α) · ‖v‖_{W^{2,2}_chart(M)},
```

for a constant `C(g, α)` depending only on `g`, the chart point `α`, and
sup-norms of the smooth chart coefficients `ρα`, `∇ρα`, `Δρα` on the
closed manifold `M`. Combined with linearity of the smooth-residual
operator and the chart-W^{2,2}-Cauchy property of the approximator
sequence (`smoothApproxSeq_wkpNormChart_diff_le`), this yields the
chart-W^{1,2}-Cauchy property.

The identification hypothesis identifies the chart-W^{1,2}-limit with
`fChartResidual g α u_h` via the chart-Lp continuity of the residual
operator `fHLeibnizResidualLp` (linear combination of `gradInnerCLM` and
`smoothMulLp`, both continuous on `H1Compl` / `Lp`) and the
`chartPushedRawLpFromLp_tendsto` continuity bridge.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace FChartResidual

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
open DifferentialGeometry.Analysis.Laplacian.MemW1pFChartResidualFull
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For each `n`, the chart-pulled smooth residual of the `n`-th approximator
is in `MemW1p 2 chartTargetEuclid α`. -/
theorem smoothApproxSeq_smoothFChartResidual_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (smoothFChartResidual (I := I) (M := M) g α
        (smoothApproxSeq (I := I) (M := M) g hu_h n))
      (chartTargetEuclid (I := I) (M := M) α) :=
  memW1p_fChartResidual_smoothToH1Compl (I := I) (M := M) g α
    (smoothApproxSeq (I := I) (M := M) g hu_h n)

/-- For each `n`, the chart-pulled smooth residual is in `MemWkp 1 2
chartTargetEuclid α` (equivalent reformulation of `MemW1p 2`). -/
theorem smoothApproxSeq_smoothFChartResidual_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (smoothFChartResidual (I := I) (M := M) g α
        (smoothApproxSeq (I := I) (M := M) g hu_h n))
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
  exact smoothApproxSeq_smoothFChartResidual_memW1p (I := I) (M := M) g α hu_h n

/-- **Packaged `MemW1p 2` discharge of `fChartResidual g α u_h`** from the
chart-W^{1,2}-Cauchy and identification hypotheses on the smooth-
approximator residual sequence `smoothApproxSeq`.

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, and any
`u_h ∈ laplacianDomainPow g 2`, the chart-pulled residual `fChartResidual
g α u_h` lies in `MemW1p 2 chartTargetEuclid α` whenever the chart-target
`wkpNorm 1 2`-Cauchy property holds for `smoothFChartResidual g α
(smoothApproxSeq g hu_h n)` and the identification hypothesis identifies
the chart-W^{1,2}-limit with `fChartResidual g α u_h` (a.e. on
`volume.restrict chartTarget`).

The two hypotheses capture the chart-bilinear continuity analytical
content:

* The chart-target `wkpNorm 1 2`-Cauchy property follows from the
  chart-W^{2,2}-Cauchy property of the approximator sequence
  (`smoothApproxSeq_wkpNormChart_diff_le`) and the bilinear continuity
  bound for the smooth-residual operator (chart-W^{2,2} input →
  chart-W^{1,2} output).

* The identification hypothesis follows from the chart-Lp continuity of
  the residual operator `fHLeibnizResidualLp` and the
  `chartPushedRawLpFromLp_tendsto` continuity bridge. -/
theorem fChartResidual_memW1p_from_smoothApprox_cauchy_identification
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y =>
          smoothFChartResidual (I := I) (M := M) g α
            (smoothApproxSeq (I := I) (M := M) g hu_h m) y -
          smoothFChartResidual (I := I) (M := M) g α
            (smoothApproxSeq (I := I) (M := M) g hu_h n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y =>
            smoothFChartResidual (I := I) (M := M) g α
              (smoothApproxSeq (I := I) (M := M) g hu_h n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        fChartResidual (I := I) (M := M) g α u_h) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  fChartResidual_memW1p_unconditional (I := I) (M := M) g α hu_h
    h_cauchy h_identification

end FChartResidual
end Laplacian
end Analysis
end DifferentialGeometry

end
