import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.SmoothMulH1Compl
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PerChartWitness

/-!
# Manifold-side Lp decomposition of `fHLeibnizResidualLp`

For a closed Riemannian manifold `(M, g)` and chart point `α`, this module
exhibits the Lp-class identity expressing the residual

```
fHLeibnizResidualLp g α u_h = -2 g(∇ρα, ∇u_h) - Δρα · u_h
```

in terms of `(1-Δ_g)`-preimage data: namely

```
fHLeibnizResidualLp = preimage⟨smoothMulH1Compl ρα u_h⟩
                       - smoothMulLp ρα (preimage⟨u_h⟩).
```

The identity packages the manifold-side Leibniz rule
`Δ_g(ρα u_h) = ρα Δ_g u_h + 2 g(∇ρα, ∇u_h) + u_h Δ_g ρα` at the `Lp` class
level, using

* `laplacianDomain_preimage_smoothMulH1Compl` — the preimage identity
  `preimage⟨smoothMulH1Compl ρα u_h⟩ = fHLeibnizGeneral g ρα u_h hu_dom`.

* `fHLeibnizGeneral` definitional unfolding into
  `smoothMulLp ρα (preimage⟨u_h⟩) + fHLeibnizGeneralResidualCLM g ρα u_h`.

* `fHLeibnizGeneralResidualCLM g (chartAtlasPOU I M α) u_h =
  fHLeibnizResidualLp g α u_h` (definitionally, since the relevant
  `smoothLaplacianBundle g (chartAtlasPOU I M α)` equals
  `laplacianOfChartPOU g α`).

## Main result

* `fHLeibnizResidualLp_eq_preimageDiff` — for `u_h ∈ laplacianDomain g`:

  ```
  fHLeibnizResidualLp g α u_h
    = preimage⟨smoothMulH1Compl ρα u_h, smoothMulH1Compl_mem_laplacianDomain⟩
       - smoothMulLp ρα (preimage⟨u_h, hu_dom⟩).
  ```

## Connection to `MemW1p 2 fChartResidual chartTarget` discharge

The chart-pulled-raw `fChartResidual` is
`chartPushedRawLpFromLp(fHLeibnizResidualLp).coeFn`. By the decomposition
identity above and additivity of `chartPushedRawLpFromLp` at the `coeFn`
level (in `DiffChartBilinearH1ComplFromDomainPow.lean`),

```
fChartResidual =ᵃᵉ
    chartPushedRawLpFromLp(preimage⟨smoothMulH1Compl ρα u_h⟩).coeFn
       - chartPushedRawLpFromLp(smoothMulLp ρα (preimage⟨u_h⟩)).coeFn.
```

The second summand has `MemW1p 2 chartTarget` regularity for
`u_h ∈ laplacianDomainPow g 2` via:

* `laplacianDomainPow_two_h2_plus_rhs_h2.2.1` (the `Lp`-side preimage
  `preimage⟨u_h⟩.coeFn ∈ MemWkpChart g 2 2`).

* `MemWkpChart_smooth_mul` (smooth-bounded multiplication closure of
  `MemWkpChart g 2 2`), giving `ρα · preimage⟨u_h⟩.coeFn ∈ MemWkpChart g 2 2`.

* `memW1p_chartPushedRaw_pou_mul_of_memWkpChart` (the existing chart-pulled
  weighted bridge to `MemW1p 2 chartTarget`).

The first summand `chartPushedRawLpFromLp(preimage⟨smoothMulH1Compl ρα u_h⟩)`
would require `preimage⟨smoothMulH1Compl ρα u_h⟩.coeFn ∈ MemWkpChart g 1 2`, which
in turn requires `smoothMulH1Compl ρα u_h ∈ laplacianDomainPow g 2` (iterated
closure of the Laplacian domain). This iterated closure is not automatic
from `u_h ∈ laplacianDomainPow g 2` alone: it requires the chart-Sobolev
third-order control on `u_h` arising from differentiating the Leibniz
expansion of `(1-Δ_g)(ρα u_h)`. The remaining infrastructure for this
iterated closure is the subject of follow-up work.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ResidualLpDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The Leibniz cross-term CLM and the residual Lp-class agree on
`u_h : H1Compl g`, for `φ := chartAtlasPOU I M α`. -/
lemma fHLeibnizGeneralResidualCLM_eq_fHLeibnizResidualLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    fHLeibnizGeneralResidualCLM (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  classical
  rw [fHLeibnizGeneralResidualCLM_apply]
  rfl

/-- **The manifold-side Lp decomposition for `fHLeibnizResidualLp`**.

For `u_h ∈ laplacianDomain g`,

```
preimage⟨smoothMulH1Compl ρα u_h⟩
  = smoothMulLp ρα (preimage⟨u_h⟩) + fHLeibnizGeneralResidualCLM g ρα u_h.
```

This is the preimage identity unfolded; it underlies the
identification of `fHLeibnizResidualLp` with the difference of two
`(1-Δ_g)`-preimages. -/
theorem preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
          smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom⟩ =
      smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) +
        fHLeibnizGeneralResidualCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h := by
  classical
  have h_preimage_smoothMulH1Compl :=
    laplacianDomain_preimage_smoothMulH1Compl (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom
  unfold fHLeibnizGeneral at h_preimage_smoothMulH1Compl
  have h_diff_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq] at h_preimage_smoothMulH1Compl
  exact h_preimage_smoothMulH1Compl

/-- **Rearranged form of the decomposition**: for `u_h ∈ laplacianDomain g`,

```
fHLeibnizGeneralResidualCLM g (chartAtlasPOU I M α) u_h
  = preimage⟨smoothMulH1Compl ρα u_h⟩ - smoothMulLp ρα (preimage⟨u_h⟩).
```
-/
theorem fHLeibnizGeneralResidualCLM_eq_preimageDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    fHLeibnizGeneralResidualCLM (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h =
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom⟩ -
        smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) := by
  classical
  have h := preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual
    (I := I) (M := M) g α hu_dom
  rw [h]
  abel

end ResidualLpDecomposition
end Laplacian
end Analysis
end DifferentialGeometry

end
