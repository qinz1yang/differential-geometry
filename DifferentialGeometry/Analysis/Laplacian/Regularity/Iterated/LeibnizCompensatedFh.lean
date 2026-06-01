import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.CLM
import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothScalar.MulLp
import DifferentialGeometry.Analysis.Laplacian.Operator.Operator
import DifferentialGeometry.Geometry.Laplacian

/-!
# The Leibniz-compensated `L²` class on the chart at `α`

For a closed Riemannian manifold `(M, g)` and a chart point `α : M`, this
file constructs the `L²` class

`f_h := ρα · (1 - Δ_g) u_h - 2 g(grad ρα, grad u_h) - u_h · Δ_g ρα`

associated with an element `u_h` of the variational Laplacian's domain.
Here `ρα := chartAtlasPOU I M α` is the canonical smooth partition-of-unity
weight at `α`, `(1 - Δ_g) u_h := H1ComplToLp u_h - laplacianOp ⟨u_h, _⟩` is the
inhomogeneous right-hand side associated with `u_h`, and `Δ_g ρα` is the
classical chart-local Laplace-Beltrami operator applied to the smooth weight.

The construction uses three previously built building blocks:

* `gradInnerCLM g ρα : H1Compl g →L[ℝ] Lp ℝ 2 μ_g` — the H¹-continuous extension
  of the smooth pointwise gradient inner product `x ↦ g(grad ρα x, grad v x)`.
* `smoothMulLp g φ : Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g` — pointwise multiplication of
  an `Lp` element by a smooth bounded function.
* `laplacianOp` and the smooth bridge `laplacianOp_smoothToH1Compl` — the
  variational Laplacian on its domain, with a known `Lp`-class for smooth
  inputs.

## Smooth-case identity

For `v : SmoothScalar g`, the canonical inclusion `smoothToH1Compl g v` lies in
`laplacianDomain g`, and `f_h` reduces to the explicit `Lp` arithmetic

```
fHLeibniz g α (smoothToH1Compl g v) _
  = smoothMulLp g ρα (smoothToLp g v.oneSubLapClassical)
    - (2 : ℝ) • gradInnerSmooth g ρα v
    - smoothMulLp g (laplacianOfChartPOU α) (smoothToLp g v),
```

where `v.oneSubLapClassical = v - Δ_g v` is the smooth `(1 - Δ_g) v`. This is
the rigorous content of "by Leibniz" in the H¹ analysis of the regularity step:
on the dense smooth subspace, the chart-pushed elliptic right-hand side is the
classically computed `(1 - Δ_g)(ρα · v)` expressed via the product rule in the
combination above. The smooth-case identity is proved by direct rewriting
using the smooth-bridge lemmas `H1ComplToLp_smoothToH1Compl`,
`laplacianOp_smoothToH1Compl`, and `gradInnerCLM_smoothToH1Compl`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The classical Laplace–Beltrami operator applied to the canonical
partition-of-unity weight at `α`, packaged as a bundled smooth map. -/
noncomputable def laplacianOfChartPOU (g : SmoothRiemannianMetric I M) (α : M) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff,
    Δ_g_contMDiff (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff⟩

@[simp] lemma laplacianOfChartPOU_apply
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x =
      Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x := rfl

/-- The Leibniz-compensated `L²` class associated with an element `u_h` of the
variational Laplacian's domain at the chart point `α`. -/
noncomputable def fHLeibniz (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
    - (2 : ℝ) • gradInnerCLM (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h
    - smoothMulLp (I := I) (M := M) g
        (laplacianOfChartPOU (I := I) (M := M) g α)
        (H1ComplToLp (I := I) (M := M) g u_h)

/-- Unfolding identity for the Leibniz-compensated right-hand side. -/
lemma fHLeibniz_def (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    fHLeibniz (I := I) (M := M) g α u_h hu_h =
      smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
        - (2 : ℝ) • gradInnerCLM (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h
        - smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (H1ComplToLp (I := I) (M := M) g u_h) := rfl

/-- The smooth-case identity: for `v : SmoothScalar g`, the Leibniz-compensated
right-hand side equals the explicit `Lp` arithmetic combination obtained by
substituting the smooth bridges for each building block. -/
theorem fHLeibniz_smoothToH1Compl (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    fHLeibniz (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v)
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
        - (2 : ℝ) • gradInnerSmooth (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v
        - smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (smoothToLp (I := I) (M := M) g v) := by
  rw [fHLeibniz_def]
  have h_oneSubLap :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) -
        laplacianOp (I := I) (M := M) g
          ⟨smoothToH1Compl (I := I) (M := M) g v,
            smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v⟩ =
      smoothToLp (I := I) (M := M) g v.oneSubLapClassical := by
    rw [H1ComplToLp_smoothToH1Compl, laplacianOp_smoothToH1Compl]
    abel
  rw [h_oneSubLap]
  rw [gradInnerCLM_smoothToH1Compl]
  rw [H1ComplToLp_smoothToH1Compl]

example (g : SmoothRiemannianMetric I M) (α : M) :
    C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α

example (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  fHLeibniz (I := I) (M := M) g α u_h hu_h

end Laplacian
end Analysis
end DifferentialGeometry

end
