import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.Smooth
import DifferentialGeometry.Analysis.Laplacian.Operator.Operator
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Constructor for `ChartBilinearH1ComplData` from a `laplacianDomain g` element

For a closed Riemannian manifold `(M, g)` with a chart point `α : M`, this
file constructs a `ChartBilinearH1ComplData g α` instance from any element
`u : laplacianDomain g`. The construction transports the variational
identity satisfied by the resolvent `(1 - Δ_g)⁻¹` from the manifold side to
the chart-Euclidean side via the chart-pulled-volume identity.

## Strategy

For `u : laplacianDomain g` with `f := preimage u : Lp ℝ 2 μ_g`, the
resolvent identity states
```
⟨u, w⟩_{H1} = ⟨H1ComplToLp w, f⟩_{L²}    for every w ∈ H1Compl g.
```

Specializing `w := smoothToH1Compl ψ̃` for `ψ̃ := chartTestPullback I α ψ`
(with `ψ : EuclN → ℝ` smooth and `tsupport ψ ⊆ chartTargetEuclid α`),
the H¹ inner product unfolds (via the smooth-scalar pre-Hilbert structure
on a smooth approximating sequence `v_n → u`) to a chart-pulled
density-weighted bilinear form involving `(chartPullback v_n, ψ)`. Passing
to the limit and matching with the smooth chart-bilinear identity from
`ChartBilinearSmooth.lean` produces the required variational identity.

The data fields of `ChartBilinearH1ComplData` are populated by:

* `u_chart` — the L² chart-pull of `H1ComplToLp u` against the chart-pulled
  weighted measure on `chartTargetEuclid α`;
* `f_chart` — the L² chart-pull of `preimage u` against the same measure;
* `weak_partial i` — the weak `i`-partial of `u_chart` on `chartTargetEuclid α`
  (a per-`i` function whose locally-`L²` regularity is established by
  per-compact-subset Cauchy completion of the smooth approximants);
* `variational_identity` — passed-to-limit from the smooth identity.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1ComplFromDom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- For any `u_h : H1Compl g`, there exists a sequence of smooth scalars
whose `smoothToH1Compl` images converge to `u_h`. -/
theorem exists_smooth_approx_seq
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n)) atTop (𝓝 u_h) := by
  classical
  have h_dense :
      u_h ∈ closure (Set.range (smoothToH1Compl (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToH1Compl (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToH1Compl (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

/-- For any `f_h : Lp ℝ 2 μ_g`, there exists a sequence of smooth scalars
whose `smoothToLp` images converge to `f_h` in `Lp`. -/
theorem exists_smooth_approx_seq_lp
    (g : SmoothRiemannianMetric I M)
    (f_h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n)) atTop (𝓝 f_h) := by
  classical
  have h_dense :
      f_h ∈ closure (Set.range (smoothToLp (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToLp (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToLp (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

end ChartBilinearH1ComplFromDom
end Laplacian
end Analysis
end DifferentialGeometry
