import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.LiftedMetricSmoothness
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Geometry.Hessian
import DifferentialGeometry.Geometry.Curvature.Riemann
import DifferentialGeometry.Geometry.Curvature.Ricci
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic

/-!
# Chart-pullback naturality of `chartBasisVecFiber` under the universal cover

The chart-local frame vectors `chartBasisVecFiber α' i x'` on the universal
cover identify, under the projection `proj : UC M → M`, with the chart-local
frame vectors on the base manifold at the projected points.

Concretely, for `x' ∈ (coverChartAt α').source`,
```
chartBasisVecFiber α' i x' = chartBasisVecFiber (proj α') i (proj x')
```
viewed through the definitional identification
`TangentSpace I x' = E = TangentSpace I (proj x')`.

The proof unfolds `chartBasisVecFiber` to the inverse tangent trivialisation
applied to the fixed model-space basis vector, rewrites both sides through
`TangentBundle.symmL_trivializationAt_eq_core`, and concludes by
`uc_tangentBundleCore_coordChange_agree`.
-/

open Set Function Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Integral.Measure
  (SmoothRiemannianMetric chartBasisVecFiber chartModelBasis chartGramMatrix)
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartInvGramMatrix chartGramOnE chartChristoffel partialDeriv
   chartRiemannTensor chartRicciTensor)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

/-- **`chartBasisVecFiber` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, basis index `i`, and cover-point
`x' ∈ (chartAt H α').source` (equivalently `x' ∈ (coverChartAt α').source`,
since `chartAt H α' = coverChartAt α'` by the universal-cover charted-space
instance), the cover-side chart-basis fibre vector at `x'` (defined via the
inverse tangent trivialisation centred at `α'`) identifies with the
base-side chart-basis fibre vector at `proj x'` (defined via the inverse
tangent trivialisation centred at `proj α'`), through the definitional
identification of the tangent fibres with `E`.

Proof. Both sides unfold to `triv.symmL ℝ x (chartModelBasis E i)`,
the difference being whether `triv` is `trivializationAt E (TangentSpace I)`
on `UC M` (with base point `α'`, fibre point `x'`) or on `M` (with base
point `proj α'`, fibre point `proj x'`). On the chart source, the
membership hypothesis unfolds, via `coverChartAt_source_eq`, to give in
particular `proj x' ∈ (chartAt H (proj α')).source`. By
`TangentBundle.symmL_trivializationAt_eq_core`, each side equals the
corresponding `tangentBundleCore.coordChange` evaluated at the chart-source
membership; by `uc_tangentBundleCore_coordChange_agree`, the cover-side
`coordChange` agrees with the base-side `coordChange` at the projected
point. The result follows by applying both sides to `chartModelBasis E i`.
-/
theorem chartBasisVecFiber_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (i : Fin (Module.finrank ℝ E))
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source) :
    chartBasisVecFiber (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        α' i x' =
      chartBasisVecFiber (I := I) (M := M)
        (proj (X := M) α') i (proj (X := M) x') := by
  let _ := g
  have hx'_cover : x' ∈ (coverChartAt α').source := hx'
  have hx'_inter : x' ∈ (localSection (M := M) α').source ∩
      (localSection (M := M) α') ⁻¹' (chartAt H (proj α')).source := by
    have hsrc : ((coverChartAt α') :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection α').source ∩
          (localSection α') ⁻¹' (chartAt H (proj α')).source :=
      coverChartAt_source_eq α'
    rw [hsrc] at hx'_cover; exact hx'_cover
  obtain ⟨_hLSsrc, hLSchart⟩ := hx'_inter
  have hLS_x' : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  have hprojx'_chartM : proj x' ∈ (chartAt H (proj α')).source := by
    rw [Set.mem_preimage, hLS_x'] at hLSchart
    exact hLSchart
  have hLHS_symm :
      chartBasisVecFiber (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          α' i x'
        = (trivializationAt E (TangentSpace I :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
              → Type _) α').symmL ℝ x' (chartModelBasis E i) := by
    change (trivializationAt E (TangentSpace I :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
          → Type _) α').symm x' (chartModelBasis E i)
      = (trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            → Type _) α').symmL ℝ x' (chartModelBasis E i)
    rw [Bundle.Trivialization.symmL_apply]
  have hRHS_symm :
      chartBasisVecFiber (I := I) (M := M)
          (proj (X := M) α') i (proj (X := M) x')
        = (trivializationAt E (TangentSpace I : M → Type _)
            (proj α')).symmL ℝ (proj x') (chartModelBasis E i) := by
    change (trivializationAt E (TangentSpace I : M → Type _) (proj α')).symm
        (proj x') (chartModelBasis E i)
      = (trivializationAt E (TangentSpace I : M → Type _)
          (proj α')).symmL ℝ (proj x') (chartModelBasis E i)
    rw [Bundle.Trivialization.symmL_apply]
  rw [hLHS_symm, hRHS_symm]
  have hSymmL :
      ((trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            → Type _) α').symmL ℝ x' : E →L[ℝ] E)
        = ((trivializationAt E (TangentSpace I : M → Type _)
            (proj α')).symmL ℝ (proj x') : E →L[ℝ] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (b₀ := α') (b := x') hx',
        TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
          (b₀ := proj α') (b := proj x') hprojx'_chartM]
    exact uc_tangentBundleCore_coordChange_agree (I := I) α' x'
      ⟨hx', mem_chart_source H x'⟩
  have hAt := congrArg (fun L : E →L[ℝ] E => L (chartModelBasis E i)) hSymmL
  exact hAt

/-- **`chartGramMatrix` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, indices `i j : Fin (finrank ℝ E)`, and a
cover-point `x' ∈ (chartAt H α').source`, the Gram matrix entry of the
lifted metric on the universal cover equals the corresponding entry of
the base-side Gram matrix at the projected points.

Proof. Both sides unfold via `chartGramMatrix_apply` (a `rfl`-style simp
lemma) to inner products of the chart-basis fibre vectors. The lifted
metric is defined by `(liftedMetric g).inner x' v w = g.inner (proj x') v w`
(definitional from the `liftedMetric` `def`), and
`chartBasisVecFiber_lifted` identifies the cover-side basis fibre vector
at `x'` with the base-side one at `proj x'` (through the definitional
identification of the tangent fibre with `E`). Combining these three
rewrites yields the claim. -/
theorem chartGramMatrix_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (i j : Fin (Module.finrank ℝ E))
    (hx' : x' ∈ (chartAt H α').source) :
    chartGramMatrix
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' x' i j =
      chartGramMatrix (M := M) g
        (proj (X := M) α') (proj (X := M) x') i j := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' x' i j,
      DifferentialGeometry.Integral.Measure.chartGramMatrix_apply
        (I := I) (M := M) g (proj α') (proj x') i j]
  rw [chartBasisVecFiber_lifted (I := I) (M := M) g α' i x' hx',
      chartBasisVecFiber_lifted (I := I) (M := M) g α' j x' hx']
  rfl

/-- **Chart-basepoint coordinate identity under the universal cover.**

For any cover-point `x' ∈ (chartAt H α').source`, the extended-chart
coordinate of `x'` in the cover-chart at `α'` agrees with the
extended-chart coordinate of `proj x'` in the base-chart at `proj α'`.
Direct consequence of `uc_coverChartAt_extend_conjugacy` applied
pointwise at `x'`, identifying `extChartAt I α' = (coverChartAt α').extend I`
and using `localSection α' x' = proj x'`. -/
lemma extChartAt_proj_eq
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    extChartAt I α' x' = extChartAt I (proj (X := M) α') (proj (X := M) x') := by
  have hConj := (uc_coverChartAt_extend_conjugacy (I := I) α').1
  have := congrArg (fun f => f x') hConj
  simp only [Function.comp_apply] at this
  have hLS : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  change ((coverChartAt α').extend I) x' = _ at this
  rw [hLS] at this
  exact this

/-- **`chartChristoffel` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, lower indices `i j` and upper index `k`,
and a cover-point `x' ∈ (chartAt H α').source`, the chart-coordinate
Christoffel symbol of the lifted metric on the universal cover at the
chart-coordinate of `x'` equals the chart-coordinate Christoffel symbol
of the base metric at the chart-coordinate of `proj x'` in the base chart
at `proj α'`.

Proof outline:

1. By `extChartAt_proj_eq`, the two chart-coordinate base points agree:
   `extChartAt I α' x' = extChartAt I (proj α') (proj x')`. Call the common
   value `y₀`. After this rewrite both sides of the conclusion are evaluated
   at the same `y₀ : E`.

2. Unfolding `chartChristoffel_def`, the `chartInvGramMatrix` factor on each
   side becomes `chartInvGramMatrix (lifted/base metric) anchor manifold-point k l`
   where the manifold point is `(extChartAt I anchor).symm y₀` — which is
   `x'` on the cover side (by `extChartAt_left_inv` on the `coverChartAt`
   source) and `proj x'` on the base side (by `extend_left_inv` on the
   `chartAt H (proj α')` source, with the latter membership extracted from
   the source-structure description `coverChartAt_source_eq`).
   By `chartGramMatrix_lifted` the cover-side Gram matrix at `x'` agrees
   entry-by-entry with the base-side Gram matrix at `proj x'`, so the two
   matrices are equal (Matrix-extensionality) and hence their inverses
   are equal (`congrArg`).

3. For the `partialDeriv` factor, the inner factor `chartGramOnE` on each
   side is a function `E → ℝ`. We show these two functions are eventually
   equal at `y₀` (`=ᶠ[𝓝 y₀]`) by producing an open neighbourhood of `y₀` on
   which the pointwise identity holds — concretely, the neighbourhood is
   carved out by openness of two preimages:
     (a) `(extChartAt I α').symm ⁻¹' (chartAt H α').source` (open by
          continuity of the inverse on its source),
     (b) `(extChartAt I (proj α')).symm ⁻¹' (localSection α').target`
          (open by continuity of the base-side chart inverse plus openness
          of the local-section target).
   On their intersection, the conjugacy identifies the cover-side chart
   inverse with `(localSection α').symm` composed with the base-side chart
   inverse, and `proj ((localSection α').symm w) = w` for `w` in the
   local-section target (via `localSection`-vs-`proj` agreement). The
   pointwise Gram-matrix identity then follows from `chartGramMatrix_lifted`
   applied at the appropriate cover-side point.
   `Filter.EventuallyEq.fderiv_eq` then propagates the equality of
   functions to equality of their Fréchet derivatives at `y₀`, hence
   to equality of `partialDeriv` (which is `fderiv` applied to the model
   basis vector). -/
theorem chartChristoffel_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k (extChartAt I α' x') =
      chartChristoffel (M := M) g (proj (X := M) α') i j k
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  set y₀ : E := extChartAt I α' x' with hy₀_def
  have hy_eq : extChartAt I α' x' = extChartAt I (proj α') (proj x') :=
    extChartAt_proj_eq (I := I) (M := M) α' x'
  rw [show extChartAt I (proj (X := M) α') (proj (X := M) x') = y₀ from hy_eq.symm]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k y₀,
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_def
        (I := I) (M := M) g (proj α') i j k y₀]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  have hx'_ext : x' ∈ (extChartAt I α').source := by
    rw [extChartAt_source]; exact hx'
  have hsymm_LHS : (extChartAt I α').symm y₀ = x' := by
    rw [hy₀_def]
    exact (extChartAt I α').left_inv hx'_ext
  have hx'_inter : x' ∈ (localSection (M := M) α').source ∩
      (localSection (M := M) α') ⁻¹' (chartAt H (proj α')).source := by
    have hsrc : ((coverChartAt α') :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection α').source ∩
          (localSection α') ⁻¹' (chartAt H (proj α')).source :=
      coverChartAt_source_eq α'
    have hx'_cover : x' ∈ (coverChartAt α').source := hx'
    rw [hsrc] at hx'_cover; exact hx'_cover
  obtain ⟨hx'_LSsrc, hx'_LSchart⟩ := hx'_inter
  have hLS_x' : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  have hproj_x'_chart : proj x' ∈ (chartAt H (proj α')).source := by
    rw [Set.mem_preimage, hLS_x'] at hx'_LSchart
    exact hx'_LSchart
  have hproj_x'_ext : proj x' ∈ (extChartAt I (proj α')).source := by
    rw [extChartAt_source]; exact hproj_x'_chart
  have hsymm_RHS : (extChartAt I (proj α')).symm y₀ = proj x' := by
    rw [hy₀_def, hy_eq]
    exact (extChartAt I (proj α')).left_inv hproj_x'_ext
  rw [hsymm_LHS, hsymm_RHS]
  have hGramMatEq :
      chartGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x' =
        chartGramMatrix (M := M) g (proj α') (proj x') := by
    ext p q
    exact chartGramMatrix_lifted (I := I) (M := M) g α' x' p q hx'
  have hInvGramEq :
      chartInvGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x' k l =
        chartInvGramMatrix (M := M) g (proj α') (proj x') k l := by
    change (chartGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x')⁻¹ k l =
        (chartGramMatrix (M := M) g (proj α') (proj x'))⁻¹ k l
    rw [hGramMatEq]
  rw [hInvGramEq]
  congr 1
  have hGramOnE_eventuallyEq :
      ∀ (p q : Fin (Module.finrank ℝ E)),
        chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' p q
          =ᶠ[𝓝 y₀]
        chartGramOnE (M := M) g (proj α') p q := by
    intro p q
    set ECov : OpenPartialHomeomorph
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
      coverChartAt α' with hECov_def
    have hContCoverInv : ContinuousAt (ECov.extend I).symm y₀ := by
      have : (ECov.extend I) x' = y₀ := by
        rw [hy₀_def]
        rfl
      rw [← this]
      exact OpenPartialHomeomorph.continuousAt_extend_symm (I := I) ECov hx'
    have hOpenCoverSrc : IsOpen ECov.source := ECov.open_source
    have hCoverSrc_mem : (ECov.extend I).symm y₀ ∈ ECov.source := by
      have hy₀_alt : (ECov.extend I) x' = y₀ := by
        rw [hy₀_def]; rfl
      have : (ECov.extend I).symm ((ECov.extend I) x') = x' :=
        OpenPartialHomeomorph.extend_left_inv (I := I) ECov hx'
      rw [hy₀_alt] at this
      rw [this]
      exact hx'
    have hPreCover : (ECov.extend I).symm ⁻¹' ECov.source ∈ 𝓝 y₀ :=
      hContCoverInv (hOpenCoverSrc.mem_nhds hCoverSrc_mem)
    set EBase : OpenPartialHomeomorph M H := chartAt H (proj α') with hEBase_def
    have hContBaseInv : ContinuousAt (EBase.extend I).symm y₀ := by
      have hy₀_base : (EBase.extend I) (proj x') = y₀ := by
        change extChartAt I (proj α') (proj x') = y₀
        exact hy_eq.symm
      rw [← hy₀_base]
      exact OpenPartialHomeomorph.continuousAt_extend_symm (I := I)
        EBase hproj_x'_chart
    have hOpenLSTgt : IsOpen (localSection α').target := (localSection α').open_target
    have hLSTgt_mem : (EBase.extend I).symm y₀ ∈ (localSection α').target := by
      have hy₀_base : (EBase.extend I) (proj x') = y₀ := by
        change extChartAt I (proj α') (proj x') = y₀
        exact hy_eq.symm
      have hinv : (EBase.extend I).symm ((EBase.extend I) (proj x')) = proj x' :=
        OpenPartialHomeomorph.extend_left_inv (I := I) EBase hproj_x'_chart
      rw [hy₀_base] at hinv
      rw [hinv]
      have := (localSection α').map_source hx'_LSsrc
      rwa [hLS_x'] at this
    have hPreBase : (EBase.extend I).symm ⁻¹' (localSection α').target ∈ 𝓝 y₀ :=
      hContBaseInv (hOpenLSTgt.mem_nhds hLSTgt_mem)
    filter_upwards [hPreCover, hPreBase] with y hyCover hyBase
    change chartGramMatrix
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' ((extChartAt I α').symm y) p q
        = chartGramMatrix (M := M) g (proj α')
            ((extChartAt I (proj α')).symm y) p q
    have hConjSymm := (uc_coverChartAt_extend_conjugacy (I := I) α').2
    have hSymmDecomp : (extChartAt I α').symm y =
        (localSection α').symm ((EBase.extend I).symm y) := by
      change (ECov.extend I).symm y = (localSection α').symm ((EBase.extend I).symm y)
      have := congrArg (fun f => f y) hConjSymm
      simpa [Function.comp_apply] using this
    have hsrc_cover_y : (extChartAt I α').symm y ∈ (chartAt H α').source := by
      change (ECov.extend I).symm y ∈ ECov.source
      exact hyCover
    rw [chartGramMatrix_lifted (I := I) (M := M) g α'
          ((extChartAt I α').symm y) p q hsrc_cover_y]
    have hProj_eq : proj ((extChartAt I α').symm y)
        = (extChartAt I (proj α')).symm y := by
      rw [hSymmDecomp]
      have hproj_eq_LS :
          proj ((localSection α').symm ((EBase.extend I).symm y))
            = (localSection α')
                ((localSection α').symm ((EBase.extend I).symm y)) := by
        have := congrArg
            (fun f => f ((localSection α').symm ((EBase.extend I).symm y)))
            (proj_eq_localSection α')
        simpa using this
      rw [hproj_eq_LS, (localSection α').right_inv hyBase]
      rfl
    rw [hProj_eq]
  have hP_ij_lj :
      partialDeriv (E := E) i
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' l j) y₀
        = partialDeriv (E := E) i
            (chartGramOnE (M := M) g (proj α') l j) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' l j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E i)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') l j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E i)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq l j)]
  have hP_ji_li :
      partialDeriv (E := E) j
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' l i) y₀
        = partialDeriv (E := E) j
            (chartGramOnE (M := M) g (proj α') l i) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' l i) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E j)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') l i) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E j)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq l i)]
  have hP_lij :
      partialDeriv (E := E) l
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' i j) y₀
        = partialDeriv (E := E) l
            (chartGramOnE (M := M) g (proj α') i j) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' i j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E l)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') i j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E l)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq i j)]
  rw [hP_ij_lj, hP_ji_li, hP_lij]

/-- **`chartChristoffelContraction` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, vectors `v w : E`, and a cover-point
`x' ∈ (chartAt H α').source`, the chart-coordinate Christoffel
contraction of the lifted metric on the universal cover, evaluated at
the chart coordinate of `x'`, equals the chart-coordinate Christoffel
contraction of the base metric, evaluated at the chart coordinate of
`proj x'` in the base chart at `proj α'`.

Proof. Unfolding both sides via `chartChristoffelContraction_def`, each is
an inner triple sum
`∑_k (∑_{i, j} Γ^k_{ij}(·, ·)(y) · v^i · w^j) • e_k`
with the same outer index set, the same coordinate factors `chartCoord i v`,
`chartCoord j w`, and the same model basis vectors `chartModelBasis E k`.
The Christoffel-symbol factor agrees pointwise by `chartChristoffel_lifted`,
once we rewrite the base-side evaluation point `extChartAt I (proj α') (proj x')`
back to `extChartAt I α' x'` via `extChartAt_proj_eq`. The conclusion then
follows by `Finset.sum_congr` applied three times. -/
theorem chartChristoffelContraction_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source) (v w : E) :
    DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' v w (extChartAt I α' x') =
      DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction
        (M := M) g (proj (X := M) α') v w
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  rw [DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' v w (extChartAt I α' x'),
      DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_def
        (I := I) (M := M) g (proj α') v w
        (extChartAt I (proj (X := M) α') (proj (X := M) x'))]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [chartChristoffel_lifted (I := I) (M := M) g α' x' hx' i j k]

/-- **Eventually-equal form of `chartChristoffel_lifted`.**

For any chart anchor `α' : UC M` and any cover-point `x' ∈ (chartAt H α').source`,
the cover-side chart-Christoffel function `y ↦ Γ^k_{ij}(liftedMetric g, α', y)`
agrees with the base-side function `y ↦ Γ^k_{ij}(g, proj α', y)` on a
neighbourhood of `y₀ := extChartAt I α' x'`.

Proof. The neighborhood is
`(extChartAt I α').target ∩ (extChartAt I α').symm ⁻¹' (chartAt H α').source`.
On this set, every point `y` corresponds to a manifold point
`x'_y := (extChartAt I α').symm y` lying in `(chartAt H α').source`, and we
have `extChartAt I α' x'_y = y`. Applying `chartChristoffel_lifted` at `x'_y`
gives the cover-side Christoffel at `y` equal to the base-side Christoffel at
`extChartAt I (proj α') (proj x'_y) = extChartAt I α' x'_y = y`
(the latter via `extChartAt_proj_eq`). -/
lemma chartChristoffel_lifted_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i j k : Fin (Module.finrank ℝ E)) :
    (fun y => chartChristoffel
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k y)
      =ᶠ[𝓝 (extChartAt I α' x')]
    (fun y => chartChristoffel (M := M) g (proj (X := M) α') i j k y) := by
  classical
  set y₀ : E := extChartAt I α' x' with hy₀_def
  have hx'_ext : x' ∈ (extChartAt I α').source := by
    rw [extChartAt_source]; exact hx'
  have hContInv : ContinuousAt (extChartAt I α').symm y₀ := by
    have hy₀_alt : (extChartAt I α') x' = y₀ := by rw [hy₀_def]
    rw [← hy₀_alt]
    exact continuousAt_extChartAt_symm' (I := I) (x := α') hx'_ext
  have hOpenSrc : IsOpen (chartAt H α').source :=
    (chartAt H α').open_source
  have hSrc_mem : (extChartAt I α').symm y₀ ∈ (chartAt H α').source := by
    have hinv : (extChartAt I α').symm ((extChartAt I α') x') = x' :=
      (extChartAt I α').left_inv hx'_ext
    have hy₀_alt : (extChartAt I α') x' = y₀ := by rw [hy₀_def]
    rw [← hy₀_alt, hinv]; exact hx'
  have hPreImage :
      (extChartAt I α').symm ⁻¹' (chartAt H α').source ∈ 𝓝 y₀ :=
    hContInv (hOpenSrc.mem_nhds hSrc_mem)
  have hTargetOpen : IsOpen (extChartAt I α').target :=
    isOpen_extChartAt_target (I := I) α'
  have hy₀_target : y₀ ∈ (extChartAt I α').target := by
    rw [hy₀_def]; exact (extChartAt I α').map_source hx'_ext
  have hTgtMem : (extChartAt I α').target ∈ 𝓝 y₀ :=
    hTargetOpen.mem_nhds hy₀_target
  filter_upwards [hPreImage, hTgtMem] with y hyPre hyTgt
  set x'_y :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M :=
    (extChartAt I α').symm y with hx'_y_def
  have hx'_y_src : x'_y ∈ (chartAt H α').source := hyPre
  have hExt_x'_y : extChartAt I α' x'_y = y := by
    rw [hx'_y_def]; exact (extChartAt I α').right_inv hyTgt
  have hLifted := chartChristoffel_lifted (I := I) (M := M) g α' x'_y hx'_y_src i j k
  have hExt_proj_x'_y :
      extChartAt I (proj (X := M) α') (proj (X := M) x'_y) =
        extChartAt I α' x'_y :=
    (extChartAt_proj_eq (I := I) (M := M) α' x'_y).symm
  rw [hExt_x'_y, hExt_proj_x'_y, hExt_x'_y] at hLifted
  exact hLifted

/-- **`chartRiemannTensor` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, indices `i j k l`, and cover-point
`x' ∈ (chartAt H α').source`, the chart-coordinate Riemann curvature
tensor of the lifted metric at the chart-coordinate of `x'` equals the
chart-coordinate Riemann curvature tensor of the base metric at the
chart-coordinate of `proj x'` in the base chart at `proj α'`.

Proof outline. Unfold `chartRiemannTensor_def` on both sides. The formula
is a sum of two `partialDeriv`-of-`chartChristoffel` terms and a finite
sum of Christoffel products. The first two factors agree at `y₀` by
`Filter.EventuallyEq.fderiv_eq` applied to the eventually-equal form of
`chartChristoffel` (`chartChristoffel_lifted_eventuallyEq`); the product
terms agree pointwise at `y₀` by `chartChristoffel_lifted`. -/
theorem chartRiemannTensor_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannTensor
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k l (extChartAt I α' x') =
      chartRiemannTensor (M := M) g (proj (X := M) α') i j k l
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  set y₀ : E := extChartAt I α' x' with hy₀_def
  have hy_eq : extChartAt I α' x' = extChartAt I (proj α') (proj x') :=
    extChartAt_proj_eq (I := I) (M := M) α' x'
  rw [show extChartAt I (proj (X := M) α') (proj (X := M) x') = y₀ from hy_eq.symm]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k l y₀,
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor_def
        (I := I) (M := M) g (proj α') i j k l y₀]
  have hChristAt : ∀ (a b c : Fin (Module.finrank ℝ E)),
      chartChristoffel
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' a b c y₀
        = chartChristoffel (M := M) g (proj α') a b c y₀ := by
    intro a b c
    have h := chartChristoffel_lifted (I := I) (M := M) g α' x' hx' a b c
    rw [show extChartAt I α' x' = y₀ from rfl,
        show extChartAt I (proj (X := M) α') (proj (X := M) x') = y₀ from hy_eq.symm] at h
    exact h
  have hChristEvEq : ∀ (a b c : Fin (Module.finrank ℝ E)),
      (fun y => chartChristoffel
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' a b c y)
        =ᶠ[𝓝 y₀]
      (fun y => chartChristoffel (M := M) g (proj α') a b c y) := by
    intro a b c
    have := chartChristoffel_lifted_eventuallyEq (I := I) (M := M) g α' x' hx' a b c
    exact this
  have hPartialDeriv : ∀ (n : Fin (Module.finrank ℝ E)) (a b c : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) n
          (chartChristoffel
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' a b c) y₀
        = partialDeriv (E := E) n
            (chartChristoffel (M := M) g (proj α') a b c) y₀ := by
    intro n a b c
    change fderiv ℝ
        (chartChristoffel
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' a b c) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E n)
      = fderiv ℝ
          (chartChristoffel (M := M) g (proj α') a b c) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E n)
    rw [Filter.EventuallyEq.fderiv_eq (hChristEvEq a b c)]
  rw [hPartialDeriv j i k l, hPartialDeriv k i j l]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [hChristAt j m l, hChristAt i k m, hChristAt k m l, hChristAt i j m]

/-- **`chartRicciTensor` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, lower indices `i k`, and cover-point
`x' ∈ (chartAt H α').source`, the chart-coordinate Ricci tensor of the
lifted metric at the chart-coordinate of `x'` equals the chart-coordinate
Ricci tensor of the base metric at the chart-coordinate of `proj x'` in
the base chart at `proj α'`.

Proof. Unfold `chartRicciTensor_def` on both sides (a finite sum over `j`
of `chartRiemannTensor` entries) and apply `chartRiemannTensor_lifted`
term-by-term. -/
theorem chartRicciTensor_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i k : Fin (Module.finrank ℝ E)) :
    chartRicciTensor
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i k (extChartAt I α' x') =
      chartRicciTensor (M := M) g (proj (X := M) α') i k
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i k (extChartAt I α' x'),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor_def
        (I := I) (M := M) g (proj α') i k
        (extChartAt I (proj (X := M) α') (proj (X := M) x'))]
  refine Finset.sum_congr rfl ?_
  intro j _
  exact chartRiemannTensor_lifted (I := I) (M := M) g α' x' hx' i j k j

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
