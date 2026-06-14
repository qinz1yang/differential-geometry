import DifferentialGeometry.Geometry.Operator.Hessian

/-! # Joint `(t, x)`-`C∞` smoothness of the chart-Gram readout

For a metric family `g_DT : ℝ → SmoothRiemannianMetric I M` whose bundle inner-product
`Hom`-section `(t, x) ↦ (g_DT t).inner x` is jointly `C∞` over the product model
`𝓘(ℝ, ℝ).prod I` on `J ×ˢ baseSet`, each scalar chart-Gram entry
`(t, x) ↦ chartGramMatrix (g_DT t) x₀ x i j` is jointly `C∞` on `J ×ˢ baseSet`, and the
chart-pulled-back entry `(t, x) ↦ chartGramOnE (g_DT t) α i j (extChartAt I α x)` is jointly
`C∞` on `J ×ˢ (chartAt H α).source`.

These are the intrinsic readout lemmas that reduce joint smoothness of the metric
`Hom`-section to joint smoothness of the scalar chart-Gram entries: the chart-Gram entry is
the metric `Hom`-section paired against the (`t`-independent, jointly smooth) chart frame
`chartBasisVec`, delivered by `ContMDiffOn.clm_bundle_apply₂` over base `M` with base map
`Prod.snd`. The `chartGramOnE` form transports along the chart round-trip identity on the
chart source and the identification of the tangent-bundle trivialization base set with the
chart source. -/

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- **The chart-Gram entry is jointly `(t, x)` `C∞` on the base set (`C∞` arm of the
spectral → chart-local readout).**

From the joint `(t, x)`-`C∞` smoothness of the metric inner-product `Hom`-section
`(t, x) ↦ (g_DT t).inner x` over the product model `𝓘(ℝ, ℝ).prod I` on `J ×ˢ baseSet`
(`hsmooth`), each scalar chart-Gram entry `(t, x) ↦ chartGramMatrix (g_DT t) x₀ x i j` is
jointly `C∞` on `J ×ˢ baseSet`.

The chart-Gram entry is the metric `Hom`-section paired against the (`t`-independent,
jointly smooth) chart frame `chartBasisVec`, so it is delivered by
`ContMDiffOn.clm_bundle_apply₂` over base `M` with base map `Prod.snd`, then read off the
fiber component of the total-space section via `Bundle.contMDiffWithinAt_totalSpace`. -/
theorem chartGramMatrix_jointContMDiffOn_of_innerSmooth
    (x₀ : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => chartBasisVec (I := I) x₀ i q.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    (chartBasisVec_contMDiffOn (I := I) x₀ i).comp contMDiffOn_snd (fun q hq => hq.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => chartBasisVec (I := I) x₀ j q.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    (chartBasisVec_contMDiffOn (I := I) x₀ j).comp contMDiffOn_snd (fun q hq => hq.2)
  have happ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
          ((g_DT q.1).inner q.2
            (chartBasisVecFiber (I := I) x₀ i q.2)
            (chartBasisVecFiber (I := I) x₀ j q.2))))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) hsmooth hv hw
  intro p hp
  have hpb := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] in
/-- **The chart-pulled-back Gram entry `chartGramOnE` is jointly `(t, x)`-`C∞` on the chart
source (`C∞` arm of the spectral → chart-local readout).**

The `C∞` analogue of `chartGramMatrix_jointContMDiffOn_of_innerSmooth` on the chart-pulled-back
entry: from the joint smoothness of the metric inner-product `Hom`-section
`(t, x) ↦ (g_DT t).inner x` over the product model `𝓘(ℝ, ℝ).prod I` on `J ×ˢ baseSet`
(`hsmooth`), the chart-`α`-pulled-back Gram entry
`(t, x) ↦ chartGramOnE (g_DT t) α i j (extChartAt I α x)` is jointly `C∞` on
`J ×ˢ (chartAt H α).source`.

On the chart source the chart round-trip is the identity (`(extChartAt I α).left_inv`), so the
`chartGramOnE` value collapses to the chart-Gram entry `chartGramMatrix (g_DT t) α x i j`; the
statement is then `chartGramMatrix_jointContMDiffOn_of_innerSmooth` transported along the
identification `(trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source`
(`TangentBundle.trivializationAt_baseSet`).  Off the chart source the round-trip is junk, so a
`Set.univ` formulation would be false-as-stated; the source statement is the honest one. -/
theorem chartGramOnE_jointContMDiffOn_of_innerSmooth
    (α : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2))
      (J ×ˢ (chartAt H α).source) := by
  have hbase :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (I := I) α
  have hjoint := chartGramMatrix_jointContMDiffOn_of_innerSmooth (I := I) (M := M)
    α i j g_DT hsmooth
  rw [hbase] at hjoint
  refine hjoint.congr ?_
  rintro ⟨t, x⟩ ⟨_, hx⟩
  change Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) α i j (extChartAt I α x)
    = chartGramMatrix (I := I) (g_DT t) α x i j
  rw [Integral.DivergenceTheorem.chartGramOnE_def]
  have hxsource : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  rw [(extChartAt I α).left_inv hxsource]

end Measure
end Integral
end DifferentialGeometry
