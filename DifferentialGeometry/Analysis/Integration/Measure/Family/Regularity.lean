import DifferentialGeometry.Analysis.Integration.Measure.Family.Defs
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Analysis.Integration.Measure.Family.VolumeVariation

/-!
# A chart-local constructor for `MetricFamilyRegularAt`

`MetricFamilyRegularAt` is the regularity hypothesis of
`Integral.Measure.volume_variation_formula`. Its only constructor,
`MetricFamilyRegularAt.of_chartGram_timeDeriv`, asks for continuity of the chart Gram
entries and of their time derivative as functions on `ℝ × M`, restricted to
`Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet`.

That shape is awkward to verify, because the data one actually has is usually a function of
`(t, y) ∈ ℝ × E`: a chart representation. This file reduces the hypothesis to exactly that,
by transporting along `extChartAt I x₀`:

* the chart Gram entries are read on `ℝ × E` through the library's own
  `Geometry.Operator.chartGramOnE`, at the metric of each time;
* `MetricFamilyRegularAt.of_chartGramOnE` builds `MetricFamilyRegularAt` from the
  derivative property together with continuity *on the chart target*, where ordinary
  Fréchet calculus applies.

The transport is possible because `(trivializationAt E (TangentSpace I) x₀).baseSet` is the
chart source, on which `extChartAt I x₀` is continuous, maps into the chart target and is
inverted by its symm.

It also adds `volume_variation_formula_of_eventuallyEq`, which lets the transport formula be
applied to an integrand that is regular only *near* the time in question. That is needed in
practice: `FunctionRegularAt` asks for continuity on all of `ℝ × M`, which a backward heat
kernel centred at `t₀` cannot satisfy, being singular there. Since the conclusion is a
`HasDerivAt` at a point, and so local, the formula transfers along eventual equality of the
integrand.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- On the chart source, the chart-representation form agrees with the chart Gram entry. -/
lemma chartGramOnE_extChartAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) {x : M}
    (hx : x ∈ (extChartAt I x₀).source) :
    DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) (g_fam t) x₀ i j
      (extChartAt I x₀ x) =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam t) x₀ x i j := by
  rw [DifferentialGeometry.Geometry.Operator.chartGramOnE, (extChartAt I x₀).left_inv hx]

omit [Module.Finite ℝ E] in
/-- The trivialization base set is contained in the source of the extended chart. -/
lemma baseSet_subset_extChartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet ⊆ (extChartAt I x₀).source := by
  rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
  exact subset_of_eq
    (DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source
      (I := I) x₀)

/-- **Chart-local constructor for `MetricFamilyRegularAt`.**

The time derivative is supplied as a function `D` of a time and a point of the model space,
and the two continuity conditions are imposed on the chart target, where they are ordinary
statements about functions on `ℝ × E`. -/
theorem MetricFamilyRegularAt.of_chartGramOnE
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (D : M → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ → E → ℝ)
    (hderiv : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) (t : ℝ) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      HasDerivAt
        (fun s : ℝ ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_fam s) x₀ x i j)
        (D x₀ i j t (extChartAt I x₀ x)) t)
    (hcontG : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E ↦
        DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) (g_fam p.1) x₀ i j p.2)
        (univ ×ˢ (extChartAt I x₀).target))
    (hcontD : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E ↦ D x₀ i j p.1 p.2)
        (univ ×ˢ (extChartAt I x₀).target)) :
    MetricFamilyRegularAt (I := I) g_fam t₀ := by
  refine MetricFamilyRegularAt.of_chartGram_timeDeriv (I := I) ?_
  intro x₀ i j
  refine ⟨fun t x ↦ D x₀ i j t (extChartAt I x₀ x), ?_, ?_, ?_⟩
  · intro t x hx
    exact hderiv x₀ i j t hx
  · -- continuity of the Gram entries, transported from the chart target
    have hmap : ContinuousOn (fun p : ℝ × M ↦ (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      refine ContinuousOn.prodMk (continuous_fst.continuousOn) ?_
      exact (continuousOn_extChartAt (I := I) x₀).comp continuousOn_snd
        (fun p hp ↦ baseSet_subset_extChartAt_source (I := I) x₀ hp.2)
    have hmaps : MapsTo (fun p : ℝ × M ↦ (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (univ ×ˢ (extChartAt I x₀).target) := by
      intro p hp
      exact ⟨mem_univ _,
        (extChartAt I x₀).map_source (baseSet_subset_extChartAt_source (I := I) x₀ hp.2)⟩
    have hcomp := (hcontG x₀ i j).comp hmap hmaps
    refine hcomp.congr ?_
    intro p hp
    exact (chartGramOnE_extChartAt (I := I) g_fam x₀ i j p.1
      (baseSet_subset_extChartAt_source (I := I) x₀ hp.2)).symm
  · -- continuity of the derivative, transported the same way
    have hmap : ContinuousOn (fun p : ℝ × M ↦ (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      refine ContinuousOn.prodMk (continuous_fst.continuousOn) ?_
      exact (continuousOn_extChartAt (I := I) x₀).comp continuousOn_snd
        (fun p hp ↦ baseSet_subset_extChartAt_source (I := I) x₀ hp.2)
    have hmaps : MapsTo (fun p : ℝ × M ↦ (p.1, extChartAt I x₀ p.2))
        (univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (univ ×ˢ (extChartAt I x₀).target) := by
      intro p hp
      exact ⟨mem_univ _,
        (extChartAt I x₀).map_source (baseSet_subset_extChartAt_source (I := I) x₀ hp.2)⟩
    exact (hcontD x₀ i j).comp hmap hmaps


/-! ## Transferring the transport formula along eventual equality -/

/-- **The transport formula for a locally regular integrand.**

`FunctionRegularAt` is a global-in-time hypothesis, which rules out integrands that are
singular at some time, such as a backward heat kernel centred at `t₀`. The conclusion of
`volume_variation_formula` is a derivative at a point, hence local, so it is enough that the
integrand agree near that time with one that *is* globally regular. -/
theorem volume_variation_formula_of_eventuallyEq
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M} {f f' : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf' : FunctionRegularAt (M := M) f' t₀)
    (hff : ∀ᶠ s in nhds t₀, f s = f' s) :
    HasDerivAt
      (fun s : ℝ ↦ ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ ↦ f s x) t₀
              + (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ := by
  have hbase := volume_variation_formula (I := I) (M := M) (g_fam := g_fam) (f := f')
    (t₀ := t₀) hg hf'
  -- at `t₀` the two integrands agree, and so do their time derivatives
  have ht₀ : f t₀ = f' t₀ := hff.self_of_nhds
  have hderiv : ∀ x : M,
      deriv (fun s : ℝ ↦ f s x) t₀ = deriv (fun s : ℝ ↦ f' s x) t₀ := by
    intro x
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hff] with s hs
    exact congrFun hs x
  have hintegrand : (fun x : M ↦ deriv (fun s : ℝ ↦ f s x) t₀
        + (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
      = fun x : M ↦ deriv (fun s : ℝ ↦ f' s x) t₀
        + (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g_fam t₀ x * f' t₀ x := by
    funext x
    rw [hderiv x, ht₀]
  rw [hintegrand]
  -- the integrals as functions of `s` agree near `t₀`
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [hff] with s hs
  rw [hs]

end DifferentialGeometry.Integral.Measure
