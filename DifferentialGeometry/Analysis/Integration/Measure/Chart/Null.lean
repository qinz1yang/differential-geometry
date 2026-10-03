import DifferentialGeometry.Analysis.Integration.Measure.Family.Decomposition

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem chartLocalMeasure_null_of_chart_image_null
    (g : SmoothRiemannianMetric I M) (α : M)
    {A : Set M}
    (hA : modelHaar (E := E)
      ((extChartAt I α) '' (A ∩ (chartAt H α).source)) = 0) :
    chartLocalMeasure (I := I) g α A = 0 := by
  classical
  obtain ⟨N, hAN, hN, hNzero⟩ :=
    exists_measurable_superset_of_null hA
  have hhaar : ∀ᵐ y ∂modelHaar (E := E), y ∉ N :=
    measure_eq_zero_iff_ae_notMem.mp hNzero
  have hchart : ∀ᵐ x ∂chartLocalMeasure (I := I) g α,
      x ∈ (chartAt H α).source → extChartAt I α x ∉ N :=
    ae_chart_of_haar (I := I) g α hN.compl hhaar
  have hout : chartLocalMeasure (I := I) g α
      ((chartAt H α).source)ᶜ = 0 :=
    chartLocalMeasure_apply_of_disjoint_source (I := I) g α
      (chartAt H α).open_source.measurableSet.compl
      (show Disjoint ((chartAt H α).source)ᶜ
        (chartAt H α).source from disjoint_compl_left)
  have hsource : ∀ᵐ x ∂chartLocalMeasure (I := I) g α,
      x ∈ (chartAt H α).source := by
    simpa only [mem_compl_iff, not_not] using
      measure_eq_zero_iff_ae_notMem.mp hout
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hchart, hsource] with x hx hxs
  intro hxA
  exact hx hxs (hAN ⟨x, ⟨hxA, hxs⟩, rfl⟩)

theorem riemannianMeasure_null_of_chartLocalMeasure
    [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {A : Set M}
    (hA : ∀ α : M, chartLocalMeasure (I := I) g α A = 0) :
    riemannianMeasure (I := I) g ρ A = 0 := by
  classical
  let J : Set M := {α : M | (Function.support (ρ α)).Nonempty}
  let w : M → MeasureTheory.Measure M := fun α =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))
  let : Countable J :=
    (countable_nonempty_support_of_pou (I := I) ρ).to_subtype
  have hoff : ∀ α : M, α ∉ J → w α = 0 := by
    intro α hα
    have hweight : (fun x : M => ENNReal.ofReal (ρ α x)) = 0 := by
      funext x
      have hρα : ρ α x = 0 := by
        by_contra hne
        exact hα ⟨x, hne⟩
      simp only [hρα, ENNReal.ofReal_zero, Pi.zero_apply]
    change (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x)) = 0
    rw [hweight, withDensity_zero]
  have hsum : riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : J => w α.val) := by
    change MeasureTheory.Measure.sum w = _
    refine MeasureTheory.Measure.ext (fun B hB => ?_)
    rw [MeasureTheory.Measure.sum_apply _ hB,
      MeasureTheory.Measure.sum_apply _ hB]
    refine tsum_subtype_eq_of_support_subset ?_
    intro α hα
    by_contra hnot
    exact hα (by
      change (w α) B = 0
      rw [hoff α hnot]
      rfl)
  rw [hsum]
  apply MeasureTheory.Measure.sum_apply_eq_zero.mpr
  intro α
  exact (withDensity_absolutelyContinuous
    (chartLocalMeasure (I := I) g α.val)
    (fun x : M => ENNReal.ofReal (ρ α.val x))) (hA α.val)

end DifferentialGeometry.Geometry.Measure

end
