import DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure

section Atlas

variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem finite_chart_cover [CompactSpace M] :
    ∃ s : Finset M, (⋃ x ∈ s, (chartAt H x).source) = (Set.univ : Set M) := by
  classical
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := M))
    (fun x : M => (chartAt H x).source) (fun x => (chartAt H x).open_source)
    (by rw [iUnion_source_chartAt])
  refine ⟨s, Set.eq_univ_of_univ_subset ?_⟩
  simpa only using hs

variable [MeasurableSpace M]

theorem null_of_chart_cover
    (μ : Measure M) (A : Set M) (s : Finset M)
    (hcover : A ⊆ ⋃ x ∈ s, (chartAt H x).source)
    (hnull : ∀ x ∈ s, μ (A ∩ (chartAt H x).source) = 0) :
    μ A = 0 := by
  classical
  have hsub : A ⊆ ⋃ x : ↑s, A ∩ (chartAt H (x : M)).source := by
    intro y hy
    rcases Set.mem_iUnion.mp (hcover hy) with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxs, hyx⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hxs⟩, hy, hyx⟩
  exact measure_mono_null hsub (measure_iUnion_null fun x => hnull x x.property)

end Atlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev EuclN := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem chart_preimage_null
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {N : Set EuclN} (hN0 : (volume : Measure EuclN)
      (N ∩ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) x₀) = 0) :
    riemannianVolumeMeasure (I := I) (M := M) g
      ((chartAt H x₀).source ∩
        {x : M | (toEuclidean (E := E)) ((extChartAt I x₀) x) ∈ N}) = 0 := by
  classical
  let T : Set EuclN :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) x₀
  let A : Set M := (chartAt H x₀).source ∩
    {x : M | (toEuclidean (E := E)) ((extChartAt I x₀) x) ∈ N}
  have hT : MeasurableSet T :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) x₀
  have hNT0 : (volume : Measure EuclN) (N ∩ T) = 0 := hN0
  obtain ⟨K, hNT_sub, hK, hK0⟩ := exists_measurable_superset_of_null hNT0
  have hae : ∀ᵐ y ∂(volume : Measure EuclN), y ∉ K :=
    measure_eq_zero_iff_ae_notMem.mp hK0
  have hchart : ∀ᵐ x ∂chartLocalMeasure (I := I) g x₀,
      x ∈ (chartAt H x₀).source →
        (toEuclidean (E := E)) ((extChartAt I x₀) x) ∉ K :=
    DifferentialGeometry.Analysis.Sobolev.Chart.ae_chart_of_volume
      (I := I) (M := M) g x₀ hK.compl hae
  have hA_sub : A ⊆ (chartAt H x₀).source := inter_subset_left
  have hlocal : chartLocalMeasure (I := I) g x₀ A = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hchart] with x hx
    intro hxA
    have hx_source : x ∈ (chartAt H x₀).source := hxA.1
    have hx_ext : x ∈ (extChartAt I x₀).source := by
      rwa [extChartAt_source_eq_chartAt_source (I := I) (M := M)]
    have hxT : (toEuclidean (E := E)) ((extChartAt I x₀) x) ∈ T := by
      exact ⟨(extChartAt I x₀) x, (extChartAt I x₀).map_source hx_ext, rfl⟩
    exact hx hx_source (hNT_sub ⟨hxA.2, hxT⟩)
  calc
    riemannianVolumeMeasure (I := I) (M := M) g A =
        (riemannianVolumeMeasure (I := I) (M := M) g).restrict
          (chartAt H x₀).source A :=
      (Measure.restrict_eq_self _ hA_sub).symm
    _ = (chartLocalMeasure (I := I) g x₀).restrict
          (chartAt H x₀).source A := by
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.volume_restrict_eq
        (I := I) (M := M) g x₀]
    _ = chartLocalMeasure (I := I) g x₀ A :=
      Measure.restrict_eq_self _ hA_sub
    _ = 0 := hlocal

theorem chart_model_null
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {N : Set E} (hN0 : modelHaar (E := E) (N ∩ (extChartAt I x₀).target) = 0) :
    riemannianVolumeMeasure (I := I) (M := M) g
      ((chartAt H x₀).source ∩ {x : M | (extChartAt I x₀) x ∈ N}) = 0 := by
  classical
  let e := toEuclidean (E := E)
  have he : MeasurableEmbedding (e : E → EuclN) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have himage0 : (volume : Measure EuclN)
      (e '' (N ∩ (extChartAt I x₀).target)) = 0 := by
    rw [← map_toEuclidean_modelHaar_eq_volume (E := E)]
    rw [he.map_apply]
    rw [he.injective.preimage_image]
    exact hN0
  have htarget :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) x₀ = e '' (extChartAt I x₀).target := rfl
  have hEucl0 : (volume : Measure EuclN)
      ((e '' N) ∩ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) x₀) = 0 := by
    rw [htarget, ← Set.image_inter he.injective]
    exact himage0
  have hpull := chart_preimage_null (I := I) (M := M) g x₀ hEucl0
  have hset :
      (chartAt H x₀).source ∩
          {x : M | e ((extChartAt I x₀) x) ∈ e '' N} =
        (chartAt H x₀).source ∩ {x : M | (extChartAt I x₀) x ∈ N} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_right_iff]
    intro _
    constructor
    · rintro ⟨y, hyN, hy⟩
      exact he.injective hy ▸ hyN
    · intro hxN
      exact ⟨(extChartAt I x₀) x, hxN, rfl⟩
  rw [hset] at hpull
  exact hpull

end Measure
end Integral
end DifferentialGeometry
