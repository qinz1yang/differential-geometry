import DifferentialGeometry.Analysis.Schauder.ParabolicChart
import DifferentialGeometry.Analysis.Schauder.ParabolicJetCompactness

noncomputable section

open Filter Set
open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem isParabolicC2On_parabolicEuclideanChartRepresentation_of_tendsto_locally_uniformly_on_of_lower_jets_gauge
    [FiniteDimensional Real E] [FiniteDimensional Real F]
    (center : M) {Q : Set (ParabolicPoint (EuclN E))} (hQ : IsOpen Q)
    (uApprox : Nat → Real → M → F)
    (dtimeUApprox : Nat → ParabolicPoint (EuclN E) → F)
    (duApprox : Nat → ParabolicPoint (EuclN E) → EuclN E →L[Real] F)
    (d2uApprox : Nat → ParabolicPoint (EuclN E) →
      EuclN E →L[Real] EuclN E →L[Real] F)
    (u : Real → M → F)
    {alpha : NNReal} (halpha : 0 < alpha) (C : NNReal)
    (hgauge : ∀ n,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        alpha I center Q (uApprox n) ≤ C)
    (hrealize : ∀ n, ParabolicJetRealizesOn Q
      (fun p => parabolicEuclideanChartRepresentation
        I center (uApprox n) p.time p.space)
      (dtimeUApprox n) (duApprox n) (d2uApprox n))
    (hu : TendstoLocallyUniformlyOn
      (fun n p => parabolicEuclideanChartRepresentation
        I center (uApprox n) p.time p.space)
      (fun p => parabolicEuclideanChartRepresentation
        I center u p.time p.space) atTop Q) :
    IsParabolicC2On Q (parabolicEuclideanChartRepresentation I center u) := by
  let uApproxChart : Nat → ParabolicPoint (EuclN E) → F :=
    fun n p => parabolicEuclideanChartRepresentation
      I center (uApprox n) p.time p.space
  rcases exists_parabolic_jet_subseq_of_lower_jets_gauge hQ
      uApproxChart dtimeUApprox duApprox d2uApprox halpha C
      (fun n => hgauge n) hrealize with
    ⟨phi, uLimit, _, _, _, hphi,
      huLimit, _, _, _, _, hclassical, _⟩
  have heq : Set.EqOn uLimit
      (fun p => parabolicEuclideanChartRepresentation
        I center u p.time p.space) Q := by
    intro p hp
    exact tendsto_nhds_unique (huLimit.tendsto_at hp)
      ((hu.tendsto_at hp).comp hphi.tendsto_atTop)
  apply isParabolicC2On_congr_of_eqOn_open hQ Subset.rfl
    (u := fun t x => uLimit (parabolicPoint t x))
    (v := parabolicEuclideanChartRepresentation I center u)
  · simpa only [parabolicPoint_time_space] using heq
  · exact hclassical

theorem isParabolicC2InEuclideanChartsOn_of_tendsto_locally_uniformly_on_of_chartwise_lower_jets_gauge
    [FiniteDimensional Real E] [FiniteDimensional Real F]
    {A : Type*} (center : A → M) (Q : A → Set (ParabolicPoint (EuclN E)))
    (hQ : ∀ i, IsOpen (Q i))
    (uApprox : Nat → Real → M → F)
    (dtimeUApprox : A → Nat → ParabolicPoint (EuclN E) → F)
    (duApprox : A → Nat → ParabolicPoint (EuclN E) → EuclN E →L[Real] F)
    (d2uApprox : A → Nat → ParabolicPoint (EuclN E) →
      EuclN E →L[Real] EuclN E →L[Real] F)
    (u : Real → M → F)
    {alpha : NNReal} (halpha : 0 < alpha)
    (hgauge : ∀ i, ∃ C : NNReal, ∀ n,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        alpha I (center i) (Q i) (uApprox n) ≤ C)
    (hrealize : ∀ i n, ParabolicJetRealizesOn (Q i)
      (fun p => parabolicEuclideanChartRepresentation
        I (center i) (uApprox n) p.time p.space)
      (dtimeUApprox i n) (duApprox i n) (d2uApprox i n))
    (hu : ∀ i, TendstoLocallyUniformlyOn
      (fun n p => parabolicEuclideanChartRepresentation
        I (center i) (uApprox n) p.time p.space)
      (fun p => parabolicEuclideanChartRepresentation
        I (center i) u p.time p.space) atTop (Q i)) :
    IsParabolicC2InEuclideanChartsOn I center Q u := by
  intro i
  obtain ⟨C, hC⟩ := hgauge i
  exact
    isParabolicC2On_parabolicEuclideanChartRepresentation_of_tendsto_locally_uniformly_on_of_lower_jets_gauge
      (center i) (hQ i) uApprox (dtimeUApprox i) (duApprox i)
      (d2uApprox i) u halpha C hC (hrealize i) (hu i)

theorem isParabolicC2InEuclideanChartsOn_of_tendsto_locally_uniformly_on_of_lower_jets_gauge
    [FiniteDimensional Real E] [FiniteDimensional Real F]
    {A : Type*} (center : A → M) (Q : A → Set (ParabolicPoint (EuclN E)))
    (hQ : ∀ i, IsOpen (Q i))
    (uApprox : Nat → Real → M → F)
    (dtimeUApprox : A → Nat → ParabolicPoint (EuclN E) → F)
    (duApprox : A → Nat → ParabolicPoint (EuclN E) → EuclN E →L[Real] F)
    (d2uApprox : A → Nat → ParabolicPoint (EuclN E) →
      EuclN E →L[Real] EuclN E →L[Real] F)
    (u : Real → M → F)
    {alpha : NNReal} (halpha : 0 < alpha) (C : NNReal)
    (hgauge : ∀ n,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
        alpha I center Q (uApprox n) ≤ C)
    (hrealize : ∀ i n, ParabolicJetRealizesOn (Q i)
      (fun p => parabolicEuclideanChartRepresentation
        I (center i) (uApprox n) p.time p.space)
      (dtimeUApprox i n) (duApprox i n) (d2uApprox i n))
    (hu : ∀ i, TendstoLocallyUniformlyOn
      (fun n p => parabolicEuclideanChartRepresentation
        I (center i) (uApprox n) p.time p.space)
      (fun p => parabolicEuclideanChartRepresentation
        I (center i) u p.time p.space) atTop (Q i)) :
    IsParabolicC2InEuclideanChartsOn I center Q u := by
  apply
    isParabolicC2InEuclideanChartsOn_of_tendsto_locally_uniformly_on_of_chartwise_lower_jets_gauge
      center Q hQ uApprox dtimeUApprox duApprox d2uApprox u halpha
  · intro i
    refine ⟨C, fun n => ?_⟩
    exact
      (eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_euclideanCharts
        alpha I center Q (uApprox n) i).trans (hgauge n)
  · exact hrealize
  · exact hu

end DifferentialGeometry.Analysis.Schauder

end
