import DifferentialGeometry.Analysis.Schauder.ParabolicChart
import DifferentialGeometry.Analysis.Schauder.HolderSpace

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]

def IsBoundedParabolicC2HolderInEuclideanChartsOn
    [FiniteDimensional Real E]
    {A : Type*} (alpha : NNReal) (I : ModelWithCorners Real E H)
    (center : A → M)
    (Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E)))))
    (u : Real → M → F) : Prop :=
  ∀ i, IsBoundedParabolicC2HolderOn alpha (Q i)
    (parabolicEuclideanChartRepresentation I (center i) u)

namespace IsBoundedParabolicC2HolderInEuclideanChartsOn

theorem isParabolicC2InEuclideanChartsOn
    [FiniteDimensional Real E]
    {A : Type*} {alpha : NNReal}
    {center : A → M}
    {Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    {u : Real → M → F}
    (hu : IsBoundedParabolicC2HolderInEuclideanChartsOn
      alpha I center Q u) :
    IsParabolicC2InEuclideanChartsOn I center Q u := by
  intro i
  exact (hu i).1.1

theorem gauge_ne_top
    [FiniteDimensional Real E]
    {A : Type*} [Finite A] {alpha : NNReal}
    {center : A → M}
    {Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    {u : Real → M → F}
    (hu : IsBoundedParabolicC2HolderInEuclideanChartsOn
      alpha I center Q u) :
    eParabolicC2HolderGaugeInEuclideanChartsOn
      alpha I center Q u ≠ ⊤ := by
  classical
  letI := Fintype.ofFinite A
  let C : A → NNReal := fun i ↦
    (eParabolicC2HolderGaugeInEuclideanChartOn
      alpha I (center i) (Q i) u).toNNReal
  have hlocal : ∀ i,
      eParabolicC2HolderGaugeInEuclideanChartOn
        alpha I (center i) (Q i) u ≤ C i := by
    intro i
    change eParabolicC2HolderGaugeInEuclideanChartOn
        alpha I (center i) (Q i) u ≤
      ((eParabolicC2HolderGaugeInEuclideanChartOn
        alpha I (center i) (Q i) u).toNNReal : ENNReal)
    exact (ENNReal.coe_toNNReal (hu i).2).symm.le
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top
    (eParabolicC2HolderGaugeInEuclideanChartsOn_le_sum_of_finite
      alpha I center Q u C hlocal)

theorem of_isParabolicC2On_of_gauge_ne_top
    [FiniteDimensional Real E]
    {A : Type*} {alpha : NNReal}
    {center : A → M}
    {Q : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    {u : Real → M → F}
    (hu : ∀ i, IsParabolicC2On (Q i)
      (parabolicEuclideanChartRepresentation I (center i) u))
    (hfinite : eParabolicC2HolderGaugeInEuclideanChartsOn
      alpha I center Q u ≠ ⊤) :
    IsBoundedParabolicC2HolderInEuclideanChartsOn
      alpha I center Q u := by
  intro i
  have hlocalFinite : eParabolicC2HolderGaugeInEuclideanChartOn
      alpha I (center i) (Q i) u ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite
      (eParabolicC2HolderGaugeInEuclideanChartOn_le_euclideanCharts
        alpha I center Q u i)
  exact IsBoundedParabolicC2HolderOn.of_isParabolicC2On_of_gauge_ne_top
    (hu i) hlocalFinite

theorem mono
    [FiniteDimensional Real E]
    {A : Type*} {alpha : NNReal}
    {center : A → M}
    {Q R : A → Set (ParabolicPoint
      (EuclideanSpace Real (Fin (Module.finrank Real E))))}
    (hQR : ∀ i, Q i ⊆ R i)
    {u : Real → M → F}
    (hu : IsBoundedParabolicC2HolderInEuclideanChartsOn
      alpha I center R u) :
    IsBoundedParabolicC2HolderInEuclideanChartsOn
      alpha I center Q u := by
  intro i
  exact IsBoundedParabolicC2HolderOn.mono (hQR i) (hu i)

end IsBoundedParabolicC2HolderInEuclideanChartsOn

end DifferentialGeometry.Analysis.Schauder

end
