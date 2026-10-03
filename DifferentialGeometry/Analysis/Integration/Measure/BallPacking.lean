import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Zorn
import Mathlib.Topology.MetricSpace.Cover

open scoped NNReal ENNReal

namespace MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem isBounded_of_uniform_ball_measure_lower_bound
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} {r : ℝ} (hr : 0 < r)
    {v : ℝ≥0∞} (hv : 0 < v) (hvol : ∀ x ∈ S, v ≤ μ (Metric.ball x r)) :
    Bornology.IsBounded S := by
  let δ : ℝ≥0 := ⟨2 * r, by positivity⟩
  obtain ⟨N, hN⟩ : ∃ N, Maximal (fun N : Set X => N ⊆ S ∧ Metric.IsSeparated δ N) N := by
    apply zorn_subset
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, ?_⟩
    · exact Set.sUnion_subset fun s hs => (hc hs).1
    · exact hchain.pairwise_sUnion.mpr fun s hs => (hc hs).2
    · exact fun s hs => Set.subset_sUnion_of_mem hs
  have hd : Pairwise (fun x y : N => Disjoint (Metric.ball (x : X) r) (Metric.ball (y : X) r)) := by
    intro x y hxy
    apply Metric.ball_disjoint_ball
    have hs := hN.1.2 x.property y.property (fun h => hxy (Subtype.ext h))
    change (δ : ℝ≥0∞) < edist (x : X) (y : X) at hs
    rw [edist_nndist] at hs
    have hn : δ < nndist (x : X) (y : X) := ENNReal.coe_lt_coe.mp hs
    have hr' : 2 * r < dist (x : X) (y : X) := hn
    linarith
  have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion μ hv
    (fun x : N => measurableSet_ball (x := (x : X)) (ε := r)) hd (measure_ne_top μ _)
  have hNfin : N.Finite := by
    have hall : ({x : N | v ≤ μ (Metric.ball (x : X) r)} : Set N) = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hvol x (hN.1.1 x.property)
    rw [hall] at hfin
    exact Set.finite_coe_iff.mpr (Set.finite_univ_iff.mp hfin)
  have hcover := Metric.IsCover.of_maximal_isSeparated hN
  exact ((Bornology.isBounded_biUnion hNfin).mpr fun _ _ =>
    Metric.isBounded_closedBall).subset hcover.subset_iUnion_closedBall

end MeasureTheory
