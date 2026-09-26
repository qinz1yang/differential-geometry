import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuityMinimizer
noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryAttainment

theorem exists_regularizedCost_minimizer_of_ne_top
    (H : ObservedHistory.{uHistoryAttainment})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (hB : 0 ≤ B)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hfinite : H.regularizedCost first last hle T B u v p q ≠ ⊤) :
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      H.regularizedExtendedAction first last T B u v gamma =
        H.regularizedCost first last hle T B u v p q := by
  classical
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle T B u v p q, A = ⊤ :=
    fun h => hfinite ((H.regularizedCost_eq_top_iff first last hle T B u v p q).mpr h)
  push Not at hsome
  obtain ⟨A, hA, hAtop⟩ := hsome
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hAtop
  rw [← ha] at hA
  have hu : 0 ≤ u := hA.1
  have huv : u ≤ v := hA.2.1
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := hA.2.2.1
  have hpast : T - v ^ 2 ∈ H.stageDomain first := hA.2.2.2.1
  obtain ⟨c, hc, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper hscalar p q hA (ε := 1) zero_lt_one
  let V := H.regularizedC1ActionValues first last hle T u v p q
  have hV : V.Nonempty := ⟨c, hc⟩
  have hbdd : BddBelow V :=
    H.regularizedC1ActionValues_bddBelow_of_scalar_lower first last hle T u v B hscalar p q
  obtain ⟨values, hanti, hlim, hvalues⟩ := exists_seq_tendsto_sInf hV hbdd
  choose alpha halpha hint hstart hend hnodes hsum using fun n => (hvalues n).2.2.2.2
  have haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      atTop (𝓝 (sInf V)) := by
    simpa only [hsum] using hlim
  obtain ⟨_, gamma, _, _, _, hgammaAC, hgammaInt, hgammaU, hgammaV, hgammaNodes, hgammaAction⟩ :=
    H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action first last hle
      hu huv hupper hpast p q (values 0) B (sInf V) hB alpha
      (fun n j => (halpha n j).contMDiffOn) hint hstart hend hnodes
      (fun n j t ht => hscalar j t ht (alpha n j t))
      (fun n => by rw [hsum n]; exact hanti (Nat.zero_le n)) haction
  have hext := H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
    gamma hgammaInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hscalar j t ht (gamma j t))
  have hmember : H.regularizedExtendedAction first last T B u v gamma ∈
      H.regularizedActionValues first last hle T B u v p q :=
    ⟨hu, huv, hupperIcc, hpast, gamma, hgammaAC, hgammaU, hgammaV, hgammaNodes, rfl⟩
  refine ⟨gamma, hgammaAC, hgammaInt, hgammaU, hgammaV, hgammaNodes, ?_⟩
  apply le_antisymm ?_ (H.regularizedCost_le_of_competitor first last hle T B u v p q hmember)
  rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar p q, hext]
  apply le_csInf (hV.image (fun r : ℝ => (r : WithTop ℝ)))
  rintro _ ⟨r, hr, rfl⟩
  exact WithTop.coe_le_coe.mpr (hgammaAction.trans (csInf_le hbdd hr))

theorem exists_regularizedCost_spatial_minimizer
    (H : ObservedHistory.{uHistoryAttainment})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u v p q ≠ ⊤) :
    ∃ (q : (H.stage first).Carrier) (m : ℝ)
      (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier),
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      H.regularizedExtendedAction first last T B u v gamma = (m : WithTop ℝ) ∧
      (m : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v p q ∧
      H.regularizedCost first last hle T B u v p q = (m : WithTop ℝ) ∧
      ∀ z : (H.stage first).Carrier, (m : WithTop ℝ) ≤ H.regularizedCost first last hle T B u v p z := by
  classical
  obtain ⟨q₀, hq₀⟩ := hfinite
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle T B u v p q₀, A = ⊤ :=
    fun h => hq₀ ((H.regularizedCost_eq_top_iff first last hle T B u v p q₀).mpr h)
  push Not at hsome
  obtain ⟨A, hA, hAtop⟩ := hsome
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hAtop
  rw [← ha] at hA
  have hu : 0 ≤ u := hA.1
  have huv : u ≤ v := hA.2.1
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := hA.2.2.1
  have hpast : T - v ^ 2 ∈ H.stageDomain first := hA.2.2.2.1
  obtain ⟨c, hc, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper hscalar p q₀ hA (ε := 1) zero_lt_one
  let V : Set ℝ := {r | ∃ q : (H.stage first).Carrier,
    r ∈ H.regularizedC1ActionValues first last hle T u v p q}
  have hV : V.Nonempty := ⟨c, q₀, hc⟩
  have hbdd : BddBelow V := by
    refine ⟨-(2 * B / 3) * (v ^ 3 - u ^ 3), ?_⟩
    rintro r ⟨q, hr⟩
    exact H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T u v B hscalar p q hr
  obtain ⟨values, hanti, hlim, hvalues⟩ := exists_seq_tendsto_sInf hV hbdd
  choose endpoints hvaluesEnd using hvalues
  choose alpha halpha hint hstart hend hnodes hsum using fun n => (hvaluesEnd n).2.2.2.2
  have haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      atTop (𝓝 (sInf V)) := by
    simpa only [hsum] using hlim
  obtain ⟨_, gamma, _, _, _, hgammaAC, hgammaInt, hgammaU, hgammaNodes, hgammaAction⟩ :=
    H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_free_endpoint first last hle
      hu huv hupper hpast p (values 0) (max B 0) (sInf V) (le_max_right _ _) alpha
      (fun n j => (halpha n j).contMDiffOn) hint hstart hnodes
      (fun n j t ht => (neg_le_neg (le_max_left B 0)).trans (hscalar j t ht (alpha n j t)))
      (fun n => by rw [hsum n]; exact hanti (Nat.zero_le n)) haction
  let q := gamma ⟨first, le_rfl, hle⟩ v
  let m := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  have hext : H.regularizedExtendedAction first last T B u v gamma = (m : WithTop ℝ) :=
    H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
      gamma hgammaInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hscalar j t ht (gamma j t))
  have hmember : (m : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v p q :=
    ⟨hu, huv, hupperIcc, hpast, gamma, hgammaAC, hgammaU, rfl, hgammaNodes, hext⟩
  have hmin (z : (H.stage first).Carrier) :
      (m : WithTop ℝ) ≤ H.regularizedCost first last hle T B u v p z := by
    rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar]
    by_cases hne : (H.regularizedC1ActionValues first last hle T u v p z).Nonempty
    · apply le_csInf (hne.image (fun r : ℝ => (r : WithTop ℝ)))
      rintro _ ⟨r, hr, rfl⟩
      exact WithTop.coe_le_coe.mpr (hgammaAction.trans (csInf_le hbdd ⟨z, hr⟩))
    · rw [H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p z
        (Set.not_nonempty_iff_eq_empty.mp hne)]
      exact le_top
  exact ⟨q, m, gamma, hgammaAC, hgammaInt, hgammaU, rfl, hgammaNodes, hext, hmember,
    le_antisymm (H.regularizedCost_le_of_competitor first last hle T B u v p q hmember) (hmin q), hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
