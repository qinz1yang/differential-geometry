import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import DifferentialGeometry.Topology.Manifold.CurveIntervalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuityStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Attainment
noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryC1Attainment

theorem exists_regularizedC1Cost_minimizer_of_ne_top
    (H : ObservedHistory.{uHistoryC1Attainment})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hfinite : H.regularizedC1Cost first last hle T u v p q ≠ ⊤) :
    ∃ beta : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (beta j)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (beta j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      beta ⟨last, hle, le_rfl⟩ u = p ∧ beta ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = beta ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = beta ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      (((∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (beta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) : ℝ) : WithTop ℝ) =
        H.regularizedC1Cost first last hle T u v p q := by
  classical
  have hne : (H.regularizedC1ActionValues first last hle T u v p q).Nonempty := by
    by_contra hn
    exact hfinite (H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p q
      (Set.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨value, hvalue⟩ := hne
  have hu : 0 ≤ u := hvalue.1
  have huv : u ≤ v := hvalue.2.1
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := hvalue.2.2.1
  have hpast : T - v ^ 2 ∈ H.stageDomain first := hvalue.2.2.2.1
  have hB : 0 ≤ max B 0 := le_max_right _ _
  have hscalar' (j : H.StageInterval first last)
      (t : ℝ) (ht : t ∈ Ioo (H.regularizedStageStart T u j.val)
        (H.regularizedStageEnd T v j.val)) (x : (H.stage j.val).Carrier) :
      -(max B 0) ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x :=
    (neg_le_neg (le_max_left B 0)).trans (hscalar j t ht x)
  have hcost := H.regularizedCost_eq_regularizedC1Cost first last hle T (max B 0) u v
    hupper hscalar' p q
  have hfiniteAC : H.regularizedCost first last hle T (max B 0) u v p q ≠ ⊤ := by
    simpa only [hcost] using hfinite
  obtain ⟨gamma, hgammaAC, hgammaInt, hgammaU, hgammaV, hgammaNodes, hgammaMin⟩ :=
    H.exists_regularizedCost_minimizer_of_ne_top first last hle T (max B 0) u v
      hB hupper hscalar' p q hfiniteAC
  have hgammaC1 := H.contMDiffOn_stage_of_regularizedExtendedAction_eq_regularizedCost
    first last hle hu huv hupper hpast hscalar' gamma hgammaAC hgammaInt hgammaNodes
    (by simpa only [hgammaU, hgammaV] using hgammaMin)
  choose beta hbeta heq using fun j =>
    DifferentialGeometry.Topology.exists_contMDiff_extension_Icc (hgammaC1 j)
  have hbounds := H.regularizedStage_bounds hu huv hupperIcc hpast
  have hlag (j : H.StageInterval first last) :
      EqOn (H.stageRegularizedLagrangian j.val T (beta j))
        (H.stageRegularizedLagrangian j.val T (gamma j))
        (uIoo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) := by
    intro r hr
    rw [uIoo_of_le (hbounds j).2.1] at hr
    have hev : beta j =ᶠ[𝓝 r] gamma j := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact heq j (Ioo_subset_Icc_self ht)
    have hval := hev.self_of_nhds
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
    have hvel : lVelocity (I := ThreeModel) (beta j) r =
        lVelocity (I := ThreeModel) (gamma j) r := by
      with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
    unfold stageRegularizedLagrangian
    rw [hval, hvel]
  have hbetaInt (j : H.StageInterval first last) := (hgammaInt j).congr_uIoo (hlag j).symm
  have hsum : (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (beta j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) =
      ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    apply Finset.sum_congr rfl
    intro j _
    apply H.stageRegularizedAction_congr
    intro r hr
    rw [uIoo_of_le (hbounds j).2.1] at hr
    exact heq j (Ioo_subset_Icc_self hr)
  refine ⟨beta, hbeta, hbetaInt, ?_, ?_, ?_, ?_⟩
  · have hh := heq ⟨last, hle, le_rfl⟩ ⟨le_rfl, (hbounds ⟨last, hle, le_rfl⟩).2.1⟩
    rw [H.regularizedStageStart_eq_of_mem_Icc hu hupperIcc] at hh
    exact hh.trans hgammaU
  · have hh := heq ⟨first, le_rfl, hle⟩ ⟨(hbounds ⟨first, le_rfl, hle⟩).2.1, le_rfl⟩
    rw [H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast] at hh
    exact hh.trans hgammaV
  · intro i hf hl
    obtain ⟨z, hzold, hznew⟩ := hgammaNodes i hf hl
    have ho := heq ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
      ⟨le_rfl, (hbounds ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩).2.1⟩
    have hn := heq ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
      ⟨(hbounds ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩).2.1, le_rfl⟩
    rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl] at ho
    rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
    exact ⟨z, hzold.trans ho.symm, hznew.trans hn.symm⟩
  · have hext := H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
      gamma hgammaInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hscalar' j t ht (gamma j t))
    rw [hsum, ← hext, hgammaMin, hcost]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
