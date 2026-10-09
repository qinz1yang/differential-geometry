import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Density
import Mathlib.Topology.Semicontinuity.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import Mathlib.Topology.Sequences
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedIntervalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment

section

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_regularizedC1Action_lt_of_regularizedCost_le
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) (A ε : ℝ) (hε : 0 < ε)
    (hcost : H.regularizedCost first last hle T B u v p q ≤ (A : WithTop ℝ)) :
    ∃ r ∈ H.regularizedC1ActionValues first last hle T u v p q, r < A + ε := by
  rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar] at hcost
  have hne : (H.regularizedC1ActionValues first last hle T u v p q).Nonempty := by
    by_contra h
    rw [H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p q
      (Set.not_nonempty_iff_eq_empty.mp h)] at hcost
    exact WithTop.not_top_le_coe A hcost
  have hlt : H.regularizedC1Cost first last hle T u v p q < ((A + ε : ℝ) : WithTop ℝ) :=
    hcost.trans_lt (WithTop.coe_lt_coe.mpr (lt_add_of_pos_right A hε))
  obtain ⟨_, ⟨r, hr, rfl⟩, hbound⟩ :=
    exists_lt_of_csInf_lt (hne.image (fun r : ℝ => (r : WithTop ℝ))) hlt
  exact ⟨r, hr, WithTop.coe_lt_coe.mp hbound⟩

theorem isClosed_regularizedCost_sublevel
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (A : ℝ) :
    IsClosed {q : (H.stage first).Carrier | H.regularizedCost first last hle T B u v p q ≤ (A : WithTop ℝ)} := by
  classical
  let : TopologicalSpace.MetrizableSpace (H.stage first).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stage first).Carrier
  apply IsSeqClosed.isClosed
  intro q qlim hq hlim
  have happrox (n : ℕ) := exists_regularizedC1Action_lt_of_regularizedCost_le H first last hle
    T B u v hupper hscalar p (q n) A (1 / ((n : ℝ) + 1)) (by positivity) (hq n)
  choose values hvalues hbound using happrox
  have hu : 0 ≤ u := (hvalues 0).1
  have huv : u ≤ v := (hvalues 0).2.1
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := (hvalues 0).2.2.1
  have hpast : T - v ^ 2 ∈ H.stageDomain first := (hvalues 0).2.2.2.1
  let lower := -(2 * B / 3) * (v ^ 3 - u ^ 3)
  have hmem (n : ℕ) : values n ∈ Icc lower (A + 1) := by
    refine ⟨H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T u v B hscalar p (q n) (hvalues n), ?_⟩
    have heps : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    exact (hbound n).le.trans (by nlinarith [heps])
  obtain ⟨ell, _, psi, hpsi, hvaluesLim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hell : ell ≤ A := by
    have hup : Tendsto (fun n : ℕ => A + 1 / ((psi n : ℝ) + 1)) atTop (𝓝 A) := by
      simpa only [add_zero, Function.comp_def] using
        (tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hpsi.tendsto_atTop))
    exact le_of_tendsto_of_tendsto' hvaluesLim hup (fun n => (hbound (psi n)).le)
  choose alpha halpha hint hstart hend hnodes hsum using fun n => (hvalues (psi n)).2.2.2.2
  have haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) atTop (𝓝 ell) := by
    simpa only [hsum, Function.comp_def] using hvaluesLim
  obtain ⟨phi, gamma, hgamma, hphi, hconv, hAC, hInt, hgammaU, hgammaNodes, hgammaAction⟩ :=
    H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_free_endpoint first last hle
      hu huv hupper hpast p (A + 1) (max B 0) ell (le_max_right _ _) alpha
      (fun n j => (halpha n j).contMDiffOn) hint hstart hnodes
      (fun n j t ht => (neg_le_neg (le_max_left B 0)).trans (hscalar j t ht (alpha n j t)))
      (fun n => by rw [hsum n]; exact (hmem (psi n)).2) haction
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hbFirst : H.regularizedStageEnd T v jfirst.val = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast
  have hvFirst : v ∈ Icc (H.regularizedStageStart T u jfirst.val)
      (H.regularizedStageEnd T v jfirst.val) :=
    ⟨(H.regularizedStage_bounds hu huv hupperIcc hpast jfirst).2.1.trans_eq hbFirst, hbFirst.ge⟩
  have heval : Tendsto (fun n => alpha (phi n) jfirst v) atTop (𝓝 (gamma jfirst v)) :=
    (continuous_eval_const (⟨v, hvFirst⟩ : Icc (H.regularizedStageStart T u jfirst.val)
      (H.regularizedStageEnd T v jfirst.val))).continuousAt.tendsto.comp (hconv jfirst)
  have hgammaV : gamma jfirst v = qlim := by
    apply tendsto_nhds_unique heval
    simpa only [jfirst, hend, Function.comp_def] using hlim.comp (hpsi.comp hphi).tendsto_atTop
  have hext := H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
    gamma hInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hscalar j t ht (gamma j t))
  have hmember : H.regularizedExtendedAction first last T B u v gamma ∈
      H.regularizedActionValues first last hle T B u v p qlim :=
    ⟨hu, huv, hupperIcc, hpast, gamma, hAC, hgammaU, hgammaV, hgammaNodes, rfl⟩
  exact (H.regularizedCost_le_of_competitor first last hle T B u v p qlim hmember).trans
    (hext.trans_le (WithTop.coe_le_coe.mpr (hgammaAction.trans hell)))

theorem lowerSemicontinuous_regularizedCost
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) :
    LowerSemicontinuous (H.regularizedCost first last hle T B u v p) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro A
  cases A using WithTop.recTopCoe with
  | top => simpa only [preimage_univ, Iic_top] using isClosed_univ
  | coe A => exact H.isClosed_regularizedCost_sublevel first last hle T B u v hupper hscalar p A

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

end

section

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryCostLsc

theorem lowerSemicontinuous_regularizedC1Cost_past_endpoint
    (H : ObservedHistory.{uHistoryCostLsc})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (p : (H.stage last).Carrier) :
    LowerSemicontinuous (fun q => H.regularizedC1Cost first last hle T u v p q) := by
  classical
  let : TopologicalSpace.MetrizableSpace (H.stage first).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stage first).Carrier
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro bound
  cases bound using WithTop.recTopCoe with
  | top => simpa only [Iic_top, preimage_univ] using (isClosed_univ : IsClosed (univ : Set (H.stage first).Carrier))
  | coe bound =>
    apply IsSeqClosed.isClosed
    intro qseq q hqseq hq
    have hfinite (n : ℕ) : H.regularizedC1Cost first last hle T u v p (qseq n) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (hqseq n)
    choose alpha halpha hint hstart hend hnodes hminimum using fun n =>
      H.exists_regularizedC1Cost_minimizer_of_ne_top first last hle T B u v
        hupper hscalar p (qseq n) (hfinite n)
    let action (n : ℕ) := ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
    have hmember (n : ℕ) : action n ∈ H.regularizedC1ActionValues first last hle T u v p (qseq n) :=
      ⟨hu, huv, hupperIcc, hpast, alpha n, halpha n, hint n, hstart n, hend n, hnodes n, rfl⟩
    have hbound (n : ℕ) : action n ∈ Icc (-(2 * B / 3) * (v ^ 3 - u ^ 3)) bound := by
      refine ⟨H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T u v B
        hscalar p (qseq n) (hmember n), ?_⟩
      exact WithTop.coe_le_coe.mp ((hminimum n).trans_le (hqseq n))
    obtain ⟨ell, hell, phi, hphi, haction⟩ := isCompact_Icc.tendsto_subseq hbound
    have hendLimit : Tendsto (fun n => alpha (phi n) ⟨first, le_rfl, hle⟩ v) atTop (𝓝 q) := by
      simpa only [hend, Function.comp_def] using hq.comp hphi.tendsto_atTop
    obtain ⟨_, gamma, _, _, _, hgammaAC, hgammaInt, hgammaU, hgammaV, hgammaNodes, hgammaAction⟩ :=
      H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_of_tendsto_endpoint
        first last hle hu huv hupper hpast p q bound B ell (fun n => alpha (phi n))
        (fun n j => (halpha (phi n) j).contMDiffOn) (fun n => hint (phi n))
        (fun n => hstart (phi n)) hendLimit (fun n => hnodes (phi n))
        (fun n j r hr => hscalar j r hr (alpha (phi n) j r))
        (fun n => (hbound (phi n)).2) haction
    have hext := H.regularizedExtendedAction_eq_sum_action first last hu huv hupperIcc hpast
      gamma hgammaInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hscalar j r hr (gamma j r))
    have hgammaMember : H.regularizedExtendedAction first last T B u v gamma ∈
        H.regularizedActionValues first last hle T B u v p q :=
      ⟨hu, huv, hupperIcc, hpast, gamma, hgammaAC, hgammaU, hgammaV, hgammaNodes, rfl⟩
    change H.regularizedC1Cost first last hle T u v p q ≤ (bound : WithTop ℝ)
    rw [← H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar p q]
    refine (H.regularizedCost_le_of_competitor first last hle T B u v p q hgammaMember).trans ?_
    rw [hext]
    exact WithTop.coe_le_coe.mpr (hgammaAction.trans hell.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

end
