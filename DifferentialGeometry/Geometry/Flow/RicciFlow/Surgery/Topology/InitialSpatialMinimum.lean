import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.MinimumPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionRegularCrossingRecenter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPoleAction

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_low_action_seed_off_event_times_of_parabolicallyRmControlledBall
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r) :
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (a : ℝ)
      (q₀ : (H.stage first).Carrier) (L₀ : ℝ),
      0 < a ∧ a ≤ r / 2 ∧
      t.val - a ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
      L₀ ∈ H.regularizedC1ActionValues first (H.activeStage t) hle t 0 a p q₀ ∧
      2 * a * L₀ - 6 * a ^ 2 < 0 := by
  classical
  have hr : 0 < r := hball.1
  let S : Finset ℝ := Finset.univ.image fun j : Fin (H.eventCount + 1) => Real.sqrt (t.val - H.time j)
  have hinf : (Ioc (0 : ℝ) (r / 2)).Infinite := Set.Ioc_infinite (by linarith)
  obtain ⟨a, ha, haS⟩ := hinf.exists_notMem_finset S
  have hapos : 0 < a := ha.1
  obtain ⟨a', hat, hclock, A, hA, action, hmem, -, -, hneg⟩ :=
    H.exists_short_low_action_seed_of_parabolicallyRmControlledBall t p hball a hapos ha.2
  have hdom : t.val - a ^ 2 ∈ H.stageDomain (H.activeStage a') := by
    rw [← hclock]
    exact H.activeStage_mem a'
  have hne : H.time (H.activeStage a') ≠ t.val - a ^ 2 := by
    intro heq
    apply haS
    refine Finset.mem_image.mpr ⟨H.activeStage a', Finset.mem_univ _, ?_⟩
    rw [heq, sub_sub_cancel, Real.sqrt_sq hapos.le]
  have hlower : H.time (H.activeStage a') < t.val - a ^ 2 :=
    lt_of_le_of_ne (H.time_le_of_mem_stageDomain hdom) hne
  have hupper : t.val - a ^ 2 < H.stageEndTime (H.activeStage a') := by
    cases hk : H.activeStage a' using Fin.lastCases with
    | last =>
      rw [H.stageEndTime_last]
      have ha2 : 0 < a ^ 2 := pow_pos hapos 2
      linarith [t.property.2]
    | cast i =>
      rw [hk] at hdom
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at hdom
      rw [H.stageEndTime_castSucc]
      exact hdom.2
  exact ⟨H.activeStage a', H.activeStage_mono hat, a,
    A.point (H.activeStage a') le_rfl (H.activeStage_mono hat), action, hapos, ha.2,
    ⟨hlower, hupper⟩, hmem, hneg⟩

theorem exists_uniform_initial_spatial_regularizedCost_minimum_lt_three_mul
    (E rTerm qDeriv a₀ ρ : ℝ) (Cderiv : ℝ≥0) (hE : 0 ≤ E) (hrTerm : 0 < rTerm)
    (hqDeriv : 0 < qDeriv) (ha₀ : 0 < a₀) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ →
      (∀ j : Fin H.eventCount,
        parameters.recenterConstant * parameters.delta (H.time j.succ) ≤ 1 / 2) →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        ((records i).static b).hasCanonicalWindow) →
      ∀ (t : Icc (0 : ℝ) H.horizon),
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p rTerm →
      Real.sqrt t.val ≤ E →
      ∃ (q : (H.stage 0).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues 0 (H.activeStage t) (Fin.zero_le _) t 0
          (Real.sqrt t.val) p q ∧
        H.regularizedCost 0 (H.activeStage t) (Fin.zero_le _) t (3 / a₀) 0
          (Real.sqrt t.val) p q = (L : WithTop ℝ) ∧
        (∀ z : (H.stage 0).Carrier, (L : WithTop ℝ) ≤
          H.regularizedCost 0 (H.activeStage t) (Fin.zero_le _) t (3 / a₀) 0
            (Real.sqrt t.val) p z) ∧
        L < 3 * Real.sqrt t.val := by
  have hB : 0 ≤ 3 / a₀ := (div_pos (by norm_num : (0 : ℝ) < 3) ha₀).le
  obtain ⟨mN, RN, εN, δN, hRN, hεN, hδN, hnode⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_nonregular_node_of_recenter_budget.{u}
      (3 * E + 1) (3 / a₀) E rTerm qDeriv a₀ ρ Cderiv hB hE hrTerm hqDeriv ha₀ hρ
  obtain ⟨mP, RP, εP, δP, hRP, hεP, hδP, hpoint⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_nonregular_initial_point_of_recenter_budget.{u}
      (3 * E + 1) (3 / a₀) E rTerm qDeriv a₀ ρ Cderiv hB hE hrTerm hqDeriv ha₀ hρ
  refine ⟨max mN mP, max RN RP, min εN εP, min δN δP, hRN.trans_le (le_max_left _ _),
    lt_min hεN hεP, lt_min hδN hδP, ?_⟩
  intro H parameters hm hmodel haccuracy hpc hδ hρp records hfixed hscalarInitial hcanonical
    t hderiv p hball htE
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hscalar (j : Fin (H.eventCount + 1)) (s : ℝ) (hs : s ∈ H.stageDomain j)
      (z : (H.stage j).Carrier) : -(3 / a₀) ≤ metricScalarAt (H.stageMetric j s) z := by
    have hs0 : 0 ≤ s := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right hs0)
    have hlow : -(3 / a₀) ≤ -3 / (a₀ + s) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hlow.trans (hpreserve.1 j s hs z).2
  obtain ⟨first, hle, a, q₀, L₀, ha, har, hpast, hseed, hneg⟩ :=
    H.exists_low_action_seed_off_event_times_of_parabolicallyRmControlledBall t p hball
  have hr2 := hball.radius_sq_le_time
  have hrt : rTerm ≤ Real.sqrt t.val :=
    Real.le_sqrt_of_sq_le hr2
  have haw : a ≤ Real.sqrt t.val := har.trans (by linarith)
  have hwpast : t.val - Real.sqrt t.val ^ 2 ∈ H.stageDomain 0 := by
    rw [Real.sq_sqrt t.property.1, sub_self]
    simpa only [H.time_zero] using H.time_mem_stageDomain 0
  have hfloor (first' : Fin (H.eventCount + 1)) (v : ℝ)
      (γ : (j : H.StageInterval first' (H.activeStage t)) → ℝ → (H.stage j.val).Carrier)
      (j : H.StageInterval first' (H.activeStage t)) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (γ j s) :=
    hscalar j.val _ (H.mapsTo_regularizedStage_Ioo t 0 v j.val hs) _
  obtain ⟨q, L, hmem, hcost, hmin, hlt⟩ := H.exists_spatial_regularizedCost_minimum_lt_three_mul
    0 (H.activeStage t) (T := t.val) (B := 3 / a₀) (Abar := 3 * E + 1) (w := Real.sqrt t.val)
    (H.activeStage_mem t) hscalar p (by linarith)
    (by
      intro first' hle' v hv hvw hvdom gamma hgamma hint hrecent hnodes hsum i hf hl _
      by_contra hbad
      have hlarge := hnode H parameters ((le_max_left _ _).trans hm)
        ((le_max_left _ _).trans hmodel) (haccuracy.trans (min_le_left _ _)) hpc
        (fun j => (hδ j).trans (min_le_left _ _)) hρp records hfixed hscalarInitial t hderiv p
        hball first' hle' v hv.le (hvw.trans htE) hvdom gamma hgamma hint
        (hfloor first' v gamma) hrecent hnodes i hf hl (hcanonical i) hbad
      linarith)
    (by
      intro i hl q' A' hk hkw hA' hA'lt
      by_contra hnone
      obtain ⟨-, hv0, -, -, alpha, halpha, hint, hrecent, hq', hnodes, hsum⟩ := hA'
      have hti : H.time i.succ ≤ t.val :=
        (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
      have hstart : t.val - Real.sqrt (t.val - H.time i.succ) ^ 2 = H.time i.succ := by
        rw [Real.sq_sqrt (sub_nonneg.mpr hti)]
        ring
      have hlarge := hpoint H parameters ((le_max_right _ _).trans hm)
        ((le_max_right _ _).trans hmodel) (haccuracy.trans (min_le_right _ _)) hpc
        (fun j => (hδ j).trans (min_le_right _ _)) hρp records hfixed hscalarInitial i
        (hcanonical i) t hderiv p hball (Real.sqrt (t.val - H.time i.succ)) hv0
        (hkw.le.trans htE) hstart alpha halpha hint (hfloor i.succ _ alpha) hrecent hnodes
        (by rw [hq']; exact hnone)
      rw [hsum] at hlarge
      linarith)
    hwpast first (Fin.zero_le _) hle ha haw hpast q₀ L₀ hseed hneg
  exact ⟨q, L, hmem, hcost, hmin, hlt⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
