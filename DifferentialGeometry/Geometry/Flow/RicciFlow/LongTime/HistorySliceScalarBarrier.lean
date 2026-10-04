import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialScalarBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
namespace FILL910
universe u
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness

/-- Transport a metric assertion along the actual stage and metric identifications. -/
theorem stageMetricAssertion_of_heq {P Q : OrientedThreeStage.{u}} {g : P.Metric}
    {h : Q.Metric} (hP : P = Q) (hg : HEq g h)
    (A : (S : OrientedThreeStage.{u}) → S.Metric → Prop) (ha : A P g) : A Q h := by
  cases hP
  cases hg
  exact ha

theorem postStage_prefix {P : OrientedThreeStage.{u}} {g : P.Metric}
    (O : ObservationTower P g) (t : ℝ) (ht : 0 ≤ t) :
    GC.LongTime.postStage O t = (O.history (Nat.ceil t)).stage
      ((O.history (Nat.ceil t)).activeStage
        ⟨t, ht, by rw [O.horizon_eq]; exact Nat.le_ceil t⟩) := by
  have he : O.observe (max t 0) (le_max_right t 0) = O.observe t ht := by
    have hsub : (⟨max t 0, le_max_right t 0⟩ : {s : ℝ // 0 ≤ s}) = ⟨t, ht⟩ :=
      Subtype.ext (max_eq_left ht)
    exact congrArg (fun a : {s : ℝ // 0 ≤ s} => O.observe a.val a.property) hsub
  change (O.observe (max t 0) (le_max_right t 0)).stage
    (Fin.last (O.observe (max t 0) (le_max_right t 0)).eventCount) = _
  refine (congrArg (fun H : ObservedHistory.{u} => H.stage (Fin.last H.eventCount)) he).trans ?_
  change (O.history (Nat.ceil t)).stage
    (Fin.castLE _ (Fin.last (O.observe t ht).eventCount)) = _
  congr 1

theorem postMetric_prefix {P : OrientedThreeStage.{u}} {g : P.Metric}
    (O : ObservationTower P g) (t : ℝ) (ht : 0 ≤ t) :
    HEq (GC.LongTime.postMetric O t) ((O.history (Nat.ceil t)).stageMetric
      ((O.history (Nat.ceil t)).activeStage
        ⟨t, ht, by rw [O.horizon_eq]; exact Nat.le_ceil t⟩) t) := by
  let H := O.history (Nat.ceil t)
  let a : Icc (0 : ℝ) H.horizon := ⟨t, ht, by rw [O.horizon_eq]; exact Nat.le_ceil t⟩
  have hmem : t ∈ (H.restrict a).stageDomain (Fin.last (H.restrict a).eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc]
    change H.time (H.activeStage a) ≤ t ∧ t ≤ t
    exact ⟨H.activeStage_time_le a, le_rfl⟩
  have hm := H.restrict_stageMetric a (Fin.last (H.restrict a).eventCount) t hmem
  have hj : Fin.castLE
      (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1)
      (Fin.last (H.restrict a).eventCount) = H.activeStage a := by
    apply Fin.ext
    rfl
  rw [hj] at hm
  have he : O.observe (max t 0) (le_max_right t 0) = O.observe t ht := by
    have hsub : (⟨max t 0, le_max_right t 0⟩ : {s : ℝ // 0 ≤ s}) = ⟨t, ht⟩ :=
      Subtype.ext (max_eq_left ht)
    exact congrArg (fun a : {s : ℝ // 0 ≤ s} => O.observe a.val a.property) hsub
  have hmetric : ∀ (J J' : ObservedHistory.{u}), J = J' → ∀ s τ : ℝ, s = τ →
      HEq (J.stageMetric (Fin.last J.eventCount) s)
        (J'.stageMetric (Fin.last J'.eventCount) τ) := by
    intro J J' hJ s τ hs
    cases hJ
    cases hs
    rfl
  exact (hmetric _ _ he (max t 0) t (max_eq_left ht)).trans hm

theorem A03a_stageMetric_scalar_lower (H : ObservedHistory.{u}) {p : CutoffParameters}
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ y : (H.stage 0).Carrier, -3 / (2 * c) ≤ metricScalarAt (H.initialMetric 0) y) :
    ∀ j : Fin (H.eventCount + 1), ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -3 / (2 * (t + c)) ≤ metricScalarAt (H.stageMetric j t) x := by
  have hi := stageInitial_scalarLowerBound_of_history cutoff hc
    (by simpa only [H.time_zero, zero_add] using h0)
  intro j
  cases j using Fin.lastCases with
  | last =>
    intro t ht x
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc] at ht
    simp only [ObservedHistory.stageMetric, Fin.lastCases_last]
    split_ifs with h
    · apply closedSlab_scalarLowerBarrier_le h (H.time_nonneg _) hc (H.finalSlab h)
      · intro y
        rw [H.final_initial h]
        exact hi _ y
      · exact ht
    · have he : t = H.time (Fin.last H.eventCount) := by
        linarith [H.time_le_horizon]
      subst t
      exact hi _ x
  | cast i =>
    intro t ht x
    simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    apply incomingSlab_scalarLowerBarrier_le (H.time_nonneg _) hc (H.event i).incoming
    · intro y
      rw [H.event_initial i]
      exact hi _ y
    · simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using ht

theorem A03b_postMetric_scalar_lower {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    {c : ℝ} (hc : 0 < c) (h0 : ∀ x : P.Carrier, -3 / (2 * c) ≤ metricScalarAt g x) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : (GC.LongTime.postStage F.observation t).Carrier,
      -3 / (2 * (t + c)) ≤ metricScalarAt (GC.LongTime.postMetric F.observation t) x := by
  intro t ht
  let O := F.observation
  let H := O.history (Nat.ceil t)
  let a : Icc (0 : ℝ) H.horizon := ⟨t, ht, by rw [O.horizon_eq]; exact Nat.le_ceil t⟩
  have hinit : ∀ y : (H.stage 0).Carrier,
      -3 / (2 * c) ≤ metricScalarAt (H.initialMetric 0) y := by
    have hi := (O.initial (Nat.ceil t)).stageZero_scalarLowerBound h0
    simpa only [ObservedHistory.time_zero, zero_add] using hi
  have hb := A03a_stageMetric_scalar_lower H (records (Nat.ceil t)) hc hinit
    (H.activeStage a) t (H.activeStage_mem a)
  exact stageMetricAssertion_of_heq (postStage_prefix O t ht).symm
    (postMetric_prefix O t ht).symm
    (fun S m => ∀ x : S.Carrier, -3 / (2 * (t + c)) ≤ metricScalarAt m x) hb

end FILL910
