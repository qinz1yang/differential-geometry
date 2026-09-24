import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionTimeBound

set_option autoImplicit false

noncomputable section

open scoped Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

namespace ObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def ExtinctByLevelWithin (T : ObservationTower P g) (B : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ B ∧ (T.history n).IsExtinctAtHorizon

theorem extinctByLevelWithin_mono (T : ObservationTower P g) {B B' : ℝ} (hBB' : B ≤ B')
    (h : T.ExtinctByLevelWithin B) : T.ExtinctByLevelWithin B' := by
  obtain ⟨n, hn, hnB, hext⟩ := h
  exact ⟨n, hn, hnB.trans hBB', hext⟩

theorem extinctBy_of_history_isExtinctAtHorizon (T : ObservationTower P g) {n : ℕ} {B : ℝ}
    (hn : 0 < n) (hnB : (n : ℝ) ≤ B) (h : (T.history n).IsExtinctAtHorizon) :
    T.ExtinctBy B :=
  ⟨(n : ℝ), Nat.cast_pos.mpr hn, hnB,
    (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation
      (T.observe_eq_history n)).mpr h⟩

theorem extinctAbove_of_history_isExtinctAtHorizon (T : ObservationTower P g) {n : ℕ} {B : ℝ}
    (hnB : (n : ℝ) ≤ B) (h : (T.history n).IsExtinctAtHorizon) :
    T.ExtinctAbove B := by
  intro b hb hBb
  have hnb : (n : ℝ) ≤ b := hnB.trans hBb.le
  have hobs : IsEmpty ((T.observe (n : ℝ) (Nat.cast_nonneg n)).stage
      (Fin.last (T.observe (n : ℝ) (Nat.cast_nonneg n)).eventCount)).Carrier :=
    (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation
      (T.observe_eq_history n)).mpr h
  exact @ObservationTower.empty_absorbing P g T (n : ℝ) b (Nat.cast_nonneg n) hb.le hnb hobs

theorem extinctBy_of_extinctByLevelWithin (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctByLevelWithin B) : T.ExtinctBy B := by
  obtain ⟨n, hn, hnB, hext⟩ := h
  exact T.extinctBy_of_history_isExtinctAtHorizon hn hnB hext

theorem extinctAbove_of_extinctByLevelWithin (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctByLevelWithin B) : T.ExtinctAbove B := by
  obtain ⟨n, _hn, hnB, hext⟩ := h
  exact T.extinctAbove_of_history_isExtinctAtHorizon hnB hext

theorem extinctByLevelWithin_of_extinctBy (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctBy B) : T.ExtinctByLevelWithin ((max 1 (Nat.ceil B) : ℕ) : ℝ) := by
  obtain ⟨b, hb, hbB, hempty⟩ := h
  let n := max 1 (Nat.ceil B)
  have hbn : b ≤ (n : ℝ) :=
    hbB.trans ((Nat.le_ceil B).trans (by exact_mod_cast le_max_right 1 (Nat.ceil B)))
  have hempty' : IsEmpty ((T.observe (n : ℝ) (Nat.cast_nonneg n)).stage
      (Fin.last (T.observe (n : ℝ) (Nat.cast_nonneg n)).eventCount)).Carrier :=
    @ObservationTower.empty_absorbing P g T b (n : ℝ) hb.le (Nat.cast_nonneg n) hbn hempty
  exact ⟨n, lt_of_lt_of_le one_pos (le_max_left 1 (Nat.ceil B)), le_rfl,
    (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation
      (T.observe_eq_history n)).mp hempty'⟩

theorem exists_extinctByLevelWithin_iff_towerExtinct (T : ObservationTower P g) :
    (∃ B : ℝ, T.ExtinctByLevelWithin B) ↔ towerExtinct T := by
  constructor
  · rintro ⟨B, hB⟩
    exact T.towerExtinct_of_extinctBy (T.extinctBy_of_extinctByLevelWithin hB)
  · intro h
    obtain ⟨B, hB⟩ := T.exists_extinctBy_iff_towerExtinct.mpr h
    exact ⟨((max 1 (Nat.ceil B) : ℕ) : ℝ), T.extinctByLevelWithin_of_extinctBy hB⟩

theorem uniformRecordsAbove_of_extinctByLevelWithin_extinctionThreshold
    (T : ObservationTower P g) {c A : ℝ} (h : T.ExtinctByLevelWithin (extinctionThreshold c A)) :
    T.UniformRecordsAbove c A :=
  T.extinctAbove_extinctionThreshold_iff_uniformRecordsAbove.mp
    (T.extinctAbove_of_extinctByLevelWithin h)

theorem towerExtinct_of_extinctByLevelWithin_extinctionThreshold (T : ObservationTower P g)
    {c A : ℝ} (h : T.ExtinctByLevelWithin (extinctionThreshold c A)) : towerExtinct T :=
  T.towerExtinct_of_uniformRecordsAbove
    (T.uniformRecordsAbove_of_extinctByLevelWithin_extinctionThreshold h)

theorem pos_of_extinctByLevelWithin (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctByLevelWithin B) : 0 < B := by
  obtain ⟨n, hn, hnB, _⟩ := h
  exact lt_of_lt_of_le (Nat.cast_pos.mpr hn) hnB

theorem not_extinctByLevelWithin_of_nonpos (T : ObservationTower P g) {B : ℝ} (hB : B ≤ 0) :
    ¬ T.ExtinctByLevelWithin B :=
  fun h => absurd (T.pos_of_extinctByLevelWithin h) (not_lt.mpr hB)

theorem not_extinctByLevelWithin_of_lt_one (T : ObservationTower P g) {B : ℝ} (hB : B < 1) :
    ¬ T.ExtinctByLevelWithin B := by
  rintro ⟨n, hn, hnB, _⟩
  have h1n : 1 ≤ n := by omega
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1n
  linarith

theorem extinctBy_half_empty_not_extinctByLevelWithin (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctBy (1 / 2) ∧
      ¬ (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctByLevelWithin
        (1 / 2) :=
  ⟨extinctBy_empty P g (by norm_num), not_extinctByLevelWithin_of_lt_one _ (by norm_num)⟩

theorem extinctByLevelWithin_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) {B : ℝ} (hB : 1 ≤ B) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctByLevelWithin B :=
  ⟨1, one_pos, by simpa using hB, isExtinctAtHorizon_empty P g 1⟩

end ObservationTower

theorem hasControlledExtinctionWithin_of_retainedCoreTower_history_isExtinctAtHorizon
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {n : ℕ} (hn : 0 < n) (h : (T.toObservationTower.history n).IsExtinctAtHorizon) :
    HasControlledExtinctionWithin M.toClosedOrientedManifold g (n : ℝ) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_timeLe M g T hbfr hctrl
    (T.toObservationTower.extinctBy_of_history_isExtinctAtHorizon hn le_rfl h)

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_extinctByLevelWithin
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {B : ℝ} (hB : T.toObservationTower.ExtinctByLevelWithin B) :
    HasControlledExtinctionWithin M.toClosedOrientedManifold g B :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_timeLe M g T hbfr hctrl
    (T.toObservationTower.extinctBy_of_extinctByLevelWithin hB)

theorem hasExtinctObservationTower_of_retainedCoreTower_extinctByLevelWithin
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ}
    (h : T.toObservationTower.ExtinctByLevelWithin (extinctionThreshold c A)) :
    hasExtinctObservationTower M g :=
  hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove M g T hbfr hctrl
    (T.toObservationTower.uniformRecordsAbove_of_extinctByLevelWithin_extinctionThreshold h)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
