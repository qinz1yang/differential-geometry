import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

namespace ObservedHistory

def IsExtinctAtHorizon (H : ObservedHistory.{u}) : Prop :=
  IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

theorem isExtinctAtHorizon_iff_of_samePresentation {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) : H.IsExtinctAtHorizon ↔ K.IsExtinctAtHorizon := by
  have hstage := R.stage_eq (Fin.last H.eventCount)
  rw [show Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last H.eventCount) =
      Fin.last K.eventCount from
    Fin.ext (by rw [Fin.val_cast, Fin.val_last, Fin.val_last]; exact R.count_eq)] at hstage
  unfold IsExtinctAtHorizon
  rw [hstage]

end ObservedHistory

namespace ObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem observe_eq_history (T : ObservationTower P g) (n : ℕ) :
    (T.observe (n : ℝ) (Nat.cast_nonneg n)).SamePresentation (T.history n) :=
  (T.observe_eq_atIndex n (n : ℝ) (Nat.cast_nonneg n) le_rfl).trans
    ((T.atIndex_independent n n (n : ℝ) (Nat.cast_nonneg n) le_rfl
        (by exact_mod_cast le_rfl)).trans (T.integer_restrict n n le_rfl))

theorem towerExtinct_iff_exists_extinct_level (T : ObservationTower P g) :
    towerExtinct T ↔ ∃ n : ℕ, 0 < n ∧
      (T.observe (n : ℝ) (Nat.cast_nonneg n)).IsExtinctAtHorizon := by
  constructor
  · rintro ⟨b, hb, hempty⟩
    refine ⟨Nat.ceil b + 1, Nat.succ_pos _, ?_⟩
    have hbn : b ≤ ((Nat.ceil b + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil b).trans (by exact_mod_cast Nat.le_succ (Nat.ceil b))
    let : IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier := hempty
    exact ObservationTower.empty_absorbing T b ((Nat.ceil b + 1 : ℕ) : ℝ) hb
      (Nat.cast_nonneg (Nat.ceil b + 1)) hbn
  · rintro ⟨n, _hn, h⟩
    exact ⟨(n : ℝ), Nat.cast_nonneg n, h⟩

theorem towerExtinct_iff_exists_eventually_extinct (T : ObservationTower P g) :
    towerExtinct T ↔ ∃ b : ℝ, 0 < b ∧ ∀ (b' : ℝ) (hb' : 0 ≤ b'),
      b ≤ b' → (T.observe b' hb').IsExtinctAtHorizon := by
  constructor
  · rintro ⟨b, hb, hempty⟩
    rcases eq_or_lt_of_le hb with h0 | hpos
    · subst h0
      have h1 : (0 : ℝ) ≤ 1 := zero_le_one
      let : IsEmpty ((T.observe 0 hb).stage (Fin.last (T.observe 0 hb).eventCount)).Carrier := hempty
      have hfirst : IsEmpty ((T.observe 1 h1).stage
          (Fin.last (T.observe 1 h1).eventCount)).Carrier :=
        ObservationTower.empty_absorbing T 0 1 hb h1 zero_le_one
      refine ⟨1, one_pos, fun b' hb' h1b' => ?_⟩
      let : IsEmpty ((T.observe 1 h1).stage (Fin.last (T.observe 1 h1).eventCount)).Carrier := hfirst
      exact ObservationTower.empty_absorbing T 1 b' h1 hb' h1b'
    · refine ⟨b, hpos, fun b' hb' hbb' => ?_⟩
      let : IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier := hempty
      exact ObservationTower.empty_absorbing T b b' hb hb' hbb'
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb.le, h b hb.le le_rfl⟩

theorem towerExtinct_iff_exists_eventually_extinct_level (T : ObservationTower P g) :
    towerExtinct T ↔ ∃ n : ℕ, 0 < n ∧
      ∀ m : ℕ, n ≤ m → (T.history m).IsExtinctAtHorizon := by
  constructor
  · intro h
    obtain ⟨b, _hb, hbnd⟩ := (towerExtinct_iff_exists_eventually_extinct T).mp h
    refine ⟨Nat.ceil b + 1, Nat.succ_pos _, fun m hm => ?_⟩
    have hbm : b ≤ (m : ℝ) :=
      (Nat.le_ceil b).trans
        (by exact_mod_cast (le_trans (Nat.le_succ (Nat.ceil b)) hm))
    have hobs : (T.observe (m : ℝ) (Nat.cast_nonneg m)).IsExtinctAtHorizon :=
      hbnd (m : ℝ) (Nat.cast_nonneg m) hbm
    exact (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation (observe_eq_history T m)).mp hobs
  · rintro ⟨n, hn, h⟩
    exact (towerExtinct_iff_exists_extinct_level T).mpr
      ⟨n, hn, (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation (observe_eq_history T n)).mpr
        (h n le_rfl)⟩

theorem towerExtinct_of_history_extinct (T : ObservationTower P g) {n : ℕ} (hn : 0 < n)
    (h : (T.history n).IsExtinctAtHorizon) : towerExtinct T :=
  (towerExtinct_iff_exists_extinct_level T).mpr
    ⟨n, hn, (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation (observe_eq_history T n)).mpr h⟩

theorem towerExtinct_of_records_above_threshold (T : ObservationTower P g) {c A : ℝ}
    (h : ∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
      ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier,
        Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A)) :
    towerExtinct T := by
  have hpos : 0 < max 1 (extinctionThreshold c A + 1) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨max 1 (extinctionThreshold c A + 1), hpos.le, ?_⟩
  have hlt : extinctionThreshold c A < max 1 (extinctionThreshold c A + 1) :=
    lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  exact (T.records_iff_final_empty_of_threshold_lt _ hpos.le hlt).mp (h _ hpos hlt)

theorem not_forall_isExtinctAtHorizon (T : ObservationTower P g) [Nonempty P.Carrier] :
    ¬ ∀ (b : ℝ) (hb : 0 ≤ b), (T.observe b hb).IsExtinctAtHorizon :=
  fun h => not_isEmpty_terminal_at_zero T (h 0 le_rfl)

theorem isExtinctAtHorizon_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) (n : ℕ) :
    ((RetainedCoreObservationTower.empty P g).toObservationTower.history n).IsExtinctAtHorizon := by
  unfold ObservedHistory.IsExtinctAtHorizon
  change IsEmpty P.Carrier
  exact hP

end ObservationTower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

theorem exists_pos_nat_gt_extinctionThreshold {c A : ℝ} :
    ∃ n : ℕ, 0 < n ∧ extinctionThreshold c A < (n : ℝ) := by
  refine ⟨Nat.ceil (extinctionThreshold c A) + 1, Nat.succ_pos _, ?_⟩
  have h1 : extinctionThreshold c A ≤ ((Nat.ceil (extinctionThreshold c A) : ℕ) : ℝ) :=
    Nat.le_ceil _
  have h2 : ((Nat.ceil (extinctionThreshold c A) : ℕ) : ℝ) <
      ((Nat.ceil (extinctionThreshold c A) + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  linarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
