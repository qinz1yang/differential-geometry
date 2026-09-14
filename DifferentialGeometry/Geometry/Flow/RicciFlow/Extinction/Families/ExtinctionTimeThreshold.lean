import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionBound

set_option autoImplicit false

noncomputable section

open scoped Topology Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

namespace ObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem not_extinctBy_of_nonpos (T : ObservationTower P g) {B : ℝ} (hB : B ≤ 0) :
    ¬ T.ExtinctBy B := by
  rintro ⟨b, hb, hbB, _⟩
  exact (not_lt.mpr (hbB.trans hB)) hb

theorem extinctBy_of_extinctAbove_lt (T : ObservationTower P g) {B B' : ℝ}
    (hBB' : max 0 B < B') (h : T.ExtinctAbove B) : T.ExtinctBy B' :=
  ⟨B', lt_of_le_of_lt (le_max_left 0 B) hBB', le_rfl,
    h B' (lt_of_le_of_lt (le_max_left 0 B) hBB')
      (lt_of_le_of_lt (le_max_right 0 B) hBB')⟩

theorem extinctAbove_iff_forall_extinctBy (T : ObservationTower P g) {B : ℝ} :
    T.ExtinctAbove B ↔ ∀ B' : ℝ, max 0 B < B' → T.ExtinctBy B' := by
  constructor
  · intro h B' hB'
    exact T.extinctBy_of_extinctAbove_lt hB' h
  · intro h b hb hBb
    have hmax : max 0 B < b := max_lt hb hBb
    have hlo : max 0 B < (max 0 B + b) / 2 := by linarith
    have hhi : (max 0 B + b) / 2 < b := by linarith
    obtain ⟨b₀, hb₀, hb₀le, hempty⟩ := h ((max 0 B + b) / 2) hlo
    have hb₀b : b₀ ≤ b := hb₀le.trans hhi.le
    exact @ObservationTower.empty_absorbing P g T b₀ b hb₀.le hb.le hb₀b hempty

theorem uniformRecordsAbove_iff_forall_extinctBy (T : ObservationTower P g) {c A : ℝ} :
    T.UniformRecordsAbove c A ↔
      ∀ B' : ℝ, max 0 (extinctionThreshold c A) < B' → T.ExtinctBy B' :=
  (T.extinctAbove_extinctionThreshold_iff_uniformRecordsAbove.symm).trans
    (T.extinctAbove_iff_forall_extinctBy (B := extinctionThreshold c A))

theorem uniformScalarComparisonsAbove_iff_extinctAbove (T : ObservationTower P g) {c A : ℝ} :
    T.UniformScalarComparisonsAbove c A ↔ T.ExtinctAbove (extinctionThreshold c A) :=
  (T.uniformRecordsAbove_iff_uniformScalarComparisonsAbove.symm).trans
    (T.extinctAbove_extinctionThreshold_iff_uniformRecordsAbove (c := c)).symm

theorem uniformSlopeBoundsAbove_iff_extinctAbove (T : ObservationTower P g) {c A : ℝ}
    (hc : 0 < c) :
    T.UniformSlopeBoundsAbove c A ↔ T.ExtinctAbove (extinctionThreshold c A) :=
  ⟨fun h => T.extinctAbove_extinctionThreshold_of_uniformRecordsAbove
      (T.uniformRecordsAbove_of_uniformSlopeBoundsAbove hc h),
    fun h b hb hlt terminal =>
      False.elim ((ConnectedComponents.isEmpty_iff_isEmpty.mpr (h b hb hlt)).false terminal)⟩

theorem not_extinctBy_extinctionThreshold_of_nonpos (T : ObservationTower P g) {c A : ℝ}
    (h : extinctionThreshold c A ≤ 0) : ¬ T.ExtinctBy (extinctionThreshold c A) :=
  T.not_extinctBy_of_nonpos h

theorem not_extinctBy_extinctionThreshold_zero (T : ObservationTower P g) {c : ℝ} (hc : 0 < c) :
    ¬ T.ExtinctBy (extinctionThreshold c 0) :=
  T.not_extinctBy_extinctionThreshold_of_nonpos (by
    rw [(extinctionThreshold_eq_zero_iff hc le_rfl).mpr rfl])

def RecordsAtEveryPositiveHorizon (T : ObservationTower P g) (c A : ℝ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b),
    ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier,
      Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A)

theorem uniformRecordsAbove_of_recordsAtEveryPositiveHorizon (T : ObservationTower P g)
    {c A : ℝ} (h : T.RecordsAtEveryPositiveHorizon c A) : T.UniformRecordsAbove c A :=
  fun b hb _hlt terminal => h b hb terminal

theorem extinctAbove_extinctionThreshold_of_recordsAtEveryPositiveHorizon
    (T : ObservationTower P g) {c A : ℝ} (h : T.RecordsAtEveryPositiveHorizon c A) :
    T.ExtinctAbove (extinctionThreshold c A) :=
  T.uniformRecordsAbove_iff_isEmpty_above_threshold.mp
    (T.uniformRecordsAbove_of_recordsAtEveryPositiveHorizon h)

theorem recordsAtEveryPositiveHorizon_iff_records_below_threshold_and_extinctAbove
    (T : ObservationTower P g) {c A : ℝ} :
    T.RecordsAtEveryPositiveHorizon c A ↔
      ((∀ (b : ℝ) (hb : 0 < b), b ≤ extinctionThreshold c A →
        ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
          (Fin.last (T.observe b hb.le).eventCount)).Carrier,
          Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A)) ∧
       T.ExtinctAbove (extinctionThreshold c A)) := by
  constructor
  · intro h
    exact ⟨fun b hb _hle terminal => h b hb terminal,
      T.extinctAbove_extinctionThreshold_of_recordsAtEveryPositiveHorizon h⟩
  · rintro ⟨hbelow, habove⟩ b hb terminal
    by_cases hle : b ≤ extinctionThreshold c A
    · exact hbelow b hb hle terminal
    · exact False.elim ((ConnectedComponents.isEmpty_iff_isEmpty.mpr
        (habove b hb (lt_of_not_ge hle))).false terminal)

theorem bound_nonneg_of_recordsAtEveryPositiveHorizon (T : ObservationTower P g) {c A : ℝ}
    (h : T.RecordsAtEveryPositiveHorizon c A) {b : ℝ} (hb : 0 < b)
    (hne : Nonempty ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier) :
    0 ≤ A :=
  (h b hb (ConnectedComponents.mk hne.some)).some.bound_nonneg

theorem recordsAtEveryPositiveHorizon_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) (c A : ℝ) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.RecordsAtEveryPositiveHorizon
      c A := by
  intro b hb terminal
  have h0 : IsEmpty (((RetainedCoreObservationTower.empty P g).toObservationTower.observe 0
      le_rfl).stage
      (Fin.last ((RetainedCoreObservationTower.empty P g).toObservationTower.observe 0
        le_rfl).eventCount)).Carrier :=
    ⟨fun x => hP.false x⟩
  exact False.elim ((ConnectedComponents.isEmpty_iff_isEmpty.mpr
    (@ObservationTower.empty_absorbing P g
      ((RetainedCoreObservationTower.empty P g).toObservationTower) 0 b le_rfl hb.le hb.le
        h0)).false terminal)

end ObservationTower

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_extinctAbove_lt
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {B B' : ℝ} (hBB' : max 0 B < B') (h : T.toObservationTower.ExtinctAbove B) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_extinctBy M g T hbfr hctrl
    (T.toObservationTower.extinctBy_of_extinctAbove_lt hBB' h)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
