import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionTimeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower

noncomputable section

open Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

namespace ObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def extinctionTime (T : ObservationTower P g) : ℝ :=
  sInf {B : ℝ | T.ExtinctBy B}

theorem bddBelow_extinctBySet (T : ObservationTower P g) :
    BddBelow {B : ℝ | T.ExtinctBy B} := by
  refine ⟨0, fun B hB => ?_⟩
  obtain ⟨b, hb, hbB, _⟩ := hB
  exact (lt_of_lt_of_le hb hbB).le

theorem nonneg_extinctionTime (T : ObservationTower P g) : 0 ≤ T.extinctionTime := by
  rcases Set.eq_empty_or_nonempty {B : ℝ | T.ExtinctBy B} with hemp | hne
  · rw [extinctionTime, hemp, Real.sInf_empty]
  · refine le_csInf hne fun B hB => ?_
    obtain ⟨b, hb, hbB, _⟩ := hB
    exact (lt_of_lt_of_le hb hbB).le

theorem extinctionTime_le_of_extinctBy (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctBy B) : T.extinctionTime ≤ B :=
  csInf_le (bddBelow_extinctBySet T) h

theorem extinctBy_of_extinctionTime_lt (T : ObservationTower P g) {B : ℝ}
    (hne : ∃ B' : ℝ, T.ExtinctBy B') (h : T.extinctionTime < B) : T.ExtinctBy B := by
  obtain ⟨B', hB', hB'B⟩ :=
    exists_lt_of_csInf_lt (show {B' : ℝ | T.ExtinctBy B'}.Nonempty from hne) h
  exact T.extinctBy_mono hB'B.le hB'

theorem extinctAbove_extinctionTime (T : ObservationTower P g)
    (hne : ∃ B' : ℝ, T.ExtinctBy B') : T.ExtinctAbove T.extinctionTime := by
  intro b hb hlt
  obtain ⟨B', hB', hB'b⟩ :=
    exists_lt_of_csInf_lt (show {B' : ℝ | T.ExtinctBy B'}.Nonempty from hne) hlt
  obtain ⟨b₀, hb₀, hb₀B, hemp⟩ := hB'
  exact @ObservationTower.empty_absorbing P g T b₀ b hb₀.le hb.le (hb₀B.trans hB'b.le) hemp

theorem extinctionTime_le_of_extinctAbove (T : ObservationTower P g) {B : ℝ} (hB : 0 ≤ B)
    (h : T.ExtinctAbove B) : T.extinctionTime ≤ B := by
  have hB1pos : 0 < B + 1 := by linarith
  have hne : {B' : ℝ | T.ExtinctBy B'}.Nonempty :=
    ⟨B + 1, B + 1, hB1pos, le_rfl, h (B + 1) hB1pos (by linarith)⟩
  rw [extinctionTime, csInf_le_iff (bddBelow_extinctBySet T) hne]
  intro b hb
  by_contra hlt
  have hBb : B < b := not_le.mp hlt
  obtain ⟨x, hBx, hxb⟩ := exists_between hBb
  have hxpos : 0 < x := lt_of_le_of_lt hB hBx
  have hxS : T.ExtinctBy x := ⟨x, hxpos, le_rfl, h x hxpos hBx⟩
  exact absurd (hb hxS) (not_le.mpr hxb)

theorem extinctionTime_eq_zero_of_forall_not (T : ObservationTower P g)
    (h : ∀ B : ℝ, ¬ T.ExtinctBy B) : T.extinctionTime = 0 := by
  have hemp : {B : ℝ | T.ExtinctBy B} = ∅ := by
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact h B
  rw [extinctionTime, hemp, Real.sInf_empty]

theorem extinctionTime_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier] (g : P.Metric) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.extinctionTime = 0 := by
  refine le_antisymm ?_ (nonneg_extinctionTime _)
  rw [extinctionTime, csInf_le_iff (bddBelow_extinctBySet _) ⟨1, extinctBy_empty P g one_pos⟩]
  intro b hb
  by_contra hlt
  have hbpos : 0 < b := lt_of_not_ge hlt
  exact absurd (hb (extinctBy_empty P g (by linarith : (0 : ℝ) < b / 2))) (not_le.mpr (by linarith))

theorem extinctAbove_neg_one_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctAbove (-1) ∧
      ¬ (RetainedCoreObservationTower.empty P g).toObservationTower.extinctionTime ≤ (-1) :=
  ⟨extinctAbove_empty P g (-1), by
    rw [extinctionTime_empty P g]
    norm_num⟩


end ObservationTower

theorem hasControlledExtinctionWithin_of_tower_extinctionTime
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (hne : ∃ B : ℝ, T.toObservationTower.ExtinctBy B) :
    HasControlledExtinctionWithin M.toClosedOrientedManifold g
      (max 1 (T.toObservationTower.extinctionTime + 1)) :=
  letI : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  hasControlledExtinctionWithin_of_tower_extinctBy T.toObservationTower
    (fun b hb i => (T.hasCutCapCompletion_toObservationTower hbfr b hb i).some)
    (fun b hb i => T.coreInclusionIsSmoothEmbedding_toObservationTower b hb i)
    (fun b hb i => T.poincareStandardDiscarded_toObservationTower hctrl b hb i)
    (ObservationTower.extinctBy_of_extinctAbove T.toObservationTower
      (T.toObservationTower.extinctAbove_extinctionTime hne))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
