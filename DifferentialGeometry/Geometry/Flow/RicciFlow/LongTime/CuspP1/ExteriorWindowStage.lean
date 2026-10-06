import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowBuild

/-!
# CP1-D7 (5): the active stage is locally constant away from surgery times
-/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
namespace GC.LongTime.CuspP1
universe u

/-- `τ` is not the time of any event of any history of the tower -/
def NonSurgeryTime_CPD7 {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    (τ : ℝ) : Prop :=
  ∀ (N : ℕ) (k : Fin ((T.history N).eventCount + 1)), (T.history N).time k ≠ τ

theorem exists_const_activeStage_CPD7 (H : ObservedHistory.{u}) {τ : ℝ} (h0 : 0 ≤ τ)
    (h1 : τ ≤ H.horizon) (hne : ∀ k, H.time k ≠ τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (t : ℝ) (h0' : 0 ≤ t) (h1' : t ≤ H.horizon), |t - τ| < δ →
      H.activeStage ⟨t, h0', h1'⟩ = H.activeStage ⟨τ, h0, h1⟩ := by
  have hfin : (range H.time).Finite := Set.finite_range _
  have hopen : IsOpen (range H.time)ᶜ := hfin.isClosed.isOpen_compl
  have hτ : τ ∈ (range H.time)ᶜ := fun ⟨k, hk⟩ => hne k hk
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen τ hτ
  refine ⟨δ, hδ, fun t h0' h1' ht => ?_⟩
  have hfree : ∀ k, H.time k ∈ ball τ δ → False := fun k hk => hball hk ⟨k, rfl⟩
  set j := H.activeStage ⟨τ, h0, h1⟩ with hj
  set j' := H.activeStage ⟨t, h0', h1'⟩ with hj'
  have htj : H.time j ≤ τ := H.activeStage_time_le ⟨τ, h0, h1⟩
  have htj' : H.time j' ≤ t := H.activeStage_time_le ⟨t, h0', h1'⟩
  have hjt : H.time j ≤ t := by
    by_contra hcon
    push Not at hcon
    apply hfree j
    rw [mem_ball, Real.dist_eq, abs_lt]
    rw [abs_lt] at ht
    constructor <;> linarith
  have hjτ : H.time j' ≤ τ := by
    by_contra hcon
    push Not at hcon
    apply hfree j'
    rw [mem_ball, Real.dist_eq, abs_lt]
    rw [abs_lt] at ht
    constructor <;> linarith
  exact le_antisymm (H.le_activeStage ⟨τ, h0, h1⟩ j' hjτ) (H.le_activeStage ⟨t, h0', h1'⟩ j hjt)


/-- the active stage is right-continuous: it is constant on `[τ, τ + δ)` (event times allowed) -/
theorem exists_right_const_activeStage_CPD7 (H : ObservedHistory.{u}) {τ : ℝ} (h0 : 0 ≤ τ)
    (h1 : τ ≤ H.horizon) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (t : ℝ) (h0' : 0 ≤ t) (h1' : t ≤ H.horizon), τ ≤ t → t < τ + δ →
      H.activeStage ⟨t, h0', h1'⟩ = H.activeStage ⟨τ, h0, h1⟩ := by
  classical
  have hfin : (range H.time ∩ Ioi τ).Finite := (Set.finite_range _).inter_of_left _
  by_cases hemp : (range H.time ∩ Ioi τ).Nonempty
  · set m := hfin.toFinset.min' (by simpa using hemp) with hm
    have hmmem : m ∈ range H.time ∩ Ioi τ :=
      hfin.mem_toFinset.mp (Finset.min'_mem hfin.toFinset (by simpa using hemp))
    have hτm : τ < m := mem_Ioi.mp hmmem.2
    have hmle : ∀ y ∈ range H.time ∩ Ioi τ, m ≤ y := fun y hy =>
      Finset.min'_le _ _ (by simpa using hy)
    refine ⟨m - τ, by linarith, fun t h0' h1' hτt htm => ?_⟩
    apply le_antisymm
    · apply H.le_activeStage ⟨τ, h0, h1⟩
      by_contra hcon
      push Not at hcon
      have := hmle _ ⟨⟨_, rfl⟩, hcon⟩
      have h2 := H.activeStage_time_le ⟨t, h0', h1'⟩
      simp only at h2
      linarith
    · exact H.activeStage_mono (a := ⟨τ, h0, h1⟩) (b := ⟨t, h0', h1'⟩) hτt
  · refine ⟨1, one_pos, fun t h0' h1' hτt _ => ?_⟩
    apply le_antisymm
    · apply H.le_activeStage ⟨τ, h0, h1⟩
      by_contra hcon
      push Not at hcon
      exact hemp ⟨_, ⟨_, rfl⟩, hcon⟩
    · exact H.activeStage_mono (a := ⟨τ, h0, h1⟩) (b := ⟨t, h0', h1'⟩) hτt

end GC.LongTime.CuspP1
