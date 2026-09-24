import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

theorem stageAt_nonempty_of_lt_last (H : ObservedHistory.{u}) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u < H.time (Fin.last H.eventCount)) :
    Nonempty (H.stageAt ⟨u, hu0, hu.le.trans (H.time_le_horizon_at (Fin.last H.eventCount))⟩).Carrier := by
  rcases Fin.eq_castSucc_or_eq_last (H.activeStage ⟨u, hu0, hu.le.trans (H.time_le_horizon_at _)⟩) with
    ⟨i, hi⟩ | hi
  · rw [stageAt, hi]
    exact H.incoming_nonempty i
  · exfalso
    have hle := H.activeStage_time_le ⟨u, hu0, hu.le.trans (H.time_le_horizon_at _)⟩
    rw [hi] at hle
    exact absurd hle (not_le.mpr hu)

theorem time_last_le_of_nonemptySliceBounded (H : ObservedHistory.{u}) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ t : Icc (0 : ℝ) H.horizon, Nonempty (H.stageAt t).Carrier → t.1 ≤ B) :
    H.time (Fin.last H.eventCount) ≤ B := by
  by_contra hle
  have hT : B < H.time (Fin.last H.eventCount) := not_le.mp hle
  have hu0 : 0 ≤ (B + H.time (Fin.last H.eventCount)) / 2 := by linarith
  have huT : (B + H.time (Fin.last H.eventCount)) / 2 < H.time (Fin.last H.eventCount) := by linarith
  have huH : (B + H.time (Fin.last H.eventCount)) / 2 ≤ H.horizon :=
    huT.le.trans (H.time_le_horizon_at (Fin.last H.eventCount))
  have hne := H.stageAt_nonempty_of_lt_last hu0 huT
  have hbnd := hb ⟨(B + H.time (Fin.last H.eventCount)) / 2, hu0, huH⟩ hne
  have : B < (B + H.time (Fin.last H.eventCount)) / 2 := by linarith
  linarith

theorem mul_le_of_step {N : ℕ} (f : Fin (N + 1) → ℝ) (δ : ℝ)
    (hnonneg : ∀ i : Fin (N + 1), 0 ≤ f i)
    (hstep : ∀ i : Fin N, f i.succ + δ ≤ f i.castSucc) : N * δ ≤ f 0 := by
  have key : ∀ n : ℕ, ∀ g : Fin (n + 1) → ℝ, (∀ i : Fin (n + 1), 0 ≤ g i) →
      (∀ i : Fin n, g i.succ + δ ≤ g i.castSucc) → n * δ + g (Fin.last n) ≤ g 0 := by
    intro n
    induction n with
    | zero => intro g _ _; simp
    | succ n ih =>
      intro g hg hgs
      have hih := ih (fun j => g j.castSucc) (fun i => hg i.castSucc) (fun i => hgs i.castSucc)
      have hlast := hgs (Fin.last n)
      have hz : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 1 + 1)) = 0 := rfl
      have hl : ((Fin.last n).succ : Fin (n + 1 + 1)) = Fin.last (n + 1) := rfl
      rw [hz] at hih
      rw [hl] at hlast
      have hnat : ((n + 1 : ℕ) : ℝ) * δ = (n : ℝ) * δ + δ := by push_cast; ring
      rw [hnat]
      linarith [hg (Fin.last (n + 1)), hih, hlast]
  linarith [key N f hnonneg hstep, hnonneg (Fin.last N)]

theorem eventCount_mul_le_of_debit (H : ObservedHistory.{u}) {δ : ℝ}
    (vol : Fin (H.eventCount + 1) → ℝ) (hvol : ∀ i, 0 ≤ vol i)
    (hdebit : ∀ i : Fin H.eventCount, vol i.succ + δ ≤ vol i.castSucc) :
    (H.eventCount : ℝ) * δ ≤ vol 0 :=
  mul_le_of_step vol δ hvol hdebit


theorem mul_le_time_of_gap (H : ObservedHistory.{u}) {η : ℝ}
    (hgap : ∀ i : Fin H.eventCount, H.time i.castSucc + η ≤ H.time i.succ) :
    ∀ i : Fin (H.eventCount + 1), (i.val : ℝ) * η ≤ H.time i := by
  intro i
  induction i using Fin.induction with
  | zero => simp [H.time_zero]
  | succ i ih =>
    have hiv : i.castSucc.val = i.val := rfl
    rw [hiv] at ih
    have hsucc : i.succ.val = i.val + 1 := rfl
    have hnat : ((i.succ.val : ℕ) : ℝ) * η = (i.val : ℝ) * η + η := by
      rw [hsucc]
      push_cast
      ring
    rw [hnat]
    linarith [hgap i]

theorem eventCount_le_div_of_gap (H : ObservedHistory.{u}) {η B : ℝ} (hη : 0 < η)
    (hgap : ∀ i : Fin H.eventCount, H.time i.castSucc + η ≤ H.time i.succ)
    (hB : H.time (Fin.last H.eventCount) ≤ B) :
    (H.eventCount : ℝ) ≤ B / η := by
  have hmul := H.mul_le_time_of_gap hgap (Fin.last H.eventCount)
  rw [div_eq_mul_inv]
  exact (le_div_iff₀ hη).mpr (hmul.trans hB)

theorem eventCount_mul_le_of_debit_div (H : ObservedHistory.{u}) {δ : ℝ} {vol : Fin (H.eventCount + 1) → ℝ}
    (hvol : ∀ i, 0 ≤ vol i)
    (hdebit : ∀ i : Fin H.eventCount, vol i.succ + δ ≤ vol i.castSucc) (hδ : 0 < δ) :
    (H.eventCount : ℝ) ≤ vol 0 / δ :=
  (le_div_iff₀ hδ).mpr (H.eventCount_mul_le_of_debit vol hvol hdebit)

theorem exists_extinct_finiteHistory_bounds (H : ObservedHistory.{u}) {δ B : ℝ}
    [Nonempty (H.stage 0).Carrier] [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (vol : Fin (H.eventCount + 1) → ℝ) (hvol : ∀ i, 0 ≤ vol i)
    (hdebit : ∀ i : Fin H.eventCount, vol i.succ + δ ≤ vol i.castSucc) (hδ : 0 < δ)
    (hB0 : 0 ≤ B)
    (hb : ∀ t : Icc (0 : ℝ) H.horizon, Nonempty (H.stageAt t).Carrier → t.1 ≤ B) :
    ∃ F : FiniteSurgeryHistory.{u},
      F.1 = H.restrict (H.stageTime (Fin.last H.eventCount)) ∧
      F.1.eventCount = H.eventCount ∧ F.1.horizon = H.time (Fin.last H.eventCount) ∧
      0 < F.1.horizon ∧ F.1.horizon ≤ B ∧
      IsEmpty (F.1.stage (Fin.last F.1.eventCount)).Carrier ∧
      (H.eventCount : ℝ) ≤ vol 0 / δ := by
  obtain ⟨F, hF, hcount, hhor, hpos, _, hempty⟩ := H.exists_extinct_finiteHistory
  exact ⟨F, hF, hcount, hhor, hpos, hhor.trans_le (H.time_last_le_of_nonemptySliceBounded hB0 hb),
    hempty, H.eventCount_mul_le_of_debit_div hvol hdebit hδ⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
