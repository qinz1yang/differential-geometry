import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffAccuracyGluing

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow.PreparedSpatialChain
universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

private theorem state_delta_compat
    (S : PreparedSpatialChain pBase C P g)
    (m n : ℕ) (hmn : m ≤ n) (t : ℝ) (ht : t ≤ preparedSpatialHorizon m) :
    (S.state n).parameters.delta t = (S.state m).parameters.delta t := by
  have hclock : Monotone preparedSpatialHorizon := by
    apply monotone_nat_of_le_succ
    intro k
    have h := (S.successor k).initial_prefix.1.horizon_le
    change (S.state k).history.horizon ≤ (S.state (k + 1)).history.horizon at h
    simpa only [(S.state k).horizon_eq, (S.state (k + 1)).horizon_eq] using
      h
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact ((S.successor n).parameters_past t (ht.trans (hclock hmn))).1.trans ih

private theorem diagonal_delta_antitone
    (S : PreparedSpatialChain pBase C P g) :
    AntitoneOn
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
      (Ici 0) := by
  apply CutoffParameters.diagonal_delta_antitone
  · intro m n hmn t ht
    exact (state_delta_compat S (m + 1) (n + 1) (Nat.add_le_add_right hmn 1)
      t (ht.2.trans (nat_lt_three_pow m).le)).symm
  · intro n s hs t ht hst
    exact (S.state (n + 1)).delta_antitone hs.1 ht.1 hst

private theorem diagonal_delta_at_three_pow
    (S : PreparedSpatialChain pBase C P g) (n : ℕ) :
    (CutoffParameters.diagonal (fun k => (S.observation k).parameters)).delta
      ((3 : ℝ) ^ n) = S.accuracy n := by
  have hcast : (((3 : ℕ) ^ n : ℕ) : ℝ) = (3 : ℝ) ^ n := by norm_cast
  have hceil : Nat.ceil ((3 : ℝ) ^ n) = (3 : ℕ) ^ n := by
    rw [← hcast, Nat.ceil_natCast]
  have hindex : n + 1 ≤ (3 : ℕ) ^ n + 1 := by
    have h : n < (3 : ℕ) ^ n := by exact_mod_cast nat_lt_three_pow n
    omega
  have hcompat := state_delta_compat S (n + 1) ((3 : ℕ) ^ n + 1)
    hindex ((3 : ℝ) ^ n) le_rfl
  have hafter : preparedSpatialHorizon n < (3 : ℝ) ^ n := by
    have hcapacity := (S.state n).native_lt_capacity
    have hhorizon := (S.state n).horizon_affine
    rw [(S.state n).horizon_eq] at hhorizon
    linarith
  change (S.state (Nat.ceil ((3 : ℝ) ^ n) + 1)).parameters.delta
    ((3 : ℝ) ^ n) = S.accuracy n
  rw [hceil, hcompat]
  exact (S.successor n).delta_after _ hafter

/-- The accuracy of the actual observation diagonal tends to zero. Its values
at the geometric checkpoints are the selected accuracies of the same chain. -/
theorem diagonal_delta_tendsto
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) :
    Filter.Tendsto
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
      Filter.atTop (nhds (0 : ℝ)) := by
  let q := CutoffParameters.diagonal (fun n => (S.observation n).parameters)
  change Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ))
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨(3 : ℝ) ^ n, ?_⟩
  intro t ht
  have hT : 0 ≤ (3 : ℝ) ^ n := (pow_pos (by norm_num) n).le
  have ht0 : 0 ≤ t := hT.trans ht
  have hpositive := q.delta_pos t ht0
  rw [Real.dist_eq, sub_zero, abs_of_pos hpositive]
  calc
    q.delta t ≤ q.delta ((3 : ℝ) ^ n) :=
      diagonal_delta_antitone S hT ht0 ht
    _ = S.accuracy n := diagonal_delta_at_three_pow S n
    _ ≤ 1 / ((n : ℝ) + 2) := S.accuracy_le n
    _ ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    _ < ε := hn

end GC.GeneralFlow.PreparedSpatialChain
