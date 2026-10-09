import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData

/-!
S-CH11-FIX6 patched-at-path（astra `History/PreparedSpatialQueryReserve` 的 elaboration 修补；下游
`PreparedSpatialPhysicalVolumeEvent` 有 `open private … from` 本路径）。陈述 / 证明思路逐字不变，两处：
(a) `S.radius_eq_on_activation_band …`（`open private` 进来的 helper，dot-notation 不解析）→
    opened-private 名 `radius_eq_on_activation_band S …`；
(b) `hfitj` 里 `rw [hσj]`（目标里是 `let` 变量 `σ`，`hσj` 左端是它的值，rw 看不到）→ 先
    `have hσj' : σ = (S.state j).radius := hσj` 再 `rw [hσj']`。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow
universe u

namespace PreparedSpatialChain

open private activation nat_le_activation
  horizon_lt_half_activation radius_eq_on_activation_band from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff

/-- Select the actual delayed-radius class, with a strict native time buffer. -/
private theorem exists_query_activation_class
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hshift0 : (S.state 0).shift = 0)
    (hradius0 : ∀ t : ℝ, (S.state 0).parameters.neckRadius t = (S.state 0).radius)
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    {T : ℝ} (hT : 0 < T) :
    let σ := (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T
    ∃ j : ℕ,
      σ = (S.state j).radius ∧
      (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
        ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
          T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
      (S.state j).shift < T / 2 ∧ T < (3 : ℝ) ^ j := by
  classical
  dsimp only
  by_cases hfirst : T ≤ (5 / 6 : ℝ)
  · have hradius : ∀ m : ℕ,
        (S.state m).parameters.neckRadius T = (S.state 0).radius := by
      intro m
      induction m with
      | zero => exact hradius0 T
      | succ m ih =>
        have hp : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
        have hact : T ≤ (5 / 6 : ℝ) * 3 ^ m := by nlinarith
        exact ((S.successor m).radius_before_activation T hact).trans ih
    refine ⟨0, ?_, Or.inl ⟨rfl, hfirst⟩, ?_, ?_⟩
    · change (S.state (Nat.ceil T + 1)).parameters.neckRadius T = _
      exact hradius _
    · rw [hshift0]
      exact div_pos hT (by norm_num)
    · simpa only [pow_zero] using hfirst.trans_lt (by norm_num : (5 / 6 : ℝ) < 1)
  · have hafter : activation 0 < T := by
      simpa only [activation, pow_zero, mul_one] using lt_of_not_ge hfirst
    have hex : ∃ m : ℕ, T ≤ activation m :=
      ⟨Nat.ceil T, (Nat.le_ceil T).trans (nat_le_activation _)⟩
    cases hfind : Nat.find hex with
    | zero =>
      have hupper : T ≤ activation 0 := by
        simpa only [hfind] using Nat.find_spec hex
      exact False.elim ((not_le_of_gt hafter) hupper)
    | succ k =>
      have hleft : activation k < T :=
        lt_of_not_ge (Nat.find_min hex (by rw [hfind]; omega))
      have hright : T ≤ activation (k + 1) := by
        simpa only [hfind] using Nat.find_spec hex
      have hkT : (k : ℝ) < T := (nat_le_activation k).trans_lt hleft
      have hkceil : k ≤ Nat.ceil T := by
        exact_mod_cast hkT.le.trans (Nat.le_ceil T)
      have hhalf : preparedSpatialHorizon k < T / 2 :=
        (horizon_lt_half_activation k).trans (by linarith)
      have hlast : (S.state k).history.time (Fin.last (S.state k).history.eventCount) ≤
          preparedSpatialHorizon k := by
        simpa only [(S.state k).horizon_eq] using (S.state k).history.time_le_horizon
      have hcapacity : T < (3 : ℝ) ^ (k + 1) := by
        have hp : (0 : ℝ) < 3 ^ (k + 1) := pow_pos (by norm_num) _
        dsimp only [activation] at hright
        nlinarith
      refine ⟨k + 1, ?_, Or.inr ⟨k, rfl, hleft, hright⟩, ?_, hcapacity⟩
      · change (S.state (Nat.ceil T + 1)).parameters.neckRadius T = _
        exact radius_eq_on_activation_band S k (Nat.ceil T + 1)
          (Nat.succ_le_succ hkceil) hleft hright
      · rw [hshift k]
        exact hlast.trans_lt hhalf

end PreparedSpatialChain

/-- The actual observation radius fits its own prepared threshold and a strict
native backward window, including the old side of every activation endpoint. -/
theorem PreparedSpatialChain.exists_small_test_reserve_in_same_native_class
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {cMax : ℝ}
    (S : PreparedSpatialChain pBase C P g)
    (hcMax : 0 < cMax)
    (hfit : ∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax)
    (hshift0 : (S.state 0).shift = 0)
    (hradius0 : ∀ t : ℝ, (S.state 0).parameters.neckRadius t = (S.state 0).radius)
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    {T r : ℝ} (hr : 0 < r) (hT : 2 * r ^ 2 < T)
    (hsmall :
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T / 100 < r) :
    let σ := (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T
    ∃ j : ℕ,
      σ = (S.state j).radius ∧
      (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
        ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
          T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
      (S.state j).shift < T - (σ / 100) ^ 2 ∧
      T < (3 : ℝ) ^ j ∧
      0 < σ / 100 ∧
      σ / 100 ≤ cMax / Real.sqrt (S.state j).prepared.Qall ∧
      (let M := (S.state j).prepared.Qall
       let c := (σ / 100) * Real.sqrt M
       1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
       (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
       (S.state j).prepared.Qzero ≤ M ∧
       0 < c ∧ c ≤ cMax ∧ σ / 100 = c / Real.sqrt M ∧
       c ^ 2 / M < T - (S.state j).shift) := by
  let σ := (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T
  let b := σ / 100
  have hTpos : 0 < T := lt_of_le_of_lt (by positivity) hT
  have hσ : 0 < σ :=
    (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius_pos
      T hTpos.le
  have hb : 0 < b := div_pos hσ (by norm_num)
  have hbr : b < r := hsmall
  have hbsq : b ^ 2 < r ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hbr) (add_pos hr hb)
    nlinarith
  have hwindow : T / 2 < T - b ^ 2 := by linarith
  obtain ⟨j, hσj, hband, hshiftHalf, hcapacity⟩ :=
    S.exists_query_activation_class hshift0 hradius0 hshift hTpos
  let M := (S.state j).prepared.Qall
  let c := b * Real.sqrt M
  have hM : 0 < M := (S.state j).prepared.Qall_pos
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hfitj : σ * Real.sqrt M ≤ 100 * cMax := by
    have hσj' : σ = (S.state j).radius := hσj
    rw [hσj']
    exact hfit j
  have hc : 0 < c := mul_pos hb hsqrt
  have hc_le : c ≤ cMax := by
    dsimp only [c, b]
    nlinarith [hcMax]
  have hreserve : b ≤ cMax / Real.sqrt M :=
    (le_div_iff₀ hsqrt).mpr hc_le
  have hceq : b = c / Real.sqrt M := by
    apply (eq_div_iff (ne_of_gt hsqrt)).mpr
    rfl
  have hcsq : c ^ 2 / M = b ^ 2 := by
    dsimp only [c]
    rw [mul_pow, Real.sq_sqrt hM.le]
    field_simp [ne_of_gt hM]
  have hbirth : (S.state j).prepared.Qbirth ≤ M := by
    dsimp only [M]
    rw [(S.state j).prepared.Qall_eq]
    exact le_max_left _ _
  have hzero : (S.state j).prepared.Qzero ≤ M := by
    dsimp only [M]
    rw [(S.state j).prepared.Qall_eq]
    exact le_max_right _ _
  have hcanonical : max 1 (max (S.state j).prepared.qcan (S.state j).prepared.qs) ≤ M :=
    (S.state j).prepared.Qbirth_ge.trans hbirth
  have hone : 1 ≤ M := (le_max_left _ _).trans hcanonical
  have hcan : (S.state j).prepared.qcan ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hcanonical)
  have hspatial : (S.state j).prepared.qs ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hcanonical)
  refine ⟨j, hσj, hband, hshiftHalf.trans hwindow, hcapacity, hb, hreserve,
    hone, hcan, hspatial, hbirth, hzero, hc, hc_le, hceq, ?_⟩
  rw [hcsq]
  linarith [hshiftHalf.trans hwindow]

/-- Attach the retained quality of the very same activation-selected native class. -/
theorem PreparedSpatialChain.exists_small_test_reserve_in_same_native_class_with_reserve_quality
    {Dstar εReserve : ℝ}
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {cMax : ℝ}
    (S : PreparedSpatialChain pBase C P g)
    (hquality : ∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve)
    (hcMax : 0 < cMax)
    (hfit : ∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax)
    (hshift0 : (S.state 0).shift = 0)
    (hradius0 : ∀ t : ℝ, (S.state 0).parameters.neckRadius t = (S.state 0).radius)
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    {T r : ℝ} (hr : 0 < r) (hT : 2 * r ^ 2 < T)
    (hsmall :
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T / 100 < r) :
    let σ := (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T
    ∃ j : ℕ,
      (S.state j).prepared.HasReserveQuality Dstar εReserve ∧
      σ = (S.state j).radius ∧
      (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
        ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
          T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
      (S.state j).shift < T - (σ / 100) ^ 2 ∧
      T < (3 : ℝ) ^ j ∧
      0 < σ / 100 ∧
      σ / 100 ≤ cMax / Real.sqrt (S.state j).prepared.Qall ∧
      (let M := (S.state j).prepared.Qall
       let c := (σ / 100) * Real.sqrt M
       1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
       (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
       (S.state j).prepared.Qzero ≤ M ∧
       0 < c ∧ c ≤ cMax ∧ σ / 100 = c / Real.sqrt M ∧
       c ^ 2 / M < T - (S.state j).shift) := by
  obtain ⟨j, hj⟩ := S.exists_small_test_reserve_in_same_native_class
    hcMax hfit hshift0 hradius0 hshift hr hT hsmall
  exact ⟨j, hquality j, hj⟩

end GC.GeneralFlow
