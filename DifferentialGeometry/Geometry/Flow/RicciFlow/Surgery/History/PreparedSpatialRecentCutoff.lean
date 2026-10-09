import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain

/-!
S-CH11-FIX6 patched-at-path（astra `History/PreparedSpatialRecentCutoff` 的 elaboration 修补；
下游 `PreparedSpatialQueryReserve` / `PreparedSpatialQualitySurgery` /
`PreparedSpatialQualityTransport` 有 `open private … from` 本路径，故不做 port + shim）。
陈述 / 证明思路逐字不变，两处：
(a) `record_bound_of_prefix` 里 `simpa only [hj] using hrecords j`（simp 进不了 `HEq` 的依赖类型位）
    → `have h := hrecords j; rw [hj] at h; exact h`；
(b) `cutoff_factor_antitone` 里 `add_le_add_right (Nat.cast_le.mpr hmn) 2`（本树 Mathlib 的左右
    约定相反，给出 `2 + m ≤ 2 + n`）→ 先 `hmn'` 再 `by linarith`。
-/

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow.PreparedSpatialChain
universe u

private def activation (n : ℕ) : ℝ := (5 / 6 : ℝ) * 3 ^ n

private theorem activation_pos (n : ℕ) : 0 < activation n :=
  mul_pos (by norm_num) (pow_pos (by norm_num) n)

private theorem activation_succ (n : ℕ) : activation (n + 1) = 3 * activation n := by
  simp only [activation, pow_succ]
  ring

private theorem activation_strictMono : StrictMono activation := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [activation_succ]
  linarith [activation_pos n]

private theorem nat_le_activation (n : ℕ) : (n : ℝ) ≤ activation n := by
  induction n with
  | zero => norm_num [activation]
  | succ n ih =>
    have hsmall : (5 / 6 : ℝ) ≤ activation n := by
      have hpow : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
      dsimp only [activation]
      nlinarith
    rw [activation_succ, Nat.cast_add, Nat.cast_one]
    linarith

private theorem horizon_lt_half_activation (n : ℕ) :
    preparedSpatialHorizon n < activation n / 2 := by
  cases n with
  | zero => norm_num [preparedSpatialHorizon, activation]
  | succ n =>
    have hp : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
    simp only [preparedSpatialHorizon, activation, pow_succ]
    nlinarith

/-- The presentation identifies the actual nonempty-tubes witness domain before
using the heterogeneous equality of the selected nominal-radius functions. -/
private theorem nominal_bound_of_samePresentation
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' bound : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F)
    (f : Nonempty E.transition.trace.tubes.Index → ℝ)
    (f' : Nonempty F.transition.trace.tubes.Index → ℝ)
    (hf : HEq f f') (hbound : ∀ h, f' h ≤ bound) :
    ∀ h, f h ≤ bound := by
  cases R.incomingStage_eq
  cases R.outgoingStage_eq
  cases R.leftTime_eq
  cases R.eventTime_eq
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  cases eq_of_heq hf
  exact hbound

/-- An event reached before the old horizon is the actual old event, with its
same selected nominal-radius function and transported witness domain. -/
private theorem record_bound_of_prefix
    {H J : ObservedHistory.{u}} {pH pJ : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i pH)
    (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J i pJ)
    (hp : H.IsPrefixOf J) (hn : H.eventCount ≤ J.eventCount)
    (hrecords : ∀ i : Fin H.eventCount,
      HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius)
    {cut bound : ℝ}
    (hbound : ∀ i : Fin H.eventCount, cut < H.time i.succ →
      ∀ h, (old i).nominalRadius h ≤ bound)
    (i : Fin J.eventCount) (hpast : J.time i.succ ≤ H.horizon)
    (hafter : cut < J.time i.succ) :
    ∀ h, (records i).nominalRadius h ≤ bound := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  have hi : i.val < (J.restrict a).eventCount :=
    (J.event_reached_iff a i).mp hpast
  let iR : Fin (J.restrict a).eventCount := ⟨i.val, hi⟩
  let j : Fin H.eventCount := Fin.cast hp.presentation.count_eq iR
  have hj : j.castLE hn = i := Fin.ext rfl
  have hE : (J.event i).SamePresentation (H.event j) :=
    hp.presentation.event_eq iR
  have hnom : HEq (records i).nominalRadius (old j).nominalRadius := by
    have h := hrecords j
    rw [hj] at h
    exact h
  exact nominal_bound_of_samePresentation hE _ _ hnom
    (hbound j (by rw [← hE.eventTime_eq]; exact hafter))

private theorem cutoff_factor_antitone :
    Antitone (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
  intro m n hmn
  have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}
  (S : PreparedSpatialChain pBase C P g)

private theorem state_radius_antitone : Antitone (fun n => (S.state n).radius) :=
  antitone_nat_of_succ_le fun n => (S.successor n).radius_le

/-- All later records born after E_k retain the reserve paid at step k or a
smaller later reserve, on the same physical event and every actual witness. -/
private theorem tail_records_bound (k m : ℕ) (hkm : k + 1 ≤ m) :
    ∀ i : Fin (S.state m).history.eventCount,
      preparedSpatialHorizon k < (S.state m).history.time i.succ →
      ∀ h, ((S.state m).records i).nominalRadius h ≤
        (1 / ((k : ℝ) + 2)) * (S.state (k + 1)).radius := by
  induction m, hkm using Nat.le_induction with
  | base => exact (S.successor k).recent_records
  | succ m hkm ih =>
    intro i hafter
    by_cases hpast : (S.state (m + 1)).history.time i.succ ≤ (S.state m).history.horizon
    · exact record_bound_of_prefix (S.state m).records (S.state (m + 1)).records
        (S.successor m).initial_prefix.1 (S.successor m).count_le
        (fun j => ((S.successor m).records_preserved j).1) ih i hpast hafter
    · intro h
      have hnew := (S.successor m).recent_records i
        (by simpa only [(S.state m).horizon_eq] using lt_of_not_ge hpast) h
      have hkm' : k ≤ m := (Nat.le_succ k).trans hkm
      exact hnew.trans (mul_le_mul (cutoff_factor_antitone hkm')
        (S.state_radius_antitone (Nat.succ_le_succ hkm'))
        (S.state (m + 1)).radius_pos.le (by positivity))

/-- Later full parameters retain the same delayed radius throughout this band,
including the right endpoint before the next radius drop. -/
private theorem radius_eq_on_activation_band (k m : ℕ) (hkm : k + 1 ≤ m)
    {t : ℝ} (hleft : activation k < t) (hright : t ≤ activation (k + 1)) :
    (S.state m).parameters.neckRadius t = (S.state (k + 1)).radius := by
  induction m, hkm using Nat.le_induction with
  | base => exact (S.successor k).radius_after_activation t hleft
  | succ m hkm ih =>
    exact ((S.successor m).radius_before_activation t
      (hright.trans (activation_strictMono.monotone hkm))).trans ih

private theorem exists_activation_band (N : ℕ) (t : ℝ)
    (ht : activation (N + 1) ≤ t) :
    ∃ k : ℕ, N ≤ k ∧ activation k < t ∧ t ≤ activation (k + 1) := by
  classical
  have hex : ∃ j : ℕ, t ≤ activation j :=
    ⟨Nat.ceil t, (Nat.le_ceil t).trans (nat_le_activation _)⟩
  cases hfind : Nat.find hex with
  | zero =>
    have hupper : t ≤ activation 0 := by simpa only [hfind] using Nat.find_spec hex
    exact False.elim ((not_le_of_gt (activation_strictMono (Nat.zero_lt_succ N)))
      (ht.trans hupper))
  | succ k =>
    have hupper : t ≤ activation (k + 1) := by
      simpa only [hfind] using Nat.find_spec hex
    refine ⟨k, ?_, ?_, hupper⟩
    · by_contra hNk
      have hlt : activation (k + 1) < activation (N + 1) :=
        activation_strictMono (Nat.succ_lt_succ (lt_of_not_ge hNk))
      exact (not_le_of_gt hlt) (ht.trans hupper)
    · exact lt_of_not_ge (Nat.find_min hex (by rw [hfind]; omega))

/-- The actual recent surgery cuts are small relative to the common diagonal
radius. Every record is the one retained by the chain and its observation. -/
theorem recent_cutoff_decay :
    let q := CutoffParameters.diagonal (fun n => (S.observation n).parameters)
    ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ, t ≤ (n : ℝ) →
      ∀ i : Fin (S.observation n).history.eventCount,
        (S.observation n).history.time i.succ ∈ Icc (t / 2) t →
        ∀ h, ((S.observation n).records i).nominalRadius h ≤ η * q.neckRadius t := by
  dsimp only
  intro η hη
  let N : ℕ := Nat.ceil η⁻¹
  have hfactor : 1 / ((N : ℝ) + 2) ≤ η := by
    apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 2)).mpr
    have hm := mul_le_mul_of_nonneg_left (Nat.le_ceil η⁻¹) hη.le
    rw [mul_inv_cancel₀ (ne_of_gt hη)] at hm
    change 1 ≤ η * ((N : ℝ) + 2)
    dsimp only [N]
    nlinarith
  refine ⟨activation (N + 1), activation_pos _, ?_⟩
  intro t ht n htn i hi
  obtain ⟨k, hNk, hleft, hright⟩ := exists_activation_band N t ht
  have hkt : (k : ℝ) < t := (nat_le_activation k).trans_lt hleft
  have hkn : k ≤ n := by exact_mod_cast hkt.le.trans htn
  have hkceil : k ≤ Nat.ceil t := by
    exact_mod_cast hkt.le.trans (Nat.le_ceil t)
  have hq : (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t =
      (S.state (k + 1)).radius := by
    change (S.state (Nat.ceil t + 1)).parameters.neckRadius t = _
    exact S.radius_eq_on_activation_band k (Nat.ceil t + 1)
      (Nat.succ_le_succ hkceil) hleft hright
  have hafter : preparedSpatialHorizon k < (S.observation n).history.time i.succ := by
    have hhalf : activation k / 2 < t / 2 := by linarith
    exact ((horizon_lt_half_activation k).trans hhalf).trans_le hi.1
  let H := (S.state (n + 1)).history
  let a := S.observationTime n
  let j : Fin H.eventCount :=
    Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i
  have htime : (S.observation n).history.time i.succ = H.time j.succ :=
    ObservedHistory.restrict_time_apply H.toHistory a i.succ
  have hfull := S.tail_records_bound k (n + 1) (Nat.succ_le_succ hkn) j
    (by rw [← htime]; exact hafter)
  have hrecord : ∀ h, ((S.observation n).records i).nominalRadius h ≤
      (1 / ((k : ℝ) + 2)) * (S.state (k + 1)).radius := hfull
  intro h
  rw [hq]
  exact (hrecord h).trans (mul_le_mul_of_nonneg_right
    ((cutoff_factor_antitone hNk).trans hfactor) (S.state (k + 1)).radius_pos.le)

end GC.GeneralFlow.PreparedSpatialChain
