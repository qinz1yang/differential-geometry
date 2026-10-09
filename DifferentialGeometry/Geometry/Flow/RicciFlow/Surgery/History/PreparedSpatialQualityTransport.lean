import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

/-!
S-CH11-FIX6 patched-at-path（astra `History/PreparedSpatialQualityTransport` 的 elaboration 修补；
下游 `PreparedSpatialDiagonalDerivative` / `PreparedSpatialQualitySurgery` /
`PreparedSpatialBirthBlockLookup` 有 `open private … from` 本路径）。陈述 / 证明思路逐字不变，三处：
(a) `quality_common_prefix_open_stage` 的 `hsk` 里 `cases k using Fin.lastCases` 前先 `clear_value k`
    （`k` 是 `let`，`cases` 不替换 `hd` 里的 `k`，`hd.2` 的投影卡在 `Fin.reverseInduction.go`），
    `cast i` 分支先 `simp only [stageDomain, lastCases_castSucc, mem_Ico] at hd` 再取 `.2`；
(b) `quality_nat_le_horizon` 的 zero 分支 `exact le_rfl` → `simp [preparedSpatialHorizon]`
    （`↑0` 与 `preparedSpatialHorizon 0` 不 syntactic 一致）；
(c) succ 分支 `exact_mod_cast hh'` 前 `change ((m + 1 : ℕ) : ℝ) ≤ (3 : ℝ) ^ m`
    （`exact_mod_cast` 不展开 `preparedSpatialHorizon`）。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology NNReal

namespace GC.GeneralFlow
universe u

/-- Prefix metrics are compared only on the actual source stage domain. -/
private theorem quality_prefix_stage
    {H K : ObservedHistory.{u}} (hp : H.IsPrefixOf K)
    (hn : H.eventCount ≤ K.eventCount) (j : Fin (H.eventCount + 1)) :
    H.time j = K.time (j.castLE (Nat.succ_le_succ hn)) ∧
    H.stage j = K.stage (j.castLE (Nat.succ_le_succ hn)) ∧
    (∀ t ∈ H.stageDomain j, t ∈ K.stageDomain (j.castLE (Nat.succ_le_succ hn))) ∧
    ∀ t ∈ H.stageDomain j,
      HEq (H.stageMetric j t) (K.stageMetric (j.castLE (Nat.succ_le_succ hn)) t) := by
  let a : Icc (0 : ℝ) K.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let R := hp.presentation.symm
  let k : Fin ((K.restrict a).eventCount + 1) :=
    Fin.cast (congrArg (· + 1) R.count_eq) j
  have ht : H.time j = K.time (j.castLE (Nat.succ_le_succ hn)) := R.time_eq j
  have hstage : H.stage j = K.stage (j.castLE (Nat.succ_le_succ hn)) := R.stage_eq j
  have hdom (t : ℝ) (ht : t ∈ H.stageDomain j) : t ∈ (K.restrict a).stageDomain k := by
    rw [← R.stageDomain_eq j]
    exact ht
  refine ⟨ht, hstage, ?_, ?_⟩
  · intro t ht
    exact K.restrict_stageDomain_subset a k (hdom t ht)
  · intro t ht
    exact (R.metric_heq j t ht).trans (K.restrict_stageMetric a k t (hdom t ht))

private theorem quality_prefix_count
    {H K : ObservedHistory.{u}} (hp : H.IsPrefixOf K) : H.eventCount ≤ K.eventCount := by
  rw [← hp.presentation.count_eq]
  exact Nat.le_of_lt_succ
    (K.activeStage ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩).isLt

/-- A common later prefix identifies the same numeric open stage, including
when either source history ends in a final slab. No all-real metric equality is used. -/
private theorem quality_common_prefix_open_stage
    {H J K : ObservedHistory.{u}} (hH : H.IsPrefixOf K) (hJ : J.IsPrefixOf K)
    (j : Fin (H.eventCount + 1)) (s : ℝ)
    (hs : s ∈ Ioo (H.time j) (H.stageEndTime j)) (hsJ : s < J.horizon) :
    ∃ k : Fin (J.eventCount + 1), k.val = j.val ∧ H.stage j = J.stage k ∧
      s ∈ Ioo (J.time k) (J.stageEndTime k) ∧
      ∀ᶠ t in 𝓝 s, HEq (H.stageMetric j t) (J.stageMetric k t) := by
  have hs0 : 0 ≤ s := (H.time_nonneg j).trans hs.1.le
  have hsH : s ≤ H.horizon := hs.2.le.trans (H.stageEndTime_le_horizon j)
  let tH : Icc (0 : ℝ) H.horizon := ⟨s, hs0, hsH⟩
  let tJ : Icc (0 : ℝ) J.horizon := ⟨s, hs0, hsJ.le⟩
  let tK : Icc (0 : ℝ) K.horizon := ⟨s, hs0, hsH.trans hH.horizon_le⟩
  let k := J.activeStage tJ
  let hn := quality_prefix_count hH
  let hm := quality_prefix_count hJ
  have hHD := quality_prefix_stage hH hn j
  have hJD := quality_prefix_stage hJ hm k
  have hHactive : K.activeStage tK = j.castLE (Nat.succ_le_succ hn) :=
    (K.mem_stageDomain_iff tK _).mp
      (hHD.2.2.1 s (H.mem_stageDomain_of_mem_Ioo hs))
  have hJactive : K.activeStage tK = k.castLE (Nat.succ_le_succ hm) :=
    (K.mem_stageDomain_iff tK _).mp (hJD.2.2.1 s (J.activeStage_mem tJ))
  have hindex : j.castLE (Nat.succ_le_succ hn) = k.castLE (Nat.succ_le_succ hm) :=
    hHactive.symm.trans hJactive
  have hkval : k.val = j.val := (congrArg Fin.val hindex).symm
  have htime : H.time j = J.time k :=
    hHD.1.trans ((congrArg K.time hindex).trans hJD.1.symm)
  have hstage : H.stage j = J.stage k :=
    hHD.2.1.trans ((congrArg K.stage hindex).trans hJD.2.1.symm)
  have hsk : s ∈ Ioo (J.time k) (J.stageEndTime k) := by
    refine ⟨by rw [← htime]; exact hs.1, ?_⟩
    have hd := J.activeStage_mem tJ
    change s ∈ J.stageDomain k at hd
    clear_value k
    cases k using Fin.lastCases with
    | last => simpa only [J.stageEndTime_last] using hsJ
    | cast i =>
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hd
      simpa only [J.stageEndTime_castSucc] using hd.2
  refine ⟨k, hkval, hstage, hsk, ?_⟩
  filter_upwards [Ioo_mem_nhds hs.1 hs.2, Ioo_mem_nhds hsk.1 hsk.2] with t htH htJ
  have hmetricH := hHD.2.2.2 t (H.mem_stageDomain_of_mem_Ioo htH)
  have hmetricJ := hJD.2.2.2 t (J.mem_stageDomain_of_mem_Ioo htJ)
  rw [hindex] at hmetricH
  exact hmetricH.trans hmetricJ.symm

namespace PreparedSpatialChain
variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}
  (S : PreparedSpatialChain pBase C P g)

private theorem quality_state_prefix (m n : ℕ) (hmn : m ≤ n) :
    (S.state m).history.toHistory.IsPrefixOf (S.state n).history.toHistory := by
  induction n, hmn using Nat.le_induction with
  | base => exact ObservedHistory.IsPrefixOf.refl _
  | succ n _ ih => exact ih.trans (S.successor n).initial_prefix.1

private theorem quality_state_count : Monotone (fun n => (S.state n).history.eventCount) :=
  monotone_nat_of_le_succ (fun n => (S.successor n).count_le)

private theorem quality_state_records (m n : ℕ) (hmn : m ≤ n)
    (i : Fin (S.state m).history.eventCount) :
    HEq ((S.state n).records (i.castLE (S.quality_state_count hmn))).nominalRadius
      ((S.state m).records i).nominalRadius ∧
    HEq ((S.state n).records (i.castLE (S.quality_state_count hmn))).delta
      ((S.state m).records i).delta ∧
    HEq ((S.state n).records (i.castLE (S.quality_state_count hmn))).order
      ((S.state m).records i).order ∧
    HEq ((S.state n).records (i.castLE (S.quality_state_count hmn))).neck
      ((S.state m).records i).neck ∧
    HEq ((S.state n).records (i.castLE (S.quality_state_count hmn))).static
      ((S.state m).records i).static := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  | succ n hmn ih =>
    have hh := (S.successor n).records_preserved (i.castLE (S.quality_state_count hmn))
    exact ⟨hh.1.trans ih.1, hh.2.1.trans ih.2.1, hh.2.2.1.trans ih.2.2.1,
      hh.2.2.2.1.trans ih.2.2.2.1, hh.2.2.2.2.trans ih.2.2.2.2⟩

private theorem quality_nat_le_horizon (m : ℕ) : (m : ℝ) ≤ preparedSpatialHorizon m := by
  cases m with
  | zero => simp [preparedSpatialHorizon]
  | succ m =>
    have hh : m < (3 : ℕ) ^ m := by exact_mod_cast nat_lt_three_pow m
    have hh' := Nat.succ_le_of_lt hh
    change ((m + 1 : ℕ) : ℝ) ≤ (3 : ℝ) ^ m
    exact_mod_cast hh'


open private activation activation_strictMono from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff

private theorem quality_radius_lower_on_next_band (m k : ℕ) (hmk : m + 1 ≤ k)
    (t : ℝ) (hleft : preparedSpatialHorizon m ≤ t) (hright : t ≤ activation (m + 1)) :
    (S.state (m + 1)).radius ≤ (S.state k).parameters.neckRadius t := by
  induction k, hmk using Nat.le_induction with
  | base =>
    by_cases hlate : activation m < t
    · exact le_of_eq ((S.successor m).radius_after_activation t hlate).symm
    · rw [(S.successor m).radius_before_activation t (le_of_not_gt hlate),
        (S.state m).radius_after t hleft]
      exact (S.successor m).radius_le
  | succ k hmk ih =>
    rw [(S.successor k).radius_before_activation t
      (hright.trans (activation_strictMono.monotone hmk))]
    exact ih

/-- The next native events are strictly new; equality with the old horizon would
put their affine indices inside the old prefix and contradict the exact offset. -/
private theorem quality_native_birth_block
    (hoffset : ∀ n, (S.state (n + 1)).offset = (S.state n).history.eventCount)
    (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount) :
    let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift
    s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) := by
  let L := S.state m
  let R := S.state (m + 1)
  let j := R.affine.eventIndex i
  have ht : R.history.time j.succ = R.native.time i.succ + R.shift := by
    have hh := R.affine.stageIndex_time i.succ
    rw [R.affine.stageIndex_succ] at hh
    exact hh
  change preparedSpatialHorizon m < R.native.time i.succ + R.shift ∧
    R.native.time i.succ + R.shift ≤ (3 : ℝ) ^ m
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hp := (S.successor m).initial_prefix.1
    let a : Icc (0 : ℝ) R.history.horizon :=
      ⟨L.history.horizon, L.history.horizon_nonneg, hp.horizon_le⟩
    have hreach : R.history.time j.succ ≤ (a : ℝ) := by
      rw [ht]
      exact (le_of_not_gt hnot).trans_eq L.horizon_eq.symm
    have hidx := (R.history.toHistory.event_reached_iff a j).mp hreach
    have hcount : (R.history.restrict a).eventCount = L.history.eventCount :=
      hp.presentation.count_eq
    change j.val < (R.history.restrict a).eventCount at hidx
    rw [hcount] at hidx
    change R.offset + i.val < L.history.eventCount at hidx
    have hoff : R.offset = L.history.eventCount := hoffset m
    omega
  · rw [← ht]
    exact (R.history.toHistory.time_le_horizon_at j.succ).trans_eq R.horizon_eq

/-- Receive one already reached full-state event on the literal observation,
with all five original selected record fields. -/
private theorem quality_observation_record_of_state
    (m n : ℕ) (hmn : m ≤ n)
    (i : Fin (S.state (m + 1)).history.eventCount)
    (htime : (S.state (m + 1)).history.time i.succ ≤ (n : ℝ)) :
    ∃ j : Fin (S.observation n).history.eventCount,
      j.val = i.val ∧
      (S.observation n).history.time j.succ = (S.state (m + 1)).history.time i.succ ∧
      HEq ((S.observation n).records j).nominalRadius ((S.state (m + 1)).records i).nominalRadius ∧
      HEq ((S.observation n).records j).delta ((S.state (m + 1)).records i).delta ∧
      HEq ((S.observation n).records j).order ((S.state (m + 1)).records i).order ∧
      HEq ((S.observation n).records j).neck ((S.state (m + 1)).records i).neck ∧
      HEq ((S.observation n).records j).static ((S.state (m + 1)).records i).static := by
  let H := (S.state (n + 1)).history
  let a := S.observationTime n
  let hn := S.quality_state_count (Nat.succ_le_succ hmn)
  let k : Fin H.eventCount := i.castLE hn
  have htimeK : (S.state (m + 1)).history.time i.succ = H.time k.succ :=
    (quality_prefix_stage (S.quality_state_prefix (m + 1) (n + 1)
      (Nat.succ_le_succ hmn)) hn i.succ).1
  have hreach : k.val < (H.restrict a).eventCount :=
    (H.toHistory.event_reached_iff a k).mp (htimeK.symm.trans_le htime)
  let j : Fin (S.observation n).history.eventCount := ⟨k.val, hreach⟩
  have hrest := H.restrictRecords_preserves a (S.state (n + 1)).records j
  have hfull := S.quality_state_records (m + 1) (n + 1) (Nat.succ_le_succ hmn) i
  refine ⟨j, rfl, ?_, hrest.1.trans hfull.1, hrest.2.1.trans hfull.2.1,
    hrest.2.2.1.trans hfull.2.2.1, hrest.2.2.2.1.trans hfull.2.2.2.1,
    hrest.2.2.2.2.trans hfull.2.2.2.2⟩
  exact htimeK.symm

end PreparedSpatialChain
end GC.GeneralFlow
