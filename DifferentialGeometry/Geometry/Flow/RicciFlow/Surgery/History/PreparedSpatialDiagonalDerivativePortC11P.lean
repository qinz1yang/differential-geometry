import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffAccuracyGluing

/-!
# S-CH11-FIX9 port of astra `PreparedSpatialDiagonalDerivative`（`PortC11P`）

来源：donor `PreparedSpatialDiagonalDerivative.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `hv` 的 `last` 情形：`simpa only [hj, stageEndTime_last] using htop` 的 `htop` 是
  `(S.tower.history n).horizon`，目标是 `H.horizon`（`H` 为 let），simpa 的收尾不通过 →
  `simp only [H.stageEndTime_last]` 后 `exact htop`（defeq）；
* `hv` 的 `cast` 情形：`change … ∈ Ico (H.time i.castSucc) (H.time i.succ) at hd` 不是 defeq
  （`stageDomain` 经 `Fin.lastCases`，只有 `Fin.lastCases_castSucc` 的命题等式）→
  `simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hd`；
* 2 处 `S.quality_state_prefix …`：`open private PreparedSpatialChain.quality_state_prefix from …`
  只开放全名，点记号 `S.quality_state_prefix` 找不到 private 声明 → 写全名
  `PreparedSpatialChain.quality_state_prefix S …`。

原路径 `PreparedSpatialDiagonalDerivative` 是只 import 本文件的 re-export shim（无 donor 下游）。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal Topology

namespace GC.GeneralFlow
universe u

open private quality_prefix_stage quality_common_prefix_open_stage
  PreparedSpatialChain.quality_state_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

namespace PreparedSpatialChain
variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

private theorem state_neckRadius_compat
    (S : PreparedSpatialChain pBase C P g)
    (m n : ℕ) (hmn : m ≤ n) (t : ℝ) (ht : t ≤ preparedSpatialHorizon m) :
    (S.state n).parameters.neckRadius t = (S.state m).parameters.neckRadius t := by
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
    exact ((S.successor n).parameters_past t (ht.trans (hclock hmn))).2.1.trans ih

private theorem diagonal_neckRadius_eq_state
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (n : ℕ) (s : ℝ)
    (hs : s ≤ preparedSpatialHorizon n) :
    (CutoffParameters.diagonal (fun k => (S.observation k).parameters)).neckRadius s =
      (S.state n).parameters.neckRadius s := by
  change (S.state (Nat.ceil s + 1)).parameters.neckRadius s =
    (S.state n).parameters.neckRadius s
  have hceil : s ≤ preparedSpatialHorizon (Nat.ceil s + 1) :=
    (Nat.le_ceil s).trans (nat_lt_three_pow (Nat.ceil s)).le
  exact (state_neckRadius_compat S (Nat.ceil s + 1) (max n (Nat.ceil s + 1))
    (le_max_right _ _) s hceil).symm.trans
      (state_neckRadius_compat S n (max n (Nat.ceil s + 1)) (le_max_left _ _) s hs)

private theorem exists_geometric_open_band (s : ℝ) (hs : 0 ≤ s) :
    ∃ m : ℕ, preparedSpatialHorizon m ≤ s ∧ s < (3 : ℝ) ^ m := by
  classical
  have hex : ∃ m : ℕ, s < (3 : ℝ) ^ m :=
    ⟨Nat.ceil s, (Nat.le_ceil s).trans_lt (nat_lt_three_pow (Nat.ceil s))⟩
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, s < (3 : ℝ) ^ m ∧
      ∀ k : ℕ, k < m → ¬ s < (3 : ℝ) ^ k :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  refine ⟨m, ?_, hm⟩
  cases m with
  | zero => exact hs
  | succ k => exact le_of_not_gt (hmin k (Nat.lt_succ_self k))

end PreparedSpatialChain

/-- The retained old native estimates control the same observation flow at its
current diagonal radius, on genuine positive-age interior stage germs. -/
theorem PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hdiagonal : ∀ v : ℝ, 0 ≤ v → q.neckRadius v =
      (CutoffParameters.diagonal (fun m => (S.observation m).parameters)).neckRadius v) :
    ∀ (n : ℕ) (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (z : ((F.tower.history n).toHistory.stageAt v).Carrier),
      (F.tower.history n).time ((F.tower.history n).toHistory.activeStage v) < (v : ℝ) →
      (v : ℝ) < (F.tower.history n).toHistory.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
        C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z ^ 2 := by
  rw [hTower]
  intro n v y hage htop hscalar
  let H := (S.observation n).history.toHistory
  let j := H.activeStage v
  have hv : (v : ℝ) ∈ Ioo (H.time j) (H.stageEndTime j) := by
    refine ⟨hage, ?_⟩
    have hd := H.activeStage_mem v
    change (v : ℝ) ∈ H.stageDomain j at hd
    cases hj : j using Fin.lastCases with
    | last =>
      simp only [H.stageEndTime_last]
      exact htop
    | cast i =>
      rw [hj] at hd
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hd
      simpa only [hj, H.stageEndTime_castSucc] using hd.2
  obtain ⟨m, hlow, hupp⟩ := PreparedSpatialChain.exists_geometric_open_band (v : ℝ) v.2.1
  let L := S.state m
  let J := (S.state (m + 1)).history.toHistory
  let K := (S.state (max (n + 1) (m + 1))).history.toHistory
  have hHK : H.IsPrefixOf K :=
    ((S.state (n + 1)).initial.restrict_isPrefixOf (S.observationTime n)).1.trans
      (PreparedSpatialChain.quality_state_prefix S (n + 1) (max (n + 1) (m + 1))
        (le_max_left _ _))
  have hJK : J.IsPrefixOf K :=
    PreparedSpatialChain.quality_state_prefix S (m + 1) (max (n + 1) (m + 1))
      (le_max_right _ _)
  have hvJ : (v : ℝ) < J.horizon := by
    change (v : ℝ) < (S.state (m + 1)).history.horizon
    rw [(S.state (m + 1)).horizon_eq]
    exact hupp
  obtain ⟨k, _, hstage, hvk, hmetric⟩ :=
    quality_common_prefix_open_stage hHK hJK j v hv hvJ
  let vJ : Icc (0 : ℝ) J.horizon := ⟨v, v.2.1, hvJ.le⟩
  have hkactive : J.activeStage vJ = k :=
    (J.mem_stageDomain_iff vJ k).mp (J.mem_stageDomain_of_mem_Ioo hvk)
  let lastL : Fin (J.eventCount + 1) :=
    (Fin.last L.history.eventCount).castLE (Nat.succ_le_succ (S.successor m).count_le)
  have hprefix := quality_prefix_stage (S.successor m).initial_prefix.1
    (S.successor m).count_le (Fin.last L.history.eventCount)
  have hlastTime : J.time lastL ≤ (v : ℝ) := by
    calc J.time lastL = L.history.time (Fin.last L.history.eventCount) := hprefix.1.symm
      _ ≤ L.history.horizon := L.history.time_le_horizon
      _ = preparedSpatialHorizon m := L.horizon_eq
      _ ≤ (v : ℝ) := hlow
  have hlastle : lastL ≤ k := by
    rw [← hkactive]
    exact J.le_activeStage vJ lastL hlastTime
  have hcount : L.history.eventCount ≤ k.val := hlastle
  have hk : L.offset ≤ k.val := by
    have hcountL := L.affine.count_eq
    omega
  have hE0 : 0 ≤ preparedSpatialHorizon m := by
    rw [← L.horizon_eq]
    exact L.history.horizon_nonneg
  have hqE : q.neckRadius (preparedSpatialHorizon m) = L.radius := by
    rw [hdiagonal _ hE0,
      PreparedSpatialChain.diagonal_neckRadius_eq_state S m _ le_rfl]
    exact L.radius_after _ le_rfl
  have hRad : q.neckRadius v ≤ L.radius :=
    (hanti hE0 v.2.1 hlow).trans_eq hqE
  have hqpos : 0 < q.neckRadius v := q.neckRadius_pos v v.2.1
  have hsq : q.neckRadius v ^ 2 ≤ L.radius ^ 2 :=
    pow_le_pow_left₀ hqpos.le hRad 2
  have hthreshold : (L.radius ^ 2)⁻¹ ≤ (q.neckRadius v ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hqpos) hsq
  let z := overlapCastPoint hstage y
  have hpoint : HEq y z := (overlapCastPoint_heq hstage y).symm
  let f : ℝ → ℝ := fun t => metricScalarAt (H.stageMetric j t) y
  let fJ : ℝ → ℝ := fun t => metricScalarAt (J.stageMetric k t) z
  have hGerm : f =ᶠ[𝓝 (v : ℝ)] fJ := by
    filter_upwards [hmetric] with t ht
    exact overlap_scalar_eq hstage ht hpoint
  have hscalarJ : (L.radius ^ 2)⁻¹ < fJ v := by
    rw [← hGerm.eq_of_nhds]
    exact hthreshold.trans_lt hscalar
  have hbound := (W m).derivative_bound_on_old_native_tail
    (S.successor m) (hshift m) (hoffset m) k hk z v hvk hscalarJ
  change |derivWithin f (Iic (v : ℝ)) v| ≤ C.Ctime * f v ^ 2
  rw [hGerm.derivWithin_eq_of_nhds, hGerm.eq_of_nhds]
  exact hbound

end GC.GeneralFlow
