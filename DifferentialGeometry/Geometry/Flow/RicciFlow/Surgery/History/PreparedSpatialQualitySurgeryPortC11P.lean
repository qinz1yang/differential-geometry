import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgeryDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialLargerBallAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

/-!
# S-CH11-FIX11 port of astra `PreparedSpatialQualitySurgery`（`PortC11P`）

来源：donor `PreparedSpatialQualitySurgery.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 5 处 `S.quality_native_birth_block …` / `S.quality_radius_lower_on_next_band …` /
  `S.quality_observation_record_of_state …` / `S.quality_state_prefix …`（×2）点记号：这四个是
  `PreparedSpatialQualityTransport` 里 `namespace PreparedSpatialChain` 的 private 定理，
  `open private … from` 只开放全名，点记号报 "Invalid field … does not contain"（级联一个
  `rcases` 失败）→ 全名 `PreparedSpatialChain.quality_… S …`（S 是首个显式参数；同 FIX9 G5）；
* `hbridge` 之后 `simpa only [jF, hTower] using hh`：`F.tower.history n` 与
  `(S.observation n).history` 只差命题等式 `hTower : F.tower = S.tower`，`Fin.cast hcount.symm`
  的 index 类型依赖它，simp 进不了 → 一般引理 `hgen : ∀ T, T = S.tower → ∀ hc j, (T.history n).time
  (Fin.cast hc.symm j).succ = (S.observation n).history.time j.succ`（`subst` 后 `rfl`），
  `exact (hgen F.tower hTower hcount j).trans hh`；
* 3 处因全名变长的行重新折行（≤ 100 列）。

原路径 `PreparedSpatialQualitySurgery` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace GC.GeneralFlow
universe u

open private quality_common_prefix_open_stage
  PreparedSpatialChain.quality_state_prefix
  PreparedSpatialChain.quality_nat_le_horizon
  PreparedSpatialChain.quality_radius_lower_on_next_band
  PreparedSpatialChain.quality_native_birth_block
  PreparedSpatialChain.quality_observation_record_of_state from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private PreparedSpatialChain.activation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff

/-- Attach the actual fine-record and derivative receivers to the one surgery
already constructed from this same marked prepared chain. -/
theorem PreparedSpatialChain.exists_surgery_with_retained_quality
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    (S : PreparedSpatialChain pBase C P g)
    (hS : ∀ n, (S.state n).DistanceData Cdist)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    (hoffset : ∀ n, (S.state (n + 1)).offset = (S.state n).history.eventCount)
    (hdrop : ∀ n, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (a₀ : ℝ)
    (initialControl : ∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      (
      F.tower = S.tower ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
        ((F.tower.history n).toHistory.event i).HasUniformDistanceScalar Cdist) ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) C.epsilon t) ∧
      (∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
        ∀ i : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t
      ) ∧
      (∀ t : ℝ, 0 ≤ t →
        q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t ∧
        q.neckRadius t =
          (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t) ∧
      (∀ t : ℝ, 0 < t → q.delta t < S.diagonalLargerBallAccuracy (2 * t) (2 * t)) ∧
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) ∧
      (∀ m : ℕ, ∀ i : Fin (S.state (m + 1)).native.eventCount,
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift;
        s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
        q.delta s = S.accuracy m ∧
        (∀ u : ℝ, s ≤ u → q.delta u ≤ S.accuracy m) ∧
        (∀ T : ℝ, T ∈ Icc s (2 * s) →
          (S.state (m + 1)).radius ≤ q.neckRadius T) ∧
        (∀ A : ℝ, 0 < A → q.delta s < S.diagonalLargerBallAccuracy A s →
          A < 12 * (3 : ℝ) ^ m) ∧
        ∀ n : ℕ, s ≤ (n : ℝ) →
        ∃ j : Fin (F.tower.history n).eventCount,
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ = s ∧
          HEq (records n j).nominalRadius ((W m).fineRecords i).nominalRadius ∧
          HEq (records n j).delta ((W m).fineRecords i).delta ∧
          HEq (records n j).order ((W m).fineRecords i).order ∧
          HEq (records n j).neck ((W m).fineRecords i).neck ∧
          HEq (records n j).static
            (fun z => translate_presented_static_cap
              ((S.state (m + 1)).native.coreEvent i) (S.state (m + 1)).shift
              ((((W m).fineRecords i).restrictModelWindow ((W m).fineWindows i)
                (S.state m).parameters.modelRadius_pos
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z))) ∧
      (∀ (m n : ℕ) (j : Fin ((F.tower.history n).eventCount + 1)),
        (S.state (m + 1)).offset ≤ j.val →
        ∀ (y : ((F.tower.history n).stage j).Carrier) (s : ℝ),
          s ∈ Ioo ((F.tower.history n).time j)
            ((F.tower.history n).toHistory.stageEndTime j) →
          s < (3 : ℝ) ^ (m + 1) →
          ((S.state (m + 1)).radius ^ 2)⁻¹ <
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun u =>
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j u) y) (Iic s) s| ≤
            C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2) := by
  obtain ⟨F, q, κ, records, hOld⟩ :=
    S.exists_surgery_with_spatial_control_and_decay_with_distance_scalars hS
  have hOldKeep := hOld
  obtain ⟨hTower, hDistance, hStatic, hκpos, hκanti, hδanti, hρanti,
    hparameters, hrecords, hCanonical, hWindows, hNoncollapse,
    hCompatible, hDecay, hRecent⟩ := hOld
  have hdiagonal (t : ℝ) (ht : 0 ≤ t) :
      q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t ∧
      q.neckRadius t =
        (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t := by
    have hh := hparameters (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩
    exact ⟨hh.1, hh.2.1⟩
  refine ⟨F, q, κ, records, hOldKeep, hdiagonal, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [(hdiagonal t ht.le).1]
    exact (S.diagonalLargerBallAccuracy_spec hdrop).2.2.2.1 t ht
  · intro n
    exact initialControl (F.tower.history n).toHistory (F.tower.initial n)
  · intro m i
    let R := S.state (m + 1)
    let s := R.native.time i.succ + R.shift
    have hblock : s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) :=
      PreparedSpatialChain.quality_native_birth_block S hoffset m i
    have hs0 : 0 ≤ s :=
      ((Nat.cast_nonneg m).trans (PreparedSpatialChain.quality_nat_le_horizon m)).trans hblock.1.le
    have hdelta : q.delta s = S.accuracy m :=
      (hdiagonal s hs0).1.trans
        (S.diagonal_delta_eq_accuracy_on_block m s hblock.1 hblock.2)
    refine ⟨hblock, hdelta, ?_, ?_, ?_, ?_⟩
    · intro t hst
      exact (hδanti hs0 (hs0.trans hst) hst).trans_eq hdelta
    · intro T hT
      have hT0 : 0 ≤ T := hs0.trans hT.1
      rw [(hdiagonal T hT0).2]
      change R.radius ≤ (S.state (Nat.ceil T + 1)).parameters.neckRadius T
      have hmceil : m ≤ Nat.ceil T := by
        exact_mod_cast ((PreparedSpatialChain.quality_nat_le_horizon m).trans
          (hblock.1.le.trans (hT.1.trans (Nat.le_ceil T))))
      have hband : T ≤ PreparedSpatialChain.activation (m + 1) := by
        have hp : (0 : ℝ) < 3 ^ m := pow_pos (by norm_num) m
        change T ≤ (5 / 6 : ℝ) * 3 ^ (m + 1)
        rw [pow_succ]
        nlinarith [hT.2, hblock.2]
      exact PreparedSpatialChain.quality_radius_lower_on_next_band S m (Nat.ceil T + 1)
        (Nat.succ_le_succ hmceil) T (hblock.1.le.trans hT.1) hband
    · intro A hA heligible
      apply S.diagonalLargerBallAccuracy_birth_block_bound hdrop m A s hA hs0 hblock.2
      rwa [← (hdiagonal s hs0).1]
    · intro n hsn
      have hmn : m ≤ n := by
        exact_mod_cast
          ((PreparedSpatialChain.quality_nat_le_horizon m).trans (hblock.1.le.trans hsn))
      let iFull := R.affine.eventIndex i
      have htime : R.history.time iFull.succ = s := by
        have hh := R.affine.stageIndex_time i.succ
        rw [R.affine.stageIndex_succ] at hh
        exact hh
      obtain ⟨j, hjval, hjtime, hjr, hjd, hjo, hjn, hjs⟩ :=
        PreparedSpatialChain.quality_observation_record_of_state S m n hmn iFull
          (htime.trans_le hsn)
      have hcount : (F.tower.history n).eventCount = (S.observation n).history.eventCount := by
        rw [hTower]
        rfl
      let jF : Fin (F.tower.history n).eventCount := Fin.cast hcount.symm j
      have hbridge := hrecords n jF j rfl
      have hfine := (W m).full_records i
      refine ⟨jF, hjval, ?_, hbridge.1.trans (hjr.trans hfine.1),
        hbridge.2.1.trans (hjd.trans hfine.2.1),
        hbridge.2.2.1.trans (hjo.trans hfine.2.2.1),
        hbridge.2.2.2.1.trans (hjn.trans hfine.2.2.2.1),
        hbridge.2.2.2.2.trans (hjs.trans hfine.2.2.2.2)⟩
      have hh := hjtime.trans htime
      have hgen : ∀ (T : RetainedCoreObservationTower P g), T = S.tower →
          ∀ (hc : (T.history n).eventCount = (S.observation n).history.eventCount)
            (j : Fin (S.observation n).history.eventCount),
          (T.history n).time (Fin.cast hc.symm j).succ = (S.observation n).history.time j.succ := by
        intro T hT
        subst hT
        intro hc j
        rfl
      exact (hgen F.tower hTower hcount j).trans hh
  · rw [hTower]
    intro m n j hj y s hs hcap hscalar
    let H := (S.observation n).history
    let J := (S.state (m + 2)).history
    let K := (S.state (max (n + 1) (m + 2))).history
    have hHK : H.toHistory.IsPrefixOf K.toHistory :=
      ((S.state (n + 1)).initial.restrict_isPrefixOf (S.observationTime n)).1.trans
        (PreparedSpatialChain.quality_state_prefix S (n + 1) (max (n + 1) (m + 2))
          (le_max_left _ _))
    have hJK : J.toHistory.IsPrefixOf K.toHistory :=
      PreparedSpatialChain.quality_state_prefix S (m + 2) (max (n + 1) (m + 2)) (le_max_right _ _)
    have hsJ : s < J.horizon := by
      rw [show J.horizon = preparedSpatialHorizon (m + 2) from (S.state (m + 2)).horizon_eq]
      exact hcap
    obtain ⟨k, hkval, hstage, hsk, hmetric⟩ :=
      quality_common_prefix_open_stage hHK hJK j s hs hsJ
    let z := overlapCastPoint hstage y
    have hpoint : HEq y z := (overlapCastPoint_heq hstage y).symm
    let f : ℝ → ℝ := fun t => metricScalarAt (H.toHistory.stageMetric j t) y
    let fJ : ℝ → ℝ := fun t => metricScalarAt (J.toHistory.stageMetric k t) z
    have hGerm : f =ᶠ[𝓝 s] fJ := by
      filter_upwards [hmetric] with t ht
      exact overlap_scalar_eq hstage ht hpoint
    have hk : (S.state (m + 1)).offset ≤ k.val := by
      rw [hkval]
      exact hj
    have hscalarJ : ((S.state (m + 1)).radius ^ 2)⁻¹ < fJ s := by
      rw [← hGerm.eq_of_nhds]
      exact hscalar
    have hbound := (W (m + 1)).derivative_bound_on_old_native_tail
      (S.successor (m + 1)) (hshift (m + 1)) (hoffset (m + 1)) k hk z s hsk hscalarJ
    change |derivWithin f (Iic s) s| ≤ C.Ctime * f s ^ 2
    rw [hGerm.derivWithin_eq_of_nhds, hGerm.eq_of_nhds]
    exact hbound

end GC.GeneralFlow
