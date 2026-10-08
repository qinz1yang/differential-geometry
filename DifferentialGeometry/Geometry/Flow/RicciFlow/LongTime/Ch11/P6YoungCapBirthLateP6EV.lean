import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV6FwdC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateSupplyP6LT
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventExtension
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false

/-!
# Young cap 的 birth lateness / Birth lateness from actual cap volumes

`canonical window` 给固定归一化球的体积下界；同一 `ObservationTower` 的有限早期
`initialMetric` 给总体积上界。因此 early cap scale 有统一正下界，且不比较不同
observation 的 records。晚事件使用已有 recenter bound，合并后由 age bound 排除早 birth。

本文件不假设 query time 位于 observation horizon 内；适用于原 `SEPseq` 的全部 queries。
模型精度 `modelAccuracy ≤ 1/2` 可在固定 epsilon threshold 处支付，不依赖 A。
-/

noncomputable section

open Set Filter MeasureTheory Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow GC.GeneralFlow
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier
private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

private def stageVolume_P6EV {P : OrientedThreeStage.{u}} (g : P.Metric) : ℝ≥0∞ :=
  riemannianVolumeMeasure ThreeModel P.Carrier g univ

private theorem stageVolume_ne_top_P6EV {P : OrientedThreeStage.{u}} (g : P.Metric) :
    stageVolume_P6EV g ≠ (⊤ : ℝ≥0∞) := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  exact measure_ne_top _ univ

private theorem stageVolume_heq_P6EV {P Q : OrientedThreeStage.{u}} (h : P = Q)
    {g : P.Metric} {k : Q.Metric} (hk : HEq g k) :
    stageVolume_P6EV g = stageVolume_P6EV k := by
  cases h
  cases hk
  rfl

/-- 固定 model window 实际给出归一化体积下界 / Actual normalized volume lower bound. -/
theorem exists_static_scale_volume_lower_P6EV (q : CutoffParameters)
    (heps : q.modelAccuracy ≤ 1 / 2) :
    ∃ κ r : ℝ, 0 < κ ∧ 0 < r ∧
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount)
        (R : GeometricCutoffRecord H i q) (b : (H.event i).RetainedBoundaryIndex),
      (R.static b).hasCanonicalWindow →
      κ * (r / Real.sqrt (R.static b).neck.scale) ^ 3 ≤
        (stageVolume_P6EV (H.initialMetric i.succ)).toReal := by
  obtain ⟨κ, hκ, hvol⟩ :=
    StandardCap.exists_uniform_scaled_window_ball_volume_lower (0 : ℝ)
  let r : ℝ := min (1 / 2) (q.modelRadius / 2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos q.modelRadius_pos)
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hrD : r < q.modelRadius :=
    (min_le_right _ _).trans_lt (half_lt_self q.modelRadius_pos)
  refine ⟨κ, r, hκ, hr, ?_⟩
  intro H i R b hcan
  let S := R.static b
  obtain ⟨_, _, _, _, w, _, hmetric, _⟩ := hcan
  let p : standardCapWindow q.modelRadius :=
    ⟨0, by change ‖(0 : ThreeSpace)‖ < q.modelRadius + 1; simpa using
      (show (0 : ℝ) < q.modelRadius + 1 by linarith [q.modelRadius_pos])⟩
  have hbounds (x : standardCapWindow q.modelRadius) (hx : ‖x.val‖ < q.modelRadius)
      (v : TangentSpace ThreeModel x) :
      (1 / 4 : ℝ) * StandardCap.metric.inner x.val v v ≤
        (scaleMetric S.neck.scale S.neck.scale_pos (H.initialMetric i.succ)).inner
          (S.window x) (mfderiv ThreeModel ThreeModel S.window x v)
          (mfderiv ThreeModel ThreeModel S.window x v) ∧
      (scaleMetric S.neck.scale S.neck.scale_pos (H.initialMetric i.succ)).inner
          (S.window x) (mfderiv ThreeModel ThreeModel S.window x v)
          (mfderiv ThreeModel ThreeModel S.window x v) ≤
        4 * StandardCap.metric.inner x.val v v := by
    have hb := w.window_inner_bounds heps hx v
    simp only [SmoothRiemannianMetric.restrictOpen_inner, standardCapMetric_eq_metric] at hb
    rw [hmetric x v v, H.event_output i] at hb
    rw [scaleMetric_inner]
    have hn := metric_inner_self_nonneg StandardCap.metric x.val v
    constructor <;> nlinarith only [hb.1, hb.2, hn]
  have hv := hvol (H.initialMetric i.succ) S.window S.window_smooth
    S.neck.scale S.neck.scale_pos hbounds p (by simp [p]) r hr hr1 (by simpa [p] using hrD)
  have hv' := hv.trans (measure_mono (subset_univ _))
  have ht := ENNReal.toReal_mono (stageVolume_ne_top_P6EV (H.initialMetric i.succ)) hv'
  have hfrac : 0 ≤ r / Real.sqrt S.neck.scale :=
    div_nonneg hr.le (Real.sqrt_nonneg _)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hκ.le,
    ENNReal.toReal_ofReal hfrac] using ht

private theorem finite_stage_volumes_P6EV (T : ℕ → ObservedHistory.{u}) (N : ℕ) :
    ∃ V : ℝ, 0 < V ∧ ∀ n, n ≤ N → ∀ j : Fin ((T n).eventCount + 1),
      (stageVolume_P6EV ((T n).initialMetric j)).toReal ≤ V := by
  classical
  let v (n : Fin (N + 1)) (j : Fin ((T n).eventCount + 1)) : ℝ :=
    (stageVolume_P6EV ((T n).initialMetric j)).toReal
  let w (n : Fin (N + 1)) : ℝ := ∑ j, v n j
  have hw (n : Fin (N + 1)) : 0 ≤ w n :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  refine ⟨1 + ∑ n, w n, by positivity, ?_⟩
  intro n hn j
  let k : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hj : v k j ≤ w k := by
    dsimp only [w]
    exact Finset.single_le_sum (f := v k)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  have hk : w k ≤ ∑ n, w n :=
    Finset.single_le_sum (fun n _ => hw n) (Finset.mem_univ k)
  change v k j ≤ 1 + ∑ n, w n
  linarith only [hj, hk]

/-- 任意 observation 的早 output metric 体积统一有界 / Uniform early output volumes.
只 transport `initialMetric`，不要求 records 在不同 observations 中一致。 -/
theorem exists_early_output_volume_bound_P6EV {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (B : ℝ) :
    ∃ V : ℝ, 0 < V ∧ ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ≤ B →
      (stageVolume_P6EV ((F.tower.history n).initialMetric i.succ)).toReal ≤ V := by
  let N : ℕ := Nat.ceil (max 0 B) + 1
  have hBN : B ≤ (N : ℝ) := by
    have h := Nat.le_ceil (max 0 B)
    have hB := le_max_right (0 : ℝ) B
    dsimp only [N]
    push_cast
    linarith only [h, hB]
  let T := F.tower.toObservationTower
  obtain ⟨V, hV, hbound⟩ := finite_stage_volumes_P6EV T.history N
  refine ⟨V, hV, ?_⟩
  intro n i hi
  by_cases hn : n ≤ N
  · exact hbound n hn i.succ
  have hNn : N ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
  let H := (F.tower.history n).toHistory
  let a : Icc (0 : ℝ) H.horizon :=
    ⟨N, Nat.cast_nonneg N, by
      change (N : ℝ) ≤ (F.tower.history n).horizon
      rw [F.tower.horizon_eq]
      exact_mod_cast hNn⟩
  have hia : H.time i.succ ≤ a.val := hi.trans hBN
  have hir := (H.event_reached_iff a i).mp hia
  let j : Fin ((H.restrict a).eventCount + 1) := ⟨i.val + 1, by
    change i.val + 1 < (H.activeStage a).val + 1
    omega⟩
  have hcast : Fin.castLE
      (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1) j = i.succ :=
    Fin.ext rfl
  have hstage : (H.restrict a).stage j = H.stage i.succ := by
    rw [H.restrict_stage_apply a j, hcast]
  have hmetric : HEq ((H.restrict a).initialMetric j) (H.initialMetric i.succ) := HEq.rfl
  have hp := T.integer_restrict N n hNn
  change (H.restrict a).SamePresentation (T.history N) at hp
  let j' : Fin ((T.history N).eventCount + 1) :=
    Fin.cast (congrArg (· + 1) hp.count_eq) j
  have hv : stageVolume_P6EV (H.initialMetric i.succ) =
      stageVolume_P6EV ((T.history N).initialMetric j') := by
    exact (stageVolume_heq_P6EV hstage hmetric).symm.trans
      (stageVolume_heq_P6EV (hp.stage_eq j) (hp.initialMetric_heq j))
  change (stageVolume_P6EV (H.initialMetric i.succ)).toReal ≤ V
  rw [hv]
  exact hbound N le_rfl j'

private theorem scale_lower_of_volume_P6EV {κ r V S : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hV : 0 < V) (hS : 0 < S)
    (hv : κ * (r / Real.sqrt S) ^ 3 ≤ V) :
    (min 1 (κ * r ^ 3 / V)) ^ 2 ≤ S := by
  let a : ℝ := min 1 (κ * r ^ 3 / V)
  have ha : 0 < a := lt_min zero_lt_one (div_pos (mul_pos hκ (pow_pos hr 3)) hV)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haV : V * a ≤ κ * r ^ 3 := by
    have hh := (le_div_iff₀ hV).mp (min_le_right 1 (κ * r ^ 3 / V))
    simpa only [mul_comm] using hh
  have hz : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hzsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  have hmul : κ * r ^ 3 ≤ V * Real.sqrt S ^ 3 := by
    rw [div_pow, ← mul_div_assoc] at hv
    exact (div_le_iff₀ (pow_pos hz 3)).mp hv
  by_contra hh
  have hsmall : S < a ^ 2 := lt_of_not_ge hh
  have hza : Real.sqrt S < a := by nlinarith only [hsmall, hzsq, hz, ha]
  have hz1 : Real.sqrt S ≤ 1 := hza.le.trans ha1
  have hcube : Real.sqrt S ^ 3 ≤ Real.sqrt S := by
    calc Real.sqrt S ^ 3 = Real.sqrt S * Real.sqrt S ^ 2 := by ring
      _ ≤ Real.sqrt S * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hz.le hz1) hz.le
      _ = Real.sqrt S := mul_one _
  have hcubeV := mul_le_mul_of_nonneg_left hcube hV.le
  have hstrict := (mul_lt_mul_of_pos_left hza hV).trans_le haV
  linarith only [hmul, hcubeV, hstrict]

/-- 全部 actual records 的 scale 有统一正下界 / Uniform positive actual static scale.
早期用有限 stage volumes；晚期用 delta decay 和 antitone neck radius。 -/
theorem exists_uniform_static_scale_lower_P6EV {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (hcan : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (heps : q.modelAccuracy ≤ 1 / 2) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hlim : Tendsto q.delta atTop (𝓝 0)) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ n i b, s₀ ≤ ((records n i).static b).neck.scale := by
  have hΛ : 0 < q.recenterConstant :=
    lt_of_lt_of_le (by norm_num) q.recenterConstant_ge_four
  have hε : 0 < (1 / 2 : ℝ) / q.recenterConstant := div_pos (by norm_num) hΛ
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  obtain ⟨V, hV, hvol⟩ := exists_early_output_volume_bound_P6EV F B
  obtain ⟨κ, r, hκ, hr, hwindow⟩ := exists_static_scale_volume_lower_P6EV q heps
  let sE : ℝ := (min 1 (κ * r ^ 3 / V)) ^ 2
  let sL : ℝ := (2 * q.neckRadius 0 ^ 2)⁻¹
  have hsE : 0 < sE :=
    sq_pos_of_pos (lt_min zero_lt_one (div_pos (mul_pos hκ (pow_pos hr 3)) hV))
  have hnr : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have hsL : 0 < sL := inv_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hnr))
  refine ⟨min sE sL, lt_min hsE hsL, ?_⟩
  intro n i b
  have ht0 : 0 ≤ (F.tower.history n).time i.succ :=
    (F.tower.history n).toHistory.time_nonneg i.succ
  by_cases hi : (F.tower.history n).time i.succ ≤ B
  · have hv := (hwindow (F.tower.history n).toHistory i (records n i) b (hcan n i b)).trans
      (hvol n i hi)
    exact (min_le_left sE sL).trans
      (scale_lower_of_volume_P6EV hκ hr hV ((records n i).static b).neck.scale_pos hv)
  · have hd := (hB _ (le_of_not_ge hi)).le
    have hΛδ : q.recenterConstant * q.delta ((F.tower.history n).time i.succ) ≤ 1 / 2 := by
      have hh := (le_div_iff₀ hΛ).mp hd
      simpa only [mul_comm] using hh
    have hscale := RetainedCoreHistory.inv_two_mul_sq_lt_static_scale_record_P6LT
      (records n i) hΛδ le_rfl (hanti (by simp) ht0 ht0) b
    exact (min_le_right sE sL).trans hscale.le

/-- Young age 排除早 birth / Young age forces late birth, with no query horizon premise. -/
theorem young_cap_birth_late_P6EV {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (hcan : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (heps : q.modelAccuracy ≤ 1 / 2) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hlim : Tendsto q.delta atTop (𝓝 0)) :
    ∀ θ : ℝ, 0 ≤ θ → ∀ B : ℝ, ∃ T : ℝ, 0 < T ∧
      ∀ n (i : Fin (F.tower.history n).eventCount) (b) (t : ℝ), T ≤ t →
      t - (F.tower.history n).time i.succ ≤ θ * ((records n i).static b).neck.scale⁻¹ →
      B ≤ (F.tower.history n).time i.succ ∧ t ≤ 2 * (F.tower.history n).time i.succ := by
  obtain ⟨s₀, hs₀, hscale⟩ :=
    exists_uniform_static_scale_lower_P6EV F q records hcan heps hanti hlim
  intro θ hθ B
  let D : ℝ := θ * s₀⁻¹
  refine ⟨max 1 (max (2 * D) (B + D)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro n i b t ht hage
  have hage' : t - (F.tower.history n).time i.succ ≤ D :=
    hage.trans (mul_le_mul_of_nonneg_left (inv_anti₀ hs₀ (hscale n i b)) hθ)
  have hT1 := (le_max_left (2 * D) (B + D)).trans ((le_max_right _ _).trans ht)
  have hT2 := (le_max_right (2 * D) (B + D)).trans ((le_max_right _ _).trans ht)
  constructor <;> linarith only [hage', hT1, hT2]

/-- SCRS⁺ 解包同一 witnesses 并实际支付 birthLate / Same-witness SCRS⁺ consumer. -/
theorem young_cap_birth_late_of_scrsPlus_P6EV {pB : CutoffParameters}
    {Γ : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (h : SameConstructionRetentionSupplyPlus_C11GT6 T) (heps : pB.modelAccuracy ≤ 1 / 2) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : CutoffRecords_C11S F q),
      F.tower = T.toChain.tower ∧
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      q.recenterConstant = pB.recenterConstant ∧
      ∀ θ : ℝ, 0 ≤ θ → ∀ B : ℝ, ∃ Tq : ℝ, 0 < Tq ∧
        ∀ n (i : Fin (F.tower.history n).eventCount) (b) (t : ℝ), Tq ≤ t →
        t - (F.tower.history n).time i.succ ≤ θ * ((records n i).static b).neck.scale⁻¹ →
        B ≤ (F.tower.history n).time i.succ ∧ t ≤ 2 * (F.tower.history n).time i.succ := by
  obtain ⟨F, q, _, records, hsame, _, _, hprof, hcaps, _⟩ := h
  have hqeps : q.modelAccuracy ≤ 1 / 2 := by
    rw [hsame.2.2.2.2.2.1]
    exact heps
  exact ⟨F, q, records, hsame.1, hsame.2.1, hsame.2.2.2.2.2.2,
    young_cap_birth_late_P6EV F q records hcaps.1 hqeps hprof.2.1 hprof.2.2⟩

end GC.LongTime.Ch11
