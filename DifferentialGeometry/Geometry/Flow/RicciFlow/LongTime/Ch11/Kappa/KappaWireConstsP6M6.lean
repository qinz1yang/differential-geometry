import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaWireC11KW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841E2EFwdC11FR

/-!
# KWIRE ADP-1 的常数导出 + GAPTOP6 GAP-2 槽（S-CH11-HSCALU2 G3，后缀 `_P6M6`）

GAPTOP6 repair (c)：`blockData_of_certifiedTower_C11KW`（`Kappa/KappaWireC11KW`）的结论 `∃ N, …` 没有导出
`N` 的常数 `(epsilon, C1, C2)`（也没有导出 `N.params.modelAccuracy`），所以 same-tower Pre841
`pre841Data_of_certifiedTower_fwd_C11GT6` 的 GAP-2 前提
`N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P` 无法 discharge。
`N := nativeDataOfSupplies_C11KD F q records Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ)
Γ.Ctime …`，
`N.params = q`，故这些量其实是**定义等式**，只是被存在量词吞掉。

* **`blockData_consts_of_certifiedTower_P6M6`**：KWIRE ADP-1 证明体逐字（不改 tracked，新定理），结论多一组
  合取项 `N.epsilon = Γ.epsilon ∧ N.C1 = chainC1_C11KD Γ ∧ N.C2 = chainC2_C11KD Γ ∧ N.Ctime = Γ.Ctime ∧
  N.params.{fixed, modelRadius, modelOrder, modelAccuracy, recenterConstant} = pB.{…}`。
* `gap2_of_consts_P6M6`：常数等式 + 与 `N` 无关的 `pB.modelAccuracy ≤ epsilon0_C11FR Γ.epsilon … P`
  ⇒ GAP-2 前提。
* **`pre841Data_of_certifiedTower_fwd_gap2_P6M6`**（consumer，GAPTOP6 GAP-2 槽）：同 GT6 的 same-tower 集成，
  GAP-2 前提换成 `hacc₀`（与 `N` 无关）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **certified tower ⇒ 块数据 + 常数导出（`_P6M6`）**：`blockData_of_certifiedTower_C11KW` 的证明体逐字，
结论只多一组合取项：`N` 的常数
`N.epsilon = Γ.epsilon`、`N.C1 = chainC1_C11KD Γ`、`N.C2 = chainC2_C11KD Γ`、`N.Ctime = Γ.Ctime`
（`nativeDataOfSupplies_C11KD` 的字段，`rfl`）与 `N.params` 的静态字段 =
`pB` 的（`hStatic`：`fixed / modelRadius / modelOrder / modelAccuracy / recenterConstant`）。
KWIRE 原定理的 `∃ N` 把 `N.epsilon / C1 / C2 / params.modelAccuracy` 藏起来，GAPTOP6 same-tower 的 GAP-2 前提
`N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P` 因此无法在不依赖 `N` 的数据上 discharge。 -/
theorem blockData_consts_of_certifiedTower_P6M6 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j)) :
    ∃ (F : GC.Interface.RawSurgery P g) (_ : F.tower = T.toChain.tower)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
      (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ),
      (N.epsilon = Γ.epsilon ∧ N.C1 = chainC1_C11KD Γ ∧ N.C2 = chainC2_C11KD Γ ∧
        N.Ctime = Γ.Ctime ∧ N.params.fixed = pB.fixed ∧ N.params.modelRadius = pB.modelRadius ∧
        N.params.modelOrder = pB.modelOrder ∧ N.params.modelAccuracy = pB.modelAccuracy ∧
        N.params.recenterConstant = pB.recenterConstant) ∧
      (∀ t : ℝ, 0 ≤ t → N.params.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        N.params.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      (∀ m, 0 < rad m) ∧ (∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1) ∧
      (∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z)) ∧
      (∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1) ∧
      (∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) ∧
      (∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) := by
  have hQ := hcert
  let W : ∀ n, PreparedSpatialStepRetention (T.toChain.state n) (T.toChain.state (n + 1))
      (T.toChain.accuracy n) (1 / ((n : ℝ) + 2)) (T.request n).epsCut (T.request n).Dcut
      (T.request n).mcut := fun n => Classical.choice (T.extension n).retention
  have hraw := T.toChain.exists_surgery_with_retained_raw_caps (fun n => (T.inv n).distance)
    (fun n => (T.request n).epsCut) (fun n => (T.request n).Dcut)
    (fun n => (T.request n).mcut) W (fun n => (T.extension n).shift_eq)
    (fun n => (T.extension n).offset_eq) (fun n => T.toChain_accuracy_le_quarter n)
    (windowBarrierA₀_C11Q2 P g) (windowBarrierA₀_spec_C11Q2 P g).2.1
  obtain ⟨F, q, κ, records, hbig⟩ := hraw
  obtain ⟨⟨hW1, hdiag, -, -, hmi, -⟩, hblock⟩ := hbig
  obtain ⟨hTower, -, hStatic, -, -, hδanti, hρanti, hpref, -, hcan, hwin, -, -, hδlim, hrecent⟩ :=
    hW1
  have hP2 := timeDerivativeSupply_of_astra_C12X T.toChain (fun n => (T.request n).epsCut)
    (fun n => (T.request n).Dcut) (fun n => (T.request n).mcut) W
    (fun n => (T.extension n).shift_eq) (fun n => (T.extension n).offset_eq) F hTower q hρanti
    (fun v hv => (hdiag v hv).2)
  let N := nativeDataOfSupplies_C11KD F q records Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ)
    Γ.Ctime hρanti hδanti hδlim (canonicalConstantsSupply_of_closedBirthConstants_C11A Γ) hwin
    hcan hP2 hrecent
  have hrc : N.params.recenterConstant = pB.recenterConstant := hStatic.2.2.2.2
  have hdiagN : ∀ t : ℝ, 0 ≤ t → N.params.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      N.params.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t := hdiag
  refine ⟨F, hTower, N, fun m => (T.block m).radius, fun m => (W m).fineParameters.modelRadius,
    fun m => (W m).fineParameters.modelAccuracy, fun m => T.accuracy m,
    fun m => (W m).fineParameters.modelOrder, ⟨rfl, rfl, rfl, rfl, hStatic.1, hStatic.2.1,
      hStatic.2.2.1, hStatic.2.2.2.1, hrc⟩, hdiagN,
    fun m => (T.block m).radius_pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have h0 : q.neckRadius 0 ≤ 1 := by
      calc q.neckRadius 0 = (T.toChain.observation 0).parameters.neckRadius 0 :=
            (hpref 0 0 ⟨le_rfl, by norm_num⟩).2.1
        _ = (T.toChain.state 1).parameters.neckRadius 0 := rfl
        _ = (T.toChain.state 0).parameters.neckRadius 0 :=
            ((T.toChain.successor 0).parameters_past 0
              (by norm_num [preparedSpatialHorizon])).2.1
        _ = (T.toChain.state 0).radius :=
            (T.toChain.state 0).radius_after 0 (by norm_num [preparedSpatialHorizon])
        _ ≤ 1 := T.toChain.initial_radius_le
    exact (hρanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs).trans h0
  · intro n j
    have hb := hblock n j
    obtain ⟨m, -, i, -, -, -, htime, hIoc, -, hδ, -, -, -, hrawc⟩ := hb
    have htime' : (F.tower.history n).toHistory.time j.succ =
        (T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift := htime
    have hmi' := hmi m i
    obtain ⟨-, -, -, hnrT, hAg, -⟩ := hmi'
    refine ⟨m, hIoc.1, hIoc.2, hδ.le, ?_, ?_, ?_⟩
    · intro T hT
      rw [htime'] at hT
      exact hnrT T hT
    · intro A hA hlt
      rw [htime'] at hlt
      refine hAg A hA ?_
      rw [diagonalLargerBallAccuracy_eq_C11Q6 T.toChain q (fun t ht => (hdiag t ht).1)]
      exact hlt
    · intro b'
      have hr := hrawc b'
      obtain ⟨b, raw, -, hcanr, -, -, -, -, -, -, -, -, -, -, -, -, hsc, hcap, -⟩ := hr
      exact ⟨raw, hcanr, hsc, hcap⟩
  · intro m
    have hrN : (T.block (m + 1)).radius = (T.lookahead m).rNext := (T.extension m).radius_eq
    have hcap0 : T.accuracy m ≤ (T.request m).accuracyCap := (T.extension m).accuracy_le_cap
    have hcap1 : T.accuracy (m + 1) ≤ (T.request (m + 1)).accuracyCap :=
      (T.extension (m + 1)).accuracy_le_cap
    have hQm := hQ m
    have hQm1 := hQ (m + 1)
    obtain ⟨⟨a1, a2, a3, a4⟩, -, -, -⟩ := hQm
    obtain ⟨-, ⟨b1, b2, b3, b4⟩, -, -⟩ := hQm1
    beta_reduce
    rw [hrc, hrN]
    rw [hrN] at b1 b2 b3 b4
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4, b1.trans (W (m + 1)).fine_radius, b2.trans (W (m + 1)).fine_order,
      (W (m + 1)).fine_accuracy.trans b3, hcap1.trans b4⟩
  · intro m
    have hrN : (T.block (m + 1)).radius = (T.lookahead m).rNext := (T.extension m).radius_eq
    have hcap0 : T.accuracy m ≤ (T.request m).accuracyCap := (T.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, ⟨a1, a2, a3, a4⟩, -⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩
  · intro m
    have hrN : (T.block (m + 1)).radius = (T.lookahead m).rNext := (T.extension m).radius_eq
    have hcap0 : T.accuracy m ≤ (T.request m).accuracyCap := (T.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, -, ⟨a1, a2, a3, a4⟩⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩

/-- **GAP-2 槽（`_P6M6`）**：`N` 的常数等式（`blockData_consts_of_certifiedTower_P6M6` 导出）+ 与 `N` 无关的
`pB.modelAccuracy ≤ epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P` ⇒
GAPTOP6 `pre841Data_of_certifiedTower_fwd_C11GT6` 的 GAP-2 前提
`N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P`。 -/
theorem gap2_of_consts_P6M6 {P : OrientedThreeStage.{u}} {H : ℕ → ObservedHistory.{u}}
    {pB : CutoffParameters} {Γ : ClosedBirthConstants} (N : Pre841NativeData_C11K H)
    (hε : N.epsilon = Γ.epsilon) (hC1 : N.C1 = chainC1_C11KD Γ) (hC2 : N.C2 = chainC2_C11KD Γ)
    (hacc : N.params.modelAccuracy = pB.modelAccuracy)
    (h : pB.modelAccuracy ≤ epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P) :
    N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P := by
  rw [hε, hC1, hC2, hacc]
  exact h

/-- **same-tower Pre841，GAP-2 已 discharge（`_P6M6`）**：`pre841Data_of_certifiedTower_fwd_C11GT6` 逐字，
只把 `∃ N` 内部的 GAP-2 前提 `N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P` 换成与 `N` 无关的
`hacc₀ : pB.modelAccuracy ≤ epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P`
（GAPTOP6 D-3：reserve 取含 `epsilon0_C11FR` 的正最小值后再选 `pBase` 与 tower）。 -/
theorem pre841Data_of_certifiedTower_fwd_gap2_P6M6 {pB : CutoffParameters}
    {Γ : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    {εReserve : ℝ} (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (hF : F.tower = T.toChain.tower)
    (hacc₀ : pB.modelAccuracy ≤
      epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P) :
    ∃ N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory),
      (∀ t : ℝ, 0 ≤ t → N.params.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        N.params.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∀ᶠ n in atTop, N.params.neckRadius (t n) ≤ r n) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F', hF', N, rad, Df, εf, cap, mf, hconst, hdiagN, hrad, hnr1, hev, hdomK3, hdomE,
    hdomU⟩ := blockData_consts_of_certifiedTower_P6M6 T hcert
  obtain rfl : F' = F := rawSurgery_eq_of_tower_eq_C11KW (hF'.trans hF.symm)
  refine ⟨N, hdiagN, ?_⟩
  intro A hA hP3 hprof ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hratio
  exact nonempty_pre841Data_of_retention_fwd_C11FR N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE
    hdomU hA hP3 hprof
    (gap2_of_consts_P6M6 N hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.2.2.2.2.1 hacc₀) ind t p r
    hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist hratio

end GC.LongTime.Ch11
