import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Gamma2ContractC11G2

set_option autoImplicit false

/-!
# PB provider：`HpbaseTwoLevel_C11G2` 的 request-driven 孪生（O-CH11-HPBASE-V8 G1，后缀 `_P6HV8`）

R-C11-20 Q3 / D-20-9：NR′ 的量词序 `∀ C D ε η N ∃ R m₀`（`R ≤ modelRadius`、`m₀ ≤ modelOrder`），而冻结
`HpbaseTwoLevel_C11G2`（`P6Gamma2ContractC11G2.lean:315`）把 reserve 半径钉死在 `capWindowRadius_C11E + 1`、
order 只导出 `2 ≤ modelOrder` ⇒ 需 request-driven provider，**要证明，不只登记**；不交换 `∃Γ ∀m` 与 `∀m ∃Γ`。

本文件（**PROVED**，无新 def / 合同 Prop / binder；陈述内联）：
* **mmod 孪生** `exists_prepared_class_reserve_order_v8_P6HV8`：
  `PreparedClosedBirthClass.lean:40` 的 private 定理逐字复制，唯一实质改动 = order 请求
  `max (max mAnal mS) 2` → `max (max mAnal mS) (max 2 mmod)`
  （provider `prepare` 本就接受任意 `ℕ` order 请求），多导出 `mmod ≤ p₀.modelOrder`。distance 投影
  `exists_prepared_class_distance_reserve_order_v8_P6HV8` = `:401` 逐字 + `mmod`。
* **Rmod**：CXCA `exists_closedBirthConstants_strong_accuracy_CXCA` 的 `Γ`
  （及 `Cdist / fixed / recenter / prepareClass / analytic`）构造不用 `Dstar`
  （`Dstar` 只进 per-`(P, g)` 的 prepared-class 请求）
  ⇒ 先取 `Γ`，再对任意 `(Rmod, mmod)` 以半径请求 `max Dstar Rmod` 调 mmod 孪生：
  **`∃ Γ ∀ Rmod ∀ mmod ∃ pB`**（不交换量词）。
  tower / `BlockStep_C11W` 的 `Dstar` 不动（`blockSteps_of_astra_C11W5` 只依赖 `fixed / recenter`）⇒ 冻结
  `hP6b‴` 的 `BlockTower_C11W … (capWindowRadius_C11E + 1)` 原样可用；**同一 `pB`** 同时满足
  `HasReserveQuality (capWindowRadius_C11E + 1)` 与 PB 合取
  `Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder`。
* `exists_blockSteps_v8_P6HV8`（CXOU2 `exists_blockSteps_byPointCollarAcc_CXOU2` 的孪生）→
  `hpbase_accuracy_v8_P6HV8` → `hpbaseTwoLevel_v8_eps_P6HV8` / **`hpbaseTwoLevel_v8_P6HV8`**
  （`εW := epsW_CXOU2`）。
* consumer：v8 ⇒ 冻结 `HpbaseTwoLevel_C11G2`（投影 `Rmod := 0`、`mmod := 0`）；同一 `pB` 四条门槛 example。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow

universe u

/-- **mmod 孪生（native certificate 引擎）**：`PreparedClosedBirthClass.lean:40` 的 private 定理逐字，
只改 order 请求 `max (max mAnal mS) 2` → `max (max mAnal mS) (max 2 mmod)`，并多导出
`mmod ≤ p₀.modelOrder`（参数 `mmod : ℕ`；`hReserveOrder` 的投影路径随之改一层）。 -/
theorem exists_prepared_class_reserve_order_v8_P6HV8
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) (mmod : ℕ)
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedClassProviderWithNative certificate fixed recenter)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Qzero : ℝ, 0 < Qzero ∧
      (∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero) ∧
    ∀ B : ℝ, 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb εClass κClass κ qcan qs Qbirth Qall : ℝ),
      Dstar ≤ p₀.modelRadius ∧ p₀.modelAccuracy ≤ εReserve ∧
      2 ≤ p₀.modelOrder ∧ mmod ≤ p₀.modelOrder ∧ 32 * Qall * ρb ^ 2 ≤ 1 ∧
      (∃ C1h C2h qh : ℝ, 1 ≤ C1h ∧ 1 ≤ C2h ∧ C1h ≤ strongC1_C11SC.{u} ε C1 ∧
        C2h ≤ strongC2_C11SC.{u} ε C2 Cgrad ∧ qs ≤ qh ∧
        ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
          (pV : CutoffParameters)
          (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
          V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
          RecordHypFar_C12X (5 / 4) V records →
          V.EventSlabsStronglyCanonicalFull_C12X ε ε C1h C2h qh (Fin.last V.eventCount) ∧
          ∀ hfinal : V.time (Fin.last V.eventCount) < V.horizon,
            V.StronglyCanonicalBeforeFull_C12X (Fin.last V.eventCount)
              ((V.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1h C2h qh
              V.horizon) ∧
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧ 0 < κ ∧
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧ Qall = max Qbirth Qzero ∧ 0 < Qall ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      PreparedGeometricObservationExtensionWithNative certificate P g B εClass κClass p₀ δb ρb ∧
      ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
        V.NoncollapsedBefore κ ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  obtain ⟨Qzero, hQzero, zeroBound⟩ := exists_scalar_lt_at_initial_metric P g
  refine ⟨Qzero, hQzero, zeroBound, ?_⟩
  intro B hB
  obtain ⟨εClass, κClass, hεClass, hεClass11, hκClass, prepare⟩ := prepareClass P g B hB
  obtain ⟨κ, hκ, enlarge⟩ :=
    exists_noncollapsedBefore_radius_enlargement hκClass hεClass hε
  obtain ⟨qcan, qs, Qbirth, δAnal, ρAnal, εAnal, DAnal, mAnal,
    hqcan, hqs, hqsC, hQbirth, hδAnal, hρAnal, hεAnal, _hDAnal, control⟩ :=
    analytic P g B κ hB hκ
  have hU := native_strongFull_uniform_radial_spec_C11SC.{u} hε hstr.2.2.2.2.2
  obtain ⟨qh, δS, ρS, εS, DS, mS, hqh, hδS, hρS, hεS, hDS, hX⟩ :=
    hU P g B hB C1 C2 C1s C2s qcan qs τmin Ctime Cgrad κ hstr.1 hstr.2.1 hstr.2.2.1
      hstr.2.2.2.1 hqcan hqs hstr.2.2.2.2.1 hκ
  have hQallPos : 0 < max Qbirth Qzero := hQzero.trans_le (le_max_right _ _)
  have hRoot : 0 < Real.sqrt (64 * max Qbirth Qzero) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) hQallPos)
  obtain ⟨p₀, δb, ρb, hfixed, hrc, hδb, hδAnalBound, hρb, hρRequest,
    haccRequest, hradRequest, hordRequest, hcap, hrec, classNC, extension⟩ :=
    prepare (min δAnal δS) (min (min ρAnal ρS) (Real.sqrt (64 * max Qbirth Qzero))⁻¹)
      (min (min εAnal εS) εReserve) (max (max DAnal DS) Dstar) (max (max mAnal mS) (max 2 mmod))
      (lt_min hδAnal hδS) (lt_min (lt_min hρAnal hρS) (inv_pos.mpr hRoot))
      (lt_min (lt_min hεAnal hεS) hεReserve) (hDstar.trans_le (le_max_right _ _))
  have hδAnalB : δb ≤ δAnal := hδAnalBound.trans (min_le_left _ _)
  have hδSB : δb ≤ δS := hδAnalBound.trans (min_le_right _ _)
  have hρAnalBound : ρb ≤ ρAnal :=
    hρRequest.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρSB : ρb ≤ ρS := hρRequest.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρRoot : ρb ≤ (Real.sqrt (64 * max Qbirth Qzero))⁻¹ :=
    hρRequest.trans (min_le_right _ _)
  have hacc : p₀.modelAccuracy ≤ εAnal :=
    haccRequest.trans ((min_le_left _ _).trans (min_le_left _ _))
  have haccS : p₀.modelAccuracy ≤ εS :=
    haccRequest.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrad : DAnal ≤ p₀.modelRadius :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hradRequest
  have hradS : DS ≤ p₀.modelRadius :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hradRequest
  have hord : mAnal ≤ p₀.modelOrder :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hordRequest
  have hordS : mS ≤ p₀.modelOrder :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hordRequest
  have hReserveRadius : Dstar ≤ p₀.modelRadius := (le_max_right _ _).trans hradRequest
  have hReserveAccuracy : p₀.modelAccuracy ≤ εReserve :=
    haccRequest.trans (min_le_right _ _)
  have hReserveOrder : 2 ≤ p₀.modelOrder :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hordRequest
  have hRequestOrder : mmod ≤ p₀.modelOrder :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hordRequest
  have hReserveScale : 32 * max Qbirth Qzero * ρb ^ 2 ≤ 1 := by
    have hprod : ρb * Real.sqrt (64 * max Qbirth Qzero) ≤ 1 :=
      (le_div_iff₀ hRoot).mp (by simpa only [one_div] using hρRoot)
    have hprodSq : (ρb * Real.sqrt (64 * max Qbirth Qzero)) ^ 2 ≤ 1 := by
      simpa only [one_pow] using
        pow_le_pow_left₀ (mul_nonneg hρb.le (Real.sqrt_nonneg _)) hprod 2
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hQallPos.le)] at hprodSq
    nlinarith only [hprodSq]
  refine ⟨p₀, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, max Qbirth Qzero,
    hReserveRadius, hReserveAccuracy, hReserveOrder, hRequestOrder, hReserveScale,
    ⟨strongC1_C11SC.{u} ε C1, strongC2_C11SC.{u} ε C2 Cgrad, qh,
      one_le_strongC1_C11SC hstr.1 ε, one_le_strongC2_C11SC hstr.2.1 ε Cgrad, le_rfl, le_rfl,
      hqh, ?_⟩,
    hfixed, hrc, hδb, hρb, hεClass, hεClass11, hκClass, hκ,
    hqcan, hqs, hqsC, hQbirth, rfl, hQzero.trans_le (le_max_right _ _),
    hcap, hrec, extension, ?_⟩
  · intro V IV pV records hVB hclass hrecHyp
    have hnc := enlarge V V.horizon (classNC V IV pV records hVB hclass)
    exact hX p₀ δb ρb haccS hradS hordS hδSB hρSB hrec V IV pV records hVB hclass hrecHyp hnc
      (control p₀ δb ρb hacc hrad hord hδAnalB hρAnalBound hrec
        V IV pV records hVB hclass hnc).1
  · intro V IV pV records hVB hclass
    have hnc := enlarge V V.horizon (classNC V IV pV records hVB hclass)
    exact ⟨hnc, control p₀ δb ρb hacc hrad hord hδAnalB hρAnalBound hrec
      V IV pV records hVB hclass hnc⟩

/-- **mmod 孪生（distance certificate 投影）**：`PreparedClosedBirthClass.lean:401` 逐字，
多参数 `mmod`、多导出 `mmod ≤ p₀.modelOrder`。 -/
theorem exists_prepared_class_distance_reserve_order_v8_P6HV8
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) (mmod : ℕ)
    (Cdist : ℝ≥0)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedDistanceClassProvider.{u} fixed recenter Cdist)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Qzero : ℝ, 0 < Qzero ∧
      (∀ (V : ObservedHistory.{u}), InitialIdentification P g V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero) ∧
    ∀ B : ℝ, 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb εClass κClass κ qcan qs Qbirth Qall : ℝ),
      Dstar ≤ p₀.modelRadius ∧ p₀.modelAccuracy ≤ εReserve ∧
      2 ≤ p₀.modelOrder ∧ mmod ≤ p₀.modelOrder ∧ 32 * Qall * ρb ^ 2 ≤ 1 ∧
      (∃ C1h C2h qh : ℝ, 1 ≤ C1h ∧ 1 ≤ C2h ∧ C1h ≤ strongC1_C11SC.{u} ε C1 ∧
        C2h ≤ strongC2_C11SC.{u} ε C2 Cgrad ∧ qs ≤ qh ∧
        ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
          (pV : CutoffParameters)
          (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
          V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
          RecordHypFar_C12X (5 / 4) V records →
          V.EventSlabsStronglyCanonicalFull_C12X ε ε C1h C2h qh (Fin.last V.eventCount) ∧
          ∀ hfinal : V.time (Fin.last V.eventCount) < V.horizon,
            V.StronglyCanonicalBeforeFull_C12X (Fin.last V.eventCount)
              ((V.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1h C2h qh
              V.horizon) ∧
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧ 0 < κ ∧
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      max 1 (max qcan qs) ≤ Qbirth ∧ Qall = max Qbirth Qzero ∧ 0 < Qall ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
      PreparedGeometricObservationExtensionWithDistance Cdist P g B εClass κClass p₀ δb ρb ∧
      ∀ (V : RetainedCoreHistory.{u}) (_IV : InitialIdentification P g V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
        V.NoncollapsedBefore κ ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  exact @exists_prepared_class_reserve_order_v8_P6HV8.{u}
    Dstar εReserve hDstar hεReserve mmod (fun K => ∀ i : Fin K.eventCount,
      (K.toHistory.event i).HasUniformDistanceScalar Cdist) fixed recenter
    prepareClass.toNative ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε hstr analytic P g

end GC.GeneralFlow

open GC.GeneralFlow

namespace GC.LongTime.Ch11

universe u

/-- **request-driven 产出（`∃ Γ ∀ Rmod ∀ mmod ∃ pB`）**：CXOU2 `exists_blockSteps_byPointCollarAcc_CXOU2`
的孪生（证明逐字），只把 prepared-class 引擎换成 mmod 孪生、半径请求 `Dstar` → `max Dstar Rmod`；
`Γ := C` 取自 CXCA（在 `Rmod mmod` 之前），tower 的 `Dstar` 不变。 -/
theorem exists_blockSteps_v8_P6HV8 (Dstar : ℝ) (hDstar : 0 < Dstar) (cMax : ℝ)
    (hcMax : 0 < cMax) (εcap : ℝ) (hεcap : 0 < εcap) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ εStrong_C12X.{u} ∧ C.epsilon ≤ εcap ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ),
      0 < εReserve →
    ∃ (pBase : CutoffParameters) (prepared : ClosedBirthPreparedClass pBase C P g 1),
      prepared.parameters = pBase ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality Dstar εReserve ∧
      (Rmod ≤ pBase.modelRadius ∧ mmod ≤ pBase.modelOrder) ∧
      collarAdmitsAllOrders_C11E.{u} pBase.fixed.collarLength pBase.fixed.collar_pos ∧
      ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεcap', hεs, ⟨-, A, hA, hfix, hcol⟩, prepareClass,
      analytic, -⟩ := exists_closedBirthConstants_strong_accuracy_CXCA.{u} Dstar 1 εcap hDstar
      one_pos hεcap
  refine ⟨Cdist, hCdist, C, hεs, hεcap', fun P g Rmod mmod εReserve hεReserve => ?_⟩
  have hD' : 0 < max Dstar Rmod := hDstar.trans_le (le_max_left _ _)
  obtain ⟨Qzero, hQzero, zeroBound, prepareInitial⟩ :=
    exists_prepared_class_distance_reserve_order_v8_P6HV8
      (max Dstar Rmod) εReserve hD' hεReserve mmod Cdist fixed recenter prepareClass
      C.epsilon C.C1 C.C2 C.C1s C.C2s C.Cs C.tauMin C.Cbirth C.Ctime C.Cgrad C.epsilon_pos
      ⟨C.C1_ge_one, C.C2_ge_one, C.C1s_ge_one, C.C2s_ge_one, C.tauMin_pos, hεs⟩ analytic P g
  obtain ⟨pBase, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall,
    hDReserve, hεReserveBound, hmReserve, hmRequest, hscaleReserve, hStrong,
    hfixed, hrc, hδb, hρb, hεClass, hεClass11, hκClass, hκ,
    hqcan, hqs, hqsC, hQbirth, hQall, hQallPos,
    hcap, hrec, extension, control⟩ := prepareInitial 1 one_pos
  obtain ⟨C1h, C2h, qh, hC1h, hC2h, hC1hb, hC2hb, hqh, hStrongV⟩ := hStrong
  let prepared : ClosedBirthPreparedClass pBase C P g 1 := {
    parameters := pBase
    deltaBound := δb
    radiusBound := ρb
    epsilonClass := εClass
    kappaClass := κClass
    kappa := κ
    qcan := qcan
    qs := qs
    Qzero := Qzero
    Qbirth := Qbirth
    Qall := Qall
    fixed_eq := rfl
    recenter_eq := rfl
    deltaBound_pos := hδb
    radiusBound_pos := hρb
    epsilonClass_pos := hεClass
    epsilonClass_small := hεClass11
    kappaClass_pos := hκClass
    kappa_pos := hκ
    qcan_pos := hqcan
    qcan_le_qs := hqs
    qs_le := hqsC
    Qzero_pos := hQzero
    Qbirth_ge := hQbirth
    Qall_eq := hQall
    Qall_pos := hQallPos
    modelRadius_bound := hcap
    recenter_bound := hrec
    zero_bound := zeroBound
    extension := extension.forget
    control := control
    epsilon_strong := hεs
    C1strong := C1h
    C2strong := C2h
    qStrong := qh
    C1strong_ge_one := hC1h
    C2strong_ge_one := hC2h
    C1strong_le := hC1hb
    C2strong_le := hC2hb
    qs_le_qStrong := hqh
    strongControl := hStrongV }
  have hprep : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist := by
    rw [hfixed, hrc]
    exact prepareClass
  have hcollar : collarAdmitsAllOrders_C11E.{u} pBase.fixed.collarLength
      pBase.fixed.collar_pos := by
    subst hfixed
    exact collarAdmitsAllOrders_of_fixed_ofCollarLength_C11PB
      ⟨A, hA, hfix, collarAdmitsAllOrders_of_staticCollarAdmits_C11PB hcol⟩
  exact ⟨pBase, prepared, rfl, extension,
    ⟨(le_max_left _ _).trans hDReserve, hεReserveBound, hmReserve, hscaleReserve⟩,
    ⟨(le_max_right _ _).trans hDReserve, hmRequest⟩, hcollar,
    blockSteps_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax hprep analytic⟩

/-- **`hpbase`，strong + accuracy cap + request 形**：`hpbase_accuracy_CXOU2` 的孪生，`∃ Γ` 之后
`∀ Rmod mmod εReserve`，产出多 PB 合取（同一 `pB`）。 -/
theorem hpbase_accuracy_v8_P6HV8 (P : OrientedThreeStage.{u}) (g : P.Metric) (εcap : ℝ)
    (hεcap : 0 < εcap) :
    ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ εcap ∧
      ∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ), 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        (Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder) ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j := by
  have hD : 0 < capWindowRadius_C11E + 1 := by
    have hte := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E
    positivity
  obtain ⟨Cdist, -, C, hεs, hεc, hmake⟩ :=
    exists_blockSteps_v8_P6HV8.{u} (capWindowRadius_C11E + 1) hD 1 one_pos εcap hεcap
  exact ⟨Cdist, C, hεs, hεc, fun Rmod mmod ε hε => hmake P g Rmod mmod ε hε⟩

/-- **两级 v8 provider（泛型 `εW`）**：`hpbaseTwoLevel_of_accuracy_C11G2` 的选取顺序逐字
（`εc := epsCoarse εW` → `Γf`（cap `min εW (p6FineEta εc)`）→ `Γ := coarsenTo Γf εc`），前提由
`hpbase_accuracy_v8_P6HV8` 直接付（无假设）。`∃ Γ Γf` 在 `∀ Rmod mmod εReserve` 之前。 -/
theorem hpbaseTwoLevel_v8_eps_P6HV8 (P : OrientedThreeStage.{u}) (g : P.Metric) (εW : ℝ)
    (hεW : 0 < εW) :
    ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
      Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ εW ∧
      Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ εW ∧
      ∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ), 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        (Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder) ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j := by
  have hc0 : 0 < epsCoarse_C11G2.{u} εW := epsCoarse_pos_C11G2 hεW
  have hc1 : epsCoarse_C11G2.{u} εW < 1 / 100 :=
    (min_le_left _ _).trans_lt (by norm_num)
  have hccone : epsCoarse_C11G2.{u} εW ≤ coneAccuracy :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcs : epsCoarse_C11G2.{u} εW ≤ εStrong_C12X.{u} :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcW : epsCoarse_C11G2.{u} εW ≤ εW :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcap : 0 < min εW (p6FineEta_C11GT6 (epsCoarse_C11G2.{u} εW)) :=
    lt_min hεW (p6FineEta_pos_C11GT6 hc0)
  obtain ⟨Cdist, Γf, hfs, hfcap, hmake⟩ := hpbase_accuracy_v8_P6HV8.{u} P g _ hcap
  refine ⟨Cdist, coarsenTo_C11G2.{u} Γf (epsCoarse_C11G2.{u} εW) hc0 hc1 hccone, Γf,
    fineOf_coarsenTo_C11G2 Γf _ hc0 hc1 hccone (hfcap.trans (min_le_right _ _)), hcs, hcW, hfs,
    hfcap.trans (min_le_left _ _), hmake⟩

/-- **两级 v8 provider（闭合，PROVED）**：v6fwd:423 / GAPTOP7B:99 插入点的 request-driven 替换
（`εW := epsW_CXOU2`）。与冻结 `HpbaseTwoLevel_C11G2 epsW_CXOU2 P g` 逐字相同，只把 `∀ εReserve` 换成
`∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ)` 并在 `HasReserveQuality` 之后多 PB 合取
`Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder`（同一 `pB`、同一 `prepared`、同一 tower 数据）。 -/
theorem hpbaseTwoLevel_v8_P6HV8 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
      Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ epsW_CXOU2.{u} ∧
      Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ epsW_CXOU2.{u} ∧
      ∀ (Rmod : ℝ) (mmod : ℕ) (εReserve : ℝ), 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        (Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder) ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j :=
  hpbaseTwoLevel_v8_eps_P6HV8 P g epsW_CXOU2.{u} epsW_CXOU2_pos.{u}

/-- **投影**：v8 ⇒ 冻结 `HpbaseTwoLevel_C11G2 epsW_CXOU2 P g`（`Rmod := 0`、`mmod := 0`，丢 PB 合取）。 -/
theorem hpbaseTwoLevel_of_v8_P6HV8 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HpbaseTwoLevel_C11G2.{u} epsW_CXOU2.{u} P g := by
  obtain ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, hmake⟩ := hpbaseTwoLevel_v8_P6HV8.{u} P g
  refine ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, fun εReserve hε => ?_⟩
  obtain ⟨pB, prepared, hbase, hdist, hres, -, hcollar, hstep⟩ := hmake 0 0 εReserve hε
  exact ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩

/-- consumer（lead (c)）：v8 provider 的投影给出冻结合同 `HpbaseTwoLevel_C11G2`（GAPTOP7B:99 的类型）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HpbaseTwoLevel_C11G2.{u} epsW_CXOU2.{u} P g :=
  hpbaseTwoLevel_of_v8_P6HV8 P g

/-- consumer：任意请求 `(Rmod, mmod)`，**同一** `pB` 同时满足冻结门槛（`capWindowRadius_C11E + 1 ≤
modelRadius`、`2 ≤ modelOrder`，经 `pBase_bounds_of_reserve_C11W6`）与 PB 合取。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (Rmod : ℝ) (mmod : ℕ) :
    ∃ pB : CutoffParameters,
      capWindowRadius_C11E + 1 ≤ pB.modelRadius ∧ 2 ≤ pB.modelOrder ∧
      (Rmod ≤ pB.modelRadius ∧ mmod ≤ pB.modelOrder) := by
  obtain ⟨_, _, _, _, -, -, -, -, hmake⟩ := hpbaseTwoLevel_v8_P6HV8.{u} P g
  obtain ⟨pB, _, hbase, -, hres, hPB, -, -⟩ := hmake Rmod mmod 1 one_pos
  obtain ⟨-, hrad, hord⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  exact ⟨pB, hrad, hord, hPB⟩

end GC.LongTime.Ch11
