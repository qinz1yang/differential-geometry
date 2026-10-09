import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineRealizationC11Q5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaNoEventWindowC11Q3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialLargerBallAccuracyPortC11P

/-!
# R1 打包三件套（O-CH11-FINEPACK G1，后缀 `_C11Q6`）

FINECAP gap（`docs/geometrization/chapter8/gap-C11-finecap-hact-20261007.md`）的 R1 路线：astra retention
`PreparedSpatialStepRetention` 的 `fineRecords` 按块给出 fine tuple 上带 canonical window 的 static caps，
要把它们变成 κ 线的 cap 供给（K3 的 `FineCapRealization_C11Q5`、`EventNodeData_C11Q4` /
`UREBlockNodeData_C11Q4` 的 cap 子句）。设计见 `build-logs/resume/state-O-CH11-FINEPACK.md` G0。

* **translate 保持**：`translate_presented_static_cap_scale_C11Q6`（`neck.scale`）、
  `translate_presented_static_cap_capPoint_C11Q6`（`inclusion ∘ witness.cap`）；底层是两条 HEq 引理
  （terminal open 相等 + 度量 HEq ⇒ 字段相等）。event 层 R1：`fineCapRealization_of_retention_C11Q6`——
  retention 的粗 static cap（`translate ∘ restrictModelWindow`，即 `full_records` 的形）在 fine tuple 上有
  fine realization。
* **raw ⇒ cap 子句**：`fineCapRealization_of_raw_C11Q6`（K3 形，sameCap + mono）、
  `uniformCaps_of_raw_C11Q6`（`EventNodeData_C11Q4` 的 uniform 族子句逐字形）、`blockCaps_of_raw_C11Q6`
  （`UREBlockNodeData_C11Q4` 的逐 boundary 子句逐字形）。raw 来自 astra
  `PreparedSpatialChain.exists_surgery_with_retained_raw_caps` 的 block 子句。
* **对角支配**：`joinRequest_C11Q6`（`(ε, D, m, δ)` 的 join）及两侧支配；`k3Request_C11Q6`（K3 常数
  `(δ₀, ε₀, R₀, m₀)` 转请求形）。
* **A-guard**：`diagonalLargerBallAccuracy_eq_C11Q6`（astra 的 α 与 `diagonalAccuracy_C11S q.delta`
  逐点相等）
  ⇒ `lt_of_accuracyGuard_C11Q6`（窗口 event 的 guard 给 `A < 12·3^m`）；level 单调
  `cutoffBarrierConst_mono_C11Q6`。
* **策略 tower**：`tower_of_blockSteps_policy_C11Q6`（`tower_of_blockSteps_pred_C11GT` 同证明，谓词看
  `X ℓ req`，所以请求可依赖 lookahead 的 `rNext`——"nr 先定、再定请求"）。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. translate 保持 -/

section Translate

/-- terminal open 相等、度量 HEq、精度 / 阶相等时，HEq 的 normalized neck 有相同尺度。 -/
theorem normalizedNeck_scale_eq_of_heq_C11Q6 {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {δ δ' : ℝ} {k k' : ℕ} (hδ : δ = δ') (hk : k = k')
    {N : NormalizedNeck h δ k} {N' : NormalizedNeck h' δ' k'} (hN : HEq N N') :
    N.scale = N'.scale := by
  subst hUV hδ hk
  obtain rfl := eq_of_heq hh
  obtain rfl := eq_of_heq hN
  rfl

/-- 同上条件下，HEq 的 witness 与 inclusion 给出同一实际帽点 `inclusion (witness.cap z)`。 -/
theorem capPoint_eq_of_heq_C11Q6 {P Q : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {h' : SmoothRiemannianMetric ThreeModel V}
    (hh : HEq h h') {δ δ' : ℝ} {k k' : ℕ} (hδ : δ = δ') (hk : k = k')
    {N : NormalizedNeck h δ k} {N' : NormalizedNeck h' δ' k'} (hN : HEq N N')
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {w : StaticCapWitness N fixed D m ε} {w' : StaticCapWitness N' fixed D m ε} (hw : HEq w w')
    {f : C(w.Output, Q.Carrier)} {f' : C(w'.Output, Q.Carrier)} (hf : HEq f f')
    (z : ThreeBall) : f (w.cap z) = f' (w'.cap z) := by
  subst hUV hδ hk
  obtain rfl := eq_of_heq hh
  obtain rfl := eq_of_heq hN
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hf
  rfl

/-- 平移 event 的 terminal 度量与原 terminal 度量 HEq（沿 `translated_terminal_open` 的 cast）。 -/
theorem translate_terminal_metric_heq_C11Q6 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) :
    HEq (translate_retained_event E c).terminal.metric E.terminal.metric := by
  have key : ∀ {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
      (m : SmoothRiemannianMetric ThreeModel U), HEq (hUV ▸ m) m := by
    intro U V hUV m
    cases hUV
    exact HEq.rfl
  exact key (translated_terminal_open E.incoming c).symm E.terminal.metric

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
  {b : E.toMetricCutCapEvent.RetainedBoundaryIndex}

/-- **translate 保 neck 尺度**。 -/
theorem translate_presented_static_cap_scale_C11Q6
    (S : E.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b) :
    (translate_presented_static_cap E c S).neck.scale = S.neck.scale := by
  obtain ⟨hδ, hk, hN, -⟩ := translate_presented_static_cap_geometry E c S
  exact normalizedNeck_scale_eq_of_heq_C11Q6 (translated_terminal_open E.incoming c)
    (translate_terminal_metric_heq_C11Q6 E c) hδ hk hN

/-- **translate 保实际帽点** `inclusion ∘ witness.cap`。 -/
theorem translate_presented_static_cap_capPoint_C11Q6
    (S : E.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b) (z : ThreeBall) :
    (translate_presented_static_cap E c S).inclusion
        ((translate_presented_static_cap E c S).witness.cap z) =
      S.inclusion (S.witness.cap z) := by
  obtain ⟨hδ, hk, hN, hw, -, -, hf, -⟩ := translate_presented_static_cap_geometry E c S
  exact capPoint_eq_of_heq_C11Q6 (translated_terminal_open E.incoming c)
    (translate_terminal_metric_heq_C11Q6 E c) hδ hk hN hw hf z

end Translate

/-- **event 层 R1**：retention 的粗 static cap（`full_records` 的形 `translate ∘ restrictModelWindow`）在
fine tuple `(W.fineParameters.modelRadius, modelOrder, modelAccuracy)` 上有 fine realization——取同一平移下的
fine static cap 作 `S'`（canonical 由 `translate_presented_static_cap_canonical`，同尺度 / 同帽点由 §1）。 -/
theorem fineCapRealization_of_retention_C11Q6 {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext : ℝ}
    {L : PreparedSpatialState pBase C P g E B} {R : PreparedSpatialState pBase C P g B Bnext}
    {d eta εcut Dcut : ℝ} {mcut : ℕ}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut) (i : Fin R.native.eventCount)
    (b : (R.native.toHistory.event i).RetainedBoundaryIndex) :
    FineCapRealization_C11Q5
      (translate_presented_static_cap (R.native.coreEvent i) R.shift
        (((W.fineRecords i).restrictModelWindow (W.fineWindows i)
          L.parameters.modelRadius_pos W.full_radius W.full_order W.full_accuracy).static b))
      W.fineParameters.modelRadius W.fineParameters.modelOrder
      W.fineParameters.modelAccuracy := by
  have h1 := translate_presented_static_cap_scale_C11Q6 (R.native.coreEvent i) R.shift
    (((W.fineRecords i).restrictModelWindow (W.fineWindows i)
      L.parameters.modelRadius_pos W.full_radius W.full_order W.full_accuracy).static b)
  have h2 := translate_presented_static_cap_scale_C11Q6 (R.native.coreEvent i) R.shift
    ((W.fineRecords i).static b)
  have hc1 := translate_presented_static_cap_capPoint_C11Q6 (R.native.coreEvent i) R.shift
    (((W.fineRecords i).restrictModelWindow (W.fineWindows i)
      L.parameters.modelRadius_pos W.full_radius W.full_order W.full_accuracy).static b)
  have hc2 := translate_presented_static_cap_capPoint_C11Q6 (R.native.coreEvent i) R.shift
    ((W.fineRecords i).static b)
  exact fineCapRealization_of_sameCap_C11Q5
    (translate_presented_static_cap (R.native.coreEvent i) R.shift
      (((W.fineRecords i).restrictModelWindow (W.fineWindows i)
        L.parameters.modelRadius_pos W.full_radius W.full_order W.full_accuracy).static b))
    (translate_presented_static_cap (R.native.coreEvent i) R.shift ((W.fineRecords i).static b))
    (translate_presented_static_cap_canonical _ _ _ (W.fineWindows i b)) (h2.trans h1.symm)
    (fun z => (hc2 z).trans (hc1 z).symm)

/-! ## 2. raw ⇒ cap 子句 -/

section Raw

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold}

/-- **K3 形**：同 event 的 raw cap（fine tuple `(Df, mf, εf)`、canonical、同尺度、同帽点）支配请求
`(R₀, m₀, ε₀)` ⇒ 粗 static cap `S` 在请求上有 fine realization。 -/
theorem fineCapRealization_of_raw_C11Q6 {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) {Df εf : ℝ} {mf : ℕ}
    (raw : E.PresentedStaticCap fixed Df mf εf b) (hcan : raw.hasCanonicalWindow)
    (hscale : raw.neck.scale = S.neck.scale)
    (hcap : ∀ z, raw.inclusion (raw.witness.cap z) = S.inclusion (S.witness.cap z))
    {R₀ ε₀ : ℝ} {m₀ : ℕ} (hR₀ : StandardCap.transitionEnd < R₀) (hD : R₀ ≤ Df)
    (hm : m₀ ≤ mf) (hε : εf ≤ ε₀) : FineCapRealization_C11Q5 S R₀ m₀ ε₀ :=
  (fineCapRealization_of_sameCap_C11Q5 S raw hcan hscale hcap).mono
    (StandardCap.transitionEnd_pos.trans hR₀) hD (by linarith) hm hε

/-- **event node 形**（`EventNodeData_C11Q4` 的 cap 子句逐字形）：每个 retained boundary 有同一 fine tuple
`(Df, mf, εf)` 上的 canonical raw cap（与粗 static cap 同尺度），且该 tuple 支配请求 `req` ⇒ uniform 族。 -/
theorem uniformCaps_of_raw_C11Q6 {D₀ ε₀ : ℝ} {m₀ : ℕ}
    (S₀ : ∀ c : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D₀ m₀ ε₀ c)
    {Df εf : ℝ} {mf : ℕ}
    (hraw : ∀ c, ∃ raw : E.PresentedStaticCap fixed Df mf εf c,
      raw.hasCanonicalWindow ∧ raw.neck.scale = (S₀ c).neck.scale)
    (req : ℝ × ℝ × ℕ × ℝ) (hD : req.2.1 ≤ Df) (hm : req.2.2.1 ≤ mf) (hε : εf ≤ req.1) :
    ∃ (Dcap εcap : ℝ) (ncap : ℕ) (S : ∀ c : E.RetainedBoundaryIndex,
        E.PresentedStaticCap fixed Dcap ncap εcap c),
      req.2.1 ≤ Dcap ∧ req.2.2.1 ≤ ncap ∧ εcap ≤ req.1 ∧
      (∀ c, (S c).hasCanonicalWindow) ∧ ∀ c, (S c).neck.scale = (S₀ c).neck.scale := by
  choose raw hcan hsc using hraw
  exact ⟨Df, εf, mf, raw, hD, hm, hε, hcan, hsc⟩

/-- **URE node 形**（`UREBlockNodeData_C11Q4` 的逐 boundary cap 子句逐字形）。 -/
theorem blockCaps_of_raw_C11Q6 {D₀ ε₀ : ℝ} {m₀ : ℕ}
    (S₀ : ∀ c : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D₀ m₀ ε₀ c)
    {Df εf : ℝ} {mf : ℕ}
    (hraw : ∀ c, ∃ raw : E.PresentedStaticCap fixed Df mf εf c,
      raw.hasCanonicalWindow ∧ raw.neck.scale = (S₀ c).neck.scale)
    (req : ℝ × ℝ × ℕ × ℝ) (hD : req.2.1 ≤ Df) (hm : req.2.2.1 ≤ mf) (hε : εf ≤ req.1) :
    ∀ c : E.RetainedBoundaryIndex,
      ∃ (Dbig ζ : ℝ) (n : ℕ) (S : E.PresentedStaticCap fixed Dbig n ζ c),
        req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ n ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
          S.neck.scale = (S₀ c).neck.scale := by
  intro c
  obtain ⟨raw, hcan, hsc⟩ := hraw c
  exact ⟨Df, εf, mf, raw, hD, hm, hε, hcan, hsc⟩

end Raw

/-! ## 3. 请求的 join 与支配 -/

/-- 两个请求 `(ε, D, m, δ)` 的 join（更强者）：精度 / δ 取 min，半径 / 阶取 max。 -/
def joinRequest_C11Q6 (r₁ r₂ : ℝ × ℝ × ℕ × ℝ) : ℝ × ℝ × ℕ × ℝ :=
  (min r₁.1 r₂.1, max r₁.2.1 r₂.2.1, max r₁.2.2.1 r₂.2.2.1, min r₁.2.2.2 r₂.2.2.2)

/-- K3 常数 `(δ₀, ε₀, R₀, m₀)` 转成请求形 `(ε₀, R₀, m₀, δ₀)`。 -/
def k3Request_C11Q6 (c : ℝ × ℝ × ℝ × ℕ) : ℝ × ℝ × ℕ × ℝ :=
  (c.2.1, c.2.2.1, c.2.2.2, c.1)

theorem joinRequest_left_C11Q6 (r₁ r₂ : ℝ × ℝ × ℕ × ℝ) :
    (joinRequest_C11Q6 r₁ r₂).1 ≤ r₁.1 ∧ r₁.2.1 ≤ (joinRequest_C11Q6 r₁ r₂).2.1 ∧
      r₁.2.2.1 ≤ (joinRequest_C11Q6 r₁ r₂).2.2.1 ∧
      (joinRequest_C11Q6 r₁ r₂).2.2.2 ≤ r₁.2.2.2 :=
  ⟨min_le_left _ _, le_max_left _ _, le_max_left _ _, min_le_left _ _⟩

theorem joinRequest_right_C11Q6 (r₁ r₂ : ℝ × ℝ × ℕ × ℝ) :
    (joinRequest_C11Q6 r₁ r₂).1 ≤ r₂.1 ∧ r₂.2.1 ≤ (joinRequest_C11Q6 r₁ r₂).2.1 ∧
      r₂.2.2.1 ≤ (joinRequest_C11Q6 r₁ r₂).2.2.1 ∧
      (joinRequest_C11Q6 r₁ r₂).2.2.2 ≤ r₂.2.2.2 :=
  ⟨min_le_right _ _, le_max_right _ _, le_max_right _ _, min_le_right _ _⟩

theorem joinRequest_pos_C11Q6 {r₁ r₂ : ℝ × ℝ × ℕ × ℝ} (h₁ : 0 < r₁.1 ∧ 0 < r₁.2.2.2)
    (h₂ : 0 < r₂.1 ∧ 0 < r₂.2.2.2) :
    0 < (joinRequest_C11Q6 r₁ r₂).1 ∧ 0 < (joinRequest_C11Q6 r₁ r₂).2.2.2 :=
  ⟨lt_min h₁.1 h₂.1, lt_min h₁.2 h₂.2⟩

/-! ## 4. A-guard 与 level 单调 -/

/-- astra 的 `S.diagonalLargerBallAccuracy` 与 `diagonalAccuracy_C11S q.delta` 逐点相等（只要
`q.delta = diag.delta` on `[0, ∞)`，即 raw caps 定理的对角等式）。 -/
theorem diagonalLargerBallAccuracy_eq_C11Q6 {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t →
      q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t)
    (A s : ℝ) : S.diagonalLargerBallAccuracy A s = diagonalAccuracy_C11S q.delta A s := by
  unfold PreparedSpatialChain.diagonalLargerBallAccuracy diagonalAccuracy_C11S
  rw [hq _ (le_max_left 0 _)]

/-- **A-guard**：m-i 子句的 `q.delta s < S.diagonalLargerBallAccuracy A s → A < 12·3^m` 在 κ 线的
`α = diagonalAccuracy_C11S q.delta` 下的形。 -/
theorem lt_of_accuracyGuard_C11Q6 {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t →
      q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t)
    {s A : ℝ} {m : ℕ} (hA : 0 < A)
    (hguardS : ∀ A : ℝ, 0 < A → q.delta s < S.diagonalLargerBallAccuracy A s →
      A < 12 * (3 : ℝ) ^ m)
    (hguard : q.delta s < diagonalAccuracy_C11S q.delta A s) : A < 12 * (3 : ℝ) ^ m :=
  hguardS A hA (by rwa [diagonalLargerBallAccuracy_eq_C11Q6 S q hq])

/-- level 单调：`cutoffBarrierConst_C11Q3`（`= SingularBarrier.bound (2A + c)`，
`bound D = 76800 + 640D + D²`）
在 `A ≥ 0` 上单调。 -/
theorem cutoffBarrierConst_mono_C11Q6 {A A' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') :
    cutoffBarrierConst_C11Q3 A ≤ cutoffBarrierConst_C11Q3 A' := by
  unfold cutoffBarrierConst_C11Q3 DifferentialGeometry.Analysis.SingularBarrier.bound
  have hc : 0 ≤ 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40 := by
    positivity
  nlinarith

/-! ## 5. 策略 tower -/

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **策略 tower**：`tower_of_blockSteps_pred_C11GT` 同证明，但谓词 `Q j X ℓ req` 看块状态与 lookahead，
所以块请求可依赖 `ℓ.rNext`（= 下一块半径，先于请求选定）。多交 `∀ j, Q j (T.block j) (T.lookahead j)
(T.request j)`。 -/
theorem tower_of_blockSteps_policy_C11Q6 {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (Q : ∀ j (X : BlockState_C11W pBase C P g j), BlockLookahead_C11W X → BlockRequest_C11W →
      Prop)
    (hW0 : ∀ j, ∀ X : BlockState_C11W pBase C P g j, Inv_C11W Cdist cMax Dstar εReserve X →
      ∀ ℓ : BlockLookahead_C11W X, LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ →
        ∃ req : BlockRequest_C11W, RequestReady_C11W X req ∧ Q j X ℓ req)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
      T.block 0 = X₀ ∧ ∀ j, Q j (T.block j) (T.lookahead j) (T.request j) := by
  classical
  let Certified (n : ℕ) :=
    {X : BlockState_C11W pBase C P g n // Inv_C11W Cdist cMax Dstar εReserve X}
  let look (n : ℕ) (X : Certified n) : BlockLookahead_C11W X.1 :=
    Classical.choose (hstep n X.1 X.2)
  have look_spec (n : ℕ) (X : Certified n) :=
    Classical.choose_spec (hstep n X.1 X.2)
  let req (n : ℕ) (X : Certified n) : BlockRequest_C11W :=
    Classical.choose (hW0 n X.1 X.2 (look n X) (look_spec n X).1)
  have req_spec (n : ℕ) (X : Certified n) :
      RequestReady_C11W X.1 (req n X) ∧ Q n X.1 (look n X) (req n X) :=
    Classical.choose_spec (hW0 n X.1 X.2 (look n X) (look_spec n X).1)
  have ext (n : ℕ) (X : Certified n) := (look_spec n X).2 (req n X) (req_spec n X).1
  let next (n : ℕ) (X : Certified n) : Certified (n + 1) :=
    ⟨Classical.choose (ext n X), (Classical.choose_spec (Classical.choose_spec (ext n X))).2⟩
  let acc (n : ℕ) (X : Certified n) : ℝ := Classical.choose (Classical.choose_spec (ext n X))
  have next_spec (n : ℕ) (X : Certified n) :
      PhysicalExtension_C11W X.1 (next n X).1 (look n X) (req n X) (acc n X) :=
    (Classical.choose_spec (Classical.choose_spec (ext n X))).1
  let chain : ∀ n : ℕ, Certified n := fun n => Nat.rec ⟨X₀, hX₀⟩ (fun n X => next n X) n
  exact ⟨{ block := fun n => (chain n).1
           lookahead := fun n => look n (chain n)
           request := fun n => req n (chain n)
           accuracy := fun n => acc n (chain n)
           inv := fun n => (chain n).2
           ready := fun n => ⟨(look_spec n (chain n)).1, (req_spec n (chain n)).1⟩
           extension := fun n => next_spec n (chain n)
           initial_history := hhist
           initial_radius_le := hrad }, rfl, fun n => (req_spec n (chain n)).2⟩

/-! ## 6. consumer -/

/-- **consumer**：retention 的粗 static cap 的 fine realization 在任一被 fine tuple 支配的 K3 请求上成立
（event 层 R1 ∘ mono）。 -/
example {E B Bnext : ℝ} {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext} {d eta εcut Dcut : ℝ} {mcut : ℕ}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut) (i : Fin R.native.eventCount)
    (b : (R.native.toHistory.event i).RetainedBoundaryIndex) (c : ℝ × ℝ × ℝ × ℕ)
    (hR : StandardCap.transitionEnd < c.2.2.1) (hD : c.2.2.1 ≤ Dcut) (hm : c.2.2.2 ≤ mcut)
    (hε : εcut ≤ c.2.1) :
    FineCapRealization_C11Q5
      (translate_presented_static_cap (R.native.coreEvent i) R.shift
        (((W.fineRecords i).restrictModelWindow (W.fineWindows i)
          L.parameters.modelRadius_pos W.full_radius W.full_order W.full_accuracy).static b))
      (k3Request_C11Q6 c).2.1 (k3Request_C11Q6 c).2.2.1 (k3Request_C11Q6 c).1 :=
  (fineCapRealization_of_retention_C11Q6 W i b).mono
    (StandardCap.transitionEnd_pos.trans hR) (hD.trans W.fine_radius) (by
      change StandardCap.transitionEnd < c.2.2.1 + 1
      linarith) (hm.trans W.fine_order) (W.fine_accuracy.trans hε)

end GC.LongTime.Ch11
