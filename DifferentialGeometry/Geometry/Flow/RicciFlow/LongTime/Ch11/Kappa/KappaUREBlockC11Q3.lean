import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaNoEventWindowC11Q3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.UniformRegularEndpointBlock

/-!
# SeedRegularBlock 的 URE 实例（O-CH11-KAPPA2 续窗 G3，后缀 `_C11Q3`）

URE `exists_uniform_regular_endpoint_block_of_half_clock_action`
（`Action/UniformRegularEndpointBlock`，ch12 S-C12X-URE G1 patched-at-path）落树后，
逐种子实例化 `SeedRegularBlock_C11Q2` 的结论体：
* `request` / `hWindow` ⇐
  `exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests`
  （`Action/EventLocalWeightedTemporalSupportPortC11P:748`，`Rbirth := transitionEnd`，
  `c := params.recenterConstant`），固定为函数 `ureRequest_C11Q3`（`Classical.choose`）；
* `qHalf` = K4 的低作用量点（`B(O₁, r/10)`），`actionHalf` 由 `sInf` 取（`𝓛 ≤ (E − 1) r < (E + 1) r =
  factor · r`，`factor(A') = weightedMinLevel_C11Q2 C A`，`A' = max A 1`）；
* 地板 `3/a₀ ↔ Bf`（`scalarFloor_min_C11Q2`）、时钟 `√3 r/2 = √(3/4) r`；
* **node 数据**（每个窗口 event 的 request 形小性：δ / neck / 导数 / presented static caps 精度）是显式
  参数——它正是 R-C11-4 D-2 的 fine-cap 请求（O-CH11-FINECAP 的产物），本组不生产。
常数：`D(A) = factor(A') + e^{9/2} + 4`、`κ(A) = A'⁻¹e⁻⁵⁷/(512·100³)`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology
open ObservedHistory
  (exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests)

namespace GC.LongTime.Ch11

universe u

/-- URE 的 request 函数（EventLocal:748 的 `Classical.choose`；`a₀` = 初始数据的 `windowBarrierA₀_C11Q2`）。 -/
def ureRequest_C11Q3 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (c : ℝ) (Cderiv : ℝ≥0) :
    ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ :=
  if hc : 0 < c then
    Classical.choose
      (exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests.{u}
        (windowBarrierA₀_C11Q2 P₀ g₀) c StandardCap.transitionEnd Cderiv
        (windowBarrierA₀_spec_C11Q2 P₀ g₀).1 hc le_rfl)
  else fun _ _ _ _ _ => (0, 0, 0, 0)

/-- URE block 的作用量常数 `D(A) = factor(max A 1) + e^{9/2} + 4`。 -/
def ureBlockD_C11Q3 (A : ℝ) : ℝ :=
  GC.GeneralFlow.preparedSpatialPhysicalActionFactor (max A 1) + Real.exp (9 / 2) + 4

/-- URE block 的体积常数 `κ(A) = (max A 1)⁻¹ e⁻⁵⁷/(512·100³)`。 -/
def ureBlockKappa_C11Q3 (A : ℝ) : ℝ :=
  (max A 1)⁻¹ * Real.exp (-57) / (512 * (100 : ℝ) ^ 3)

theorem ureBlockKappa_pos_C11Q3 (A : ℝ) : 0 < ureBlockKappa_C11Q3 A := by
  have h : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  unfold ureBlockKappa_C11Q3
  positivity

theorem sqrt_three_quarters_mul_C11Q3 (r : ℝ) :
    Real.sqrt (3 / 4) * r = Real.sqrt 3 * r / 2 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_div (by norm_num) 4, h4]
  ring

/-- **SeedRegularBlock 的 URE 实例（逐种子）**：K4 点 `q₁ ∈ B(O₁, r/10)`（`l ≤ C₄(A)`，
`C₄ = weightedMinLengthConst_C11Q2 (cutoffBarrierConst_C11Q3 ∘ max · 1)`）+ URE 的 node 数据 ⇒ 时钟
`√(3/4)·r` 切片上开集 `U`，`vol U ≥ κ(A) w³`，每点非 barely admissible 极小端点且 `l ≤ D(A)`
（即 `SeedRegularBlock_C11Q2` 在该种子处的结论体）。 -/
theorem seedRegularBlock_at_of_URE_C11Q3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (R : RetainedCoreHistory.{u}) (identification : InitialIdentification P g R.toHistory)
    (params : CutoffParameters) (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf) (Cderiv : ℝ≥0)
    (t : Icc (0 : ℝ) R.toHistory.horizon) (p x : (R.toHistory.stageAt t).Carrier) {r A : ℝ}
    (hA : 0 < A) (hT : 2 * r ^ 2 < (t : ℝ))
    (hseed : hasSmallParabolicCurvature R.toHistory t p r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (R.toHistory.stageMetric (R.toHistory.activeStage t) t) p r)
    {b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) (hb : (b : ℝ) = (t : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (s₁ : Icc (0 : ℝ) R.toHistory.horizon) (hbs₁ : b ≤ s₁) (hs₁t : s₁ ≤ t)
    (hs₁ : (s₁ : ℝ) = (t : ℝ) - r ^ 2 / 2)
    (q₁ : (R.toHistory.stageAt s₁).Carrier)
    (hq₁ : q₁ ∈ riemannianBallOf (R.toHistory.stageMetric (R.toHistory.activeStage s₁) s₁)
      (seedTrace.point (R.toHistory.activeStage s₁) (R.toHistory.activeStage_mono hbs₁)
        (R.toHistory.activeStage_mono hs₁t)) (r / 10))
    (hlow : IsLowActionEndpoint_C11Q R Bf t s₁ x
      (weightedMinLengthConst_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A) q₁) :
    ∀ (a : Icc (0 : ℝ) R.toHistory.horizon), a = projIcc 0 R.toHistory.horizon
      R.toHistory.horizon_nonneg ((t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2) →
    ∀ (_has : b ≤ a) (_hat : a ≤ t),
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin R.toHistory.eventCount → ℝ),
      (∀ (i : Fin R.toHistory.eventCount) (_hf : R.toHistory.activeStage a ≤ i.castSucc)
        (_hl : i.succ ≤ R.toHistory.activeStage t),
        let req := ureRequest_C11Q3 P g params.recenterConstant Cderiv
          (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧
        Real.sqrt 3 * r / 2 ≤ nodeE i ∧
        R.toHistory.isParabolicallyRmControlledBall t x (nodeR i) ∧
        params.delta (R.toHistory.time i.succ) ≤ req.2.2.2 ∧
        params.neckRadius (R.toHistory.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin R.toHistory.eventCount, i.succ ≤ j.castSucc →
          j.succ ≤ R.toHistory.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (R.toHistory.eventCount + 1), i.succ ≤ j → j ≤ R.toHistory.activeStage t →
          ∀ y : (R.toHistory.stage j).Carrier,
          ∀ s ∈ Ioo (R.toHistory.time j) (R.toHistory.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (R.toHistory.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (R.toHistory.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (R.toHistory.stageMetric j s) y ^ 2) ∧
        (∀ b : (R.toHistory.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (R.toHistory.event i).PresentedStaticCap params.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin R.toHistory.eventCount), R.toHistory.activeStage a ≤ i.castSucc →
        i.succ ≤ R.toHistory.activeStage t →
        ureBlockD_C11Q3 A * r ≤ nodeA i) →
      ∃ U : Set
          (R.stage (R.toHistory.activeStage (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))).Carrier,
        IsOpen U ∧
        ENNReal.ofReal (ureBlockKappa_C11Q3 A * (Real.sqrt (3 / 4) * r) ^ 3) ≤
          riemannianVolumeMeasure ThreeModel
            (R.stage (R.toHistory.activeStage
              (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))).Carrier
            (R.toHistory.stageMetric
              (R.toHistory.activeStage (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))
              ((t : ℝ) - (Real.sqrt (3 / 4) * r) ^ 2)) U ∧
        ∀ y ∈ U,
          IsLowActionEndpoint_C11Q R Bf t (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)) x
            (ureBlockD_C11Q3 A) y := by
  intro a ha has hat nodeA nodeE nodeR nodeQ nodeRho hdata hbud
  subst ha
  have hr : 0 < r := hseed.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hA' : 1 ≤ max A 1 := le_max_right _ _
  have hA'pos : 0 < max A 1 := lt_of_lt_of_le one_pos hA'
  obtain ⟨ha₀, hinit, -⟩ := windowBarrierA₀_spec_C11Q2 P g
  set a₀ := windowBarrierA₀_C11Q2 P g with ha₀def
  have hstart := hinit R.toHistory identification
  have hfloor := scalarFloor_min_C11Q2 R ha₀ hBf records hstart.1 hstart.2
  have hc : 0 < params.recenterConstant :=
    lt_of_lt_of_le (by norm_num) params.recenterConstant_ge_four
  have hspec := Classical.choose_spec
    (exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests.{u}
      a₀ params.recenterConstant StandardCap.transitionEnd Cderiv ha₀ hc le_rfl)
  have hreq : ureRequest_C11Q3 P g params.recenterConstant Cderiv = Classical.choose
      (exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests.{u}
        a₀ params.recenterConstant StandardCap.transitionEnd Cderiv ha₀ hc le_rfl) := by
    unfold ureRequest_C11Q3
    rw [dite_eq_left hc]
  rw [← hreq] at hspec
  -- 种子体积对 `A' = max A 1`
  have hvol' : ENNReal.ofReal ((max A 1)⁻¹ * r ^ 3) ≤
      ballVolume (R.toHistory.stageMetric (R.toHistory.activeStage t) t) p r := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvol
    have hinv : (max A 1)⁻¹ ≤ A⁻¹ := inv_anti₀ hA (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right hinv (by positivity)
  -- 半时钟的 actionHalf
  have hv₁ : Real.sqrt ((t : ℝ) - s₁) = r / Real.sqrt 2 := by
    rw [hs₁, show (t : ℝ) - ((t : ℝ) - r ^ 2 / 2) = (r / Real.sqrt 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; ring]
    exact Real.sqrt_sq (div_pos hr hs2).le
  obtain ⟨⟨hle₁, -⟩, hcost₁⟩ := hlow
  unfold sliceCost_C11Q at hcost₁
  rw [dite_eq_left hle₁, hv₁] at hcost₁
  rw [ObservedHistory.regularizedCost_eq_of_scalar_lower_bound_le hfloor _ _ hle₁ _
    (min_le_left Bf (3 / a₀)) (min_le_right Bf (3 / a₀))] at hcost₁
  set E : ℝ := Real.exp (cutoffBarrierConst_C11Q3 (max A 1) / 2 + 32 / Real.sqrt 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hconst : 2 * weightedMinLengthConst_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A *
      (r / Real.sqrt 2) = (E - 1) * r := by
    rw [weightedMinLengthConst_C11Q2, ← hE]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    ring
  rw [hconst] at hcost₁
  have hfactor : GC.GeneralFlow.preparedSpatialPhysicalActionFactor (max A 1) = E + 1 := rfl
  have hlt : R.toHistory.regularizedCost (R.toHistory.activeStage s₁) (R.toHistory.activeStage t)
      hle₁ t (3 / a₀) 0
      (r / Real.sqrt 2) x q₁ <
        ((GC.GeneralFlow.preparedSpatialPhysicalActionFactor (max A 1) * r : ℝ) : WithTop ℝ) :=
    lt_of_le_of_lt hcost₁ (WithTop.coe_lt_coe.mpr (by rw [hfactor]; nlinarith))
  obtain ⟨actionHalf, hActionHalf, hBudget⟩ : ∃ actionHalf : ℝ,
      (actionHalf : WithTop ℝ) ∈ R.toHistory.regularizedActionValues (R.toHistory.activeStage s₁)
        (R.toHistory.activeStage t)
        (R.toHistory.activeStage_mono hs₁t) t (3 / a₀) 0 (r / Real.sqrt 2) x q₁ ∧
      actionHalf < GC.GeneralFlow.preparedSpatialPhysicalActionFactor (max A 1) * r := by
    by_cases hne : (R.toHistory.regularizedActionValues (R.toHistory.activeStage s₁)
        (R.toHistory.activeStage t) hle₁ t
        (3 / a₀) 0 (r / Real.sqrt 2) x q₁).Nonempty
    · obtain ⟨val, hval, hvlt⟩ := exists_lt_of_csInf_lt hne hlt
      have hvtop : val ≠ ⊤ := ne_top_of_lt hvlt
      obtain ⟨act, hact⟩ := WithTop.ne_top_iff_exists.mp hvtop
      rw [← hact] at hval hvlt
      exact ⟨act, hval, WithTop.coe_lt_coe.mp hvlt⟩
    · exfalso
      rw [ObservedHistory.regularizedCost_eq_top_of_no_competitor _ _ _ _ _ _ _ _ _ _
        (Set.not_nonempty_iff_eq_empty.mp hne)] at hlt
      exact not_top_lt hlt
  have hURE := ObservedHistory.exists_uniform_regular_endpoint_block_of_half_clock_action
    a₀ params.recenterConstant StandardCap.transitionEnd Cderiv ha₀ le_rfl
    (ureRequest_C11Q3 P g params.recenterConstant Cderiv) hspec.2.1 R.toHistory params records
    le_rfl hstart.1 hstart.2 t p x r (max A 1) hA' hT hseed hvol' b hbt hb seedTrace s₁ hbs₁
    hs₁t hs₁ q₁ hq₁ actionHalf hActionHalf hBudget has hat nodeA nodeE nodeR nodeQ nodeRho
    hdata hbud
  obtain ⟨U, -, hUopen, -, -, hv, hvt, -, hvolU, hU⟩ := hURE
  have hw : Real.sqrt (3 / 4) * r = Real.sqrt 3 * r / 2 := sqrt_three_quarters_mul_C11Q3 r
  rw [hw]
  have hsv : Real.sqrt ((t : ℝ) - (clockSlice_C11Q R t (Real.sqrt 3 * r / 2) : ℝ)) =
      Real.sqrt 3 * r / 2 := by
    rw [clockSlice_val_C11Q R t (by linarith),
      show (t : ℝ) - ((t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2) = (Real.sqrt 3 * r / 2) ^ 2 by ring,
      Real.sqrt_sq hv.le]
  refine ⟨U, hUopen, hvolU, ?_⟩
  intro y hy
  obtain ⟨hyE, hyc⟩ := hU y hy
  have hle : R.toHistory.activeStage (clockSlice_C11Q R t (Real.sqrt 3 * r / 2)) ≤
      R.toHistory.activeStage t := R.toHistory.activeStage_mono hat
  refine ⟨⟨hle, ?_⟩, ?_⟩
  · rw [hsv, ObservedHistory.regularMinimizerEndpoints_eq_of_scalar_lower_bound_le hfloor _ _ hle
      _ (min_le_left Bf (3 / a₀)) (min_le_right Bf (3 / a₀))]
    exact hyE
  · unfold sliceCost_C11Q
    rw [dite_eq_left hle, hsv, ObservedHistory.regularizedCost_eq_of_scalar_lower_bound_le hfloor
      _ _ hle _ (min_le_left Bf (3 / a₀)) (min_le_right Bf (3 / a₀))]
    exact hyc

/-- **consumer（G3）**：URE 实例的结论体 ⇒ 该种子处 `Ṽ(√(3/4)·r) ≥ κ(A) e^{−D(A)} (4π)^{−3/2}`
（K5 体积解释 `redVolume_ge_of_lowActionPatch_C11Q`，与 `seedReducedVolumeLower_of_block_C11Q2` 同一消费）。 -/
example (R : RetainedCoreHistory.{u}) {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf)
    (t : Icc (0 : ℝ) R.toHistory.horizon) (x : (R.toHistory.stageAt t).Carrier) {r A : ℝ}
    (hr : 0 < r) (hT : 2 * r ^ 2 < (t : ℝ))
    (U : Set (R.stage (R.toHistory.activeStage
      (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))).Carrier)
    (hUopen : IsOpen U)
    (hvolU : ENNReal.ofReal (ureBlockKappa_C11Q3 A * (Real.sqrt (3 / 4) * r) ^ 3) ≤
      riemannianVolumeMeasure ThreeModel
        (R.stage (R.toHistory.activeStage (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))).Carrier
        (R.toHistory.stageMetric
          (R.toHistory.activeStage (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))
          ((t : ℝ) - (Real.sqrt (3 / 4) * r) ^ 2)) U)
    (hlow : ∀ y ∈ U, IsLowActionEndpoint_C11Q R Bf t
      (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)) x (ureBlockD_C11Q3 A) y) :
    ENNReal.ofReal (ureBlockKappa_C11Q3 A * Real.exp (-ureBlockD_C11Q3 A) *
        (4 * Real.pi) ^ (-(3 / 2 : ℝ))) ≤
      R.reducedVolume (R.toHistory.activeStage t) x t (Real.sqrt (3 / 4) * r) := by
  have hw : 0 < (Real.sqrt (3 / 4) * r) := mul_pos (Real.sqrt_pos.2 (by norm_num)) hr
  have hw2 : (Real.sqrt (3 / 4) * r) ^ 2 = 3 / 4 * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have ht0 : (0 : ℝ) ≤ (t : ℝ) - (Real.sqrt (3 / 4) * r) ^ 2 := by rw [hw2]; nlinarith
  have hsval := clockSlice_val_C11Q R t ht0
  have hst : clockSlice_C11Q R t (Real.sqrt (3 / 4) * r) ≤ t := by
    change (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r) : ℝ) ≤ (t : ℝ)
    rw [hsval]
    nlinarith [sq_nonneg (Real.sqrt (3 / 4) * r)]
  have hsq : Real.sqrt ((t : ℝ) - (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r) : ℝ)) =
      Real.sqrt (3 / 4) * r := by
    rw [hsval, show (t : ℝ) - ((t : ℝ) - (Real.sqrt (3 / 4) * r) ^ 2) =
      (Real.sqrt (3 / 4) * r) ^ 2 by ring, Real.sqrt_sq hw.le]
  refine redVolume_ge_of_lowActionPatch_C11Q R hBf t x hw (R.toHistory.activeStage_mono hst) U
    hUopen hvolU ?_
  intro q hq
  obtain ⟨⟨hle', hmem⟩, hcost⟩ := hlow q hq
  unfold sliceCost_C11Q at hcost
  rw [dite_eq_left (R.toHistory.activeStage_mono hst)] at hcost
  rw [hsq] at hmem hcost
  exact ⟨hmem, hcost⟩

end GC.LongTime.Ch11
