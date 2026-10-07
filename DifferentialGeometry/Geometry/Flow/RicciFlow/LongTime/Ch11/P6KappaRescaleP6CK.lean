import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeSmallP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841DefsC11K

/-!
# 原尺度 κ 投影 ⇒ 重标度 `hvolK`（O-CH11-P6CGK G2a，后缀 `_P6CK`）

联合主形（G2c）的 κ 槽是 `d` 的消费投影 `∃ κd > 0, hvolK`，写在**重标度** history `Kh n =
(Ho n).rescale_P6N (c n)` 上。本文件把**原尺度**投影（`Pre841Data_C11K.volume_ge` 形，于
`(Ho n).toHistory`、时刻 `σo n = unscaleTime_P6X (σ n)`、基点 `yo n = uncastRescale_P6CK (y n)`、
尺度 `Ro n = R n / c n`）搬到重标度：`volume_ge` 是尺度不变的（`scaleMetric R̃ g̃ = scaleMetric Ro g`，
`R̃ = c·Ro`），但测试球的 trace / 受控球 / 体积要逐项搬运。全部用树内（P6SEL G4 `P6NormalizeP6X`、
P6SEL3 G4 `P6NormalizeSmallP6X3`）引理独立证明，不 import 未登记文件：
* `uncastRescale_P6CK`（重标度点 → 原点）；`ball_of_castRescale_P6CK`（球，反向）；
* `traceOfRescaleAt_P6CK`（重标度 trace → 原 trace，端点 `rescaleTime`）；
* `isRmControlled_of_rescale_P6CK`：`isRmControlled_rescale_P6X3` 的反向（半径 `b ↦ b√c`）；
* `ctrl_of_rescale_P6CK`：重标度受控球（`b`）⇒ 原受控球（`b√c`）；
* `le_ballVolume_scale_castRescale_P6CK`：`scaleMetric (c Ro) g̃` 与 `scaleMetric Ro g` 的体积下界等价；
* **`volume_rescale_P6CK`**（单个 history）/ **`hvolK_of_orig_P6CK`**（序列）/ `hvolK_of_pre841_orig_P6CK`
  （原尺度 `Pre841Data_C11K` ⇒ 重标度 `hvolK`，`κd = d.kappa`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- `scaleMetric (c Ro) (scaleMetric c⁻¹ g) = scaleMetric Ro g`。 -/
theorem scaleMetric_mul_inv_P6CK {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] (g : SmoothRiemannianMetric ThreeModel X)
    {c Ro : ℝ} (hc : 0 < c) (hRo : 0 < Ro) (hR : 0 < c * Ro) :
    scaleMetric (c * Ro) hR (scaleMetric c⁻¹ (inv_pos.mpr hc) g) = scaleMetric Ro hRo g := by
  ext x a b
  simp only [scaleMetric_inner]
  rw [show c * Ro * (c⁻¹ * g.inner x a b) = (c * c⁻¹) * (Ro * g.inner x a b) by ring,
    mul_inv_cancel₀ hc.ne', one_mul]

/-- trace 点沿指标相等 `HEq`。 -/
theorem point_heq_P6CK {Hh : ObservedHistory.{u}} {f l : Fin (Hh.eventCount + 1)} {hle : f ≤ l}
    {x : (Hh.stage l).Carrier} (A : BackwardPointTrace Hh f l hle x)
    {j j' : Fin (Hh.eventCount + 1)}
    (hj : j = j') (h1 : f ≤ j) (h2 : j ≤ l) (h1' : f ≤ j') (h2' : j' ≤ l) :
    HEq (A.point j h1 h2) (A.point j' h1' h2') := by
  subst hj
  rfl

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- 重标度 stage 点 → 原 stage 点（同一 carrier，沿 `activeStage_unscale_P6X` cast）。 -/
def uncastRescale_P6CK (v : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon)
    (z : ((K.rescale_P6N c hc).toHistory.stageAt v).Carrier) :
    (K.toHistory.stageAt (K.unscaleTime_P6X hc v)).Carrier :=
  cast (congrArg (fun j => (K.stage j).Carrier) (K.activeStage_unscale_P6X hc v)) z

theorem heq_uncastRescale_P6CK (v : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon)
    (z : ((K.rescale_P6N c hc).toHistory.stageAt v).Carrier) :
    HEq (K.uncastRescale_P6CK hc v z) z :=
  cast_heq _ _

/-- `castRescale_P6X` 满。 -/
theorem castRescale_surj_P6CK (v : Icc (0 : ℝ) K.toHistory.horizon)
    (xS : ((K.rescale_P6N c hc).toHistory.stageAt (K.rescaleTime_P6X hc v)).Carrier) :
    ∃ x, K.castRescale_P6X hc v x = xS :=
  ⟨cast (congrArg (fun j => (K.stage j).Carrier) (K.activeStage_rescaleTime_P6X hc v)) xS, by
    unfold castRescale_P6X
    exact (cast_cast _ _ _).trans (cast_eq _ _)⟩

/-- 球（反向）：`x̃ ∈ B̃(p̃, ρ/√c)` ⇒ `x ∈ B(p, ρ)`。 -/
theorem ball_of_castRescale_P6CK (v : Icc (0 : ℝ) K.toHistory.horizon)
    (p x : (K.toHistory.stageAt v).Carrier) {ρ : ℝ}
    (hx : K.castRescale_P6X hc v x ∈ riemannianBallOf ((K.rescale_P6N c hc).toHistory.stageMetric
        ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
        (K.rescaleTime_P6X hc v)) (K.castRescale_P6X hc v p) (ρ / Real.sqrt c)) :
    x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v) p ρ := by
  have h1 : riemannianEDistOf ((K.rescale_P6N c hc).toHistory.stageMetric
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
      (K.rescaleTime_P6X hc v)) (K.castRescale_P6X hc v p) (K.castRescale_P6X hc v x) <
      ENNReal.ofReal (ρ / Real.sqrt c) := hx
  rw [K.edist_castRescale_P6X hc v p x] at h1
  change riemannianEDistOf _ p x < ENNReal.ofReal ρ
  have hs : 0 < Real.sqrt c⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hc)
  have heq : ENNReal.ofReal (ρ / Real.sqrt c) =
      ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal ρ := by
    rw [← ENNReal.ofReal_mul hs.le, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
  rw [heq] at h1
  by_contra hn
  exact absurd h1 (not_lt.mpr (mul_le_mul' le_rfl (not_lt.mp hn)))

/-- 重标度 trace（端点 `rescaleTime a ≤ rescaleTime t`、点 `castRescale t x`）→ 原 trace。 -/
def traceOfRescaleAt_P6CK {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    {x : (K.toHistory.stageAt t).Carrier}
    (B : BackwardPointTrace (K.rescale_P6N c hc).toHistory
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a))
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t))
      ((K.rescale_P6N c hc).toHistory.activeStage_mono (K.rescaleTime_mono_P6X hc hat))
      (K.castRescale_P6X hc t x)) :
    BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) x :=
  trace_transfer_P6X (Hh := K.toHistory) (K.activeStage_rescaleTime_P6X hc a)
    (K.activeStage_rescaleTime_P6X hc t) (K.heq_castRescale_P6X hc t x)
    (K.traceOfRescale_P6N c hc B)

/-- `traceOfRescaleAt_P6CK` 不改点。 -/
theorem traceOfRescaleAt_point_P6CK {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    {x : (K.toHistory.stageAt t).Carrier}
    (B : BackwardPointTrace (K.rescale_P6N c hc).toHistory
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a))
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t))
      ((K.rescale_P6N c hc).toHistory.activeStage_mono (K.rescaleTime_mono_P6X hc hat))
      (K.castRescale_P6X hc t x))
    (j : Fin (K.eventCount + 1)) (h1 : K.toHistory.activeStage a ≤ j)
    (h2 : j ≤ K.toHistory.activeStage t)
    (h1' : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a) ≤ j)
    (h2' : j ≤ (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t)) :
    (K.traceOfRescaleAt_P6CK hc hat B).point j h1 h2 = B.point j h1' h2' :=
  trace_transfer_point_P6X3 (Hh := K.toHistory) (K.activeStage_rescaleTime_P6X hc a)
    (K.activeStage_rescaleTime_P6X hc t) (K.heq_castRescale_P6X hc t x)
    (K.traceOfRescale_P6N c hc B) j h1 h2

/-- **`isRmControlled` 反向重标度**（`isRmControlled_rescale_P6X3` 的逆向）：重标度 trace 半径 `b`
受控 ⇒ 原 trace 半径 `b √c` 受控（slab 项 `weighted_stage_rescale_P6X3`，crossing 项终端式）。 -/
theorem isRmControlled_of_rescale_P6CK {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    {x : (K.toHistory.stageAt t).Carrier}
    (B : BackwardPointTrace (K.rescale_P6N c hc).toHistory
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a))
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t))
      ((K.rescale_P6N c hc).toHistory.activeStage_mono (K.rescaleTime_mono_P6X hc hat))
      (K.castRescale_P6X hc t x)) {b : ℝ}
    (hB : B.isRmControlled (hat := K.rescaleTime_mono_P6X hc hat) b) :
    (K.traceOfRescaleAt_P6CK hc hat B).isRmControlled (hat := hat) (b * Real.sqrt c) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hb : b * Real.sqrt c / Real.sqrt c = b := mul_div_cancel_right₀ b hs.ne'
  have ha := K.activeStage_rescaleTime_P6X hc a
  have ht := K.activeStage_rescaleTime_P6X hc t
  refine ⟨fun s hs1 hs2 => ?_, fun i hf hl => ?_⟩
  · have hs1' : K.rescaleTime_P6X hc a ≤ K.rescaleTime_P6X hc s := K.rescaleTime_mono_P6X hc hs1
    have hs2' : K.rescaleTime_P6X hc s ≤ K.rescaleTime_P6X hc t := K.rescaleTime_mono_P6X hc hs2
    have h1' : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a) ≤
        K.toHistory.activeStage s := ha.le.trans (K.toHistory.activeStage_mono hs1)
    have h2' : K.toHistory.activeStage s ≤
        (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t) :=
      (K.toHistory.activeStage_mono hs2).trans ht.ge
    have key : ∀ (j : Fin (K.eventCount + 1))
        (_ : j = (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc s))
        (h1 : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a) ≤ j)
        (h2 : j ≤ (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t)),
        b ^ 4 * normSq0S ((K.rescale_P6N c hc).toHistory.stageMetric j (K.rescaleTime_P6X hc s))
            (B.point j h1 h2) 4
            (metricRm04At ((K.rescale_P6N c hc).toHistory.stageMetric j
              (K.rescaleTime_P6X hc s)) (B.point j h1 h2)) ≤ 1 := by
      intro j hj h1 h2
      subst hj
      exact hB.1 _ hs1' hs2'
    have e := K.weighted_stage_rescale_P6X3 hc (K.toHistory.activeStage s)
      (K.rescaleTime_P6X hc s) (b * Real.sqrt c) (B.point (K.toHistory.activeStage s) h1' h2')
    rw [K.mul_rescaleTime_P6X hc s] at e
    rw [K.traceOfRescaleAt_point_P6CK hc hat B _ _ _ h1' h2', ← e, hb]
    exact key _ (K.activeStage_rescaleTime_P6X hc s).symm h1' h2'
  · have hf' : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a) ≤
        i.castSucc := ha.le.trans hf
    have hl' : i.succ ≤ (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t) :=
      hl.trans ht.ge
    intro xO
    have hx : HEq (⟨B.point i.castSucc hf' (i.castSucc_lt_succ.le.trans hl'),
        (B.crossing i hf' hl').mem_terminalRegularRegion
          ((K.rescale_P6N c hc).toHistory.event i)⟩ :
          ((K.toHistory.event i).incoming.rescale c hc).terminalRegularOpen) xO :=
      heq_of_opens_val_P6X3 ((K.toHistory.event i).incoming.rescale_terminalRegularOpen c hc)
        _ _ (K.traceOfRescaleAt_point_P6CK hc hat B _ _ _ hf'
          (i.castSucc_lt_succ.le.trans hl')).symm
    rw [← terminal_weighted_rm_sq_rescale_P6X3 (K.toHistory.event i).terminal c hc
      (b * Real.sqrt c) _ xO hx, hb]
    exact hB.2 i hf' hl'

/-- **受控球反向重标度**：重标度 history 在 `(t/c, p̃)` 半径 `b` 受控 ⇒ 原 history 在 `(t, p)` 半径
`b √c` 受控。 -/
theorem ctrl_of_rescale_P6CK (v : Icc (0 : ℝ) K.toHistory.horizon)
    (z : (K.toHistory.stageAt v).Carrier) {b : ℝ}
    (h : (K.rescale_P6N c hc).toHistory.isParabolicallyRmControlledBall (K.rescaleTime_P6X hc v)
      (K.castRescale_P6X hc v z) b) :
    K.toHistory.isParabolicallyRmControlledBall v z (b * Real.sqrt c) := by
  obtain ⟨hb, a', hat', ha', htr⟩ := h
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  obtain ⟨a, rfl⟩ : ∃ a, K.rescaleTime_P6X hc a = a' :=
    ⟨K.unscaleTime_P6X hc a', K.rescale_unscaleTime_P6X hc a'⟩
  have hat : a ≤ v := (div_le_div_iff_of_pos_right hc).mp
    (show (a : ℝ) / c ≤ (v : ℝ) / c from hat')
  refine ⟨mul_pos hb hs, a, hat, ?_, fun x hx => ?_⟩
  · have ha'' : (a : ℝ) / c = (v : ℝ) / c - b ^ 2 := ha'
    rw [div_eq_iff hc.ne'] at ha''
    rw [ha'', sub_mul, div_mul_cancel₀ _ hc.ne', mul_pow, Real.sq_sqrt hc.le]
  · have hx' : K.castRescale_P6X hc v x ∈ riemannianBallOf
        ((K.rescale_P6N c hc).toHistory.stageMetric
          ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
          (K.rescaleTime_P6X hc v)) (K.castRescale_P6X hc v z) b := by
      have h := K.ball_castRescale_P6X hc v z x hx
      rwa [mul_div_cancel_right₀ _ hs.ne'] at h
    obtain ⟨B, hB⟩ := htr _ hx'
    exact ⟨K.traceOfRescaleAt_P6CK hc hat B, K.isRmControlled_of_rescale_P6CK hc hat B hB⟩

/-- 体积下界：`scaleMetric (c Ro)` 于重标度 stage 度量（`(t/c, p̃)`）⇔ `scaleMetric Ro` 于原 stage 度量。 -/
theorem le_ballVolume_scale_castRescale_P6CK {K : RetainedCoreHistory.{u}} {c : ℝ} (hc : 0 < c)
    {v : Icc (0 : ℝ) K.toHistory.horizon}
    {z : (K.toHistory.stageAt v).Carrier} {Ro : ℝ} (hRo : 0 < Ro) (hR : 0 < c * Ro)
    {κ ϱ : ℝ} :
    ENNReal.ofReal (κ * ϱ ^ 3) ≤ ballVolume (scaleMetric (c * Ro) hR
        ((K.rescale_P6N c hc).toHistory.stageMetric
          ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
          (K.rescaleTime_P6X hc v))) (K.castRescale_P6X hc v z) ϱ ↔
      ENNReal.ofReal (κ * ϱ ^ 3) ≤ ballVolume (scaleMetric Ro hRo
        (K.toHistory.stageMetric (K.toHistory.activeStage v) v)) z ϱ := by
  have hmetric := (K.rescale_P6N_stageMetric c hc
    ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
    (K.rescaleTime_P6X hc v)).trans
    (congrArg (fun t => scaleMetric c⁻¹ (inv_pos.mpr hc)
      (K.toHistory.stageMetric
        ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v)) t))
      (K.mul_rescaleTime_P6X hc v))
  have hmetric' : scaleMetric (c * Ro) hR ((K.rescale_P6N c hc).toHistory.stageMetric
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
      (K.rescaleTime_P6X hc v)) = scaleMetric Ro hRo (K.toHistory.stageMetric
        ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v)) v) := by
    rw [hmetric]
    exact scaleMetric_mul_inv_P6CK _ hc hRo hR
  rw [hmetric']
  exact carrier_transfer_P6X (S := K.stage)
    (Pr := fun j w => ENNReal.ofReal (κ * ϱ ^ 3) ≤
      ballVolume (scaleMetric Ro hRo (K.toHistory.stageMetric j v)) w ϱ)
    (K.activeStage_rescaleTime_P6X hc v) (K.heq_castRescale_P6X hc v z)

/-- **原尺度 volume_ge 形 ⇒ 重标度 volume_ge 形（单个 history，固定 `D L B`）**：原 history 于
`(t, p, Ro)` 的 (K-seq) 测试 ⇒ 重标度 history 于 `(s, y, R)`（`s = t/c`、`y = p̃`、`R = c Ro`）的同一测试，
`κ` 原样（尺度不变）。 -/
theorem volume_rescale_P6CK (t : Icc (0 : ℝ) K.toHistory.horizon)
    (p : (K.toHistory.stageAt t).Carrier) {Ro : ℝ} (hRo : 0 < Ro) {κ D L B : ℝ}
    (hO : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p
        (D / Real.sqrt Ro),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ t), (t : ℝ) - B / Ro ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage t) (K.toHistory.activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt))
          (ϱ / Real.sqrt Ro) →
        ENNReal.ofReal (κ * ϱ ^ 3) ≤
          ballVolume (scaleMetric Ro hRo (K.toHistory.stageMetric (K.toHistory.activeStage v) v))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) ϱ)
    (s : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon)
    (y : ((K.rescale_P6N c hc).toHistory.stageAt s).Carrier) {R : ℝ} (hR : 0 < R)
    (hs : K.rescaleTime_P6X hc t = s) (hy : HEq (K.castRescale_P6X hc t p) y)
    (hRR : c * Ro = R) :
    ∀ x ∈ riemannianBallOf ((K.rescale_P6N c hc).toHistory.stageMetric
        ((K.rescale_P6N c hc).toHistory.activeStage s) s) y (D / Real.sqrt R),
    ∀ (v : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon) (hvt : v ≤ s), (s : ℝ) - B / R ≤ v →
    ∀ tr : BackwardPointTrace (K.rescale_P6N c hc).toHistory
      ((K.rescale_P6N c hc).toHistory.activeStage v) ((K.rescale_P6N c hc).toHistory.activeStage s)
      ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt) x,
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
      (K.rescale_P6N c hc).toHistory.isParabolicallyRmControlledBall v
        (tr.point ((K.rescale_P6N c hc).toHistory.activeStage v) le_rfl
          ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt)) (ϱ / Real.sqrt R) →
      ENNReal.ofReal (κ * ϱ ^ 3) ≤
        ballVolume (scaleMetric R hR ((K.rescale_P6N c hc).toHistory.stageMetric
          ((K.rescale_P6N c hc).toHistory.activeStage v) v))
          (tr.point ((K.rescale_P6N c hc).toHistory.activeStage v) le_rfl
            ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt)) ϱ := by
  subst hs hRR
  obtain rfl := eq_of_heq hy
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsR : Real.sqrt (c * Ro) = Real.sqrt c * Real.sqrt Ro := Real.sqrt_mul hc.le Ro
  intro x' hx' v' hvt' hv' tr ϱ hϱ hϱL hball
  obtain ⟨x, rfl⟩ := K.castRescale_surj_P6CK hc t x'
  obtain ⟨v, rfl⟩ : ∃ v, K.rescaleTime_P6X hc v = v' :=
    ⟨K.unscaleTime_P6X hc v', K.rescale_unscaleTime_P6X hc v'⟩
  have hvt : v ≤ t := (div_le_div_iff_of_pos_right hc).mp
    (show (v : ℝ) / c ≤ (t : ℝ) / c from hvt')
  have hv : (t : ℝ) - B / Ro ≤ v := by
    have h : (t : ℝ) / c - B / (c * Ro) ≤ (v : ℝ) / c := hv'
    have e : B / (c * Ro) = B / Ro / c := by rw [div_div, mul_comm]
    rw [e, ← sub_div] at h
    exact (div_le_div_iff_of_pos_right hc).mp h
  have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p
      (D / Real.sqrt Ro) := by
    refine K.ball_of_castRescale_P6CK hc t p x ?_
    have e : D / Real.sqrt Ro / Real.sqrt c = D / Real.sqrt (c * Ro) := by
      rw [hsR, div_div, mul_comm]
    rw [e]
    exact hx'
  have h1' : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v) ≤
      K.toHistory.activeStage v := (K.activeStage_rescaleTime_P6X hc v).le
  have h2' : K.toHistory.activeStage v ≤
      (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t) :=
    (K.toHistory.activeStage_mono hvt).trans (K.activeStage_rescaleTime_P6X hc t).ge
  have hpt : tr.point ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v)) le_rfl
      ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt') =
      K.castRescale_P6X hc v ((K.traceOfRescaleAt_P6CK hc hvt tr).point
        (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) := by
    have h1 : HEq ((K.traceOfRescaleAt_P6CK hc hvt tr).point (K.toHistory.activeStage v) le_rfl
        (K.toHistory.activeStage_mono hvt))
        (tr.point ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v)) le_rfl
          ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt')) := by
      rw [K.traceOfRescaleAt_point_P6CK hc hvt tr _ _ _ h1' h2']
      exact point_heq_P6CK tr (K.activeStage_rescaleTime_P6X hc v).symm _ _ _ _
    exact eq_of_heq (h1.symm.trans (K.heq_castRescale_P6X hc v _).symm)
  rw [hpt] at hball ⊢
  have hctrl := K.ctrl_of_rescale_P6CK hc v _ hball
  have e : ϱ / Real.sqrt (c * Ro) * Real.sqrt c = ϱ / Real.sqrt Ro := by
    rw [hsR]
    field_simp
  rw [e] at hctrl
  exact (le_ballVolume_scale_castRescale_P6CK hc hRo hR).mpr
    (hO x hx v hvt hv (K.traceOfRescaleAt_P6CK hc hvt tr) ϱ hϱ hϱL hctrl)

end RetainedCoreHistory

/-- **原尺度 κ 投影 ⇒ 重标度 `hvolK`（序列）**：`Ho n` 的原尺度 (K-seq) 测试（于
`σo n = unscaleTime_P6X (σ n)`、`yo n = uncastRescale_P6CK (y n)`、`Ro n = R n / c n`）⇒ 重标度
`Kh n = (Ho n).rescale_P6N (c n)` 于 `(σ, y, R)` 的 `hvolK`（联合主形 κ 槽），`κ` 原样。 -/
theorem hvolK_of_orig_P6CK {Ho : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (σ : ∀ n, Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (y : ∀ n, (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) {κ : ℝ}
    (hO : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
      ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon) (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
        (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
          B / (R n / c n) ≤ v →
      ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
        ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
        ((Ho n).toHistory.activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Ho n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((Ho n).toHistory.activeStage v) le_rfl ((Ho n).toHistory.activeStage_mono hvt))
          (ϱ / Real.sqrt (R n / c n)) →
        ENNReal.ofReal (κ * ϱ ^ 3) ≤
          ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
            ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt)) ϱ) :
    ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon) (hvt : v ≤ σ n),
        (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace ((Ho n).rescale_P6N (c n) (hc n)).toHistory
        (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v)
        (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n))
        (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        ((Ho n).rescale_P6N (c n) (hc n)).toHistory.isParabolicallyRmControlledBall v
          (tr.point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl
            (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κ * ϱ ^ 3) ≤
          ballVolume (scaleMetric (R n) (hRpos n)
            (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) v))
            (tr.point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt)) ϱ := by
  intro D L B hD hL hB
  exact (hO D L B hD hL hB).mono fun n hn =>
    (Ho n).volume_rescale_P6CK (hc n) _ _ (div_pos (hRpos n) (hc n)) hn (σ n) (y n) (hRpos n)
      ((Ho n).rescale_unscaleTime_P6X (hc n) (σ n))
      (((Ho n).heq_castRescale_P6X (hc n) _ _).trans
        ((Ho n).heq_uncastRescale_P6CK (hc n) (σ n) (y n)))
      (mul_div_cancel₀ (R n) (hc n).ne')

/-- **原尺度 `Pre841Data_C11K` ⇒ 重标度 `hvolK`**（`κd = d.kappa`）：FRESH / CXSK 等原尺度 producer 的
`d` 直接喂联合主形的 κ 槽。 -/
theorem hvolK_of_pre841_orig_P6CK {Ho : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ}
    (hc : ∀ n, 0 < c n)
    (σ : ∀ n, Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (y : ∀ n, (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (d : GC.LongTime.Ch11.Pre841Data_C11K (fun n => (Ho n).toHistory)
      (fun n => (Ho n).unscaleTime_P6X (hc n) (σ n))
      (fun n => (Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (fun n => R n / c n)
      (fun n => div_pos (hRpos n) (hc n))) :
    0 < d.kappa ∧ ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon) (hvt : v ≤ σ n),
        (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace ((Ho n).rescale_P6N (c n) (hc n)).toHistory
        (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v)
        (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n))
        (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        ((Ho n).rescale_P6N (c n) (hc n)).toHistory.isParabolicallyRmControlledBall v
          (tr.point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl
            (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (d.kappa * ϱ ^ 3) ≤
          ballVolume (scaleMetric (R n) (hRpos n)
            (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) v))
            (tr.point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt)) ϱ :=
  ⟨d.kappa_pos, hvolK_of_orig_P6CK hc σ y R hRpos d.volume_ge⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
