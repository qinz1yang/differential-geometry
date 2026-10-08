import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDProtCP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceScalarLowerP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStaySeqP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDBootstrapBallP6BB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDLocalDerivP6F3

/-!
# gate 帧前 slab 导数的三情形核（HSTAY-A4 G8，后缀 `_P6HS`；lead R14）

FOOT3 guarded gate 的 `hderivL⋆` 第一合取（U_t 点 `z` 出发的 trace `B` 在前 slab `i′` 的求值点
`(v′, x = B.point i′⁻)`，c⋆ guard `(t − v′)·max(ΛR, R(t, z)) ≤ c⋆`、阈值 `ΛR < R(v′, x)`）按
SLICE-BCBD2 G8（`hslabs_of_sepRho_supply_P6SB2`）的三情形直接付，history 帧、单点：
* (A) `Q < R(v′, x)`：天花板级先验 Dt（`hslab`：被跨越 slab 与当前 slab 上 `DerivativeBoundBefore Ctime Q`）；
* (B) `R(v′, x) ≤ Q < R(t, z)/2`：不可能（`scalar_gt_of_time_local_derivative_control_P6SB2` + 本文件
  `hbound_of_slabsUpTo_P6HS`）；
* (C) 其余：`ΛR < R(v′, x) ≤ Q` 与 `R(t, z) ≤ 2Q` ⇒ `Qb·R ≤ 2Q`（**不假设** `Q ≤ Cg·R`：带内点由阈值
  自身给 `ΛR < Q`）；trace stay = SLTPROD G3 `stay_cstar_of_firstExit_P6SP`，在 `(t, p′)` 重新居中
  （`hgood′ ⇐ hgood + hmargin`，`L′ = L/2`），保护 = `hprotC_of_ceiling_guarded_P6SB2`，其 scale 分离
  `hsep : max 6 (8Q) < scale`（被跨越 records）；再 hgood ⇒ HSCTC ⇒ `deriv_incoming_of_hgood_P6F3`。
结论：`|∂ₜR(v′, x)| ≤ Ctime·R(v′, x)²`。前提全是逐点数据（无 stay binder）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- trace 起止指标同时搬运（`_P6HS`，PROVED）。 -/
theorem exists_trace_transport2_P6HS {H : ObservedHistory.{u}} {f f' l l' : Fin (H.eventCount + 1)}
    {hle : f ≤ l} (hle' : f' ≤ l') {x : (H.stage l).Carrier} (x' : (H.stage l').Carrier)
    (hf : f = f') (hl : l = l') (hx : HEq x x') (A : BackwardPointTrace H f l hle x) :
    ∃ A' : BackwardPointTrace H f' l' hle' x', ∀ (m : Fin (H.eventCount + 1)) (h1 : f ≤ m)
      (h2 : m ≤ l) (h1' : f' ≤ m) (h2' : m ≤ l'), A'.point m h1' h2' = A.point m h1 h2 := by
  subst hf hl
  obtain rfl := eq_of_heq hx
  exact ⟨A, fun _ _ _ _ _ => rfl⟩

/-- 同一 trace 在相等指标处的点 HEq（`_P6HS`）。 -/
theorem trace_point_heq_P6HS {H : ObservedHistory.{u}} {f l : Fin (H.eventCount + 1)}
    {hle : f ≤ l} {x : (H.stage l).Carrier} (A : BackwardPointTrace H f l hle x)
    {m m' : Fin (H.eventCount + 1)} (hm : m = m') (h1 : f ≤ m) (h2 : m ≤ l) (h1' : f ≤ m')
    (h2' : m' ≤ l) : HEq (A.point m h1 h2) (A.point m' h1' h2') := by
  subst hm
  rfl

/-- stage 距离搬运（`_P6HS`）：`activeStage τ = k`、`τ = s`、两端点 HEq。 -/
theorem edist_transport_P6HS {H : ObservedHistory.{u}} {τ : Icc (0 : ℝ) H.horizon}
    {k : Fin (H.eventCount + 1)} (hk : H.activeStage τ = k) {s : ℝ} (hs : (τ : ℝ) = s)
    (a b : (H.stageAt τ).Carrier) (a' b' : (H.stage k).Carrier) (ha : HEq a a') (hb : HEq b b') :
    riemannianEDistOf (H.stageMetric (H.activeStage τ) τ) a b =
      riemannianEDistOf (H.stageMetric k s) a' b' := by
  subst hk
  subst hs
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  rfl

/-- **先验 Dt（截至 slab `j₀`）⇒ trace 上逐点导数界（`_P6HS`，PROVED）**：`hbound_of_eventSlabs_P6SB2` 的
孪生，`EventSlabsDerivative … (last)` 换成 `e⁻ ≤ j₀⁻` 的 slab 上 `DerivativeBoundBefore … (time e⁺)`。 -/
theorem hbound_of_slabsUpTo_P6HS (H : ObservedHistory.{u}) {C : ℝ≥0} {Q : ℝ}
    (j₀ : Fin H.eventCount)
    (hslab : ∀ e : Fin H.eventCount, e.castSucc ≤ j₀.castSucc →
      (H.event e).incoming.DerivativeBoundBefore C Q (H.time e.succ))
    {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) (hact : H.activeStage t = j₀.castSucc)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      Q < metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric (H.activeStage v) s)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        C * metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) ^ 2 := by
  intro v hav hvt htv _ hq
  have hvj : H.activeStage v ≤ j₀.castSucc := hact ▸ H.activeStage_mono hvt
  have hlt : H.activeStage v < Fin.last H.eventCount :=
    lt_of_le_of_lt hvj (Fin.castSucc_lt_last j₀)
  obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hlt)
  have hej : e.castSucc ≤ j₀.castSucc := he ▸ hvj
  have hvlt : (H.activeStage v).val < H.eventCount := by
    rw [← he]
    exact e.isLt
  have hnext := H.activeStage_before_next v hvlt
  have hfin : (⟨(H.activeStage v).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = e.succ := by
    apply Fin.ext
    change (H.activeStage v).val + 1 = e.succ.val
    rw [Fin.val_succ, ← he, Fin.val_castSucc]
  have hv2 : (v : ℝ) < H.time e.succ := hnext.trans_eq (congrArg H.time hfin)
  have hgen : ∀ (m : Fin (H.eventCount + 1)) (hm : e.castSucc = m)
      (h1 : H.activeStage a ≤ m) (h2 : m ≤ H.activeStage t),
      H.time m < (v : ℝ) →
      Q < metricScalarAt (H.stageMetric m v) (A.point m h1 h2) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric m s) (A.point m h1 h2))
          (Iic (v : ℝ)) v| ≤
        C * metricScalarAt (H.stageMetric m v) (A.point m h1 h2) ^ 2 := by
    intro m hm h1 h2 htm hqm
    subst hm
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hqm ⊢
    exact hslab e hej _ v ⟨htm, hv2⟩ hqm
  exact hgen _ he _ _ htv hq

/-- **三情形核（`_P6HS`，PROVED，逐点）**：见模块注释。 -/
theorem prevDeriv_threeCase_P6HS {eps C1' C2' : ℝ} {Ctime : ℝ≥0} (hC2 : 0 ≤ C2')
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT 1)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - 1 ^ 2) (hone : (1 : ℝ) ≤ aSeed)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hpin : ∀ (s : Icc (0 : ℝ) H.horizon) (x : (H.stageAt s).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage s) s) (0 + s) x)
    (y : (H.stageAt σ).Carrier) {R L : ℝ} (hR1 : 1 ≤ R)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime v z)
    (i₀ : Fin H.eventCount) (hσ : (σ : ℝ) = H.time i₀.succ)
    (h1 : H.activeStage aSeed ≤ i₀.castSucc) (h2 : i₀.castSucc ≤ H.activeStage Tn)
    {Λ : ℝ} (hΛ : 4 ≤ Λ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hLbig : 4 * (r₀ + 8 * (1 / (2 * max (Ctime : ℝ) 1)) /
        min (min (1 / 50) (localPropagationRadius C2' / 2))
          (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4))))) +
        8 * localPropagationRadius C2' + 4 * r₀ + 4 ≤ L)
    (haS2 : (aSeed : ℝ) ≤ σ - 2 / R)
    {p' : (H.stage i₀.castSucc).Carrier} {t : ℝ} (ht1 : H.time i₀.castSucc < t)
    (htσ : t < σ) (ht2 : (σ : ℝ) - 1 / R ≤ t)
    (hmt : riemannianEDistOf ((H.event i₀).incoming.flow.base.metric t)
        (seedTrace.point i₀.castSucc h1 h2) p' ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (r₀ / Real.sqrt R))
    (z : (H.stage i₀.castSucc).Carrier)
    (hz : z ∈ riemannianBallOf ((H.event i₀).incoming.flow.base.metric t) p' (r₀ / Real.sqrt R))
    {first : Fin (H.eventCount + 1)} {hfl : first ≤ i₀.castSucc}
    (B : BackwardPointTrace H first i₀.castSucc hfl z)
    (i' : Fin H.eventCount) (hf : first ≤ i'.castSucc) (hij : i'.castSucc < i₀.castSucc)
    (v' : ℝ) (hv' : v' ∈ Ioo (H.time i'.castSucc) (H.time i'.succ))
    (hg : (t - v') * max (Λ * R) ((H.event i₀).incoming.flow.scalar t z) ≤
      1 / (2 * max (Ctime : ℝ) 1))
    (hthr : Λ * R < (H.event i').incoming.flow.scalar v' (B.point i'.castSucc hf hij.le))
    {Q : ℝ} (hQ : 0 < Q)
    (hslab : ∀ e : Fin H.eventCount, e.castSucc ≤ i₀.castSucc →
      (H.event e).incoming.DerivativeBoundBefore Ctime Q (H.time e.succ))
    {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e p)
    (hT₀ : T₀ ≤ v')
    (hOld : ∀ e : Fin H.eventCount,
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : p.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < p.modelRadius)
    (hnc : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < p.modelRadius)
    (hsep : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, v' < H.time e.succ →
      e.succ ≤ i₀.castSucc → max 6 (8 * Q) < ((records e he).static b).neck.scale) :
    |derivWithin (fun w => (H.event i').incoming.flow.scalar w (B.point i'.castSucc hf hij.le))
        (Iic v') v'| ≤
      Ctime * (H.event i').incoming.flow.scalar v' (B.point i'.castSucc hf hij.le) ^ 2 := by
  -- 基本数值
  have hR0 : 0 < R := by linarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hΛ0 : 0 < Λ := by linarith
  have hm1 : (1 : ℝ) ≤ max (Ctime : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime : ℝ) 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (1 / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκdef]
    have : 0 < 2 * Real.sqrt 3 * (9 + 2 * Real.exp 4) := by positivity
    exact lt_min (lt_min (by norm_num) (by positivity)) (lt_min one_pos (by positivity))
  rw [← hκdef] at hLbig
  have hq8 : 0 ≤ 8 * (1 / (2 * max (Ctime : ℝ) 1)) / κ := by positivity
  have hL2 : (2 : ℝ) ≤ L := by linarith only [hLbig, hr₀, hq8, hρ]
  have hLr : r₀ ≤ L / 2 := by linarith only [hLbig, hr₀, hq8, hρ]
  have hsi : i'.succ ≤ i₀.castSucc := by
    rw [Fin.le_def]
    have h := Fin.lt_def.mp hij
    simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
    omega
  have hvt : v' < t := hv'.2.trans_le ((H.time_strictMono.monotone hsi).trans ht1.le)
  have htv0 : 0 ≤ t - v' := sub_nonneg.mpr hvt.le
  have htv1 : t - v' ≤ 1 / R := by
    have h3 : (t - v') * (Λ * R) ≤ 1 / 2 :=
      ((mul_le_mul_of_nonneg_left (le_max_left _ _) htv0).trans hg).trans hc1
    have hpos : 0 ≤ (t - v') * R := mul_nonneg htv0 hR0.le
    have h4 := mul_le_mul_of_nonneg_right hΛ hpos
    rw [le_div_iff₀ hR0]
    nlinarith only [h3, h4, hpos]
  have hv'0 : (0 : ℝ) ≤ v' := (H.time_nonneg _).trans hv'.1.le
  have hσH : (σ : ℝ) ≤ H.horizon := σ.2.2
  let vI : Icc (0 : ℝ) H.horizon := ⟨v', hv'0, (hvt.trans htσ).le.trans hσH⟩
  let tI : Icc (0 : ℝ) H.horizon := ⟨t, hv'0.trans hvt.le, htσ.le.trans hσH⟩
  have hvtI : vI ≤ tI := hvt.le
  have htIσ : tI ≤ σ := htσ.le
  have htT : tI ≤ Tn := htIσ.trans hsT
  have hav' : (aSeed : ℝ) ≤ v' := by
    have e1 : 2 / R = 1 / R + 1 / R := by ring
    linarith only [haS2, ht2, htv1, e1]
  have hav : aSeed ≤ vI := hav'
  have hast : aSeed ≤ tI := hav.trans hvtI
  have hact_t : H.activeStage tI = i₀.castSucc :=
    H.activeStage_eq_of_mem_slab_P6F3 i₀ tI ht1.le (by rw [← hσ]; exact htσ)
  have hact_v : H.activeStage vI = i'.castSucc :=
    H.activeStage_eq_of_mem_slab_P6F3 i' vI hv'.1.le hv'.2
  have hσL : (σ : ℝ) - L ^ 2 / R ≤ v' := by
    have e1 : 2 / R ≤ L ^ 2 / R :=
      div_le_div_of_nonneg_right (by nlinarith only [hL2]) hR0.le
    have e2 : 2 / R = 1 / R + 1 / R := by ring
    have e3 : (aSeed : ℝ) ≤ v' := hav'
    linarith only [haS2, e3, e1, e2, ht2, htv1]
  -- trace A：`activeStage vI → activeStage tI`
  obtain ⟨z'', hz''⟩ := exists_heq_stageAt_P6JW H hact_t z
  have hfi : first ≤ i'.castSucc := hf
  let B1 := B.restrictFirst hfi hij.le
  obtain ⟨A, hA⟩ := exists_trace_transport2_P6HS (H.activeStage_mono hvtI) z'' hact_v.symm
    hact_t.symm hz''.symm B1
  have hAx : HEq (A.point (H.activeStage vI) (H.activeStage_mono le_rfl)
      (H.activeStage_mono hvtI)) (B.point i'.castSucc hf hij.le) := by
    have hmeq : H.activeStage vI = i'.castSucc := hact_v
    have e1 := hA (H.activeStage vI) (hact_v ▸ le_rfl) (hact_v ▸ hij.le)
      (H.activeStage_mono le_rfl) (H.activeStage_mono hvtI)
    rw [e1]
    exact trace_point_heq_P6HS B hmeq _ _ hf hij.le
  -- 标量换算
  have hRz : metricScalarAt (H.stageMetric (H.activeStage tI) tI) z'' =
      (H.event i₀).incoming.flow.scalar t z := by
    rw [ObservedHistory.scalar_transport_P6BB hact_t (rfl : (tI : ℝ) = t) z'' z hz'',
      ObservedHistory.stageMetric_castSucc_apply]
    rfl
  have hRx : metricScalarAt (H.stageMetric (H.activeStage vI) vI)
      (A.point (H.activeStage vI) (H.activeStage_mono le_rfl) (H.activeStage_mono hvtI)) =
      (H.event i').incoming.flow.scalar v' (B.point i'.castSucc hf hij.le) := by
    rw [ObservedHistory.scalar_transport_P6BB hact_v (rfl : (vI : ℝ) = v') _ _ hAx,
      ObservedHistory.stageMetric_castSucc_apply]
    rfl
  by_cases hA' : Q < (H.event i').incoming.flow.scalar v' (B.point i'.castSucc hf hij.le)
  · -- (A) 天花板以上
    exact hslab i' hij.le _ v' hv' hA'
  push Not at hA'
  by_cases hB : 2 * Q < (H.event i₀).incoming.flow.scalar t z
  · -- (B) 不可能
    exfalso
    have htime : (Ctime : ℝ) * metricScalarAt (H.stageMetric (H.activeStage tI) tI) z'' *
        ((tI : ℝ) - vI) ≤ 1 / 2 := by
      rw [hRz]
      have hRz0 : (t - v') * (H.event i₀).incoming.flow.scalar t z ≤
          1 / (2 * max (Ctime : ℝ) 1) :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hg
      have e1 := mul_le_mul_of_nonneg_left hRz0 Ctime.coe_nonneg
      have e2 : (Ctime : ℝ) * (1 / (2 * max (Ctime : ℝ) 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith [le_max_left (Ctime : ℝ) 1]
      change (Ctime : ℝ) * (H.event i₀).incoming.flow.scalar t z * (t - v') ≤ 1 / 2
      nlinarith only [e1, e2]
    have hgt := BackwardPointTrace.scalar_gt_of_time_local_derivative_control_P6SB2 hvtI A hQ
      (hbound_of_slabsUpTo_P6HS H i₀ hslab hvtI hact_t A) (by rw [hRz]; exact hB) htime vI le_rfl
      hvtI
    rw [hRx] at hgt
    exact absurd hgt (not_lt.mpr hA')
  push Not at hB
  -- (C) 天花板以下：重新居中的 c⋆ stay
  obtain ⟨y'', hy''⟩ := exists_heq_stageAt_P6JW H hact_t p'
  set dσ := riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
    (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y
    with hdσdef
  have hctl0 : ∀ zz : (H.stageAt vI).Carrier,
      riemannianEDistOf (H.stageMetric (H.activeStage vI) vI)
          (seedTrace.point (H.activeStage vI) (H.activeStage_mono hav)
            (H.activeStage_mono (hvtI.trans htT))) zz ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) →
      4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage vI) vI) zz →
      H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime vI zz :=
    fun zz hd h4 => hgood vI hav (hvtI.trans htIσ) hσL zz hd h4
  have h4x : 4 * R ≤ (H.event i').incoming.flow.scalar v' (B.point i'.castSucc hf hij.le) :=
    (mul_le_mul_of_nonneg_right hΛ hR0.le).trans hthr.le
  refine H.deriv_incoming_of_hgood_P6F3 i' (B.point i'.castSucc hf hij.le) vI hv'.1 hv'.2 h4x
    (fun zz hzz h4 => hctl0 zz ?_ h4)
  have hzzA : zz = A.point (H.activeStage vI) (H.activeStage_mono le_rfl)
      (H.activeStage_mono hvtI) := eq_of_heq (hzz.trans hAx.symm)
  subst hzzA
  by_cases hdtop : dσ = ⊤
  · rw [hdtop, top_add]
    exact le_top
  -- 重新居中的 hgood′
  have hseedt : HEq (seedTrace.point (H.activeStage tI) (H.activeStage_mono hast)
      (H.activeStage_mono htT)) (seedTrace.point i₀.castSucc h1 h2) :=
    trace_point_heq_P6HS seedTrace hact_t _ _ h1 h2
  have hdt_eq : riemannianEDistOf (H.stageMetric (H.activeStage tI) tI)
      (seedTrace.point (H.activeStage tI) (H.activeStage_mono hast) (H.activeStage_mono htT))
      y'' = riemannianEDistOf ((H.event i₀).incoming.flow.base.metric t)
        (seedTrace.point i₀.castSucc h1 h2) p' := by
    rw [edist_transport_P6HS hact_t (rfl : (tI : ℝ) = t) _ _ _ _ hseedt hy'',
      ObservedHistory.stageMetric_castSucc_apply]
  set dt := riemannianEDistOf (H.stageMetric (H.activeStage tI) tI)
    (seedTrace.point (H.activeStage tI) (H.activeStage_mono hast) (H.activeStage_mono htT)) y''
    with hdtdef
  have hdt : dt ≤ dσ + ENNReal.ofReal (r₀ / Real.sqrt R) := by rw [hdt_eq]; exact hmt
  have hdtfin : dt ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hdtop, ENNReal.ofReal_ne_top⟩) hdt
  have hbud : ∀ X : ℝ≥0∞, X ≤ dt + ENNReal.ofReal (L / 2 / Real.sqrt R) →
      X ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := by
    intro X hX
    refine hX.trans ((add_le_add hdt le_rfl).trans ?_)
    rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith only [hLr]) hsR.le
  have hgood' : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ tI),
      (tI : ℝ) - (L / 2) ^ 2 / R ≤ (v : ℝ) →
      ∀ w : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans htT))) w ≤
          dt + ENNReal.ofReal (L / 2 / Real.sqrt R) →
        Λ * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) w →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime v w := by
    intro v hav hvs hvL w hw hRw
    have hσLv : (σ : ℝ) - L ^ 2 / R ≤ v := by
      have e1 : 1 / R + (L / 2) ^ 2 / R ≤ L ^ 2 / R := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by nlinarith only [hL2]) hR0.le
      linarith only [hvL, ht2, e1]
    exact hgood v hav (hvs.trans htIσ) hσLv w (hbud _ hw)
      ((mul_le_mul_of_nonneg_right hΛ hR0.le).trans hRw)
  -- Qb / T / 数值
  set Rz := metricScalarAt (H.stageMetric (H.activeStage tI) tI) z'' with hRzdef
  obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max (Rz / R) Λ) 1 := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 / (2 * max (Ctime : ℝ) 1) / Qb := ⟨_, rfl⟩
  have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
  have hQbpos : 0 < Qb := lt_of_lt_of_le one_pos hQb1
  have hQbM : Qb * R ≤ max (Λ * R) Rz := by
    have hΛR : R ≤ Λ * R := le_mul_of_one_le_left hR0.le (by linarith)
    have hle : Qb ≤ max (Λ * R) Rz / R := by
      rw [hQbdef]
      refine max_le (max_le ?_ ?_) ?_
      · exact div_le_div_of_nonneg_right (le_max_right _ _) hR0.le
      · rw [le_div_iff₀ hR0]
        exact le_max_left _ _
      · rw [le_div_iff₀ hR0, one_mul]
        exact hΛR.trans (le_max_left _ _)
    calc Qb * R ≤ max (Λ * R) Rz / R * R := mul_le_mul_of_nonneg_right hle hR0.le
      _ = _ := div_mul_cancel₀ _ hR0.ne'
  have hQbQ : Qb * R ≤ 2 * Q := by
    refine hQbM.trans (max_le ?_ ?_)
    · linarith only [hthr, hA', hQ]
    · exact (le_of_eq hRz).trans hB
  have hguard : ((tI : ℝ) - vI) * max (Λ * R) Rz ≤ 1 / (2 * max (Ctime : ℝ) 1) := by
    have hg' := hg
    rw [← hRz] at hg'
    exact hg'
  have hdepth : (tI : ℝ) - vI ≤ T / R := by
    rw [hTdef, div_div, le_div_iff₀ (mul_pos hQbpos hR0)]
    exact (mul_le_mul_of_nonneg_left hQbM htv0).trans hguard
  have hstep : 2 * (Ctime : ℝ) * Qb * T ≤ 1 := by
    have hT' : 2 * (Ctime : ℝ) * Qb * T = (Ctime : ℝ) / max (Ctime : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [hT', div_le_one (by linarith)]
    exact le_max_left _ _
  have hσlast : H.activeStage tI < Fin.last H.eventCount := by
    rw [hact_t]
    exact Fin.castSucc_lt_last i₀
  have haL : (tI : ℝ) - (L / 2) ^ 2 / R ≤ vI := by
    have e1 : 1 / R ≤ (L / 2) ^ 2 / R :=
      div_le_div_of_nonneg_right (by nlinarith only [hL2]) hR0.le
    change t - (L / 2) ^ 2 / R ≤ v'
    linarith only [htv1, e1]
  have hRa : 1 ≤ R * vI := by
    change 1 ≤ R * v'
    nlinarith only [hR1, hone, hav']
  have hL0 : (0 : ℝ) ≤ L / 2 := by linarith only [hL2]
  have hscaleK : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, (vI : ℝ) < H.time e.succ →
      e.succ ≤ H.activeStage tI →
      2 * max (3 / 1 ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale := by
    intro e he b hve he4
    have hS := hsep e he b hve (hact_t ▸ he4)
    have e6 : (6 : ℝ) ≤ max 6 (8 * Q) := le_max_left _ _
    have e8 : 8 * Q ≤ max 6 (8 * Q) := le_max_right _ _
    have hmx : max (3 / 1 ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale / 2 := by
      refine max_lt ?_ ?_
      · norm_num
        linarith only [hS, e6]
      · linarith only [hS, e8, hQbQ]
    linarith only [hmx]
  have hzc : metricScalarAt (H.stageMetric (H.activeStage tI) tI) z'' ≤ Rz / R * R := by
    rw [div_mul_cancel₀ _ hR0.ne']
  have hQb' : max (max (Rz / R) Λ) 1 ≤ Qb := le_of_eq hQbdef.symm
  have hprot := ObservedHistory.hprotC_of_ceiling_guarded_P6SB2 H haT hsmall hclock seedTrace htT
    hast y'' (L / 2) hR0 hL0 hgood' hQb' hstep hav hvtI hσlast haL hdepth hzc A records hDm hnc
    hscaleK
  have hzy : z'' ∈ riemannianBallOf (H.stageMetric (H.activeStage tI) tI) y''
      (r₀ / Real.sqrt R) := by
    change riemannianEDistOf (H.stageMetric (H.activeStage tI) tI) y'' z'' < _
    rw [edist_transport_P6HS hact_t (rfl : (tI : ℝ) = t) _ _ _ _ hy'' hz'',
      ObservedHistory.stageMetric_castSucc_apply]
    exact hz
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (r := 1)
    (ρ := localPropagationRadius C2') (c := 1 / (2 * max (Ctime : ℝ) 1)) (Qb := Qb) (R := R)
    (Rad := r₀) (L := L / 2) one_pos hρ hc0 hQb1 hR1 hκdef
    (by linarith only [hLbig, hr₀, hq8]) (by linarith only [hLbig, hr₀, hq8, hρ])
  have hTeq : T / R = 1 / (2 * max (Ctime : ℝ) 1) / Qb / R := by rw [hTdef]
  rw [← hTeq] at hnum
  have hguard' : ((tI : ℝ) - vI) * max (Λ * R) (metricScalarAt
      (H.stageMetric (H.activeStage tI) tI) z'') ≤ 1 / (2 * max (Ctime : ℝ) 1) := hguard
  have hstay := ObservedHistory.stay_cstar_of_firstExit_P6SP hC2 (by linarith : (1 : ℝ) ≤ Λ) H
    haT hsmall hclock seedTrace (le_refl (0 : ℝ)) hpin htT hast y'' (L / 2) hR0 hgood' hav hvtI
    hσlast haL hRa hQbdef hTdef hguard' A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records
    (fun e _ => hOld e) hcan hacc hDm hprot hzy hdtfin hnum vI le_rfl hvtI
  exact hbud _ hstay

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
