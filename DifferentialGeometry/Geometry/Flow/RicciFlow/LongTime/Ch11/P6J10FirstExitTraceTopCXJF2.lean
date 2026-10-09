import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FirstExitCoreCXJD
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.DistanceContractsC11D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.FirstExitUSC_P6L4
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

/-!
# 跨 slab first-exit：σ ≤ horizon（final slab 闭端）版（CX-J10FIN2 G1，后缀 `_CXJF2`）

`f(v) = d_v(seed(v), A(v))`（seed trace 与 `(σ, z)` 的 backward trace `A`，窗口 `[a, σ]`，`σ` 在 event slab
内：`activeStage σ < Fin.last`）。G1 `firstExit_window_CXJD` 的两个输入在 history 层：
* `hchain`：`(s, σ]` 上 `f < X` ⇒ 树内 DIST 链 `edist_trace_le_of_stage_bounds_C11D`，其 `hsmooth` 由
  I.8.3(b) `smooth_distance_distortion_C11D`、`hevent` 由 (D4) `event_crossing_bound_C11D`
  （RegularCrossing
  + `oldTerminal_edist_le_of_outside_canonical_cap_windows`，records / 保护）给；两者的端点 Ricci 界只在
  `(s, σ)` 内的时刻 `t'` 用，取自**条件** `hRicC`（`[t', σ]` 上 `f < X` 时的两端 `ℓ`-球 Ricci 界）；
* `husc`：slab 内 `edist_lt_near_left_P6L4`；slab 起点（crossing）用 (D4) 的 terminal 极限
  `surgery_no_shortcut_C11D`（**不要** Ricci 界）。
* crossing 保护 `hprotC` 也是**条件**形：只在 `[time e⁺, σ]` 上 Good 时要（G5 由 ceiling + scale 分离生产）。
CXJF G1 去掉 `σ < horizon`（`σ : Icc 0 horizon` 自带 `σ ≤ horizon`）；`s = σ = horizon` 时 final slab
USC 的开区间 regular 不够，改由显式 `hUSCtop`（horizon 处 final 度量距离的左连续）给——
extendAt 上由内部 incoming slab `G`（`t < s`）付（G4）。
slab 内 USC 在 `activeStage v = last` 时用 `(finalSlab).flow`，slab 起点（含 `time last`）同 crossing。
主定理 `edist_trace_le_of_firstExit_top_CXJF2`：余量 `f(σ) + (8/ℓ)(σ − a) < X` ⇒ 整窗
`f(v) ≤ f(σ) + (8/ℓ)(σ − v)`。不以 traced region 为前提；`hRicC` 只在 Good 区间上要。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem lt_time_succ_of_le_castSucc_CXJF2 (H : ObservedHistory.{u})
    (v : Icc (0 : ℝ) H.horizon) (e : Fin H.eventCount) (h : H.activeStage v ≤ e.castSucc) :
    (v : ℝ) < H.time e.succ := by
  have hlt : (H.activeStage v : ℕ) < H.eventCount :=
    lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) e.isLt
  have h1 := H.activeStage_before_next v hlt
  refine h1.trans_le (H.time_strictMono.monotone ?_)
  rw [Fin.le_iff_val_le_val]
  simp only [Fin.val_succ]
  have := Fin.le_iff_val_le_val.mp h
  simp only [Fin.val_castSucc] at this
  omega

private theorem activeStage_eq_of_mem_CXJF2 (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ v) (h2 : (v : ℝ) < H.time e.succ) :
    H.activeStage v = e.castSucc :=
  (H.mem_stageDomain_iff v e.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (v : ℝ) ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h1, h2⟩))

/-- **跨 slab first-exit（trace 层，`_CXJD`）**。 -/
theorem edist_trace_le_of_firstExit_top_CXJF2 (H : ObservedHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (hσT : σ ≤ Tn)
    {z : (H.stageAt σ).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (hUSCtop : (σ : ℝ) = H.horizon → ∀ (hfT : H.time (Fin.last H.eventCount) < H.horizon)
      (p q : (H.stage (Fin.last H.eventCount)).Carrier) (X' : ℝ≥0∞),
      riemannianEDistOf ((H.finalSlab hfT).flow.base.metric σ) p q < X' →
      ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ (σ : ℝ),
        riemannianEDistOf ((H.finalSlab hfT).flow.base.metric s') p q < X')
    {ℓ : ℝ} (hℓ : 0 < ℓ) {X : ℝ≥0∞}
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hOld : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage Tn) (h3 : H.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage σ) (he : T₀ ≤ H.time e.succ),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), H.time e.succ ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            X) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hRicC : ∀ (k : Fin (H.eventCount + 1)) (hka : H.activeStage a ≤ k)
        (hkσ : k ≤ H.activeStage σ) (t : ℝ), H.time k < t →
        (∀ e : Fin H.eventCount, k = e.castSucc → t < H.time e.succ) → (a : ℝ) < t → t < σ →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), t ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            X) →
        ∀ w : (H.stage k).Carrier, ∀ ξ : TangentSpace ThreeModel w,
          (riemannianEDistOf (H.stageMetric k t)
              (seedTrace.point k ((H.activeStage_mono haS).trans hka)
                (hkσ.trans (H.activeStage_mono hσT))) w < ENNReal.ofReal ℓ ∨
            riemannianEDistOf (H.stageMetric k t) (A.point k hka hkσ) w <
              ENNReal.ofReal ℓ) →
          ricciTensor (H.stageMetric k t) w ξ ξ ≤ (3 / ℓ ^ 2) * (H.stageMetric k t).inner w ξ ξ)
    (hmargin : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono (haS.trans haσ))
          (H.activeStage_mono hσT)) z +
      ENNReal.ofReal ((8 / ℓ) * ((σ : ℝ) - a)) < X) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ),
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
            (H.activeStage_mono (hvσ.trans hσT)))
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono (haS.trans haσ))
              (H.activeStage_mono hσT)) z +
          ENNReal.ofReal ((8 / ℓ) * ((σ : ℝ) - v)) := by
  -- 窗口函数与其 stage 指标形
  let F : ∀ v : Icc (0 : ℝ) H.horizon, a ≤ v → v ≤ σ → ℝ≥0∞ := fun v hav hvσ =>
    riemannianEDistOf (H.stageMetric (H.activeStage v) v)
      (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
        (H.activeStage_mono (hvσ.trans hσT)))
      (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ))
  have hFk : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ)
      (k : Fin (H.eventCount + 1)) (hk : H.activeStage v = k) (h1 : H.activeStage aSeed ≤ k)
      (h2 : k ≤ H.activeStage Tn) (h3 : H.activeStage a ≤ k) (h4 : k ≤ H.activeStage σ),
      F v hav hvσ = riemannianEDistOf (H.stageMetric k v) (seedTrace.point k h1 h2)
        (A.point k h3 h4) := by
    intro v hav hvσ k hk h1 h2 h3 h4
    subst hk
    rfl
  have hFσ : F σ haσ le_rfl = riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
      (seedTrace.point (H.activeStage σ) (H.activeStage_mono (haS.trans haσ))
        (H.activeStage_mono hσT)) z := by
    change riemannianEDistOf _ _ (A.point (H.activeStage σ) _ _) = _
    rw [A.endpoint_eq]
  let f : ℝ → ℝ≥0∞ := fun r =>
    if h : (a : ℝ) ≤ r ∧ r ≤ σ then F ⟨r, a.2.1.trans h.1, h.2.trans σ.2.2⟩ h.1 h.2 else 0
  have hfv : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ),
      f v = F v hav hvσ := by
    intro v hav hvσ
    simp only [f, dite_eq_left_of_eq_true (eq_true
      (And.intro (show (a : ℝ) ≤ v from hav) (show (v : ℝ) ≤ σ from hvσ)))]
  let mk : ∀ r : ℝ, (a : ℝ) ≤ r → r ≤ σ → Icc (0 : ℝ) H.horizon :=
    fun r h1 h2 => ⟨r, a.2.1.trans h1, h2.trans σ.2.2⟩
  have hgood_of : ∀ s : ℝ, (∀ s' ∈ Ioc s σ, f s' < X) → ∀ t : ℝ, s < t →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), t ≤ (v : ℝ) →
        F v hav hvσ < X := by
    intro s hs t hst v hav hvσ htv
    rw [← hfv v hav hvσ]
    exact hs v ⟨hst.trans_le htv, hvσ⟩
  have hσnext : ∀ e : Fin H.eventCount, H.activeStage σ = e.castSucc →
      (σ : ℝ) < H.time e.succ := fun e he =>
    lt_time_succ_of_le_castSucc_CXJF2 H σ e he.le
  -- G1
  have hmain := firstExit_window_CXJD (f := f) (Λ := 8 / ℓ) (X := X)
    (show (a : ℝ) ≤ σ from haσ) (div_pos (by norm_num) hℓ).le
    (by rw [hfv σ haσ le_rfl, hFσ]; exact hmargin) ?chain ?usc
  · intro v hav hvσ
    have h := hmain v ⟨hav, hvσ⟩
    rwa [hfv v hav hvσ, hfv σ haσ le_rfl, hFσ] at h
  case chain =>
    intro s hs hgood
    let v := mk s hs.1 hs.2
    have hav : a ≤ v := hs.1
    have hvσ : v ≤ σ := hs.2
    rw [hfv v hav hvσ, hfv σ haσ le_rfl, hFσ]
    have hgv := hgood_of s hgood
    let tr := A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvσ)
    refine H.edist_trace_le_of_stage_bounds_C11D haT hσT (haS.trans hav) hvσ seedTrace tr
      (div_pos (by norm_num) hℓ).le ?smooth ?event
    case smooth =>
      intro t hvt hkt htσ
      refine H.smooth_distance_distortion_C11D (H.activeStage σ) hℓ htσ hkt hσnext σ.2.2 _ _ ?_
      intro t' ht' w ξ hw
      have hR := hRicC (H.activeStage σ) (H.activeStage_mono haσ) le_rfl t'
        (hkt.trans_lt ht'.1) (fun e he => ht'.2.trans (hσnext e he))
        ((show (a : ℝ) ≤ v from hav).trans_lt (hvt.trans_lt ht'.1)) ht'.2
        (hgv t' (hvt.trans_lt ht'.1)) w ξ
      rw [A.endpoint_eq] at hR
      exact hR hw
    case event =>
      intro e h1 h2 h3 h4 t hvt ht1 ht2
      have hat : (a : ℝ) ≤ t := (show (a : ℝ) ≤ v from hav).trans hvt
      have he : T₀ ≤ H.time e.succ := hT₀.trans (hat.trans ht2.le)
      have hpr := hprotC e h1 h2 ((H.activeStage_mono hav).trans h3) h4 he
        (hgv (H.time e.succ) ((show s ≤ t from hvt).trans_lt ht2))
      exact H.event_crossing_bound_C11D e (records e he).static (hOld e he) (hcan e he) hacc hDm
        (seedTrace.crossing e _ _) (tr.crossing e h3 h4) (fun b => (hpr b).1)
        (fun b => (hpr b).2) hℓ ht1 ht2 (fun t' ht' w ξ hw =>
          hRicC e.castSucc ((H.activeStage_mono hav).trans h3)
            (e.castSucc_lt_succ.le.trans h4) t' (ht1.trans_lt ht'.1)
            (fun e' he' => by
              obtain rfl : e = e' := Fin.castSucc_injective _ he'
              exact ht'.2)
            (hat.trans_lt ht'.1)
            (ht'.2.trans_le ((H.time_strictMono.monotone h4).trans (H.activeStage_time_le σ)))
            (hgv t' (hvt.trans_lt ht'.1)) w ξ hw)
  case usc =>
    intro s hs hgoodI
    have hfs := hgoodI s ⟨le_rfl, hs.2⟩
    let v := mk s hs.1.le hs.2
    have hav : a ≤ v := hs.1.le
    have hvσ : v ≤ σ := hs.2
    rw [hfv v hav hvσ] at hfs
    have hsH' : s ≤ H.horizon := hs.2.trans σ.2.2
    have h1 : H.activeStage aSeed ≤ H.activeStage v := H.activeStage_mono (haS.trans hav)
    have h2 : H.activeStage v ≤ H.activeStage Tn := H.activeStage_mono (hvσ.trans hσT)
    have h3 : H.activeStage a ≤ H.activeStage v := H.activeStage_mono hav
    have h4 : H.activeStage v ≤ H.activeStage σ := H.activeStage_mono hvσ
    have hev : H.time (H.activeStage v) ≤ s := H.activeStage_time_le v
    rcases hev.lt_or_eq with hlt | heq
    · by_cases hkl : H.activeStage v = Fin.last H.eventCount
      · -- final slab 内：USC（`(finalSlab).flow`）
        have hlt' : H.time (Fin.last H.eventCount) < s := hkl ▸ hlt
        have hfT : H.time (Fin.last H.eventCount) < H.horizon := hlt'.trans_le hsH'
        have g1 : H.activeStage aSeed ≤ Fin.last H.eventCount := hkl ▸ h1
        have g2 : Fin.last H.eventCount ≤ H.activeStage Tn := hkl ▸ h2
        have g3 : H.activeStage a ≤ Fin.last H.eventCount := hkl ▸ h3
        have g4 : Fin.last H.eventCount ≤ H.activeStage σ := hkl ▸ h4
        have hfinr : ∀ r : ℝ, (a : ℝ) ≤ r → H.time (Fin.last H.eventCount) ≤ r → r ≤ s →
            f r = riemannianEDistOf ((H.finalSlab hfT).flow.base.metric r)
              (seedTrace.point (Fin.last H.eventCount) g1 g2)
              (A.point (Fin.last H.eventCount) g3 g4) := by
          intro r har her hrs
          have hrσ : r ≤ σ := hrs.trans hs.2
          rw [hfv (mk r har hrσ) har hrσ, hFk (mk r har hrσ) har hrσ (Fin.last H.eventCount)
            (H.activeStage_eq_last_of_time_last_le _ her) g1 g2 g3 g4,
            stageMetric_last_of_lt (h := hfT)]
        let lo := max (a : ℝ) ((H.time (Fin.last H.eventCount) + s) / 2)
        have hlo : lo < s := max_lt hs.1 (by linarith)
        have hlo1 : H.time (Fin.last H.eventCount) < lo :=
          lt_of_lt_of_le (by linarith) (le_max_right _ _)
        have hX : riemannianEDistOf ((H.finalSlab hfT).flow.base.metric s)
            (seedTrace.point (Fin.last H.eventCount) g1 g2)
            (A.point (Fin.last H.eventCount) g3 g4) < X := by
          rw [← hfinr s hs.1.le hlt'.le le_rfl, hfv v hav hvσ]
          exact hfs
        obtain ⟨s₁, hlo₁, hs₁, hnear⟩ : ∃ s₁ : ℝ, lo ≤ s₁ ∧ s₁ < s ∧ ∀ s' ∈ Icc s₁ s,
            riemannianEDistOf ((H.finalSlab hfT).flow.base.metric s')
              (seedTrace.point (Fin.last H.eventCount) g1 g2)
              (A.point (Fin.last H.eventCount) g3 g4) < X := by
          rcases hsH'.lt_or_eq with hsH | hsH
          · exact edist_lt_near_left_P6L4 (H.finalSlab hfT).flow
              (H.finalSlab hfT).equation hlo
              (fun r hr => ⟨hlo1.trans_le hr.1, hr.2.trans_lt hsH⟩) _ _ hX
          · -- `s = σ = horizon`：final slab 在 horizon 处闭，左延拓由 `hUSCtop` 给
            have hsσ : s = (σ : ℝ) := le_antisymm hs.2 (hsH ▸ σ.2.2)
            rw [hsσ] at hX hlo ⊢
            obtain ⟨t₁, ht₁, hnear⟩ := hUSCtop (hsσ ▸ hsH) hfT _ _ X hX
            exact ⟨max lo t₁, le_max_left _ _, max_lt hlo ht₁,
              fun s' hs' => hnear s' ⟨(le_max_right _ _).trans hs'.1, hs'.2⟩⟩
        refine ⟨s₁, ⟨(le_max_left _ _).trans hlo₁, hs₁⟩, fun s' hs' => ?_⟩
        rw [hfinr s' ((le_max_left _ _).trans (hlo₁.trans hs'.1))
          (hlo1.le.trans (hlo₁.trans hs'.1)) hs'.2]
        exact hnear s' hs'
      · -- event slab 内：USC（incoming）
        obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.mpr hkl
        have hvs : s < H.time e.succ := lt_time_succ_of_le_castSucc_CXJF2 H v e he.symm.le
        have g1 : H.activeStage aSeed ≤ e.castSucc := he ▸ h1
        have g2 : e.castSucc ≤ H.activeStage Tn := he ▸ h2
        have g3 : H.activeStage a ≤ e.castSucc := he ▸ h3
        have g4 : e.castSucc ≤ H.activeStage σ := he ▸ h4
        have hlte : H.time e.castSucc < s := he ▸ hlt
        have hfin : ∀ r : ℝ, (a : ℝ) ≤ r → H.time e.castSucc ≤ r → r ≤ s →
            f r = riemannianEDistOf ((H.event e).incoming.flow.base.metric r)
              (seedTrace.point e.castSucc g1 g2) (A.point e.castSucc g3 g4) := by
          intro r har her hrs
          have hrσ : r ≤ σ := hrs.trans hs.2
          rw [hfv (mk r har hrσ) har hrσ, hFk (mk r har hrσ) har hrσ e.castSucc
            (activeStage_eq_of_mem_CXJF2 H e _ her (hrs.trans_lt hvs)) g1 g2 g3 g4,
            stageMetric_castSucc_apply]
        let lo := max (a : ℝ) ((H.time e.castSucc + s) / 2)
        have hlo : lo < s := max_lt hs.1 (by linarith)
        have hlo1 : H.time e.castSucc < lo := lt_of_lt_of_le (by linarith) (le_max_right _ _)
        have hX : riemannianEDistOf ((H.event e).incoming.flow.base.metric s)
            (seedTrace.point e.castSucc g1 g2) (A.point e.castSucc g3 g4) < X := by
          rw [← hfin s hs.1.le hlte.le le_rfl, hfv v hav hvσ]
          exact hfs
        obtain ⟨s₁, hlo₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4 (H.event e).incoming.flow
          (H.event e).incoming.equation hlo
          (fun r hr => ⟨hlo1.trans_le hr.1, hr.2.trans_lt hvs⟩) _ _ hX
        refine ⟨s₁, ⟨(le_max_left _ _).trans hlo₁, hs₁⟩, fun s' hs' => ?_⟩
        rw [hfin s' ((le_max_left _ _).trans (hlo₁.trans hs'.1))
          (hlo1.le.trans (hlo₁.trans hs'.1)) hs'.2]
        exact hnear s' hs'
    · -- slab 起点（event 或 final）：crossing 的 terminal 极限
      have hne0 : H.activeStage v ≠ H.activeStage a := by
        intro h
        have hta : H.time (H.activeStage a) ≤ a := H.activeStage_time_le a
        rw [← h, heq] at hta
        linarith [hs.1]
      have hpos : (H.activeStage v : ℕ) ≠ 0 := by
        intro h0
        apply hne0
        have h00 : H.activeStage v = 0 := Fin.ext h0
        rw [h00]
        exact (le_antisymm (h3.trans (le_of_eq h00)) (Fin.zero_le _)).symm
      obtain ⟨e', he'⟩ : ∃ e' : Fin H.eventCount, e'.succ = H.activeStage v := by
        refine ⟨⟨(H.activeStage v : ℕ) - 1, by omega⟩, Fin.ext ?_⟩
        simp only [Fin.val_succ]
        omega
      have h3' : H.activeStage a ≤ e'.castSucc := by
        rcases (he' ▸ h3 : H.activeStage a ≤ e'.succ).lt_or_eq with hl | hl
        · exact Fin.le_castSucc_iff.mpr hl
        · exact absurd (he' ▸ hl.symm) hne0
      have h1' : H.activeStage aSeed ≤ e'.castSucc := (H.activeStage_mono haS).trans h3'
      have h4' : e'.succ ≤ H.activeStage σ := he' ▸ h4
      have h2' : e'.succ ≤ H.activeStage Tn := he' ▸ h2
      have hτ : H.time e'.succ = s := by rw [he', heq]
      have heT : T₀ ≤ H.time e'.succ := hT₀.trans (hτ ▸ hs.1.le)
      have hpr := hprotC e' h1' h2' h3' h4' heT (fun w haw hwσ hw => by
        have h := hgoodI w ⟨hτ ▸ hw, hwσ⟩
        rw [hfv w haw hwσ] at h
        exact h)
      have hfs' : riemannianEDistOf (H.stageMetric e'.succ (H.time e'.succ))
          (seedTrace.point e'.succ (h1'.trans e'.castSucc_lt_succ.le) h2')
          (A.point e'.succ (h3'.trans e'.castSucc_lt_succ.le) h4') < X := by
        have hk : H.activeStage v = e'.succ := he'.symm
        rw [hτ, ← hFk v hav hvσ e'.succ hk _ _ _ _]
        exact hfs
      obtain ⟨δ, hδ, hδX⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hfs'
      have hev' := H.surgery_no_shortcut_C11D e' (records e' heT).static (hOld e' heT)
        (hcan e' heT) hacc hDm (seedTrace.crossing e' h1' h2') (A.crossing e' h3' h4')
        (fun b => (hpr b).1) (fun b => (hpr b).2) (δ := δ) (by exact_mod_cast hδ)
      obtain ⟨l, hl0, hlI⟩ := (mem_nhdsLT_iff_exists_Ioo_subset.mp hev')
      have hl : l < H.time e'.succ := hl0
      let lo := max (a : ℝ) (max ((l + H.time e'.succ) / 2)
        ((H.time e'.castSucc + H.time e'.succ) / 2))
      have hcs : H.time e'.castSucc < H.time e'.succ := H.time_strictMono e'.castSucc_lt_succ
      have hlo : lo < s := by
        rw [← hτ]
        refine max_lt (hτ ▸ hs.1) (max_lt (by linarith) (by linarith))
      refine ⟨lo, ⟨le_max_left _ _, hlo⟩, fun s' hs' => ?_⟩
      rcases hs'.2.lt_or_eq with hs'lt | hs'eq
      · have hs'a : (a : ℝ) ≤ s' := (le_max_left _ _).trans hs'.1
        have hs'σ : s' ≤ σ := hs'lt.le.trans hs.2
        have hs'1 : H.time e'.castSucc ≤ s' :=
          (by linarith : H.time e'.castSucc ≤ (H.time e'.castSucc + H.time e'.succ) / 2).trans
            ((le_max_right _ _).trans ((le_max_right _ _).trans hs'.1))
        have hs'2 : s' < H.time e'.succ := hτ ▸ hs'lt
        have hk : H.activeStage (mk s' hs'a hs'σ) = e'.castSucc :=
          activeStage_eq_of_mem_CXJF2 H e' _ hs'1 hs'2
        rw [hfv (mk s' hs'a hs'σ) hs'a hs'σ, hFk _ hs'a hs'σ e'.castSucc hk h1'
          (e'.castSucc_lt_succ.le.trans h2') h3' (e'.castSucc_lt_succ.le.trans h4')]
        have hmem : s' ∈ Ioo l (H.time e'.succ) :=
          ⟨lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans
            ((le_max_right _ _).trans hs'.1)), hs'2⟩
        have hb := hlI hmem
        rw [ENNReal.ofReal_coe_nnreal] at hb
        exact lt_of_le_of_lt hb hδX
      · rw [hs'eq, hfv v hav hvσ]
        exact hfs

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
