import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDNotKEvP6SB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStaySeqP6SP

/-!
# G4 `hceil`（cap 出生时刻 trace ceiling）⇐ CXJD 跨 slab ceiling（O-CH11-SLICE-BCBD G6，后缀 `_P6SB`）

G4 `hnotK_of_capCeiling_P6SB` 的 `hceil`：`yG` 自 `i⁺` 到 `j⁻` 的任意 trace 在 cap 出生时刻 `time i⁺` 的
标量 `≤ M n`。这里取 `M n := 2·Qb·R n`，`Qb := max (max 1 Cg) 1`，由 CXJD
`scalar_le_two_mul_crossSlab_ceiling_CXJD`（`z = y`、`Cball = 1`、`a = time i⁺`、`T = c⋆/Qb`、`D = 1`）给出：
* 深度 `σ − time i⁺ ≤ T/R` ⇐ 年龄 `≤ θ₀/scale` + (SEP′) 型 `hsepT : θ₀·R ≤ T·scale`；
* `aSeed ≤ time i⁺`、`σ − L²/R ≤ time i⁺`、`1 ≤ R·time i⁺` ⇐ `hwin T`、`L ≥ 1`、`hRa`（只能 eventually 成立）；
* 数值 ⇐ SLTPROD G3c `cstar_numerics_P6SP`（`Rad := 1`、`c := c⋆`）；
* trace 搬运 `trace_transport_both_P6SB`；`activeStage (time i⁺) = i⁺`；
  `stageMetric i⁺ (time i⁺) = outputMetric`（`stageMetric_succ_time_C11G`）。
* `hprotC` 取 G3d / G3c 的 CXJD 结构输入 binder 在 `v' = time i⁺`、`z'' = y` 的实例。
binder 块（CXJD 结构输入族）从 G3c `hstayLocStar_of_firstExit_P6SP` 逐字切出，追加 `hwin`、`θ₀`、kernel 帧
records、`hsepT`。结论（eventually）= G4 `hceil` 的单 `n` 体。不用全局 `EventSlabsDerivative`。
生成器 `build-logs/scratch/O-CH11-SLICE-BCBD/gen/gen6.py`。
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

/-- 首末两端指标 / 端点同时搬运（`_P6SB`，PROVED）：`f = f'`、`l = l'`、`HEq x x'` ⇒ 同点 trace，
对应指标处点 HEq。 -/
theorem trace_transport_both_P6SB {H : ObservedHistory.{u}} {f l f' l' : Fin (H.eventCount + 1)}
    {hle : f ≤ l} (hle' : f' ≤ l') {x : (H.stage l).Carrier} (x' : (H.stage l').Carrier)
    (hf : f = f') (hl : l = l') (hx : HEq x x') (A : BackwardPointTrace H f l hle x) :
    ∃ A' : BackwardPointTrace H f' l' hle' x', ∀ (m m' : Fin (H.eventCount + 1)), m = m' →
      ∀ (h1 : f ≤ m) (h2 : m ≤ l) (h1' : f' ≤ m') (h2' : m' ≤ l'),
        HEq (A'.point m' h1' h2') (A.point m h1 h2) := by
  subst hf hl
  obtain rfl := eq_of_heq hx
  refine ⟨A, fun m m' hm _ _ _ _ => ?_⟩
  subst hm
  exact HEq.rfl

/-- `a = time i⁺`、`i⁺ ≤ j⁻` ⇒ `activeStage a = i⁺`（`_P6SB`）。 -/
theorem RetainedCoreHistory.activeStage_eq_succ_P6SB (K : RetainedCoreHistory.{u})
    (i j : Fin K.eventCount) (hl : i.succ ≤ j.castSucc) (a : Icc (0 : ℝ) K.toHistory.horizon)
    (ha : (a : ℝ) = K.time i.succ) : K.toHistory.activeStage a = i.succ := by
  have hlt : i.val + 1 < K.eventCount := by
    have h := Fin.le_iff_val_le_val.mp hl
    simp only [Fin.val_succ, Fin.val_castSucc] at h
    have := j.isLt
    omega
  let e : Fin K.eventCount := ⟨i.val + 1, hlt⟩
  have he : e.castSucc = i.succ := Fin.ext rfl
  have h1 : K.time e.castSucc ≤ (a : ℝ) := by rw [he, ha]
  have h2 : (a : ℝ) < K.time e.succ := by
    rw [ha, ← he]
    exact K.time_strictMono e.castSucc_lt_succ
  rw [K.activeStage_eq_of_mem_slab_P6SB e a h1 h2, he]

/-- `stage i⁺` 在 `time i⁺` 的标量 = event `i` output metric 的标量（指标 HEq 搬运，`_P6SB`）。 -/
theorem scalar_output_of_stage_P6SB (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : m = i.succ) (z : (H.stage m).Carrier)
    (z' : (H.stage i.succ).Carrier) (hz : HEq z z') :
    metricScalarAt (H.stageMetric m (H.time i.succ)) z =
      metricScalarAt (H.event i).outputMetric z' := by
  subst hm
  obtain rfl := eq_of_heq hz
  rw [H.stageMetric_succ_time_C11G]

/-- **cap 出生时刻 trace ceiling（`_P6SB`，PROVED ⇐ CXJD 结构输入族 + `hwin` + (SEP′) 型 `hsepT`）**：
eventually，`yG` 自 `i⁺` 到 `j⁻` 的任意 trace 在 `time i⁺` 的标量 `≤ 2·Qb·R n`（年龄 `≤ θ₀/scale` 的 cap 配置）。 -/
theorem ObservedHistory.capCeiling_of_firstExit_P6SB
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (records : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      GeometricCutoffRecord (K n).toHistory e (q n))
    (hOld : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).toHistory.time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hacc : ∀ n, (q n).modelAccuracy ≤ 1 / 2)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hprotC : ∀ n (v' : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v')
      (hvs : v' ≤ σ n) (z'' : ((K n).toHistory.stageAt (σ n)).Carrier)
      (A : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v')
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) z'')
      (e : Fin (K n).eventCount) (h1 : (K n).toHistory.activeStage (aSeed n) ≤ e.castSucc)
      (h2 : e.succ ≤ (K n).toHistory.activeStage (Tn n))
      (h3 : (K n).toHistory.activeStage v' ≤ e.castSucc)
      (h4 : e.succ ≤ (K n).toHistory.activeStage (σ n))
      (he : T₀ n ≤ (K n).toHistory.time e.succ),
      (∀ (w : Icc (0 : ℝ) (K n).toHistory.horizon) (hw : v' ≤ w) (hwσ : w ≤ σ n),
        (K n).toHistory.time e.succ ≤ (w : ℝ) →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage w) w)
            ((seedTrace n).point ((K n).toHistory.activeStage w)
              ((K n).toHistory.activeStage_mono (hav.trans hw))
              ((K n).toHistory.activeStage_mono (hwσ.trans (hsT n))))
            (A.point ((K n).toHistory.activeStage w) ((K n).toHistory.activeStage_mono hw)
              ((K n).toHistory.activeStage_mono hwσ)) <
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) → ∀ b,
      (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
          ((records n e he).static b).window ''
            {w : standardCapWindow (q n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
          ((records n e he).static b).window ''
            {w : standardCapWindow (q n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {θ₀ : ℝ} {T₀K : ℕ → ℝ} {pK : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (pK n))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      metricScalarAt ((K n).toHistory.event i).outputMetric (A.point i.succ le_rfl hl) ≤
        2 * (max (max 1 Cg) 1 * R n) := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (r / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm0 : (0 : ℝ) < max (Ctime' : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [le_max_right (Ctime' : ℝ) 1]
  set Qb : ℝ := max (max 1 Cg) 1 with hQbdef
  have hQb1 : 1 ≤ Qb := le_max_right _ _
  have hQb0 : 0 < Qb := by linarith
  set T : ℝ := 1 / (2 * max (Ctime' : ℝ) 1) / Qb with hTdef
  have hT0 : 0 < T := div_pos (by positivity) hQb0
  have hT1 : T ≤ 1 := (div_le_one hQb0).2 (hc1.trans hQb1)
  have hstep : 2 * (Ctime' : ℝ) * Qb * T ≤ 1 := by
    have h1 : 2 * (Ctime' : ℝ) * Qb * T = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [h1]
    exact (div_le_one hm0).2 (le_max_left _ _)
  filter_upwards [hwin T hT0, hL.eventually_ge_atTop (max (max (4 * localPropagationRadius C2')
    (2 * (1 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2)) 1)] with n hwn hLn
  intro i hi hl A b hage
  have hsc : 0 < ((recordsK n i hi).static b).neck.scale :=
    ((recordsK n i hi).static b).neck.scale_pos
  have hL4 : 4 * localPropagationRadius C2' ≤ L n :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
  have hL5 : 2 * (1 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2 ≤ L n :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hLn
  have hL6 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hLn
  -- 深度：年龄 ≤ θ₀/scale 且 θ₀·R ≤ T·scale ⇒ σ − time i⁺ ≤ T/R
  have hsep := hsepT n i hi b hl hage
  have hdep : t n - (K n).time i.succ ≤ T / R n := by
    rw [le_div_iff₀ (hR n)]
    have h1 := mul_le_mul_of_nonneg_right hage (hR n).le
    have h2 : θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ * R n =
        θ₀ * R n / ((recordsK n i hi).static b).neck.scale := by
      field_simp
    have h3 : θ₀ * R n / ((recordsK n i hi).static b).neck.scale ≤ T := by
      rw [div_le_iff₀ hsc]
      exact hsep
    linarith
  have htle : (K n).time i.succ ≤ (K n).time (j n).castSucc :=
    (K n).time_strictMono.monotone hl
  have hσt : (σ n : ℝ) = t n := hσ n
  have hjσ : (K n).time (j n).castSucc < (σ n : ℝ) := by rw [hσt]; exact hjt n
  have hTR : T / R n ≤ 1 / R n := div_le_div_of_nonneg_right hT1 (hR n).le
  have haSr : (aSeed n : ℝ) ≤ (K n).time i.succ := by linarith
  let a : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨(K n).time i.succ, (aSeed n).2.1.trans haSr,
      (by linarith : (K n).time i.succ ≤ (σ n : ℝ)).trans (σ n).2.2⟩
  have haval : (a : ℝ) = (K n).time i.succ := rfl
  have haS : aSeed n ≤ a := haSr
  have haσ : a ≤ σ n := show ((K n).time i.succ : ℝ) ≤ σ n by linarith
  have hdepth : (σ n : ℝ) - a ≤ T / R n := by rw [haval, hσt]; exact hdep
  have hLR : 1 / R n ≤ L n ^ 2 / R n :=
    div_le_div_of_nonneg_right (by nlinarith) (hR n).le
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ a := by linarith
  have hRa' : 1 ≤ R n * a := by
    have := mul_le_mul_of_nonneg_left haSr (hR n).le
    rw [haval]
    linarith [hRa n]
  have hact_a : (K n).toHistory.activeStage a = i.succ :=
    (K n).activeStage_eq_succ_P6SB i (j n) hl a haval
  have hact_σ : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6SB (j n) (σ n) hjσ.le (by rw [hσt]; exact htj n)
  have hσlast : (K n).toHistory.activeStage (σ n) < Fin.last (K n).eventCount := by
    rw [hact_σ]
    exact Fin.castSucc_lt_last (j n)
  obtain ⟨A', hA'⟩ := trace_transport_both_P6SB ((K n).toHistory.activeStage_mono haσ) (y n)
    hact_a.symm hact_σ.symm (hyG n).symm A
  have hz : metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
      (y n) ≤ 1 * R n := by
    rw [(K n).scalar_of_incoming_P6X (j n) hact_σ.symm (σ n) (yG n) (y n) (hyG n), hσt, ← hRn n,
      one_mul]
  have hzy : y n ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (1 / Real.sqrt (R n)) := by
    change riemannianEDistOf _ (y n) (y n) < ENNReal.ofReal (1 / Real.sqrt (R n))
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos one_pos (Real.sqrt_pos.mpr (hR n)))
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP
    (Qb := Qb) (R := R n) (Rad := 1) (L := L n) hr hρ hc0 hQb1 (hR1 n) hκdef (by linarith)
    (by linarith)
  have hQb : max (max 1 Cg) 1 ≤ Qb := le_rfl
  have hceil := ObservedHistory.scalar_le_two_mul_crossSlab_ceiling_CXJD (Cball := 1) (Qb := Qb)
    (T := T) (K := Qb * R n / κ ^ 2) (ℓ := κ / Real.sqrt (Qb * R n)) (D := 1) hC2
    (K n).toHistory (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n)
    (y n) (L n) (hR n) (hgood n) hQb hstep haS haσ hσlast haL hdepth hRa' hz A' hℓ hKℓ hℓr hKr
    hKC hℓρ hρL ((hT₀ n).trans haSr) (records n) (hOld n) (hcan n) (hacc n) (hDm n)
    (hprotC n a haS haσ (y n) A') hzy (hdσ n) hnum a le_rfl haσ
  have hpt := hA' i.succ ((K n).toHistory.activeStage a) hact_a.symm le_rfl hl
    ((K n).toHistory.activeStage_mono (le_refl a)) ((K n).toHistory.activeStage_mono haσ)
  rw [scalar_output_of_stage_P6SB (K n).toHistory i hact_a _ _ hpt] at hceil
  exact hceil

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
