import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN

/-!
# diagonal (CWS) / hnotK 的截断孪生（O-CH11-KTRUNC2c，后缀 `_P6KT2c`）

`cws_uniform_of_diagonal_P6SN`（P6CwsUniformP6SN:61）与 `hnotK_of_diagonal_cws_P6SN`（:170）只用
`j' < j n` 的 slab（终点 `time j'.succ`）和当前 slab 到 `t n` 的导数界。截断孪生：hslabK 换成
KTRUNC1 / KTRUNC2 截断形（终点 `min (time j.succ) (tK n)`，`tK` 与 `Q T₀` 同层隐式），并加
`(∀ n, t n ≤ tK n)`。RerunEvent8 V（P6RerunEvent8NoJ10P6JB:566）的截断孪生需要它（hgapJ8 J9 截断后
无全形 hslabK）。生成器 `build-logs/scratch/O-CH11-KTRUNC2c/gen/gen_cws.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`cws_uniform_of_diagonal_P6SN` 的截断孪生（`_P6KT2c`，PROVED）**：hslabK 换截断形
`DerivativeBoundBefore … (min (time j.succ) (tK n))`，其后加 `(∀ n, t n ≤ tK n)`；证明只改 `hder` / `hcur`
两处（`j' < j n` 的 slab 终点 `time j'.succ ≤ time (j n).castSucc < t n ≤ tK n`；当前 slab 到 `t n ≤ min`）。 -/
theorem cws_uniform_of_diagonal_T_P6KT2c :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (∀ n, (K n).time (j n).castSucc < t n) → (∀ n, t n < (K n).time (j n).succ) →
      ∀ {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
        {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) →
      (∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore C (Q n)
          (min ((K n).time j.succ) (tK n))) →
      (∀ n, t n ≤ tK n) →
      (∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc) (z : ((K n).stage (j n).castSucc).Carrier)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl z)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
        ‖x.val‖ < ((n : ℝ) + 1) + 1 →
        t n - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        c * ((recordsK n i hi).static b).neck.scale ≤
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z := by
  obtain ⟨c, hc, hB⟩ :=
    RetainedCoreHistory.exists_scalar_lower_bound_of_cap_window_trace_late_P6LL.{u}
  refine ⟨c, hc, fun C => ?_⟩
  have hθ0 : ∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) := fun n => by
    have : (1 : ℝ) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hθ1 : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) < 1 := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  choose Cb hCb h2 using fun n : ℕ => hB (1 - 1 / ((n : ℝ) + 2)) (hθ0 n) (hθ1 n) C
  choose Rn hRn m₀ hm₀ ζ δ₀ hζ hζh hδ h4 using fun n : ℕ => h2 n ((n : ℝ) + 1) (by positivity)
  refine ⟨fun n => min (Cb n) (1 / ((n : ℝ) + 1) ^ 2), fun n => max (Rn n) ((n : ℝ) + 1),
    fun n => min (ζ n) (1 / ((n : ℝ) + 1)), fun n => min (δ₀ n) (1 / ((n : ℝ) + 1)),
    fun n => max (m₀ n) (n + 2), fun n => ⟨lt_min (hCb n) (by positivity), min_le_right _ _⟩,
    fun n => ⟨lt_min (hζ n) (by positivity), min_le_right _ _⟩,
    fun n => ⟨lt_min (hδ n) (by positivity), min_le_right _ _⟩,
    fun n => le_max_right _ _, fun n => le_max_right _ _, ?_⟩
  intro K j t hjt htj Q T₀ tK p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK htK
    hbirth hbirthA n i hi hl z A b x hx hxn hage
  set q := ((recordsK n i hi).static b).neck.scale with hqdef
  have hq : 0 < q := ((recordsK n i hi).static b).neck.scale_pos
  have hjc : (K n).time i.succ ≤ (K n).time (j n).castSucc := (K n).time_strictMono.monotone hl
  have hage0 : 0 ≤ t n - (K n).time i.succ := by linarith [hjt n]
  have hqage : q * (t n - (K n).time i.succ) ≤ 1 - 1 / ((n : ℝ) + 2) := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [show q * ((1 - 1 / ((n : ℝ) + 2)) * q⁻¹) = 1 - 1 / ((n : ℝ) + 2) by
      field_simp] at h1
  have hqcan : 0 < max (Q n) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hder : (K n).EventSlabsDerivative C (max (Q n) 1) (j n).castSucc :=
    fun j' hj' => derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _)
      (((K n).toHistory.event j').incoming.derivativeBoundBefore_mono
        (le_min le_rfl (((K n).time_strictMono.monotone (Fin.castSucc_lt_iff_succ_le.mp hj')).trans
          ((hjt n).le.trans (htK n)))) (hslabK n j'))
  have hcur : ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (max (Q n) 1)
      (t n) :=
    ((K n).toHistory.event (j n)).incoming.derivativeBoundBefore_mono
      (le_min (htj n).le (htK n))
      (derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _) (hslabK n (j n)))
  have hbirth' : max (Q n) 1 ≤ Cb n * q :=
    (hbirth n i hi b).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hmain := h4 n (K n) (recordsK n) (hcanK n) ((le_max_left _ _).trans (hrad n))
    (le_trans (le_max_left _ _) (hord n)) ((hacc n).trans (min_le_left _ _)) (recordsF n)
    (δ₀ n) (fun i' hi' => (hδF n i' hi').trans (min_le_left _ _)) le_rfl (max (Q n) 1) a₀
    (1 - 1 / ((n : ℝ) + 2)) hqcan le_rfl (fun x => (hHI n x).1) (fun x => (hHI n x).2)
    (j n).castSucc ((K n).time (j n).succ) ((K n).toHistory.event (j n)).incoming
    ((K n).event_initial (j n)) hder (t n) (hjt n) (htj n) hcur i hi hl z A b x hx hage hxn
    hbirth' (hbirthA n i hi b)
  exact scalar_ge_of_age_factor_P6SN hc hq hage0
    (lt_of_le_of_lt hqage (hθ1 n)) hmain

/-- **`hnotK_of_diagonal_cws_P6SN` 的截断孪生（`_P6KT2c`，PROVED）**：同上两处陈述改动；证明逐字
（diagonal 包换 `cws_uniform_of_diagonal_T_P6KT2c`）。RerunEvent8 V 截断孪生经 `t := c·σ`、`tK := Tno`
（`c·σ ≤ Tno` = 证明内 `htTO`）消费。 -/
theorem hnotK_of_diagonal_cws_T_P6KT2c :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (∀ n, (K n).time (j n).castSucc < t n) → (∀ n, t n < (K n).time (j n).succ) →
      ∀ {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
        {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) →
      (∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore C (Q n)
          (min ((K n).time j.succ) (tK n))) →
      (∀ n, t n ≤ tK n) →
      (∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      ∀ {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} {R : ℕ → ℝ},
      (∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < c * ((recordsK n i hi).static b).neck.scale) →
      ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
          (hl : i.succ ≤ (j n).castSucc)
          (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
          (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (p n).modelRadius),
          A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            t n - (K n).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hall⟩ := cws_uniform_of_diagonal_T_P6KT2c.{u}
  refine ⟨c, hc, fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, hdiag⟩ := hall C
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, ?_⟩
  intro K j t hjt htj Q T₀ tK p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK htK
    hbirth hbirthA yG R hRn' hsep
  exact RetainedCoreHistory.hnotK_of_capWindowScalar_P6R2 recordsK hRn'
    (hdiag hjt htj recordsF hHI hcanK hδF hacc hrad hord hslabK htK hbirth
      hbirthA) hsep

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
