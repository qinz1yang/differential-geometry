import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841E2EFreshC11SW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X

/-!
# fresh-activation obligation 登记 + CanonicalLateCore 的 R1/R2/R3 分解（O-CH11-SEEDWIN-P G4）

lead 13:1x 裁定：A12′ 的 hP6b 走 S15 r̄-free（`CanonicalLateCore_P6X`）路线 ⇒ `hfresh` 需要。
* `FreshActivation_C11SW`：**PROVISIONAL 显式 obligation**，逐字 = G2/G3 的 `hfresh`
  （窗口 `[t − r²/2, t]` 跨 activation `a_k = (5/6)·3^k` 时旧块半径 `nr a_k ≤ r`）；
  inhabitant `freshActivation_of_large_C11SW`（`r ≥ 1`）。
* `seedWin_of_freshActivation_C11SW` / `…_native_C11SW`（S15 路线所需形，CXCW 的 `hseedWin` 逐字）与
  逆向 `freshActivation_of_seedWin_C11SW`：band 常值下 obligation 与 hseedWin 等价（模 ceiling），
  即 residual 恰是 crossing 支，没有被放大或缩小。
* `canonicalLateCore_of_regimes_C11SW`：`K₁ ≥ 2` 时 seed 三分——R1 `nr(t − r²/2) ≤ r`（scaled core，
  反证序列逐 n 带 hseedWin，κ 线 CXCW 直接可用）、R2 `r ≤ nr t`（`hcan` 直接给 witness）、
  R3 `nr t < r`、窗口跨 `a_k` 且 `r < nr a_k`（fresh core = 本 obligation 的 seed 级形）。
* consumer `exists_pre841Data_of_retention_freshActivation_C11SW`（接 `Pre841E2EFreshC11SW`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **fresh-activation obligation（PROVISIONAL）**：最终，seed 窗 `[t n − r n²/2, t n)` 含 activation
`a_k = (5/6)·3^k` 时，旧块半径 `nr a_k ≤ r n`。逐字 = `hfresh`（G2 `eventually_seedWin_of_fresh_C11SW`）。 -/
def FreshActivation_C11SW (nr : ℝ → ℝ) (t r : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ k : ℕ, t n - r n ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k →
    (5 / 6 : ℝ) * 3 ^ k < t n → nr ((5 / 6 : ℝ) * 3 ^ k) ≤ r n

/-- **inhabitant**：`nr ≤ 1` 于 `Ici 0` 且最终 `1 ≤ r` ⇒ obligation 成立（hband 路线的情形）。 -/
theorem freshActivation_of_large_C11SW {nr : ℝ → ℝ} (hnr1 : ∀ s, 0 ≤ s → nr s ≤ 1)
    {t r : ℕ → ℝ} (hlarge : ∀ᶠ n in atTop, 1 ≤ r n) : FreshActivation_C11SW nr t r := by
  filter_upwards [hlarge] with n hn
  intro k _ _
  exact (hnr1 _ (by positivity)).trans hn

/-- 编译的 inhabitant 实例：`nr ≡ 1`、`r ≡ 1`。 -/
example : FreshActivation_C11SW (fun _ => 1) (fun n => (n : ℝ)) (fun _ => 1) :=
  freshActivation_of_large_C11SW (fun _ _ => le_rfl) (Eventually.of_forall fun _ => le_rfl)

/-- **obligation ⇒ hseedWin**（band 常值 + `t → ∞` + `2r² < t` + 最终 `nr t ≤ r`）。 -/
theorem seedWin_of_freshActivation_C11SW {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    {t r : ℕ → ℝ} (hlate : Tendsto t atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < t n)
    (hle : ∀ᶠ n in atTop, nr (t n) ≤ r n) (hfa : FreshActivation_C11SW nr t r) :
    ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n :=
  eventually_seedWin_of_fresh_C11SW hconst hlate htime hle hfa

/-- **逆向：hseedWin ⇒ obligation**（band 常值 + `t → ∞` + `2r² < t`）：crossing `a_k` 时
`t − r²/2 ∈ (a_{k−1}, a_k]`，故 `nr a_k = nr (t − r²/2) ≤ r`。obligation 恰是 hseedWin 的 crossing 支。 -/
theorem freshActivation_of_seedWin_C11SW {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    {t r : ℕ → ℝ} (hlate : Tendsto t atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < t n)
    (hseed : ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n) : FreshActivation_C11SW nr t r := by
  filter_upwards [hseed, hlate.eventually_gt_atTop (5 / 2)] with n hn hT
  intro k hk1 hk2
  have ht := htime n
  cases k with
  | zero =>
    exfalso
    rw [pow_zero, mul_one] at hk1
    nlinarith [sq_nonneg (r n)]
  | succ j =>
    have hp : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
    have hlow : (5 / 6 : ℝ) * 3 ^ j < t n - r n ^ 2 / 2 := by
      rw [pow_succ] at hk2
      nlinarith [sq_nonneg (r n)]
    have hjj : (5 / 6 : ℝ) * 3 ^ j < (5 / 6 : ℝ) * 3 ^ (j + 1) := by
      rw [pow_succ]
      nlinarith
    rw [hconst j _ hjj le_rfl, ← hconst j _ hlow hk1]
    exact hn

/-- **S15 路线所需形**：native data `N` 的 `nr = N.params.neckRadius`、`Icc` 值 seed 时刻；band 常值
（G3a 导出）+ ceiling `R ≤ nr(t)⁻²` + `hradii` + obligation ⇒ CXCW 的 `hseedWin` 逐字。 -/
theorem seedWin_of_freshActivation_native_C11SW {H : ℕ → ObservedHistory.{u}}
    (N : Pre841NativeData_C11K H) {rad : ℕ → ℝ}
    (hband : ∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
      N.params.neckRadius w = rad (k + 1))
    (t : ∀ n, Icc (0 : ℝ) (H n).horizon) {r R : ℕ → ℝ}
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hRle : ∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hfa : FreshActivation_C11SW N.params.neckRadius (fun n => (t n : ℝ)) r) :
    ∀ᶠ n in atTop, N.params.neckRadius ((t n : ℝ) - r n ^ 2 / 2) ≤ r n :=
  seedWin_of_freshActivation_C11SW (c := fun k => rad (k + 1)) hband hlate htime
    (eventually_native_le_of_ceiling_C11SW (t := fun n => (t n : ℝ))
      (fun n => N.params.neckRadius_pos _ (t n).2.1) hRle hradii) hfa

/-- **R1/R2/R3 分解**：`nr` band 常值、`hcan`（`R > nr(t)⁻²` ⇒ witness，即 `N.canonical` 形）；
R1 = scaled core（多前提 `nr(t − r²/2) ≤ r`），R3 = fresh core（多前提 `nr t < r` 与
"窗口跨 `a_k` 且 `r < nr a_k`"）⇒ `CanonicalLateCore_P6X`。R2（`r ≤ nr t`）由 `hcan` 闭合。 -/
theorem canonicalLateCore_of_regimes_C11SW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    (hcan : ∀ n (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (nr t ^ 2)⁻¹ < metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) x →
      ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hR1 : ∀ A : ℝ, 0 < A → ∃ K1 T : ℝ, 0 < K1 ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → nr ((t : ℝ) - r ^ 2 / 2) ≤ r →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K1 * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
            (H.stageMetric (H.activeStage t) t) ε C1 C2 y, W.capTubeHasNeckChart ε)
    (hR3 : ∀ A : ℝ, 0 < A → ∃ K1 T : ℝ, 0 < K1 ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → nr t < r →
        (∃ k : ℕ, (t : ℝ) - r ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k ∧ (5 / 6 : ℝ) * 3 ^ k < (t : ℝ) ∧
          r < nr ((5 / 6 : ℝ) * 3 ^ k)) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K1 * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
            (H.stageMetric (H.activeStage t) t) ε C1 C2 y, W.capTubeHasNeckChart ε) :
    CanonicalLateCore_P6X F ε C1 C2 := by
  intro A hA
  obtain ⟨K₁, T₁, -, hT₁, h1⟩ := hR1 A hA
  obtain ⟨K₃, T₃, -, hT₃, h3⟩ := hR3 A hA
  refine ⟨max (max K₁ K₃) 2, max (max T₁ T₃) 3, by positivity, by positivity,
    fun n t p r hT ht hs hv y hy hK => ?_⟩
  have hr : 0 < r := hs.1
  have hrinv : 0 < (r ^ 2)⁻¹ := by positivity
  have hT1 : T₁ ≤ (t : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hT3 : T₃ ≤ (t : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hT5 : (5 / 2 : ℝ) < (t : ℝ) := by linarith [(le_max_right (max T₁ T₃) 3).trans hT]
  have hK1 : K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt _ y := (mul_le_mul_of_nonneg_right
    ((le_max_left _ _).trans (le_max_left _ _)) hrinv.le).trans hK
  have hK3 : K₃ * (r ^ 2)⁻¹ ≤ metricScalarAt _ y := (mul_le_mul_of_nonneg_right
    ((le_max_right _ _).trans (le_max_left _ _)) hrinv.le).trans hK
  have hK2 : 2 * (r ^ 2)⁻¹ ≤ metricScalarAt _ y :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hrinv.le).trans hK
  by_cases hw : nr ((t : ℝ) - r ^ 2 / 2) ≤ r
  · exact h1 n t p r hT1 ht hw hs hv y hy hK1
  by_cases hle : r ≤ nr t
  · refine hcan n t y ?_
    have hsq : r ^ 2 ≤ nr t ^ 2 := pow_le_pow_left₀ hr.le hle 2
    have hinv : (nr t ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
    linarith
  · have hlt : nr t < r := lt_of_not_ge hle
    have hgt : r < nr ((t : ℝ) - r ^ 2 / 2) := lt_of_not_ge hw
    rcases window_value_C11SW hconst ht hT5 with heq | ⟨k, hk1, hk2, hk3⟩
    · rw [heq] at hgt
      exact absurd hlt (not_lt.mpr hgt.le)
    · exact h3 n t p r hT3 ht hlt ⟨k, hk1, hk2, hk3 ▸ hgt⟩ hs hv y hy hK3

/-- **consumer（S15 路线所需形）**：`exists_pre841Data_of_retention_fresh_C11SW` 的 `hfresh` 位
以具名 obligation `FreshActivation_C11SW` 给出（逐字同一命题，`Iff.rfl` 级）；其余前提逐字同 CXCW
bridge。 -/
theorem exists_pre841Data_of_retention_freshActivation_C11SW (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P →
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
      (∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹) →
      FreshActivation_C11SW N.params.neckRadius (fun n => (t n : ℝ)) r →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) :=
  exists_pre841Data_of_retention_fresh_C11SW P g

end GC.LongTime.Ch11
