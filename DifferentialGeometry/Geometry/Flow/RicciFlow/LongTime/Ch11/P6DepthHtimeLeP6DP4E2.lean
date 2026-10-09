import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthPreP6DP4

/-!
# GAP[htime-boundary] 修法 (i)：driver 种子链的 htime ≤ 孪生（O-CH11-DEPTH4E2 G3，后缀 `_P6DP4E2`）

DEPTH4A anyPos 链的 `htime : 2·r² < Tn` 只在 `earlier_seed_on_half_depth_P6B` 末行用到（推 `2·(r/100)² < v`）。
由 `v ≥ T − r²/2` 与 `r > 0`，非严格 `2r² ≤ T` 已足够（`v ≥ 1.5 r² > 2r²/10⁴`）。本文件把这条链逐字孪生，
只改不等号：
* `earlier_seed_on_half_depth_le_P6DP4E2`（P6SeedShiftP6B 孪生；末行 nlinarith 加 `mul_pos hr hr`）；
* `earlier_seed_on_half_depth_le_C11G3_P6DP4E2` / `earlier_seed_small_on_half_depth_le_P6DP4E2`
  （Dist/EarlierSeedC11G3 孪生）；
* `hdistC_anyPos_le_P6DP4E2` /
  `hwitC_hderivC_of_hPN_anyPos_le_P6DP4E2`（P6DepthPreP6DP4 (b1)/(b2) 孪生）。
源段 sha256 由生成器 `build-logs/scratch/O-CH11-DEPTH4E2/gen/gen_g3.py` 断言并打印。PROVED，无新数学，无新 binder。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **seed shift**（L5 的几何核心）：种子 `(p, t, r)`（`A > 1`）在任意 `v ∈ [t − r²/2, t]` 给出以
种子 trace 点 `O_v` 为中心、半径 `R = r/100` 的种子：`hasSmallParabolicCurvature H v O_v R`、
`vol B(O_v, R) ≥ (A⁻¹ e⁻⁵⁷/512) R³`，且 `2R² < v`。
（htime ≤ 孪生，`_P6DP4E2`：原文逐字，只把 `2·r² < T` 改为 `2·r² ≤ T`。） -/
theorem earlier_seed_on_half_depth_le_P6DP4E2
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r A : ℝ)
    (htime : 2 * r ^ 2 ≤ (T : ℝ))
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage T) T) p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        ballVolume (H.stageMetric (H.activeStage v) v) O R ∧
      2 * R ^ 2 < (v : ℝ) := by
  classical
  intro O R
  have hr : 0 < r := hseed.1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hrr : r ≤ Real.sqrt 3 * r := le_mul_of_one_le_left hr.le hsqrt
  have hball : H.isParabolicallyRmControlledBall T p r := by
    obtain ⟨_hr, a, hat, ha, htraces⟩ := hseed
    refine ⟨hr, a, hat, ha, ?_⟩
    intro x hx
    obtain ⟨B, hB⟩ := htraces x hx
    have hpow : r ^ 4 ≤ (Real.sqrt 3 * r) ^ 4 := pow_le_pow_left₀ hr.le hrr 4
    refine ⟨B, ?_, ?_⟩
    · intro u hau hut
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hB.1 u hau hut)
    · intro i hi hl
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hB.2 i hi hl)
  let clock : ℝ := Real.sqrt ((T : ℝ) - v)
  have hclockNonneg : 0 ≤ clock := Real.sqrt_nonneg _
  have hclockSq : clock ^ 2 = (T : ℝ) - v :=
    Real.sq_sqrt (sub_nonneg.mpr (show (v : ℝ) ≤ T from hvT))
  have hclockLe : clock ≤ r := (sq_le_sq₀ hclockNonneg hr.le).mp (by
    rw [hclockSq]
    nlinarith [sq_nonneg r])
  have hclockEq : (v : ℝ) = (T : ℝ) - clock ^ 2 := by rw [hclockSq]; ring
  have hratio : clock ^ 2 / r ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    rw [hclockSq]
    linarith
  have hdistortion : Real.exp (2 * (3 / r ^ 2) * clock ^ 2) ≤ (10 : ℝ) ^ 2 := by
    have hcoef : 2 * (3 / r ^ 2) * clock ^ 2 ≤ 3 := by
      calc
        _ = 6 * (clock ^ 2 / r ^ 2) := by ring
        _ ≤ 6 * (1 / 2) := mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ = 3 := by norm_num
    have heq : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [show (3 : ℝ) = (1 + 1) + 1 by norm_num, Real.exp_add, Real.exp_add]
      ring
    have he2 : (Real.exp 1) ^ 2 < 9 := by
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have he3 : (Real.exp 1) ^ 3 < 27 := by
      have hmul := mul_lt_mul_of_pos_right he2 (Real.exp_pos 1)
      have hnine := mul_lt_mul_of_pos_left Real.exp_one_lt_three (by norm_num : (0 : ℝ) < 9)
      nlinarith only [hmul, hnine]
    refine le_of_lt ?_
    calc
      _ ≤ Real.exp 3 := Real.exp_le_exp.mpr hcoef
      _ < 27 := by rwa [heq]
      _ ≤ (10 : ℝ) ^ 2 := by norm_num
  have hmargin : R < (3 * r / 4) / (10 : ℝ) := by dsimp only [R]; linarith
  obtain ⟨b0, hb0v, hb0, htraces⟩ :=
    H.exists_past_seed_core_traces_P6B T v hvT p r clock hball
      hclockNonneg hclockLe hclockEq
      (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT))
      R 10 (by norm_num) hdistortion hmargin
  have hb0a : b0 = aSeed := Subtype.ext (hb0.trans hclock.symm)
  subst b0
  have hstart : (aSeed : ℝ) ≤ (v : ℝ) - R ^ 2 := by
    rw [hclock]
    dsimp only [R]
    nlinarith [sq_nonneg r]
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨(v : ℝ) - R ^ 2, aSeed.property.1.trans hstart,
      (sub_le_self _ (sq_nonneg R)).trans v.property.2⟩
  have hab : aSeed ≤ b := hstart
  have hbv : b ≤ v := sub_le_self _ (sq_nonneg R)
  have hstrongScale : Real.sqrt 3 * R ≤ r := by
    have hsqrtLe : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    dsimp only [R]
    nlinarith [mul_le_mul_of_nonneg_right hsqrtLe hr.le]
  have hsmall : hasSmallParabolicCurvature H v O R := by
    refine ⟨hR, b, hbv, rfl, ?_⟩
    intro y hy
    have hO :
        (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT)).point
          (H.activeStage v) le_rfl (H.activeStage_mono hvT) = O := rfl
    have hphysical : riemannianEDistOf
        (H.stageMetric (H.activeStage v) ((T : ℝ) - clock ^ 2))
        ((seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT)).point
          (H.activeStage v) le_rfl (H.activeStage_mono hvT)) y < ENNReal.ofReal R := by
      rw [← hclockEq, hO]
      exact hy
    obtain ⟨B, hB⟩ := htraces y hphysical
    exact ⟨B.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbv),
      hB.restrictFirst B (by positivity) hstrongScale hab hbv⟩
  refine ⟨hsmall, ?_, ?_⟩
  · have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (r / 4) := by
      change riemannianEDistOf _ p p < ENNReal.ofReal (r / 4)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have hvStart : (T : ℝ) - r ^ 2 ≤ (v : ℝ) := by rw [← hclock]; exact hav
    have hvol := (volume_lower_along_nearby_trace_P6B hseed hvolume hp v hvT hvStart).2
      (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT))
      R hR (by dsimp only [R]; linarith)
    exact hvol
  · dsimp only [R]
    nlinarith [sq_nonneg r, mul_pos hr hr]

/-- **半深度种子回推，带新时钟与新 trace（`_C11G3`）**：种子 `(p, T, r)`（时钟 `aSeed = T − r²`、
`2r² < T`、体积 `≥ A⁻¹ r³`、种子 trace）在 `v ∈ [T − r²/2, T]`（`aSeed ≤ v`）给出：新时钟 `a' = v − (r/100)²`
（`aSeed ≤ a' ≤ v`）、新 trace（`a'` → `v`，终点 `O_v := seedTrace.point v`，逐点等于原 trace）、
新种子 `hasSmallParabolicCurvature H v O_v (r/100)`、体积 `≥ (A⁻¹ e⁻⁵⁷/512)(r/100)³`、`2(r/100)² < v`。
（htime ≤ 孪生，`_P6DP4E2`：原文逐字，只把 `2·r² < T` 改为 `2·r² ≤ T`。） -/
theorem earlier_seed_on_half_depth_le_C11G3_P6DP4E2
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r A : ℝ)
    (htime : 2 * r ^ 2 ≤ (T : ℝ)) (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage T) T) p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    ∃ (a' : Icc (0 : ℝ) H.horizon) (haa' : aSeed ≤ a') (hav' : a' ≤ v)
      (seedTrace' : BackwardPointTrace H (H.activeStage a') (H.activeStage v)
        (H.activeStage_mono hav') O),
      (a' : ℝ) = (v : ℝ) - R ^ 2 ∧
      hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        ballVolume (H.stageMetric (H.activeStage v) v) O R ∧
      2 * R ^ 2 < (v : ℝ) ∧
      ∀ (u : Icc (0 : ℝ) H.horizon) (hau : a' ≤ u) (huv : u ≤ v),
        seedTrace'.point (H.activeStage u) (H.activeStage_mono hau) (H.activeStage_mono huv) =
          seedTrace.point (H.activeStage u) (H.activeStage_mono (haa'.trans hau))
            (H.activeStage_mono (huv.trans hvT)) := by
  intro O R
  have h : hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        ballVolume (H.stageMetric (H.activeStage v) v) O R ∧ 2 * R ^ 2 < (v : ℝ) :=
    earlier_seed_on_half_depth_le_P6DP4E2 haT p r A htime hclock hseed hvolume seedTrace v hav
      hvT hv
  obtain ⟨hsmall, hvol, hR2⟩ := h
  have hr : 0 < r := hseed.1
  have hRsq : R ^ 2 = r ^ 2 / 10000 := by
    dsimp only [R]
    ring
  have hv0 : 0 ≤ (v : ℝ) - R ^ 2 := by
    have := sq_nonneg R
    linarith
  let a' : Icc (0 : ℝ) H.horizon :=
    ⟨(v : ℝ) - R ^ 2, hv0, (sub_le_self _ (sq_nonneg R)).trans v.2.2⟩
  have haa' : aSeed ≤ a' := by
    change (aSeed : ℝ) ≤ (v : ℝ) - R ^ 2
    rw [hclock, hRsq]
    nlinarith [sq_nonneg r]
  have hav' : a' ≤ v := sub_le_self _ (sq_nonneg R)
  exact ⟨a', haa', hav', (seedTrace.restrictFirst (H.activeStage_mono haa')
      (H.activeStage_mono (hav'.trans hvT))).restrictLast (H.activeStage_mono hav')
      (H.activeStage_mono hvT), rfl, hsmall, hvol, hR2, fun u hau huv => rfl⟩

/-- **体积无关版（`_C11G3`）**：`hasSmallParabolicCurvature` 种子的半深度回推（新时钟 / 新 trace / 种子
`(O_v, r/100)` / `2(r/100)² < v`），不要体积前提（取 `A := 0`，`0⁻¹ = 0` 使体积前提平凡）。
（htime ≤ 孪生，`_P6DP4E2`：原文逐字，只把 `2·r² < T` 改为 `2·r² ≤ T`。） -/
theorem earlier_seed_small_on_half_depth_le_P6DP4E2
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r : ℝ)
    (htime : 2 * r ^ 2 ≤ (T : ℝ)) (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    ∃ (a' : Icc (0 : ℝ) H.horizon) (haa' : aSeed ≤ a') (hav' : a' ≤ v)
      (seedTrace' : BackwardPointTrace H (H.activeStage a') (H.activeStage v)
        (H.activeStage_mono hav') O),
      (a' : ℝ) = (v : ℝ) - R ^ 2 ∧ hasSmallParabolicCurvature H v O R ∧
      2 * R ^ 2 < (v : ℝ) ∧
      ∀ (u : Icc (0 : ℝ) H.horizon) (hau : a' ≤ u) (huv : u ≤ v),
        seedTrace'.point (H.activeStage u) (H.activeStage_mono hau) (H.activeStage_mono huv) =
          seedTrace.point (H.activeStage u) (H.activeStage_mono (haa'.trans hau))
            (H.activeStage_mono (huv.trans hvT)) := by
  intro O R
  obtain ⟨a', haa', hav', tr, hclk, hsmall, -, hR2, hpt⟩ :=
    earlier_seed_on_half_depth_le_C11G3_P6DP4E2 haT p r 0 htime hclock hseed (by simp) seedTrace
      v hav hvT hv
  exact ⟨a', haa', hav', tr, hclk, hsmall, hR2, hpt⟩

end GC.LongTime.Ch11

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **(b1) 位置无关 hdistC（`_P6DP4`）**：`hdistC_final_P6DC2`（P6DistCFinalP6DC2:125）逐字，删去其未用的
final 位置参数 `t` / `_htl` / `_htK` / `σ ≤ t`（DC2 证明 `intro K _t _htl _htK … _hσt` 不消费它们；G0 孪生
`hdistC_of_traced_final_P6DC2` 本即无位置）。(SEP) 对全部 event。证明逐字。
（htime ≤ 孪生，`_P6DP4E2`：原文逐字，只把 `2·r² < T` 改为 `2·r² ≤ T`。） -/
theorem hdistC_anyPos_le_P6DP4E2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)),
      (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) → (∀ n, 2 * r n ^ 2 ≤ (Tn n : ℝ)) →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_final_P6DC2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K Kh σ y R r L Tn aSeed haT hsT has pT seedTrace hhalf htime hR hL
    hsmallK hclockK hRr a₀ ha₀ hpinK q T₀ recordsK hcanK hacc0 hm hDm hsepWK hT₀ φ hφ D T Kc hD hT
    hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hshift := fun n => GC.LongTime.Ch11.earlier_seed_small_on_half_depth_le_P6DP4E2 (haT n)
    (pT n)
    (r n) (htime n) (hclockK n) (hsmallK n) (seedTrace n) (σ n) (has n) (hsT n) (hhalf n)
  choose a' haa' hav' tr' hclk' hsm' hR2' hpt' using hshift
  have hRr' : Tendsto (fun n => R n * (r n / 100) ^ 2) atTop atTop := by
    refine ((hRr.atTop_div_const (by norm_num : (0 : ℝ) < 10000)).congr fun n => ?_)
    ring
  have hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (a' n : ℝ) ≤ (σ n : ℝ) - T / R n := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop T] with n hRn hn
    rw [hclk' n]
    have : T / R n ≤ (r n / 100) ^ 2 := by
      rw [div_le_iff₀ hRn]
      linarith
    linarith
  have hlate' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop (T + 1)] with n hRn hn
    have h1 : R n * (2 * (r n / 100) ^ 2) < R n * (σ n : ℝ) :=
      mul_lt_mul_of_pos_left (hR2' n) hRn
    have h2 : R n * ((σ n : ℝ) - T / R n) = R n * (σ n : ℝ) - T := by
      field_simp
    rw [h2]
    linarith
  have hmain := hC K σ y R (fun n => r n / 100) L σ a' hav' (fun n => le_rfl) hav'
    (fun n => (seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
      ((Kh n).activeStage_mono (hsT n))) tr' hR hL hsm' hclk' hRr' ha₀ hpinK q T₀ recordsK
    hcanK hacc0 hm hDm hwin' hlate' hsepWK hT₀ φ hφ D T Kc hD hT hKc htr
  filter_upwards [hmain, Filter.Eventually.filter_mono hφt (hwin' T hT)] with n hn hw
  intro x hx v hav hvs hvT tr
  have hav'' : a' n ≤ v := by
    have h1 : (a' n : ℝ) ≤ v := hw.trans hvT
    exact h1
  have h := hn x hx v hav'' hvs hvT tr
  rw [hpt' n v hav'' hvs, hpt' n (σ n) (hav' n) le_rfl] at h
  exact h

/-- **(b2) 位置无关的条件形 hwitC / hderivC（`_P6DP4`，PROVISIONAL[hsepWK（全部 event）, hpin]）**：
DEPTH1 final 支（`hwitC_hderivC_of_hPN_final_C11G3`）删去位置前提的同构版，内部改调 (b1)；对任意 σ
（含 σ = horizon）成立。用于 `time last ≤ σ` 的子列（此时全部 event 都在 σ 之前）。
（htime ≤ 孪生，`_P6DP4E2`：原文逐字，只把 `2·r² < T` 改为 `2·r² ≤ T`。） -/
theorem hwitC_hderivC_of_hPN_anyPos_le_P6DP4E2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
      (K : ℕ → RetainedCoreHistory.{u}),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory
        ((K n).toHistory.activeStage (aSeed n)) ((K n).toHistory.activeStage (Tn n))
        ((K n).toHistory.activeStage_mono (haT n)) (pT n)),
      (∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) →
      (∀ᶠ n in atTop, 2 * r n ^ 2 ≤ (Tn n : ℝ)) →
      (∀ n, 0 < R n) → Tendsto L atTop atTop →
      (∀ᶠ n in atTop,
        GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n)) →
      (∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ᶠ n in atTop, ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
        (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ᶠ n in atTop, (q n).modelAccuracy ≤ ε₀) → (∀ᶠ n in atTop, 2 ≤ (q n).modelOrder) →
      (∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart eps) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_anyPos_le_P6DP4E2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' K Kh σ y R r L Tn aSeed haT hsT has pT seedTrace
    hhalf htime hR hL hsmall hclock hRr a₀ ha₀ hpin q T₀ recordsK hcan hacc hord hrad hsep hT₀
    hgood hwin
  refine ObservedHistory.hwitC_hderivC_of_hdistC_P6M2 (eps := eps) (C1' := C1') (C2' := C2')
    (Ctime' := Ctime') Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR hL hgood hwin ?_
  intro φ hφ D T Kc hD hT hKc htr
  obtain ⟨N, hN⟩ := exists_shift_forall_of_eventually_P6HQ (hhalf.and (htime.and (hsmall.and
    (hclock.and (hpin.and (hcan.and (hacc.and (hord.and hrad))))))))
  have hsh : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  refine eventually_map_of_shift_P6HQ hφ N (fun h => ?_) htr
  exact hC (fun n => K (n + N)) (fun n => σ (n + N)) (fun n => y (n + N)) (fun n => R (n + N))
    (fun n => r (n + N)) (fun n => L (n + N)) (fun n => Tn (n + N)) (fun n => aSeed (n + N))
    (fun n => haT (n + N)) (fun n => hsT (n + N)) (fun n => has (n + N)) (fun n => pT (n + N))
    (fun n => seedTrace (n + N)) (fun n => (hN n).1) (fun n => (hN n).2.1)
    (Filter.Eventually.of_forall fun n => hR (n + N)) (hL.comp hsh)
    (fun n => (hN n).2.2.1) (fun n => (hN n).2.2.2.1) (hRr.comp hsh)
    ha₀ (fun n => (hN n).2.2.2.2.1) (fun n => q (n + N)) (fun n => T₀ (n + N))
    (fun n => recordsK (n + N)) (fun n => (hN n).2.2.2.2.2.1)
    (fun n => (hN n).2.2.2.2.2.2.1) (fun n => (hN n).2.2.2.2.2.2.2.1)
    (fun n => (hN n).2.2.2.2.2.2.2.2) (fun T hT C hC => hsh.eventually (hsep T hT C hC))
    (fun T hT => hsh.eventually (hT₀ T hT)) (fun m => φ (m + N) - N)
    (strictMono_shiftSub_P6HQ hφ N) D T Kc hD hT hKc h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
