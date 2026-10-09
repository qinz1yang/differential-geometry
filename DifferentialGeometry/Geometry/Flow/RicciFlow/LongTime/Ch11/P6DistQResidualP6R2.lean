import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.HdistCondAnySeedC11G3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841DefsC11K

/-!
# `hdistQ` 的残余义务 = (TR) + (SEP)（O-CH11-P6REST2 G3，后缀 `_P6R2`）

closed 主形 `false_of_selection_eventSlab_late_closed_Cg_P6S3` 的全局 `hdistQ`（余量 `L/4`）由 HDISTC
`hdistC_of_traced_anySeed_C11G3`（`L := L/4`、`φ := id`）给出。本文件把 HDISTC 的前提逐项对到主形 /
G1 retained selection / 链上种子数据，只留下两条**真实分析义务**，以显式 binder 形写出（不包装成
producer）：

* **(TR)** `htr`：`∀ D T > 0, ∃ Kc ≥ 0, ∀ᶠ n, isTracedRegion σ y (2D/√R) (T/R) (Kc R)`（全局 traced
  region = BCAD 型）。全局路线里循环：closed 主形的证明体用 `hdistQ` 造 `hbcad`，而全深度 traced region
  是 depth-extension driver 吃 `hwit/hbcad` 后的输出（设计文档 §4）。
* **(SEP)** `hsepWK`：新近 late record（`i < j`、`σ − T/R < tᵢ`）的尺度分离
  `2 max(3/(r/100)², C R) < scale`（主形 `hscaleK` 不含 `R`）。

已生产的前提：`hpin` ⇐ 主形 `d.native.pinching`（`a₀ := d.native.pinchingShift`）；半深度
`Tn − r²/2 ≤ σ` ⇐ G1 per-n `hroom`；`σ ≤ t` ⇐ `hσ`；accuracy / order / radius 的 `∀ n` 版 ⇐ 主形
`hacc / hord / hrad`（只在尾部成立）经平移 `n ↦ n + N`（`eventually_of_add_P6R2`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 平移：`∀ᶠ m, P (m + N)` ⇒ `∀ᶠ n, P n`。 -/
theorem eventually_of_add_P6R2 {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ m in atTop, P (m + N)) :
    ∀ᶠ n in atTop, P n := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 h
  refine Filter.eventually_atTop.2 ⟨a + N, fun n hn => ?_⟩
  have h1 := ha (n - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at h1

/-- 尾部指标：`1/(N+1) ≤ ε₀` 且 `B < N + 1`。 -/
theorem exists_tail_index_P6R2 {ε₀ : ℝ} (hε₀ : 0 < ε₀) (B : ℝ) :
    ∃ N : ℕ, ∀ m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ≤ ε₀ ∧ B < ((m + N : ℕ) : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ε₀) B)
  refine ⟨N, fun m => ⟨?_, ?_⟩⟩
  · have h1 : 1 / ε₀ < (N : ℝ) := (le_max_left _ _).trans_lt hN
    have h2 : 1 < (N : ℝ) * ε₀ := (div_lt_iff₀ hε₀).1 h1
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  · have h1 : B < (N : ℝ) := (le_max_right _ _).trans_lt hN
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    push_cast
    linarith

/-- **`hdistQ` ⇐ (TR) + (SEP) + 主形 / retained selection / 种子数据（`_P6R2`）**：结论逐字 = closed
主形的 `hdistQ` binder（余量 `L/4`）。显式残余义务只有 `hsepWK`（SEP）与 `htr`（TR）；其余 HDISTC 前提
全部由主形 binder（`d`、`hσ`、`hacc/hrad/hord`、`hcanK`、`hT₀`）、G1 per-n `hroom` 与链上种子数据
（`htime hsmall hclock hRr`）生产。 -/
theorem hdistQ_of_traced_sep_P6R2 {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {Kh : ℕ → ObservedHistory.{u}} (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (d : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (r L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {p : ℕ → CutoffParameters} {T₀ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (hsepWK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (htr : ∀ D T : ℝ, 0 < D → 0 < T → ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ n in atTop,
      (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_anySeed_C11G3.{u}
  obtain ⟨N, hN⟩ := exists_tail_index_P6R2 hε₀ (StandardCap.transitionEnd + 10)
  have hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    linarith [hroom n]
  have hLsh : Tendsto (fun m => L (m + N) / 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun n => L n / 4) N).2 (hL.atTop_div_const (by norm_num))
  have hRrsh : Tendsto (fun m => R (m + N) * r (m + N) ^ 2) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun n => R n * r n ^ 2) N).2 hRr
  have hacc' : ∀ m : ℕ, (p (m + N)).modelAccuracy ≤ ε₀ := fun m =>
    (hacc (m + N)).trans (hN m).1
  have hord' : ∀ m : ℕ, 2 ≤ (p (m + N)).modelOrder := fun m => by
    have := hord (m + N)
    omega
  have hrad' : ∀ m : ℕ, StandardCap.transitionEnd + 10 < (p (m + N)).modelRadius := fun m =>
    (hN m).2.trans_le (hrad (m + N))
  intro D T hD hT
  obtain ⟨Kc, hKc, htrDT⟩ := htr D T hD hT
  have hmap : Filter.map (id : ℕ → ℕ) atTop = atTop := Filter.map_id
  have key := hC (fun m => K (m + N)) (fun m => j (m + N)) (fun m => t (m + N))
    (fun m => hjt (m + N)) (fun m => htj (m + N)) (fun m => σ (m + N)) (fun m => y (m + N))
    (fun m => R (m + N)) (fun m => r (m + N)) (fun m => L (m + N) / 4) (fun m => Tn (m + N))
    (fun m => aSeed (m + N)) (fun m => haT (m + N)) (fun m => hsT (m + N))
    (fun m => has (m + N)) (fun m => pT (m + N)) (fun m => seedTrace (m + N))
    (fun m => (hσ (m + N)).le) (fun m => hhalf (m + N)) (fun m => htime (m + N))
    (Eventually.of_forall fun m => hRpos (m + N)) hLsh (fun m => hsmall (m + N))
    (fun m => hclock (m + N)) hRrsh d.native.pinchingShift_pos.le
    (fun m => d.native.pinching (m + N)) (fun m => p (m + N)) (fun m => T₀ (m + N))
    (fun m => recordsK (m + N)) (fun m => hcanK (m + N)) hacc' hord' hrad'
    (fun T' hT' C hC' => (tendsto_add_atTop_nat N).eventually (hsepWK T' hT' C hC'))
    (fun T' _ => (tendsto_add_atTop_nat N).eventually (hT₀ T')) id strictMono_id D T Kc hD hT
    hKc (by rw [hmap]; exact (tendsto_add_atTop_nat N).eventually htrDT)
  rw [hmap] at key
  exact eventually_of_add_P6R2 N key

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
