import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.HdistCondAnySeedC11G3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepTnP6SN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CondBridgeP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowBcadCP6BC

/-!
# hdistQC ⇐ HDISTC C11G3，eventually 版接线（O-CH11-HDISTQC G1 / G2，后缀 `_P6HQ`）

HBCADC `hbcadC_of_pickedCenter_P6BC` 的 binder `hdistQC`（traced-conditioned、余量 `L/4`、跨 stage 的种子距离
闭合）的 owner 是 HDISTC `hdistC_of_traced_anySeed_C11G3`（取 `L ↦ L/4`）。
C11G3 的 accuracy / order / radius / half-depth / `2r² < Tn` / records 前提都是 `∀ n`，
而 T1（PICKT1 / HBCADC）的 records 参数只给 `modelAccuracy ≤ 1/(n+1)`、`n+1 ≤ modelRadius`——
对固定 `ε₀`、`transitionEnd + 10` 只 eventually 成立。本文件把 C11G3 升成 eventually 版，
并把三处消费端接上：

* **G2（Reindex 节，PROVED）**：通用平移重索引 `exists_shift_forall_of_eventually_P6HQ`、
  `eventually_of_shift_P6HQ`、`strictMono_shiftSub_P6HQ`、`map_eq_map_shift_P6HQ`、
  `eventually_map_of_shift_P6HQ`（`K′ := K ∘ (· + N)`、子列 `φ′ m := φ (m + N) − N`、
  `map φ atTop = map (· + N) (map φ′ atTop)`；只对 `P Q : ℕ → Prop` 陈述，无 dependent rewrite，
  K→E 桥等可直接复用）。
* **G1 `hdistQC_of_C11G3_eventually_P6HQ`（PROVED）**：C11G3 的全部逐 `n` Prop 前提降为 `∀ᶠ n in atTop`，
  结论逐字（`L` 通用）。
* **G1b `hdistQC_of_C11G3_sepTn_eventually_P6HQ`（PROVED）**：G1 的 `hsepWK` 由
  `sepWK_of_smallAtTn_eventually_P6HQ`（SEPTN `sepWK_of_smallAtTn_P6SN` 的 eventually 版）付，
  换成数据 binder `ρn`、`t ≤ Tn`、`hsel4 : R ≤ ρn⁻²`、at-Tn (DLT) `hδ`、late records 小性 `hsm`。
* T1 适配：`eventually_modelAccuracy_le_P6HQ`、`eventually_modelRadius_gt_P6HQ`、
  `eventually_two_le_modelOrder_P6HQ`。
* consumer（各一个 `example`）：(1) HBCADC `hbcadC_of_pickedCenter_P6BC` 的 `hdistQC` 槽（G1b，`L/4`）；
  (2) J10GEN driver 的 `hdistC` 槽 = P6CD `hwitC_hderivC_of_hdistC_Cg_P6CD` 的 `hdistC`（G1，K 层实例
  `Kh = (K ·).toHistory`）；(3) PICKT1 core `hsliceR_lateHI_core_pickedCenter_C11PT` 的 `hdl` 槽（G1b，
  `l := map φ atTop`、traced 深度 `T > −σ₁`）。

**剩余 binder（按 owner）**：SEED / P6M4：`r`、half-depth `Tn − r²/2 ≤ σ`、`2r² < Tn`、`hsmall`、`hclock`、`hRr`
（后四个与 P6DW / hdistW 链同源）；E 层 event slab：`hjt`（ANCHOR3 链有）；HI 传播：固定 `a₀` 的 `hpin`
（与 J10GEN `hpinX` 同一义务，见 G1 docstring）；SEP′ / hnomId：`hsepWK`（G1）或 `ρn hsel4 hδ hsm`（G1b）。
非循环：G1 / G1b 的依赖闭包不含 `hdistW` / `hscalW` / `hbcadC` / `HU_*` / `hclosG` / `CanonicalLateCore` /
`hspine` / `_P6AN*` 常量（审计 deny 扫描）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Reindex

/-! ### 通用平移重索引（`K′ := K ∘ (· + N)`、`φ′ m := φ (m + N) − N`）

所有引理只对 `P Q : ℕ → Prop` 陈述：依赖型数据（`K n`、`σ n : Icc 0 (K n).horizon`、trace…）一律以
`fun n => X (n + N)` 平移，谓词经 beta 与原谓词在 `n + N` 处定义相等，**不做任何 dependent rewrite**；
`map φ atTop = map (· + N) (map φ′ atTop)` 把沿子列 `φ` 的 eventually 搬到平移后的子列 `φ′`。 -/

/-- `∀ᶠ n, P n` ⇒ 某个平移下逐点成立（`∃ N, ∀ m, P (m + N)`）。 -/
theorem exists_shift_forall_of_eventually_P6HQ {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
    ∃ N : ℕ, ∀ m : ℕ, P (m + N) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  exact ⟨N, fun m => hN (m + N) (Nat.le_add_left N m)⟩

/-- 平移后的 eventually 回到原序列：`(∀ᶠ m, P (m + N)) ⇒ ∀ᶠ n, P n`。 -/
theorem eventually_of_shift_P6HQ {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ m in atTop, P (m + N)) :
    ∀ᶠ n in atTop, P n := by
  rw [← Filter.map_add_atTop_eq_nat N]
  exact Filter.eventually_map.2 h

/-- 平移子列 `φ′ m := φ (m + N) − N` 严格单调。 -/
theorem strictMono_shiftSub_P6HQ {φ : ℕ → ℕ} (hφ : StrictMono φ) (N : ℕ) :
    StrictMono (fun m => φ (m + N) - N) := by
  intro a b hab
  have h1 : a + N ≤ φ (a + N) := hφ.id_le (a + N)
  have h2 : φ (a + N) < φ (b + N) := hφ (by omega)
  change φ (a + N) - N < φ (b + N) - N
  omega

/-- 滤子恒等式 `map φ atTop = map (· + N) (map φ′ atTop)`（`φ′ m := φ (m + N) − N`）。 -/
theorem map_eq_map_shift_P6HQ {φ : ℕ → ℕ} (hφ : StrictMono φ) (N : ℕ) :
    map φ atTop = map (fun m => m + N) (map (fun m => φ (m + N) - N) atTop) := by
  rw [Filter.map_map]
  have hfun : ((fun m => m + N) ∘ fun m => φ (m + N) - N) = φ ∘ fun m => m + N := by
    funext m
    have h1 : m + N ≤ φ (m + N) := hφ.id_le (m + N)
    change φ (m + N) - N + N = φ (m + N)
    omega
  rw [hfun, ← Filter.map_map, Filter.map_add_atTop_eq_nat]

/-- **沿子列的平移搬运（`_P6HQ`）**：若平移后的子列 `φ′` 上 `P (· + N) ⇒ Q (· + N)`（eventually），
则原子列 `φ` 上 `P ⇒ Q`（eventually）。用于把只对 `∀ n` 前提成立的条件形结论（`∀ φ, … → ∀ᶠ n in map φ
atTop, …`）搬到只有 eventually 前提的原序列。 -/
theorem eventually_map_of_shift_P6HQ {φ : ℕ → ℕ} (hφ : StrictMono φ) (N : ℕ) {P Q : ℕ → Prop}
    (h : (∀ᶠ m in map (fun m => φ (m + N) - N) atTop, P (m + N)) →
      ∀ᶠ m in map (fun m => φ (m + N) - N) atTop, Q (m + N))
    (hP : ∀ᶠ n in map φ atTop, P n) : ∀ᶠ n in map φ atTop, Q n := by
  rw [map_eq_map_shift_P6HQ hφ N] at hP ⊢
  exact Filter.eventually_map.2 (h (Filter.eventually_map.1 hP))

end Reindex

section Main

/-- **G1：条件形 hdistQC ⇐ C11G3，eventually 版（`_P6HQ`，PROVED）**：HDISTC
`hdistC_of_traced_anySeed_C11G3` 的所有逐 `n` Prop 前提（`hjt htj`、`σ ≤ t`、half-depth `Tn − r²/2 ≤ σ`、
`2r² < Tn`、`hsmall`、`hclock`、`hpin`、`hcan`、accuracy / order / radius）降为 `∀ᶠ n in atTop`；
`haT hsT has` 保持 `∀ n`（`seedTrace` 与结论的类型要用）。结论 = C11G3 结论逐字（`Kh` 展开成 `(K n).toHistory`），
`L` 通用（HBCADC 的 `hdistQC` 取 `L ↦ L/4`）。
证明：取 `N` 使全部 eventually 前提在 `n ≥ N` 成立，对平移数据 `K ∘ (· + N)`（及 `j t σ y R r L Tn aSeed …`
同样平移）调 C11G3，子列 `φ′ m := φ (m + N) − N`，`eventually_map_of_shift_P6HQ` 搬回。
`hpin` 是**固定 `a₀`**、沿 history 全时刻（K 层）的 Hamilton–Ivey：owner = HI 传播；与 J10GEN G1b 的新 binder
`hpinX`（E 层 `Hs n`、逐 `n` 的 `a₀X n + τ`）是**同一义务**（初始 HI ⇒ 沿 history 的 HI，`a₀ + τ` 形）的两个
形状：本形（K 层、`a₀` 一致）经 K→E 限制给出 `hpinX`（`a₀X := fun _ => a₀`），反向不行（`a₀X n` 依 `n`）；
T1 的 `hHI` 只给初始时刻、逐 `n` 的 `a₀ n`，不能直接付。 -/
theorem hdistQC_of_C11G3_eventually_P6HQ :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ),
      (∀ᶠ n in atTop, (K n).time (j n).castSucc < t n) →
      (∀ᶠ n in atTop, t n < (K n).time (j n).succ) →
    ∀ (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory
        ((K n).toHistory.activeStage (aSeed n)) ((K n).toHistory.activeStage (Tn n))
        ((K n).toHistory.activeStage_mono (haT n)) (pT n)),
      (∀ᶠ n in atTop, (σ n : ℝ) ≤ t n) →
      (∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) →
      (∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
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
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_anySeed_C11G3.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj σ y R r L Tn aSeed haT hsT has pT seedTrace hσt hhalf htime hR hL
    hsmall hclock hRr a₀ ha₀ hpin q T₀ recordsK hcan hacc hord hrad hsep hT₀ φ hφ D T Kc hD hT
    hKc htr
  obtain ⟨N, hN⟩ := exists_shift_forall_of_eventually_P6HQ (hjt.and (htj.and (hσt.and
    (hhalf.and (htime.and (hsmall.and (hclock.and (hpin.and (hcan.and (hacc.and
    (hord.and hrad)))))))))))
  have hsh : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  refine eventually_map_of_shift_P6HQ hφ N (fun h => ?_) htr
  exact hC (fun n => K (n + N)) (fun n => j (n + N)) (fun n => t (n + N)) (fun n => (hN n).1)
    (fun n => (hN n).2.1) (fun n => σ (n + N)) (fun n => y (n + N)) (fun n => R (n + N))
    (fun n => r (n + N)) (fun n => L (n + N)) (fun n => Tn (n + N)) (fun n => aSeed (n + N))
    (fun n => haT (n + N)) (fun n => hsT (n + N)) (fun n => has (n + N)) (fun n => pT (n + N))
    (fun n => seedTrace (n + N)) (fun n => (hN n).2.2.1) (fun n => (hN n).2.2.2.1)
    (fun n => (hN n).2.2.2.2.1) (hsh.eventually hR) (hL.comp hsh)
    (fun n => (hN n).2.2.2.2.2.1) (fun n => (hN n).2.2.2.2.2.2.1) (hRr.comp hsh) ha₀
    (fun n => (hN n).2.2.2.2.2.2.2.1) (fun n => q (n + N)) (fun n => T₀ (n + N))
    (fun n => recordsK (n + N)) (fun n => (hN n).2.2.2.2.2.2.2.2.1)
    (fun n => (hN n).2.2.2.2.2.2.2.2.2.1) (fun n => (hN n).2.2.2.2.2.2.2.2.2.2.1)
    (fun n => (hN n).2.2.2.2.2.2.2.2.2.2.2) (fun T hT C hC => hsh.eventually (hsep T hT C hC))
    (fun T hT => hsh.eventually (hT₀ T hT)) (fun m => φ (m + N) - N)
    (strictMono_shiftSub_P6HQ hφ N) D T Kc hD hT hKc h

/-! ### T1 数据 ⇒ C11G3 的 eventually 前提（`_P6HQ`）

T1 / PICKT1 / HBCADC 的 records 参数是 `hacc : ≤ 1/(n+1)`、`hrad : n+1 ≤`、`hord : n+2 ≤`——对 C11G3 的固定
`ε₀`、`transitionEnd + 10` 只 eventually 成立，这正是 G1 要 eventually 版的原因。 -/

/-- T1 accuracy `≤ 1/(n+1)` ⇒ eventually `≤ ε₀`。 -/
theorem eventually_modelAccuracy_le_P6HQ {p : ℕ → CutoffParameters}
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ε₀ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε₀)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (hacc n).trans ?_
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 < (N : ℝ) * ε₀ := (div_lt_iff₀ hε₀).1 hN
  have h2 : (N : ℝ) * ε₀ ≤ n * ε₀ := mul_le_mul_of_nonneg_right hn' hε₀.le
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- T1 radius `n+1 ≤` ⇒ eventually `transitionEnd + 10 <`。 -/
theorem eventually_modelRadius_gt_P6HQ {p : ℕ → CutoffParameters}
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) :
    ∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (p n).modelRadius := by
  obtain ⟨N, hN⟩ := exists_nat_gt (StandardCap.transitionEnd + 10)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith [hrad n]

/-- T1 order `n+2 ≤` ⇒ `2 ≤`（逐 `n`，包成 eventually）。 -/
theorem eventually_two_le_modelOrder_P6HQ {p : ℕ → CutoffParameters}
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) : ∀ᶠ n in atTop, 2 ≤ (p n).modelOrder :=
  Eventually.of_forall fun n => le_trans (Nat.le_add_left 2 n) (hord n)

/-! ### (SEP) at-Tn 核的 eventually 版 -/

/-- **`sepWK_of_smallAtTn_eventually_P6HQ`**：SEPTN `sepWK_of_smallAtTn_P6SN` 的逐 `n` 前提
（`hjt htT hhalf htime hRpos hsel4`）降为 eventually（平移重索引）；`hδ hsm` 与结论原样。 -/
theorem sepWK_of_smallAtTn_eventually_P6HQ {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {s t Tn r R ρn : ℕ → ℝ}
    (hjt : ∀ᶠ n in atTop, (K n).time (j n).castSucc < t n) (htT : ∀ᶠ n in atTop, t n ≤ Tn n)
    (hhalf : ∀ᶠ n in atTop, Tn n - r n ^ 2 / 2 ≤ s n)
    (htime : ∀ᶠ n in atTop, 2 * r n ^ 2 < Tn n)
    (hRpos : ∀ᶠ n in atTop, 0 < R n) (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hsel4 : ∀ᶠ n in atTop, R n ≤ (ρn n ^ 2)⁻¹)
    (hδ : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρn n) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
        s n - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale := by
  obtain ⟨N, hN⟩ := exists_shift_forall_of_eventually_P6HQ (hjt.and (htT.and (hhalf.and
    (htime.and (hRpos.and hsel4)))))
  have hsh : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  intro T hT C hC
  refine eventually_of_shift_P6HQ N ?_
  exact sepWK_of_smallAtTn_P6SN (K := fun n => K (n + N)) (j := fun n => j (n + N))
    (T₀ := fun n => T₀ (n + N)) (p := fun n => p (n + N)) (fun n => recordsK (n + N))
    (s := fun n => s (n + N)) (t := fun n => t (n + N)) (Tn := fun n => Tn (n + N))
    (r := fun n => r (n + N)) (R := fun n => R (n + N)) (ρn := fun n => ρn (n + N))
    (fun n => (hN n).1) (fun n => (hN n).2.1) (fun n => (hN n).2.2.1) (fun n => (hN n).2.2.2.1)
    (fun n => (hN n).2.2.2.2.1) (hRr.comp hsh) (fun n => (hN n).2.2.2.2.2)
    (hsh.eventually hδ) (fun ε hε => hsh.eventually (hsm ε hε)) T hT C hC

/-- **G1b：hdistQC ⇐ C11G3 + SEPTN，eventually 版（`_P6HQ`，PROVED）**：G1 的 `hsepWK` 由
`sepWK_of_smallAtTn_eventually_P6HQ`（`s := σ`、`Tn := Tn`）付，换成数据 binder：`ρn`、`t ≤ Tn`、
选择尺度 `R ≤ ρn⁻²`（`hsel4`）、at-Tn (DLT) `hδ`、late records 小性 `hsm`（owner = SEP′ / hnomId 线，
同 `sepWK_of_smallAtTn_P6SN`）。其余前提与结论同 G1。 -/
theorem hdistQC_of_C11G3_sepTn_eventually_P6HQ :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ),
      (∀ᶠ n in atTop, (K n).time (j n).castSucc < t n) →
      (∀ᶠ n in atTop, t n < (K n).time (j n).succ) →
    ∀ (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory
        ((K n).toHistory.activeStage (aSeed n)) ((K n).toHistory.activeStage (Tn n))
        ((K n).toHistory.activeStage_mono (haT n)) (pT n)),
      (∀ᶠ n in atTop, (σ n : ℝ) ≤ t n) →
      (∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) →
      (∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
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
    ∀ ρn : ℕ → ℝ, (∀ᶠ n in atTop, t n ≤ (Tn n : ℝ)) →
      (∀ᶠ n in atTop, R n ≤ (ρn n ^ 2)⁻¹) →
      (∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
        (K n).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) →
        (q n).recenterConstant * (q n).delta ((K n).time i.succ) ≤ 1 / 2) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
        (K n).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
          (recordsK n i hi).nominalRadius h ≤ ε * ρn n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hG⟩ := hdistQC_of_C11G3_eventually_P6HQ.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj σ y R r L Tn aSeed haT hsT has pT seedTrace hσt hhalf htime hR hL
    hsmall hclock hRr a₀ ha₀ hpin q T₀ recordsK hcan hacc hord hrad ρn htT hsel4 hδ hsm hT₀
  exact hG K j t hjt htj σ y R r L Tn aSeed haT hsT has pT seedTrace hσt hhalf htime hR hL
    hsmall hclock hRr ha₀ hpin q T₀ recordsK hcan hacc hord hrad
    (sepWK_of_smallAtTn_eventually_P6HQ recordsK (s := fun n => (σ n : ℝ))
      (Tn := fun n => (Tn n : ℝ)) hjt htT hhalf htime hR hRr hsel4 hδ hsm) hT₀

end Main

section Consumers

/-! ### 三个 consumer（HBCADC / J10GEN driver / T1 core `hdl`） -/

/-- **consumer 1（HBCADC，PROVISIONAL[G1b 剩余数据 binder]）**：`hbcadC_of_pickedCenter_P6BC` 的
`hdistQC` 槽由 G1b（`L ↦ L/4`）付；T1 自己的 `hacc / hrad / hord / hcanK / hT₀ / hσ / hRpos / hL` 经
`eventually_*_P6HQ` 适配直接喂 C11G3。binder = P6BC 原 binder 去 `hdistQC`，加 G1b 剩余数据：`hjt`、
seed 组 `r hhalf htime hsmall hclock hRr`、HI `a₁ hpin`（固定 `a₁`，HI 传播 owner）、SEP′ 组
`ρn hsel4 hδ hsm`。结论 = SHALLOW T0 `ShallowBcadC_C11SH` 逐字。 -/
example
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hPC : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ ε C1 C2
        Cgrad (K n) (σ n) (y n))
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (r : ℕ → ℝ)
    (hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₁ : ℝ} (ha₁ : 0 ≤ a₁)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₁ + τ') x)
    (ρn : ℕ → ℝ) (hsel4 : ∀ᶠ n in atTop, R n ≤ (ρn n ^ 2)⁻¹)
    (hδ : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρn n) :
    ObservedHistory.ShallowBcadC_C11SH (fun n => (K n).toHistory) σ y R := by
  obtain ⟨ε₀, hε₀, hQC⟩ := hdistQC_of_C11G3_sepTn_eventually_P6HQ.{u}
  have htT : ∀ n, t n ≤ (Tn n : ℝ) := fun n => by
    rw [← hσ n]
    exact Subtype.coe_le_coe.2 (hsT n)
  exact ObservedHistory.hbcadC_of_pickedCenter_P6BC hθ₀ hεle hκ hphi hCg htj recordsF hHI hcanK
    hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT
    has pT seedTrace L hL hwin ρV hρV
    (hQC K j t (.of_forall hjt) (.of_forall htj) σ y R r (fun n => L n / 4) Tn aSeed haT hsT
      has pT seedTrace (.of_forall fun n => (hσ n).le) (.of_forall hhalf) (.of_forall htime)
      (.of_forall hRpos) (hL.atTop_div_const (by norm_num)) (.of_forall hsmall)
      (.of_forall hclock) hRr ha₁ (.of_forall hpin) p T₀ recordsK (.of_forall hcanK)
      (eventually_modelAccuracy_le_P6HQ hacc hε₀) (eventually_two_le_modelOrder_P6HQ hord)
      (eventually_modelRadius_gt_P6HQ hrad) ρn (.of_forall htT) hsel4 hδ hsm
      (fun T _ => hT₀ T)) hPC

/-- **consumer 2（J10GEN driver 的 `hdistC` 槽，PROVISIONAL[G1 剩余 binder]）**：J10GEN G1
`kRouteHICond_noJ10_P6JG` 的 `hdistC` 槽与 P6CD `hwitC_hderivC_of_hdistC_Cg_P6CD` 的 `hdistC` 前提同形
（`Hs ↦ Kh`、`ts ↦ σ`、`ys ↦ y`），driver 正是把它喂进后者（`.2` = `hderivC`）。这里 `Kh = (KK ·).toHistory`
（K 层实例）：G1 的结论逐字填 P6CD 的 `hdistC`，结论 = P6CD 的 `hwitC ∧ hderivC`。E 层（`Hs` = extendAt 族）
需 K→E 桥 `hdistC_seq_of_eventPrefix`（J10GEN2 的 (P2)，可复用本文件 Reindex 节）。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (KK : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (KK n).eventCount) (t : ℕ → ℝ)
    (hjt : ∀ᶠ n in atTop, (KK n).time (j n).castSucc < t n)
    (htj : ∀ᶠ n in atTop, t n < (KK n).time (j n).succ)
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
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
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hKh : Kh = fun n => (KK n).toHistory)
    (r : ℕ → ℝ) (hσt : ∀ᶠ n in atTop, (σ n : ℝ) ≤ t n)
    (hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ))
    (htime : ∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ᶠ n in atTop, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (p n) (r n))
    (hclock : ∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ᶠ n in atTop, ∀ (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (KK n).eventCount), T₀ n ≤ (KK n).time i.succ →
      GeometricCutoffRecord (KK n).toHistory i (q n))
    (hcan : ∀ᶠ n in atTop, ∀ (i : Fin (KK n).eventCount) (hi : T₀ n ≤ (KK n).time i.succ) b,
      ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (q n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hord : ∀ᶠ n in atTop, 2 ≤ (q n).modelOrder)
    (hrad : ∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (KK n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (KK n).time i.succ) b,
        (σ n : ℝ) - T / R n < (KK n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) :
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        Cg * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
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
        Cg * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2)
 := by
  subst hKh
  obtain ⟨ε₀, hε₀, hG⟩ := hdistQC_of_C11G3_eventually_P6HQ.{u}
  exact ObservedHistory.hwitC_hderivC_of_hdistC_Cg_P6CD (fun n => (KK n).toHistory) Tn aSeed σ haT
    hsT has p seedTrace y R L hR hL hgood hwin
    (hG KK j t hjt htj σ y R r L Tn aSeed haT hsT has p seedTrace hσt hhalf htime
      (.of_forall hR) hL hsmall hclock hRr ha₀ hpin q T₀ recordsK hcan
      (eventually_modelAccuracy_le_P6HQ hacc hε₀) hord hrad hsep hT₀)

/-- **consumer 3（T1 core / StepOne 的 `hdl`，PROVISIONAL[G1b 剩余数据 binder]）**：PICKT1 core
`hsliceR_lateHI_core_pickedCenter_C11PT` 的 `hdl` 槽（`l := map φ atTop`、`σ + σ₁/R ≤ v`、余量 `L/4`）由 G1b
（traced 深度 `T > −σ₁`，同 C11PT 壳）付；`hPC` 取 P6BC 的族形。
PICKSEL `seedDist_slice_P6PS` 的 `hdl`（固定 `n`、`σ − Tc/R ≤ v`）= G1b 结论在 `n` 处的体（`Tc := T`），不另写。 -/
example
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (r : ℕ → ℝ)
    (hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₁ : ℝ} (ha₁ : 0 ≤ a₁)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₁ + τ') x)
    (ρn : ℕ → ℝ) (hsel4 : ∀ᶠ n in atTop, R n ≤ (ρn n ^ 2)⁻¹)
    (hδ : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc ((Tn n : ℝ) / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρn n)
    (A Dd : ℝ) (hA : 1 ≤ A) (hDd : 0 < Dd) (φ : ℕ → ℕ) (hφ : StrictMono φ) (σ₁ σ₂ : ℝ)
    (h12 : σ₁ ≤ σ₂) (hσ₂ : σ₂ < 0) (Dw T Kc : ℝ) (hDw : 0 < Dw) (hT : -σ₁ < T)
    (hKc : 0 ≤ Kc)
    (htr : ∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
      (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n))
    (hPC : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ ε C1 C2
        Cgrad (K n) (σ n) (y n))
 :
    True := by
  obtain ⟨ε₀, hε₀, hQC⟩ := hdistQC_of_C11G3_sepTn_eventually_P6HQ.{u}
  have htT : ∀ n, t n ≤ (Tn n : ℝ) := fun n => by
    rw [← hσ n]
    exact Subtype.coe_le_coe.2 (hsT n)
  obtain ⟨_, _, _, Rad, _, _, hcore⟩ := ObservedHistory.hsliceR_lateHI_core_pickedCenter_C11PT
    (C1 := C1) (C2 := C2) (Cgrad := Cgrad) hθ₀ hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK
    hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT
    has pT seedTrace L hL hwin ρV hρV A Dd hA hDd
  have hT0 : 0 < T := by linarith
  have hdist :=
    (hQC K j t (.of_forall hjt) (.of_forall htj) σ y R r (fun n => L n / 4) Tn aSeed haT hsT
      has pT seedTrace (.of_forall fun n => (hσ n).le) (.of_forall hhalf) (.of_forall htime)
      (.of_forall hRpos) (hL.atTop_div_const (by norm_num)) (.of_forall hsmall)
      (.of_forall hclock) hRr ha₁ (.of_forall hpin) p T₀ recordsK (.of_forall hcanK)
      (eventually_modelAccuracy_le_P6HQ hacc hε₀) (eventually_two_le_modelOrder_P6HQ hord)
      (eventually_modelRadius_gt_P6HQ hrad) ρn (.of_forall htT) hsel4 hδ hsm
      (fun T _ => hT₀ T))
    φ hφ Dw T Kc hDw hT0 hKc htr
  have _hT1 := hcore (map φ atTop) hφ.tendsto_atTop σ₁ σ₂ h12 hσ₂ Dw hDw
    (by
      filter_upwards [hdist] with n hn
      intro x hx v hav hvs hv tr
      refine hn x hx v hav hvs ?_ tr
      have h2 : 0 ≤ (σ₁ + T) / R n := div_nonneg (by linarith) (hRpos n).le
      have h3 : (σ₁ + T) / R n = σ₁ / R n + T / R n := add_div σ₁ T (R n)
      linarith)
    (hPC Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
  trivial

end Consumers

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
