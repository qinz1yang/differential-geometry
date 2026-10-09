import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthStep1P6DP

/-!
# 深度归纳期 4 前半 G1：driver 合成的三项预处理（O-CH11-DEPTH4A，后缀 `_P6DP4`）

设计依据：`docs/geometrization/chapter8/out/P6-CORE-INDUCTION-DESIGN-20261008.md` §6 / §8 期 4；
DEPTH1 state 的三个待处理点。全部 PROVED，不新增 binder：
* **(a) event / 末 slab 子列统一**：`exists_subseq_of_forall_or_P6DP4`（∀ n, P n ∨ Q n ⇒ 子列全 P 或全 Q）；
  `exists_eventSlab_pos_of_lt_last_P6DP4`（`0 ≤ σ < time last` ⇒ `∃ j t`，
  `time j.castSucc < t < time j.succ`、`σ ≤ t`：event 时刻自动落到下一个 slab，即 DEPTH1 event 支要的位置）；
  `condForm_comp_P6DP4` / `eventually_comp_P6DP4`：eventually 前提与
  「∀ φ ↑, (∀ᶠ in map φ, A) → (∀ᶠ in map φ, B)」
  条件形前提沿子列 ψ 搬运（φ ↦ ψ ∘ φ）。
* **(b) σ = horizon**：HDISTC2 的 `hdistC_final_P6DC2`（P6DistCFinalP6DC2:125）中
  `t` / `_htl` / `_htK` / `σ ≤ t`
  是未用参数（:175 的 `intro K _t _htl _htK … _hσt`；G0 孪生 `hdistC_of_traced_final_P6DC2`（:48）本就无位置）。
  `hdistC_anyPos_P6DP4` = 该定理逐字删去这四个未用前提（生成器断言其余逐字）；
  `hwitC_hderivC_of_hPN_anyPos_P6DP4` = DEPTH1 final 支删去位置前提的同构版。两者对任意 σ（含 σ = horizon）成立，
  代价是 (SEP) 对全部 event；在 `time last ≤ σ` 情形，全部 event 都在 σ 之前，与 DC2 合同同义。
* **(c) 阈值衔接**：`hgood_of_four_le_P6DP4`：selection 的 `4R` 版 hgood ⇒ kernel body 的 `Cg·R` 版
  （`4 ≤ Cg`，Q5.4）。
陈述由 `build-logs/scratch/O-CH11-DEPTH4A/gen/gen_g1.py` 生成（DC2 / P6M2 / DEPTH1 文本 sha256 断言）。
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

/-! ### (a) 子列统一与重索引 -/

/-- **(a1)**：逐 `n` 二分 ⇒ 子列上一致（全 `P` 或全 `Q`）。 -/
theorem exists_subseq_of_forall_or_P6DP4 {P Q : ℕ → Prop} (h : ∀ n, P n ∨ Q n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ((∀ m, P (ψ m)) ∨ (∀ m, Q (ψ m))) := by
  by_cases hP : ∃ᶠ n in atTop, P n
  · obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_of_frequently_atTop hP
    exact ⟨ψ, hψ, Or.inl hψP⟩
  · have hQ : ∃ᶠ n in atTop, Q n := by
      rw [Filter.not_frequently] at hP
      exact (hP.mono fun n hn => (h n).resolve_left hn).frequently
    obtain ⟨ψ, hψ, hψQ⟩ := Filter.extraction_of_frequently_atTop hQ
    exact ⟨ψ, hψ, Or.inr hψQ⟩

/-- **(a2)**：`0 ≤ σ < time last` ⇒ σ 之后、同一 event slab 内的位置 `t`（DEPTH1 event 支的 `j, t`）。
σ 恰为 event 时刻时落到下一个 slab（`time j.castSucc = σ < t`）。 -/
theorem exists_eventSlab_pos_of_lt_last_P6DP4 (K : RetainedCoreHistory.{u}) {σ : ℝ}
    (h0 : 0 ≤ σ) (hσ : σ < K.time (Fin.last K.eventCount)) :
    ∃ (j : Fin K.eventCount) (t : ℝ), K.time j.castSucc < t ∧ t < K.time j.succ ∧ σ ≤ t := by
  classical
  let S : Finset (Fin (K.eventCount + 1)) := Finset.univ.filter (fun k => σ < K.time k)
  have hS : S.Nonempty := ⟨Fin.last K.eventCount, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩
  have hkS : S.min' hS ∈ S := S.min'_mem hS
  have hk : σ < K.time (S.min' hS) := (Finset.mem_filter.mp hkS).2
  have hk0 : S.min' hS ≠ 0 := by
    intro h
    rw [h, K.time_zero] at hk
    linarith
  obtain ⟨j, hj⟩ : ∃ j : Fin K.eventCount, S.min' hS = j.succ :=
    ⟨(S.min' hS).pred hk0, (Fin.succ_pred _ hk0).symm⟩
  have hjle : K.time j.castSucc ≤ σ := by
    by_contra hlt
    have hmem : j.castSucc ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hlt⟩
    have hle := S.min'_le _ hmem
    rw [hj] at hle
    exact absurd hle (not_le.mpr (Fin.castSucc_lt_succ (i := j)))
  rw [hj] at hk
  refine ⟨j, (σ + K.time j.succ) / 2, ?_, ?_, ?_⟩ <;> linarith

/-- **(a3)**：eventually 前提沿子列 ψ 搬运。 -/
theorem eventually_comp_P6DP4 {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {P : ℕ → Prop}
    (h : ∀ᶠ n in atTop, P n) : ∀ᶠ m in atTop, P (ψ m) :=
  hψ.tendsto_atTop.eventually h

/-- **(a3)**：条件形前提（`hwitC` / `hderivC` / `hkappaC` / `hdistC` 型：沿任一子列 φ 的 eventually 蕴含）
沿子列 ψ 搬运：对 φ 用 `ψ ∘ φ`。 -/
theorem condForm_comp_P6DP4 {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {A B : ℕ → Prop}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → (∀ᶠ n in map φ atTop, A n) → ∀ᶠ n in map φ atTop, B n) :
    ∀ φ : ℕ → ℕ, StrictMono φ → (∀ᶠ m in map φ atTop, A (ψ m)) →
      ∀ᶠ m in map φ atTop, B (ψ m) := by
  intro φ hφ hA
  have h1 : ∀ᶠ n in map (ψ ∘ φ) atTop, A n := by
    rw [← Filter.map_map]
    exact Filter.eventually_map.2 hA
  have h2 := h (ψ ∘ φ) (hψ.comp hφ) h1
  rw [← Filter.map_map] at h2
  exact Filter.eventually_map.1 h2

/-! ### (b) σ = horizon：位置无关版 -/

/-- **(b1) 位置无关 hdistC（`_P6DP4`）**：`hdistC_final_P6DC2`（P6DistCFinalP6DC2:125）逐字，删去其未用的
final 位置参数 `t` / `_htl` / `_htK` / `σ ≤ t`（DC2 证明 `intro K _t _htl _htK … _hσt` 不消费它们；G0 孪生
`hdistC_of_traced_final_P6DC2` 本即无位置）。(SEP) 对全部 event。证明逐字。 -/
theorem hdistC_anyPos_P6DP4 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)),
      (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) → (∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
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
  have hshift := fun n => GC.LongTime.Ch11.earlier_seed_small_on_half_depth_C11G3 (haT n) (pT n)
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
（含 σ = horizon）成立。用于 `time last ≤ σ` 的子列（此时全部 event 都在 σ 之前）。 -/
theorem hwitC_hderivC_of_hPN_anyPos_P6DP4 :
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
      (∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ)) →
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
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_anyPos_P6DP4.{u}
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

/-! ### (c) 阈值衔接 -/

/-- **(c) 阈值衔接（`_P6DP4`）**：selection 的 `4R` 版 hgood（P6M2:38 binder 逐字）⇒ 阈值 `Cg·R` 版
（`4 ≤ Cg`，Q5.4 共享选择子约束；kernel body 的 hgood 槽形）。`L` 只出现在 hgood 内。 -/
theorem hgood_of_four_le_P6DP4 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    {Cg : ℝ} (hCg : 4 ≤ Cg)
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
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) :
    ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
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
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  intro n v hav hvs hw z hd hz
  exact hgood n v hav hvs hw z hd (le_trans (mul_le_mul_of_nonneg_right hCg (hR n).le) hz)

/-- **consumer（G1）**：event / 末 slab 子列统一——任意坏点时刻序列 `σ n ≥ 0`，存在子列使得要么全部有
DEPTH1 event 支位置 `(j, t)`，要么全部 `time last ≤ σ`（走 (b) 的位置无关版）。 -/
example (K : ℕ → RetainedCoreHistory.{u}) (σ : ℕ → ℝ) (h0 : ∀ n, 0 ≤ σ n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ m, ∃ (j : Fin (K (ψ m)).eventCount) (t : ℝ), (K (ψ m)).time j.castSucc < t ∧
          t < (K (ψ m)).time j.succ ∧ σ (ψ m) ≤ t) ∨
        (∀ m, (K (ψ m)).time (Fin.last (K (ψ m)).eventCount) ≤ σ (ψ m))) :=
  exists_subseq_of_forall_or_P6DP4 fun n =>
    (lt_or_ge (σ n) ((K n).time (Fin.last (K n).eventCount))).imp
      (fun h => exists_eventSlab_pos_of_lt_last_P6DP4 (K n) (h0 n) h) id

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
