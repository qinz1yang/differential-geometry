import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixUniformC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixTracedC11G3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalCrossEventP6E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WitnessConditionalP6M2

/-!
# 条件形 `hdistC` ⇐ traced region（S-CH11-HDISTC G0，后缀 `_C11G3`）

P6ANCH2 `P6WitnessConditionalP6M2` 的 `hdistC` binder（深度自举的最后一个缺口）：沿子列 `φ`，
traced region `(2D, T, K)` eventually ⇒ 相对 `hdist (D, T)`。本文件把它接成：

1. traced region（K 层）→ E 层（`isTracedRegion_eventPrefix_C11G3`，`Hs := K.eventPrefix j t`）；
2. 取 `ℓ₀ := min 1 (D e^{-9 K T})`（`ℓ₀ e^{9KT} ≤ D`）⇒ P6CE `exists_hscal_of_isTracedRegion_P6E` 给完整
   `hscal(D, T, ℓ₀)`（E 层）；
3. P6PFX uniform 版 `hdist_Kdata_pointwise_eventPrefix_uniform_C11G2`（`∃ ε₀, ∀ ℓ₀ ∈ (0,1]`）在
   **子列 `K ∘ φ`** 上取值（序列整体重排；`∀ᶠ n in map φ atTop` ⇔ `∀ᶠ m in atTop, · (φ m)`）；
4. E 层数据（`Te aE sE pe yE seedE`）由 `exists_eventPrefixData_C11G3` + `choose` 造出。

**`Tn` 限制**：K0 种子时刻 `(Tn n : ℝ) ≤ t n`（E 的 horizon = `t n`）；K-route 里 `σ = t`、`σ ≤ Tn`，
即 `Tn = σ = t`。`Tn > σ` 的情形由 G1/G2（`earlier_seed_on_half_depth_C11G3`）去掉。
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

/-- `ℓ₀ := min 1 (D e^{-9KT})`：`0 < ℓ₀ ≤ 1` 且 `ℓ₀ e^{9KT} ≤ D`（`_C11G3`）。 -/
theorem exists_radius_C11G3 {D T Kc : ℝ} (hD : 0 < D) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ℓ₀ ≤ 1 ∧ ℓ₀ * Real.exp (9 * Kc * T) ≤ D := by
  have he := Real.exp_pos (9 * Kc * T)
  refine ⟨min 1 (D / Real.exp (9 * Kc * T)), lt_min one_pos (div_pos hD he), min_le_left _ _, ?_⟩
  calc min 1 (D / Real.exp (9 * Kc * T)) * Real.exp (9 * Kc * T)
      ≤ D / Real.exp (9 * Kc * T) * Real.exp (9 * Kc * T) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) he.le
    _ = D := div_mul_cancel₀ _ he.ne'

/-- **条件形 `hdistC` ⇐ traced region（`_C11G3`）**：`ε₀`（端点保护精度，来自
`exists_hprot_window_C11G`）与一切无关；对 K 层种子数据 `(Tn, aSeed, pT, r, seedTrace)`（`Tn ≤ t`）、
K0 / pinching / late records，**P6ANCH2 `hwitC_hderivC_of_hdistC_P6M2` 的 `hdistC` binder 逐字**：
沿任意 `φ`，traced region `(2D, T, K)` eventually ⇒ 相对 hdist `(D, T)`。 -/
theorem hdistC_of_traced_C11G3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
      (_hjt : ∀ n, (K n).time (j n).castSucc < t n) (_htj : ∀ n, t n < (K n).time (j n).succ),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)),
      (∀ n, (Tn n : ℝ) ≤ t n) →
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
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (σ n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n)) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
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
  obtain ⟨ε₀, hε₀, hC⟩ := hdist_Kdata_pointwise_eventPrefix_uniform_C11G2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t hjt htj Kh σ y R r L Tn aSeed haT hsT has pT seedTrace hTt hR hL hsmallK hclockK
    hRr a₀ ha₀ hpinK q T₀ recordsK hcanK hacc0 hm hDm hwin hlate hsepWK hT₀ φ hφ D T Kc hD hT
    hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hE := fun n => (K n).exists_eventPrefixData_C11G3 (j n) (hjt n) (htj n) (haT n) (hsT n)
    (has n) (hTt n) (y n) (seedTrace n)
  choose Te aE sE haTe hsTe hasE pe yE seedE hsE haE hTe hyE hpE hseed using hE
  obtain ⟨ℓ₀, hℓ₀, hℓ₀1, hℓD⟩ := exists_radius_C11G3 (T := T) (Kc := Kc) hD
  have hRφ : ∀ᶠ m in atTop, 0 < R (φ m) := hφt.eventually hR
  have htrE : ∀ᶠ m in atTop,
      ((K (φ m)).eventPrefix (j (φ m)) (t (φ m)) (hjt (φ m)) (htj (φ m))).toHistory.isTracedRegion
        (sE (φ m)) (yE (φ m)) (2 * D / Real.sqrt (R (φ m))) (T / R (φ m)) (Kc * R (φ m)) := by
    filter_upwards [Filter.eventually_map.mp htr] with m hm'
    exact (K (φ m)).isTracedRegion_eventPrefix_C11G3 (j (φ m)) (hjt (φ m)) (htj (φ m))
      (sE (φ m)) (σ (φ m)) (hsE (φ m)) (yE (φ m)) (y (φ m)) (hyE (φ m)) hm'
  have hscal := ObservedHistory.exists_hscal_of_isTracedRegion_P6E
    (Hs := fun m => ((K (φ m)).eventPrefix (j (φ m)) (t (φ m)) (hjt (φ m))
      (htj (φ m))).toHistory)
    (s := fun m => sE (φ m)) (y := fun m => yE (φ m)) (aSeed := fun m => aE (φ m))
    (R := fun m => R (φ m)) hRφ hKc hℓ₀ hℓD htrE
  have hmain := hC ℓ₀ hℓ₀ hℓ₀1 (fun m => K (φ m)) (fun m => j (φ m)) (fun m => t (φ m))
    (fun m => hjt (φ m)) (fun m => htj (φ m)) (fun m => σ (φ m)) (fun m => y (φ m))
    (fun m => R (φ m)) (fun m => r (φ m)) (fun m => L (φ m)) (fun m => Tn (φ m))
    (fun m => aSeed (φ m)) (fun m => haT (φ m)) (fun m => hsT (φ m)) (fun m => has (φ m))
    (fun m => pT (φ m)) (fun m => seedTrace (φ m)) (fun m => Te (φ m)) (fun m => aE (φ m))
    (fun m => sE (φ m)) (fun m => haTe (φ m)) (fun m => hsTe (φ m)) (fun m => hasE (φ m))
    (fun m => pe (φ m)) (fun m => yE (φ m)) (fun m => seedE (φ m)) (fun m => hsE (φ m))
    (fun m => haE (φ m)) (fun m => hTe (φ m)) (fun m => hyE (φ m)) (fun m => hpE (φ m))
    (fun m => hseed (φ m)) hRφ (hL.comp hφt) (fun m => hsmallK (φ m))
    (fun m => hclockK (φ m)) (hRr.comp hφt) ha₀ (fun m => hpinK (φ m)) (fun m => q (φ m))
    (fun m => T₀ (φ m)) (fun m => recordsK (φ m)) (fun m => hcanK (φ m))
    (fun m => hacc0 (φ m)) (fun m => hm (φ m)) (fun m => hDm (φ m)) D T hD hT
    (hφt.eventually (hwin T hT)) (hφt.eventually (hlate T hT)) hscal
    (fun C hC' => hφt.eventually (hsepWK T hT C hC')) (hφt.eventually (hT₀ T hT))
  exact Filter.eventually_map.mpr hmain

/-- **consumer（P6ANCH2 的条件形接口）**：`hdistC_of_traced_C11G3` 的结论（`Kh := fun n => (K n).toHistory`）
逐字就是 `hwitC_hderivC_of_hdistC_P6M2` 的 `hdistC` binder（`hwin` 同形）；下面的 `example` 把它喂进去。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (t : ℕ → ℝ)
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R r L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
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
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hTt : ∀ n, ((Tn n : Icc (0 : ℝ) (Kh n).horizon) : ℝ) ≤ t n)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (p n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ((∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n)) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) → True) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_C11G3.{u}
  refine ⟨ε₀, hε₀, fun hcan hacc hord hrad hlate hsep hT₀ => ?_⟩
  have _hwit := ObservedHistory.hwitC_hderivC_of_hdistC_P6M2 (eps := eps) (C1' := C1') (C2' := C2')
    (Ctime' := Ctime') (fun n => (K n).toHistory) Tn aSeed σ haT hsT has p seedTrace y R L hR hL
    hgood hwin
    (hC K j t hjt htj σ y R r L Tn aSeed haT hsT has p seedTrace hTt
      (Filter.Eventually.of_forall hR) hL hsmall hclock hRr ha₀ hpin q T₀ recordsK hcan hacc hord
      hrad hwin hlate hsep hT₀)
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
