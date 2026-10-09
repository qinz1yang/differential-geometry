import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StatementP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E

/-!
# P6(b) 最小合同 `CanonicalLateCore_P6X` 与其 selection 反证骨架（O-CH11-P6SEL G2，后缀 `_P6X`）

R-C11-5 D-18：(b) 的最小 history-level 合同 = 审稿给的 `CanonicalLateCore`（逐字；= `∀ A > 0`,
`LargerBallCanonicalLateAt_P6A` 的结论形，`K₁ T` 在 history index 之前，无 `r ≤ r̄√t`、无 band 上界）。
本文件：

* `CanonicalLateCore_P6X`（def，逐字照审稿）+ `canonicalLateCore_iff_P6X`（与
  `LargerBallCanonicalLateSupply_P6A` 定义等）；
* `lateCoreAt_mono_P6X`：对放大因子 `A` 向下单调（D-14：`A ≤ 2` 借 `max A 2`）；
* `stageDerivative_of_timeDerivativeSupply_P6X`：S11（incoming / final slab 形）⇒ selector 要的
  stage 形 `hderivative`；
* **`canonicalLateCore_of_selected_P6X`**：producer 输入 = native canonical（S5 history 形，阈值
  `ρ⁻²`）+ native time-derivative（S11）+ `ρ` antitone + **显式缺口 `hP6`**（selected 坏序列的反证：
  对 selection 输出逐字形的任意序列给 False）⇒ `CanonicalLateCore_P6X`。证明：`¬(b)(A)` 对
  `K₁ = T = k+1` 取反例 ⇒ 坏点无 witness ⇒ `¬Good(ε, C1, C2, Ctime)` ⇒ `selection_of_bad_sequence_P6X`
  ⇒ `hP6`。不经任何含 S8 的 profile（D-18 producer 输入纪律）。
* `seed_half_le_sigma_P6X`：selection 的 κ 形窗口 ⇒ eventually `Tn − r²/2 ≤ σ`（HDISTC 的后半深度条件）。

`hP6` 的生产（主形 + 显式缺口）：event 内部类 + `R` 无界 ⇒ `false_of_selected_eventInterior_P6X`（G1）；
final / 边界 / `R` 有界（D-17 normalization）类见 G3、G4。
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set Filter
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-- **(b) 最小合同**（R-C11-5 Q5(c) 审稿形，逐字）：`K1 T` 在 history index、测试时刻、种子、半径与
测试点之前。 -/
def CanonicalLateCore_P6X
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (ε C1 C2 : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ K1 T : ℝ, 0 < K1 ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon)
        (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf
            (H.stageMetric (H.activeStage t) t) p (A * r),
          K1 * (r ^ 2)⁻¹ ≤
            metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          ∃ W : SpatialCanonicalWitness
              (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
            W.capTubeHasNeckChart ε

/-- consumer：`CanonicalLateCore_P6X` 与 P6A 的 `LargerBallCanonicalLateSupply_P6A` 定义等。 -/
theorem canonicalLateCore_iff_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} :
    CanonicalLateCore_P6X F ε C1 C2 ↔ LargerBallCanonicalLateSupply_P6A F ε C1 C2 :=
  Iff.rfl

/-- **对 `A` 向下单调**（D-14）：`A ≤ A'` 时种子体积前提变强、球变小。 -/
theorem lateCoreAt_mono_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 A A' : ℝ}
    (h : LargerBallCanonicalLateAt_P6A F ε C1 C2 A') (hA : 0 < A) (hAA : A ≤ A') :
    LargerBallCanonicalLateAt_P6A F ε C1 C2 A := by
  obtain ⟨K₁, T, hK₁, hT, hB⟩ := h
  refine ⟨K₁, T, hK₁, hT, fun n t p r hTt ht hs hv y hy hK => ?_⟩
  have hv' : ENNReal.ofReal (A'⁻¹ * r ^ 3) ≤ ballVolume
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hv
    have hr : 0 < r := hs.1
    have : A'⁻¹ ≤ A⁻¹ := inv_anti₀ hA hAA
    have h3 : 0 < r ^ 3 := by positivity
    nlinarith
  have hr : 0 < r := hs.1
  exact hB n t p r hTt ht hs hv' y (riemannianBallOf_mono _ _ (by nlinarith) hy) hK

/-- S11 ⇒ stage 形导数界（单个 history，按 `m = activeStage` 的 `Fin.lastCases` 分 event / final）。 -/
theorem stageDerivative_aux_P6X (K : RetainedCoreHistory.{u}) {ρ : ℝ → ℝ} {Ctime : ℝ≥0}
    (h1 : ∀ (j : Fin K.eventCount) (y : (K.stage j.castSucc).Carrier) (t : ℝ),
      t ∈ Ioo (K.time j.castSucc) (K.time j.succ) →
      (ρ t ^ 2)⁻¹ < (K.toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (K.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        Ctime * (K.toHistory.event j).incoming.flow.scalar t y ^ 2)
    (h2 : ∀ (h : K.time (Fin.last K.eventCount) < K.horizon)
      (y : (K.stage (Fin.last K.eventCount)).Carrier) (t : ℝ),
      t ∈ Ioo (K.time (Fin.last K.eventCount)) K.horizon →
      (ρ t ^ 2)⁻¹ < (K.finalSlab h).flow.scalar t y →
      |derivWithin (fun v => (K.finalSlab h).flow.scalar v y) (Iic t) t| ≤
        Ctime * (K.finalSlab h).flow.scalar t y ^ 2)
    (m : Fin (K.eventCount + 1)) (v : ℝ) (hvm : v ∈ K.toHistory.stageDomain m)
    (hlo : K.time m < v) (hhi : v < K.horizon) (z : (K.stage m).Carrier)
    (hR : (ρ v ^ 2)⁻¹ < metricScalarAt (K.toHistory.stageMetric m v) z) :
    |derivWithin (fun t => metricScalarAt (K.toHistory.stageMetric m t) z) (Iic v) v| ≤
      Ctime * metricScalarAt (K.toHistory.stageMetric m v) z ^ 2 := by
  induction m using Fin.lastCases with
  | last =>
    have hlt : K.time (Fin.last K.eventCount) < K.horizon := hlo.trans hhi
    have hfun : ∀ t, metricScalarAt (K.toHistory.stageMetric (Fin.last K.eventCount) t) z =
        (K.finalSlab hlt).flow.scalar t z := fun t => by
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, hlt, ↓reduceDIte]
      rfl
    simp only [hfun] at hR ⊢
    exact h2 hlt z v ⟨hlo, hhi⟩ hR
  | cast j =>
    have hv2 : v < K.time j.succ := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hvm
      exact hvm.2
    have hfun : ∀ t, metricScalarAt (K.toHistory.stageMetric j.castSucc t) z =
        (K.toHistory.event j).incoming.flow.scalar t z := fun t => by
      rw [ObservedHistory.stageMetric_castSucc_apply]
      rfl
    simp only [hfun] at hR ⊢
    exact h1 j z v ⟨hlo, hv2⟩ hR

/-- **S11 ⇒ selector 的 `hderivative`**（stage 形，`v` 在 slab 正年龄、视界前）。 -/
theorem stageDerivative_of_timeDerivativeSupply_P6X {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime : ℝ≥0}
    (h : TimeDerivativeSupply_C11E F ρ Ctime) (n : ℕ)
    (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
    (z : ((F.tower.history n).toHistory.stageAt v).Carrier)
    (hlo : (F.tower.history n).toHistory.time ((F.tower.history n).toHistory.activeStage v) <
      (v : ℝ))
    (hhi : (v : ℝ) < (F.tower.history n).toHistory.horizon)
    (hR : (ρ v ^ 2)⁻¹ < metricScalarAt ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage v) v) z) :
    |derivWithin (fun t => metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
      Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) v) z ^ 2 :=
  stageDerivative_aux_P6X (F.tower.history n) (h.1 n) (h.2 n) _ v
    (((F.tower.history n).toHistory.mem_stageDomain_iff v _).mpr rfl) hlo hhi z hR

/-- **HDISTC 后半深度条件**：selection 的 κ 形窗口 `∀ T > 0, ∀ᶠ n, Tn − r²/2 ≤ σ − T/R` 与 `R > 0`
⇒ eventually `Tn − r²/2 ≤ σ`。 -/
theorem seed_half_le_sigma_P6X {Tn σ r R : ℕ → ℝ} (hRpos : ∀ n, 0 < R n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, Tn n - r n ^ 2 / 2 ≤ σ n - T / R n) :
    ∀ᶠ n in atTop, Tn n - r n ^ 2 / 2 ≤ σ n := by
  filter_upwards [hwin 1 one_pos] with n hn
  have : 0 < 1 / R n := one_div_pos.mpr (hRpos n)
  linarith

/-- 单个 `A > 1` 处的 (b)（结论 = `LargerBallCanonicalLateAt_P6A` 体）⇐ selection 反证。 -/
theorem lateCoreAt_of_selected_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {A : ℝ} (hA : 1 < A)
    (hP6 : ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k = metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop → False) :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
            W.capTubeHasNeckChart ε := by
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (k : ℝ) + 1 ≤ (t : ℝ) ∧ 2 * r ^ 2 < (t : ℝ) ∧
      hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r ∧
      x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p (A * r) ∧
      ((k : ℝ) + 1) * (r ^ 2)⁻¹ ≤ metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) x ∧
      ¬ ∃ W : SpatialCanonicalWitness ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε := by
    intro k
    by_contra hk
    refine hcon ⟨(k : ℝ) + 1, (k : ℝ) + 1, by positivity, by positivity, ?_⟩
    intro n _ t p r hT ht hs hv x hx hK
    by_contra hW
    exact hk ⟨n, t, p, r, x, hT, ht, hs, hv, hx, hK, hW⟩
  choose ind Tn pT r x hlate htime hsmall hvol hx hK hW using hk
  have hr : ∀ k, 0 < r k := fun k => (hsmall k).1
  have hseed : ∀ k, ∃ (a : Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon)
      (hat : a ≤ Tn k), (a : ℝ) = (Tn k : ℝ) - r k ^ 2 ∧
      Nonempty (BackwardPointTrace (F.tower.history (ind k)).toHistory
        ((F.tower.history (ind k)).toHistory.activeStage a)
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k))
        ((F.tower.history (ind k)).toHistory.activeStage_mono hat) (pT k)) := fun k => by
    obtain ⟨hrk, a, hat, ha, htr⟩ := hsmall k
    have hp : pT k ∈ riemannianBallOf ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (pT k) (r k) := by
      change riemannianEDistOf _ (pT k) (pT k) < ENNReal.ofReal (r k)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hrk
    obtain ⟨tr, -⟩ := htr (pT k) hp
    exact ⟨a, hat, ha, ⟨tr⟩⟩
  choose aSeed haT hclock hst using hseed
  have hRx : ∀ k : ℕ, (k : ℝ) + 1 ≤ metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) * r k ^ 2 := by
    intro k
    have h2 : 0 < r k ^ 2 := by have := hr k; positivity
    have := mul_le_mul_of_nonneg_right (hK k) h2.le
    rwa [mul_assoc, inv_mul_cancel₀ h2.ne', mul_one] at this
  have hRpos0 : ∀ k, 0 < metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) := by
    intro k
    have h2 : 0 < r k ^ 2 := by have := hr k; positivity
    have : 0 < ((k : ℝ) + 1) * (r k ^ 2)⁻¹ := by positivity
    exact this.trans_le (hK k)
  have hdiv : Tendsto (fun k => metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) * r k ^ 2)
      atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => (by linarith [hRx k] : (k : ℝ) ≤ _))
      tendsto_natCast_atTop_atTop
  have hsel := ObservedHistory.selection_of_bad_sequence_P6X
    (Kh := fun k => (F.tower.history (ind k)).toHistory) (fun _ => q) le_rfl le_rfl le_rfl
    (fun _ => hanti) (fun k => hcan (ind k))
    (fun k v z hlo hhi hR =>
      stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR)
    Tn pT r A hr (zero_lt_one.trans hA) aSeed haT hclock (fun k => (hst k).some) x hx hRpos0
    (fun k hG => hW k hG.1) hdiv
  obtain ⟨σ, y, R, hsT, has, L, hRdef, hRpos, hRle, -, hL, hbad, hgood, hwin, hwin', hroom,
    hradii⟩ := hsel
  have hRr : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2 := fun k => by
    have h2 : 0 ≤ r k ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right (hRle k) h2
    linarith [hRx k]
  exact hP6 ind Tn pT r hr hlate htime hsmall hvol aSeed haT hclock (fun k => (hst k).some) σ y R
    hsT has L hRdef hRpos hRr hL hbad hgood hwin hwin' hroom hradii

/-- **G2 主定理：(b) 最小合同 ⇐ native canonical + native time-derivative + selection 反证缺口 `hP6`**。
`A ≤ 2` 借 `max A 2`（D-14，`lateCoreAt_mono_P6X`）；`A' = max A 2 > 1` 处用 `lateCoreAt_of_selected_P6X`。
`hP6` 是**唯一**的 P6 缺口 binder：对 selection 输出逐字形的任意 selected 坏序列（`F` 的 histories
`ind k`、种子 `(Tn, pT, r)` 满足 KL 84.1 前提、`t ≥ k+1`、`R r² ≥ k+1`、Good 区 / 窗口 / window-room）
给 False。其生产：event 内部 + `R` 无界类 ⇐ `false_of_selected_eventInterior_P6X`（G1，主形 P6D + 显式
K 层 / κ / hdist / hslice / hcwp 缺口）；其余类见 G3。 -/
theorem canonicalLateCore_of_selected_P6X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hP6 : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k = metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop → False) :
    CanonicalLateCore_P6X F ε C1 C2 := by
  intro A hA
  have hA2 : 1 < max A 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  exact lateCoreAt_mono_P6X (lateCoreAt_of_selected_P6X hanti hcan hder hA2 (hP6 _ hA2)) hA
    (le_max_left _ _)

end GC.LongTime.Ch11
