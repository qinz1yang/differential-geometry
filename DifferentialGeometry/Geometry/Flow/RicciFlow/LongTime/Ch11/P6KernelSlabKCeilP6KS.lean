import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelSlabKSupplyP6KS

set_option autoImplicit false

/-!
# hslabK / (D1)(D2) 天花板 ⇐ C12-7′ + 最小 ind（O-CH11-KSLABK G2，后缀 `_P6KS`）

lead 08:1x 裁定：不走截断槽孪生；走 **最小 ind 路线 + C12-7′**。本文件（PROVED，无新 binder）：
* **C12-7′**（HNOT 08:0x，绝对时间尺度局部跳比）：`∀ t′ t, 0 ≤ t′ ≤ t ≤ t′ + τ₀ → ρ(t′) ≤ Λ·ρ(t)`，`Λ ≥ 1`。
  `ceil_of_ratio_P6KS`：C12-7′ + antitone ⇒ `t ≤ T ≤ σ + τ₀` 处 `(ρ t²)⁻¹ ≤ Λ²·(ρ σ²)⁻¹`。
* **最小 ind**（`ind := ⌈Tno⌉`，`horizon = ind`，`RetainedCoreObservationTower.horizon_eq`）+ selection
  `Tno − σo ≤ r²/2` ⇒ `horizon − σo ≤ 1 + r²/2 ≤ τ₀` ⇒ G1 显式前提 `(ρ(horizon_n)²)⁻¹ ≤ Q n` 在
  `Q n := max(·, Λ²·ρ(σo n)⁻²)` 下成立：`ceiling_of_C127prime_minInd_P6KS`（τ₀ ≥ 2、0 ≤ r ≤ 1 形）/
  `ceiling_of_C127prime_minInd_gen_P6KS`（`1 + r²/2 ≤ τ₀` 形）；序列形
  `hslabK_of_C127prime_minInd_P6KS`（hgapJ 元组，原尺度）、
  `hfinalDt_of_C127prime_minInd_P6KS`（hgapJF，K 帧）。
* 另：锐形（event slabs 只到 `time last`）`eventSlabsDerivative_of_supply_last_P6KS` /
  `hslabK_of_supply_last_P6KS`。
* `ind k ≤ Tno k + 1` 在冻结 hPN / hgapJ 帧**不是**现有前提（ind 由 `P6LateTimeCoreP6TC:192–213` 的 choose 给出）；
  最小 ind 提取孪生的清单见 state-O-CH11-KSLABK.md（KIND 车道候补 brief）。
-/

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **锐形 hslabK（event slabs 只到 `time last`）**：点态前提只要求 `t < time last`。 -/
theorem eventSlabsDerivative_of_supply_last_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀) (n : ℕ) {Q : ℝ}
    (hQ : ∀ t : ℝ, 0 ≤ t →
      t < (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) →
      (ρ t ^ 2)⁻¹ ≤ Q) :
    (F.tower.history n).EventSlabsDerivative Ctime₀ Q
      (Fin.last (F.tower.history n).eventCount) := by
  intro j _ y t ht hR
  have h0 : 0 ≤ t := by
    have hz : (F.tower.history n).time 0 ≤ (F.tower.history n).time j.castSucc :=
      (F.tower.history n).time_strictMono.monotone (Fin.zero_le _)
    rw [(F.tower.history n).time_zero] at hz
    exact hz.trans ht.1.le
  have htL : t < (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) :=
    ht.2.trans_le ((F.tower.history n).time_strictMono.monotone (Fin.le_last _))
  refine (hTD.1 n j y t ht ((hQ t h0 htL).trans_lt hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (sq_nonneg _)

/-- **hslabK 锐天花板（hgapJ 元组形）**：`(ρ(time last_n)²)⁻¹ ≤ Qs n` + antitone ⇒ HPB3 :639 / :917 合取项。 -/
theorem hslabK_of_supply_last_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) (ind : ℕ → ℕ) (Qs : ℕ → ℝ)
    (hQs : ∀ n, (ρ ((F.tower.history (ind n)).time
      (Fin.last (F.tower.history (ind n)).eventCount)) ^ 2)⁻¹ ≤ Qs n) :
    ∀ n, (F.tower.history (ind n)).EventSlabsDerivative Ctime₀ (Qs n)
      (Fin.last (F.tower.history (ind n)).eventCount) := fun n =>
  eventSlabsDerivative_of_supply_last_P6KS hTD hC (ind n) fun _ ht0 htL =>
    ceil_of_antitone_P6KS hρ hpos (hQs n) ht0 htL.le

/-- **C12-7′ ⇒ 天花板前提**：局部跳比（绝对时间尺度 `τ₀`）+ antitone ⇒ `t ≤ T ≤ σ + τ₀` 处
`(ρ t²)⁻¹ ≤ Λ²·(ρ σ²)⁻¹ ≤ Q`。 -/
theorem ceil_of_ratio_P6KS {ρ : ℝ → ℝ} (hρ : AntitoneOn ρ (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {τ₀ Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hratio : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ t' + τ₀ → ρ t' ≤ Λ * ρ t)
    {σ T Q : ℝ} (hσ : 0 ≤ σ) (hT : T ≤ σ + τ₀) (hQ : Λ ^ 2 * (ρ σ ^ 2)⁻¹ ≤ Q) :
    ∀ t : ℝ, 0 ≤ t → t ≤ T → (ρ t ^ 2)⁻¹ ≤ Q := by
  intro t ht0 htT
  have hs2 : 0 < ρ σ ^ 2 := pow_pos (hpos σ hσ) 2
  have ht2 : 0 < ρ t ^ 2 := pow_pos (hpos t ht0) 2
  have hΛ2 : 1 ≤ Λ ^ 2 := one_le_pow₀ hΛ
  have hinv0 : 0 ≤ (ρ σ ^ 2)⁻¹ := (inv_pos.mpr hs2).le
  rcases le_or_gt t σ with hts | hst
  · have hle : (ρ t ^ 2)⁻¹ ≤ (ρ σ ^ 2)⁻¹ :=
      ceil_of_antitone_P6KS hρ hpos le_rfl ht0 hts
    calc (ρ t ^ 2)⁻¹ ≤ (ρ σ ^ 2)⁻¹ := hle
      _ = 1 * (ρ σ ^ 2)⁻¹ := (one_mul _).symm
      _ ≤ Λ ^ 2 * (ρ σ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hΛ2 hinv0
      _ ≤ Q := hQ
  · have hr : ρ σ ≤ Λ * ρ t := hratio σ t hσ hst.le (htT.trans hT)
    have hsq : ρ σ ^ 2 ≤ Λ ^ 2 * ρ t ^ 2 := by
      have := pow_le_pow_left₀ (hpos σ hσ).le hr 2
      rwa [mul_pow] at this
    have hΛpos : 0 < Λ ^ 2 := zero_lt_one.trans_le hΛ2
    have key : (ρ t ^ 2)⁻¹ = Λ ^ 2 * (Λ ^ 2 * ρ t ^ 2)⁻¹ := by
      field_simp
    calc (ρ t ^ 2)⁻¹ = Λ ^ 2 * (Λ ^ 2 * ρ t ^ 2)⁻¹ := key
      _ ≤ Λ ^ 2 * (ρ σ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hs2 hsq) hΛpos.le
      _ ≤ Q := hQ

/-- **C12-7′ + 最小 ind ⇒ G1 天花板前提（一般形）**：`H ≤ Tno + 1`、`Tno − σo ≤ r²/2`、
`1 + r²/2 ≤ τ₀` ⇒ `H ≤ σo + τ₀` ⇒ `(ρ H²)⁻¹ ≤ Λ²·(ρ σo²)⁻¹ ≤ Q`。 -/
theorem ceiling_of_C127prime_minInd_gen_P6KS {ρ : ℝ → ℝ} (hρ : AntitoneOn ρ (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {τ₀ Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hratio : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ t' + τ₀ → ρ t' ≤ Λ * ρ t)
    {H Tno σo r Q : ℝ} (hσo : 0 ≤ σo) (hH0 : 0 ≤ H) (hind : H ≤ Tno + 1)
    (hsel : Tno - σo ≤ r ^ 2 / 2) (hτ : 1 + r ^ 2 / 2 ≤ τ₀) (hQ : Λ ^ 2 * (ρ σo ^ 2)⁻¹ ≤ Q) :
    (ρ H ^ 2)⁻¹ ≤ Q := by
  have hT : H ≤ σo + τ₀ := by linarith
  exact ceil_of_ratio_P6KS hρ hpos hΛ hratio hσo hT hQ H hH0 le_rfl

/-- **C12-7′（`τ₀ ≥ 2`）+ 最小 ind + selection（`0 ≤ r ≤ 1`）⇒ G1 天花板前提**（lead 08:1x 指定形）。 -/
theorem ceiling_of_C127prime_minInd_P6KS {ρ : ℝ → ℝ} (hρ : AntitoneOn ρ (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {τ₀ Λ : ℝ} (hτ₀ : 2 ≤ τ₀) (hΛ : 1 ≤ Λ)
    (hratio : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ t' + τ₀ → ρ t' ≤ Λ * ρ t)
    {H Tno σo r Q : ℝ} (hσo : 0 ≤ σo) (hH0 : 0 ≤ H) (hind : H ≤ Tno + 1)
    (hsel : Tno - σo ≤ r ^ 2 / 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hQ : Λ ^ 2 * (ρ σo ^ 2)⁻¹ ≤ Q) : (ρ H ^ 2)⁻¹ ≤ Q := by
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  exact ceiling_of_C127prime_minInd_gen_P6KS hρ hpos hΛ hratio hσo hH0 hind hsel
    (by linarith) hQ

/-- **hslabK（hgapJ 元组形，原尺度）⇐ supply + C12-7′ + 最小 ind**：`(ind n : ℝ) ≤ Tno n + 1`、
`Tno n − σo n ≤ r n²/2`、`0 ≤ r n ≤ 1`、`Λ²·ρ(σo n)⁻² ≤ Qs n` ⇒ HPB3 :639 / :917 合取项。 -/
theorem hslabK_of_C127prime_minInd_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {τ₀ Λ : ℝ} (hτ₀ : 2 ≤ τ₀)
    (hΛ : 1 ≤ Λ) (hratio : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ t' + τ₀ → ρ t' ≤ Λ * ρ t)
    (ind : ℕ → ℕ) (Tno σo r Qs : ℕ → ℝ) (hσo : ∀ n, 0 ≤ σo n)
    (hind : ∀ n, (ind n : ℝ) ≤ Tno n + 1) (hsel : ∀ n, Tno n - σo n ≤ r n ^ 2 / 2)
    (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n ≤ 1) (hQs : ∀ n, Λ ^ 2 * (ρ (σo n) ^ 2)⁻¹ ≤ Qs n) :
    ∀ n, (F.tower.history (ind n)).EventSlabsDerivative Ctime₀ (Qs n)
      (Fin.last (F.tower.history (ind n)).eventCount) :=
  hslabK_of_supply_P6KS hTD hC hρ hpos ind Qs fun n =>
    ceiling_of_C127prime_minInd_P6KS hρ hpos hτ₀ hΛ hratio (hσo n)
      ((F.tower.horizon_eq (ind n)).symm ▸ Nat.cast_nonneg (ind n))
      ((F.tower.horizon_eq (ind n)).le.trans (hind n)) (hsel n) (hr0 n) (hr1 n) (hQs n)

/-- **final (D1)(D2)（hgapJF 元组形，K 帧）⇐ supply + C12-7′ + 最小 ind**：同前提，K 帧阈值 `c n · Qo n`。 -/
theorem hfinalDt_of_C127prime_minInd_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {τ₀ Λ : ℝ} (hτ₀ : 2 ≤ τ₀)
    (hΛ : 1 ≤ Λ) (hratio : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ t' + τ₀ → ρ t' ≤ Λ * ρ t)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (Tno σo r Qo : ℕ → ℝ)
    (hσo : ∀ n, 0 ≤ σo n) (hind : ∀ n, (ind n : ℝ) ≤ Tno n + 1)
    (hsel : ∀ n, Tno n - σo n ≤ r n ^ 2 / 2) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n ≤ 1)
    (hQo : ∀ n, Λ ^ 2 * (ρ (σo n) ^ 2)⁻¹ ≤ Qo n) :
    let K : ℕ → RetainedCoreHistory.{u} := fun n =>
      (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
    (∀ n, (K n).EventSlabsDerivative Ctime₀ (c n * Qo n) (Fin.last (K n).eventCount)) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
          Ctime₀ (c n * Qo n) (K n).horizon) :=
  hfinalDt_of_supply_P6KS hTD hC hρ hpos ind c hc Qo fun n =>
    ceiling_of_C127prime_minInd_P6KS hρ hpos hτ₀ hΛ hratio (hσo n)
      ((F.tower.horizon_eq (ind n)).symm ▸ Nat.cast_nonneg (ind n))
      ((F.tower.horizon_eq (ind n)).le.trans (hind n)) (hsel n) (hr0 n) (hr1 n) (hQo n)

/-- consumer：锐天花板形喂 HPB3 :639 / :917 hslabK 合取项（`Qs n := max ((n+1)/c n) ρ(time last_n)⁻²`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0} (hρ : AntitoneOn q.neckRadius (Ici 0))
    (hTD : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (ind : ℕ → ℕ) (c : ℕ → ℝ) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let Qs : ℕ → ℝ := fun n =>
      max (((n : ℝ) + 1) / c n) (q.neckRadius ((Ho n).time (Fin.last (Ho n).eventCount)) ^ 2)⁻¹
    (∀ n, (Ho n).EventSlabsDerivative Ctime (Qs n) (Fin.last (Ho n).eventCount)) :=
  hslabK_of_supply_last_P6KS hTD le_rfl hρ q.neckRadius_pos ind _ fun _ => le_max_right _ _

/-- consumer：C12-7′ + 最小 ind 形喂 HPB3 :639 / :917 hslabK 合取项，
`Qs n := max ((n+1)/c n) (Λ²·ρ(σo n)⁻²)`（lead 指定 `Q n := max(n+1, Λ²ρ(σ)⁻²)` 的原尺度形）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0} (hρ : AntitoneOn q.neckRadius (Ici 0))
    (hTD : TimeDerivativeSupply_C11E F q.neckRadius Ctime) {τ₀ Λ : ℝ} (hτ₀ : 2 ≤ τ₀)
    (hΛ : 1 ≤ Λ) (hratio : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ t' + τ₀ →
      q.neckRadius t' ≤ Λ * q.neckRadius t)
    (ind : ℕ → ℕ) (c Tno σo r : ℕ → ℝ) (hσo : ∀ n, 0 ≤ σo n)
    (hind : ∀ n, (ind n : ℝ) ≤ Tno n + 1) (hsel : ∀ n, Tno n - σo n ≤ r n ^ 2 / 2)
    (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n ≤ 1) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let Qs : ℕ → ℝ := fun n =>
      max (((n : ℝ) + 1) / c n) (Λ ^ 2 * (q.neckRadius (σo n) ^ 2)⁻¹)
    (∀ n, (Ho n).EventSlabsDerivative Ctime (Qs n) (Fin.last (Ho n).eventCount)) :=
  hslabK_of_C127prime_minInd_P6KS hTD le_rfl hρ q.neckRadius_pos hτ₀ hΛ hratio ind Tno σo r _
    hσo hind hsel hr0 hr1 fun _ => le_max_right _ _

end GC.LongTime.Ch11
