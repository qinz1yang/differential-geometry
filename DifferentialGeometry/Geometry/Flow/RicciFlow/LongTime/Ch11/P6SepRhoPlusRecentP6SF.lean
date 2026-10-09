import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoPlusFixV2P6SF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepWindowLateCXW

/-!
# (SEP-ρ⁺)′ 的 recent 路线（不经 haccuracy、不需 hcap；O-CH11-SEPFIX，后缀 `_P6SF`）

A1/A3（kernel / SLICEDICH `hscaleK`）、A2（G8″ `hsepρ`）、A4（J6）的 recent 版。
`sepRhoPlus'_of_recent_P6SF`（G1）只需逐 record `nominalRadius ≤ η·ρ(T)`、`2η²N ≤ 1`、
recenter@tᵢ。本文件用 `RecentCutoffSupply_C11S` 形的 recent 前提（逐 n 阈值 `Tr n`）付
`nominalRadius ≤ η·ρ(T)`：`tᵢ ≤ T` 取 `t := T`，`tᵢ > T` 取 `t := tᵢ` 并用 `ρ` 反单调。

与 haccuracy 版的差异：`Tr(η_n)` 随 `n` 增长且与 `Tno n` 无已知关系，故 `∀ n` 形需要阈值前提
`Tr n ≤ Tn n`（A1–A3，逐 n 的显式前提；由上游取子列付），J6 序列形取子列 `φ`
（`exists_subseq_ge_P6SF`；与 CXW `j6_on_tail_of_accuracy_delta_CXW` 同形）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ### §0 子列抽取与逐 record 天花板 -/

/-- 子列抽取（`_P6SF`）：`Tno → ∞` 时任一阈值列 `Θ` 被某严格单调子列越过。 -/
theorem exists_subseq_ge_P6SF {Tno : ℕ → ℝ} (h : Tendsto Tno atTop atTop) (Θ : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, Θ n ≤ Tno (φ n) :=
  Filter.extraction_forall_of_eventually (fun n => h.eventually_ge_atTop (Θ n))

/-- **recent ⇒ 天花板处的名义半径界（`_P6SF`，PROVED）**：`Tr ≤ T ≤ 2tᵢ`，recent 前提
（`t ≥ Tr`、`tᵢ ∈ [t/2, t]` 时 `nominal ≤ η ρ(t)`）。`tᵢ ≤ T` 用 `t := T`；`tᵢ > T` 用 `t := tᵢ` 与
`ρ` 反单调（窗口 / 未来 records 不分情形）。 -/
theorem nominal_le_ceiling_of_recent_P6SF {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hanti : AntitoneOn p.neckRadius (Ici 0)) {η Tr T : ℝ} (hη : 0 ≤ η) (hT : 0 ≤ T)
    (hTr : Tr ≤ T) (hlate : T ≤ 2 * H.time i.succ)
    (hrec : ∀ t : ℝ, Tr ≤ t → H.time i.succ ∈ Icc (t / 2) t →
      ∀ h, R.nominalRadius h ≤ η * p.neckRadius t) :
    ∀ h, R.nominalRadius h ≤ η * p.neckRadius T := by
  intro h
  rcases le_or_gt (H.time i.succ) T with hle | hlt
  · exact hrec T hTr ⟨by linarith, hle⟩ h
  · have ht0 := H.time_nonneg i.succ
    refine (hrec _ (hTr.trans hlt.le) ⟨by linarith, le_rfl⟩ h).trans ?_
    exact mul_le_mul_of_nonneg_left
      (hanti (mem_Ici.mpr hT) (mem_Ici.mpr ht0) hlt.le) hη

/-- **(SEP-ρ⁺)′ ⇐ recent（`_P6SF`，PROVED）**：`N·(ρ(T)²)⁻¹ ≤ static.scale`。 -/
theorem sepRhoPlus'_of_recentSupply_P6SF {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hanti : AntitoneOn p.neckRadius (Ici 0))
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    {η Tr T N : ℝ} (hη : 0 ≤ η) (hηN : 2 * η ^ 2 * N ≤ 1) (hT : 0 ≤ T) (hTr : Tr ≤ T)
    (hlate : T ≤ 2 * H.time i.succ)
    (hrec : ∀ t : ℝ, Tr ≤ t → H.time i.succ ∈ Icc (t / 2) t →
      ∀ h, R.nominalRadius h ≤ η * p.neckRadius t) :
    N * (p.neckRadius T ^ 2)⁻¹ ≤ (R.static b).neck.scale :=
  sepRhoPlus'_of_recent_P6SF R b hΛδ (p.neckRadius_pos T hT)
    (nominal_le_ceiling_of_recent_P6SF R hanti hη hT hTr hlate hrec) hηN

/-! ### §1 A1 / A3：kernel / SLICEDICH `hscaleK` 槽 ⇐ recent -/

/-- **A1 / A3 ⇐ recent（`_P6SF`，PROVED，∀ n）**。结论同 `hscaleK_of_accuracy_P6SF`
（`Q n := ρ̂(Tn)⁻²`）；前提把 `hacc` / `hNT` 换成逐 n 的 recent 前提 `hrec`（阈值 `Tr n`）与
`Tr n ≤ Tn n`、`2 η_n² (n+1) ≤ 1`。 -/
theorem hscaleK_of_recent_P6SF {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {Tn Tr η : ℕ → ℝ} (hTn0 : ∀ n, 0 ≤ Tn n) (hT₀ : ∀ n, Tn n ≤ 2 * T₀ n)
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0))
    (hΛδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (habs : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹)
    (hη : ∀ n, 0 ≤ η n) (hηN : ∀ n : ℕ, 2 * η n ^ 2 * ((n : ℝ) + 1) ≤ 1)
    (hTr : ∀ n, Tr n ≤ Tn n)
    (hrec : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) (t : ℝ),
      Tr n ≤ t → (K n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (recordsK n i hi).nominalRadius h ≤ η n * (p n).neckRadius t) :
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) ((p n).neckRadius (Tn n) ^ 2)⁻¹ ≤
      ((recordsK n i hi).static b).neck.scale := by
  intro n i hi b
  rw [max_eq_right (habs n)]
  exact sepRhoPlus'_of_recentSupply_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) (hη n)
    (hηN n) (hTn0 n) (hTr n) ((hT₀ n).trans (by linarith)) (hrec n i hi)

/-! ### §2 A2：SLICE-BCBD3 G8″ `hsepρ`（窗口支 + 年轻 cap 支）⇐ recent -/

/-- **A2 ⇐ recent（`_P6SF`，PROVED）**。结论与前提同 `sepRhoPlusK_branch_of_accuracy_P6SF`，
去掉 `hacc` / `hNT`，加入逐 n 的 recent 前提（同 A1）。年轻 cap 支经 `youngCap_age_lt_P6SF`。 -/
theorem sepRhoPlusK_branch_of_recent_P6SF {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {c Tno Tn R Tr η : ℕ → ℝ} {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀) (hR : ∀ n, 0 < R n)
    (hc : ∀ n, 0 < c n) (hTn : ∀ n, Tn n = Tno n / c n) (h2 : ∀ n, 2 * c n < Tno n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, Tn n - 1 ^ 2 / 2 ≤ t n - T / R n)
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0))
    (hΛδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hρ0 : ∀ᶠ n in atTop, 8 * θ₀ * (p n).neckRadius 0 ^ 2 ≤ Tn n)
    (habs : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹)
    (hη : ∀ n, 0 ≤ η n) (hηN : ∀ n : ℕ, 2 * η n ^ 2 * ((n : ℝ) + 1) ≤ 1)
    (hTr : ∀ n, Tr n ≤ Tn n)
    (hrec : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) (s : ℝ),
      Tr n ≤ s → (K n).time i.succ ∈ Icc (s / 2) s →
      ∀ h, (recordsK n i hi).nominalRadius h ≤ η n * (p n).neckRadius s) :
    ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) ((p n).neckRadius (Tn n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale := by
  intro B hB
  filter_upwards [hwin B hB, hρ0] with n hw hρn
  intro i hi b hij hbr
  have hcn := hc n
  have hTn2 : 2 < Tn n := by
    rw [hTn n, lt_div_iff₀ hcn]
    linarith [h2 n]
  have hBR : 0 ≤ B / R n := div_nonneg hB.le (hR n).le
  have hlate : Tn n ≤ 2 * (K n).time i.succ := by
    rcases hbr with hwb | hyc
    · linarith
    · have hage := youngCap_age_lt_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) hθ₀ hyc
      nlinarith
  rw [max_eq_right (habs n)]
  exact sepRhoPlus'_of_recentSupply_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) (hη n)
    (hηN n) (by linarith) (hTr n) hlate (hrec n i hi)

/-! ### §3 A4：KTRUNC2c J6 ⇐ recent -/

/-- **A4 ⇐ recent（`_P6SF`，PROVED，单 history）**：同 `hpastJ6_of_accuracy_P6SF`，`hacc` 换成 recent。 -/
theorem hpastJ6_of_recent_P6SF {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {T₀ σ N c Tr η : ℝ}
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hanti : AntitoneOn p.neckRadius (Ici 0)) (hσ0 : 0 ≤ σ) (hN : 0 < N) (hc : 0 < c)
    (hρc : p.neckRadius σ ^ 2 ≤ c / N) (hlate : σ ≤ 2 * T₀)
    (hη : 0 ≤ η) (hηN : 2 * η ^ 2 * N ≤ 1) (hTr : Tr ≤ σ)
    (hrec : ∀ i hi (t : ℝ), Tr ≤ t → H.time i.succ ∈ Icc (t / 2) t →
      ∀ h, (records i hi).nominalRadius h ≤ η * p.neckRadius t)
    (hΛδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2) :
    ∀ i hi b, N * max (N / c) (p.neckRadius σ ^ 2)⁻¹ ≤ ((records i hi).static b).neck.scale := by
  intro i hi b
  have hρ := p.neckRadius_pos σ hσ0
  have habs : N / c ≤ (p.neckRadius σ ^ 2)⁻¹ := by
    rw [div_le_iff₀ hc, inv_mul_eq_div, le_div_iff₀ (pow_pos hρ 2)]
    have := (le_div_iff₀ hN).mp hρc
    linarith
  rw [max_eq_right habs]
  have hl : σ ≤ 2 * H.time i.succ := hlate.trans (by linarith)
  exact sepRhoPlus'_of_recentSupply_P6SF (records i hi) b hanti (hΛδ i hi) hη hηN hσ0 hTr hl
    (hrec i hi)

/-- **A4 序列形（取子列）⇐ recent + delta 衰减（`_P6SF`，PROVED）**：J6 的
`(n+1)·max((n+1)/c, Qs_loc)`（`Qs_loc` 同 KTRUNC2 L5 的 Q）在严格单调子列 `φ` 的 records 上成立；
recenter 用 late 形（`exists_late_recenter_CXW`），窗口 records 晚于 `Tδ` 由 `Tno(φ n)/2 ≥ Tδ` 给。
`recordsK` 的参数就是 profile `q`；`hrecent` 即 `RecentCutoffSupply_C11S` 限于这族 records。 -/
theorem j6_on_tail_of_recent_P6SF {Ho : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
    {T₀ c σ L R Tno Tn : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (Ho n).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ →
        GeometricCutoffRecord (Ho n).toHistory i q)
    (hc : ∀ n, 0 < c n) (hTn : ∀ n, Tn n = Tno n / c n)
    (h2 : ∀ n, 2 * c n < Tno n) (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ Tno n)
    (hR1 : ∀ n, 1 ≤ R n) (hL : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hdelta : Tendsto q.delta atTop (𝓝 0))
    (hρc : ∀ n : ℕ, q.neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1))
    (hrecent : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ s : ℝ, T ≤ s →
      ∀ n (i : Fin (Ho n).eventCount)
        (hi : max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ),
        (Ho n).time i.succ ∈ Icc (s / 2) s →
        ∀ h, (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius s) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c (φ n))
        (max (((n : ℝ) + 1) / c (φ n)) (q.neckRadius (Tno (φ n)) ^ 2)⁻¹) ≤
      ((recordsK (φ n) i hi).static b).neck.scale := by
  have hTno : Tendsto Tno atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hNT n]) tendsto_natCast_atTop_atTop
  obtain ⟨Tδ, _, hδlate⟩ := exists_late_recenter_CXW hdelta
  let η : ℕ → ℝ := fun n => 1 / (2 * ((n : ℝ) + 1))
  have hηpos : ∀ n, 0 < η n := fun n => by positivity
  have hηN : ∀ n : ℕ, 2 * η n ^ 2 * ((n : ℝ) + 1) ≤ 1 := fun n => by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hpos : 0 < (n : ℝ) + 1 := by linarith
    have heq : 2 * η n ^ 2 * ((n : ℝ) + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
      dsimp only [η]
      field_simp
    rw [heq]
    rw [div_le_one (by positivity)]
    linarith
  choose Tr _hTr0 hTrp using fun n => hrecent (η n) (hηpos n)
  obtain ⟨φ, hφ, hφT⟩ := exists_subseq_ge_P6SF hTno (fun n => max (Tr n) (2 * Tδ))
  refine ⟨φ, hφ, ?_⟩
  intro n i hi b
  rw [← max_assoc, max_self]
  have hk := hφT n
  have hTrk : Tr n ≤ Tno (φ n) := (le_max_left _ _).trans hk
  have hδk : Tδ ≤ Tno (φ n) / 2 := by linarith [(le_max_right _ _).trans hk]
  have hTno0 : 0 ≤ Tno (φ n) := by linarith [hc (φ n), h2 (φ n)]
  have hlate : Tno (φ n) ≤ 2 * max (T₀ (φ n)) (c (φ n) * (σ (φ n) - L (φ n) / R (φ n))) := by
    have := late_of_Ldomain_P6SF (hc (φ n)) (hTn (φ n)) (h2 (φ n)) (hR1 (φ n)) (hL (φ n))
      (le_max_right (T₀ (φ n)) (c (φ n) * (σ (φ n) - L (φ n) / R (φ n))))
    linarith
  have hnφ : (n : ℝ) + 1 ≤ ((φ n : ℕ) : ℝ) + 1 := by
    have : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
    linarith
  have hρc' : q.neckRadius (Tno (φ n)) ^ 2 ≤ c (φ n) / ((n : ℝ) + 1) :=
    (hρc (φ n)).trans (div_le_div_of_nonneg_left (hc (φ n)).le (Nat.cast_add_one_pos n) hnφ)
  refine hpastJ6_of_recent_P6SF (recordsK (φ n)) hanti hTno0 (Nat.cast_add_one_pos n)
    (hc (φ n)) hρc' hlate (hηpos n).le (hηN n) hTrk
    (fun i' hi' s hs hm h => hTrp n s hs (φ n) i' hi' hm h) ?_ i hi b
  intro i' hi'
  apply hδlate
  have := late_of_Ldomain_P6SF (hc (φ n)) (hTn (φ n)) (h2 (φ n)) (hR1 (φ n)) (hL (φ n))
    (le_max_right (T₀ (φ n)) (c (φ n) * (σ (φ n) - L (φ n) / R (φ n)))) |>.le
  linarith [(le_max_right _ _).trans hk, hi', hlate]

/-! ### §4 K 帧桥：原尺度 recent ⇒ 重标度 records 的 recent 前提 -/

/-- **重标度桥（`_P6SF`，PROVED）**：原尺度 records（参数 `q`）满足 recent 前提（阈值 `Tr`）⇒
`recordsKRescale_P6X3` 的重标度 records（参数 `q.rescale_P6N c`）满足 K 帧 recent 前提，阈值 `Tr/c`。
用 `nominal̃ = nominal/√c`、`ρ̂(t) = ρ(ct)/√c`、`timẽ = time/c`。 -/
theorem recent_rescale_P6SF {K : RetainedCoreHistory.{u}} {c : ℝ} (hc : 0 < c)
    {q : CutoffParameters} {T₀ Tr η : ℝ}
    (recs : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i q)
    (hrec : ∀ i hi (t : ℝ), Tr ≤ t → K.time i.succ ∈ Icc (t / 2) t →
      ∀ h, (recs i hi).nominalRadius h ≤ η * q.neckRadius t)
    (i : Fin (K.rescale_P6N c hc).eventCount)
    (hi : max 1 (T₀ / c) ≤ (K.rescale_P6N c hc).time i.succ)
    (t : ℝ) (ht : Tr / c ≤ t) (hm : (K.rescale_P6N c hc).time i.succ ∈ Icc (t / 2) t) :
    ∀ h, (K.recordsKRescale_P6X3 hc recs i hi).nominalRadius h ≤
      η * (q.rescale_P6N c hc).neckRadius t := by
  intro h
  have hi0 : T₀ ≤ K.time i.succ := RetainedCoreHistory.le_time_of_rescale_P6X3 hc
    (t := K.time i.succ) hi
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have htm : (K.rescale_P6N c hc).time i.succ = K.time i.succ / c := rfl
  rw [htm] at hm
  obtain ⟨hm1, hm2⟩ := hm
  rw [div_le_iff₀ hc] at hm2
  rw [le_div_iff₀ hc] at hm1
  have hTr : Tr ≤ c * t := by
    rw [div_le_iff₀ hc] at ht
    linarith
  have hm1' : c * t / 2 ≤ K.time i.succ := by
    calc c * t / 2 = t / 2 * c := by ring
      _ ≤ _ := hm1
  have hm2' : K.time i.succ ≤ c * t := by
    calc K.time i.succ ≤ t * c := hm2
      _ = c * t := by ring
  have hb := hrec i hi0 (c * t) hTr ⟨hm1', hm2'⟩ h
  change (recs i hi0).nominalRadius h / Real.sqrt c ≤ η * (q.neckRadius (c * t) / Real.sqrt c)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hb hs.le

/-- **consumer（`_P6SF`）**：原尺度 recent 前提 + 重标度桥 + A1/A3：K 帧
`K n = (Ho n).rescale_P6N (c n)`、`recordsK n = recordsKRescale_P6X3`、`p n = q.rescale_P6N (c n)`
上的 `hscaleK`（`Q n = ρ̂(Tn)⁻²`）。 -/
example {Ho : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters} {T₀ Tro Tno : ℕ → ℝ}
    {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (recs : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i q)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hΛδ : ∀ n (i : Fin ((Ho n).rescale_P6N (c n) (hc n)).eventCount),
      max 1 (T₀ n / c n) ≤ ((Ho n).rescale_P6N (c n) (hc n)).time i.succ →
        (q.rescale_P6N (c n) (hc n)).recenterConstant *
          (q.rescale_P6N (c n) (hc n)).delta (((Ho n).rescale_P6N (c n) (hc n)).time i.succ)
          ≤ 1 / 2)
    (hTno0 : ∀ n, 0 ≤ Tno n) (hseed : ∀ n, Tno n / c n ≤ 2 * max 1 (T₀ n / c n))
    (habs : ∀ n : ℕ, (n : ℝ) + 1 ≤
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tno n / c n) ^ 2)⁻¹)
    {η : ℕ → ℝ} (hη : ∀ n, 0 ≤ η n) (hηN : ∀ n : ℕ, 2 * η n ^ 2 * ((n : ℝ) + 1) ≤ 1)
    (hTro : ∀ n, Tro n ≤ Tno n)
    (hrec : ∀ n i hi (t : ℝ), Tro n ≤ t → (Ho n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (recs n i hi).nominalRadius h ≤ η n * q.neckRadius t) :
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) *
      max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tno n / c n) ^ 2)⁻¹ ≤
      ((((Ho n).recordsKRescale_P6X3 (hc n) (recs n)) i hi).static b).neck.scale :=
  hscaleK_of_recent_P6SF (fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recs n))
    (Tn := fun n => Tno n / c n) (Tr := fun n => Tro n / c n)
    (fun n => div_nonneg (hTno0 n) (hc n).le) hseed
    (fun n => anti_rescale_P6SF (hc n) hanti) hΛδ habs hη hηN
    (fun n => div_le_div_of_nonneg_right (hTro n) (hc n).le)
    (fun n i hi t ht hm => recent_rescale_P6SF (hc n) (recs n) (hrec n) i hi t ht hm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
