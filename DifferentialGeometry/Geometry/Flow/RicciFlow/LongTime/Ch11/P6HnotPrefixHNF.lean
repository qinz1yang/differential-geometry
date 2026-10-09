import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceRecords_P6N

/-!
# HNOTF G1：J10 帧 `hnot`（prefix 帧 cap 不命中）的 θ 换算、帧搬运与 ∀ᶠ → ∀ 工具（`_HNF`）

DRV-J10F `J10ResE_DJ`（`P6DrvResJ10DJ`）的 `hnot` 项是 prefix 帧
`H n := (K n).prefixAt (j n).castSucc` 上、trace 终点 `Fin.last`、年龄 `≤ θcap n·scale⁻¹`
（`1 − 1/(n+2) ≤ θcap n`）、窗口 `‖x‖ < D n + 1` 的 cap 不命中。本文件（全部 PROVED）：
* **θ 方向**：cap 不命中命题对 `(θ, D)` 反单调（`capNot_mono_HNF`）。`θ₀ ≤ 1/2 ≤ 1 − 1/(n+2)`
  （`theta0_le_thetaCap_HNF`）⇒ θcap 形蕴含 θ₀ 形（`hnot_theta0_of_thetaCap_HNF`），**反向不成立**
  （θ₀ 形只排除年龄 `≤ θ₀/scale` 的 cap；取 n 大无用，θcap n ↑ 1 而 θ₀ 固定）。故 J10 项须由 HNOT 的
  θ n 形（`θ n = 1 − 1/(n+2)`）付，不能由 θ₀ 形付。
* **帧搬运**：`hnot_prefix_of_hnotK_HNF`——K 帧（event 帧 `i.succ ≤ (j n).castSucc`，`‖x‖ < n + 2`，
  年龄 θ n）⇒ prefix 帧（records := `prefixLateRecords_P6N`，`θcap ≤ θ`、`D ≤ n + 1`），
  经 `not_capWindowPoint_prefix_of_late_P6N`。
* **∀ᶠ → ∀（T₀ 有限前段抬高）**：`raiseT0_HNF K T₀ N`（`n < N` 处抬过 horizon，否则不变）；抬高后 records
  （`raiseRecords_HNF`）在前段为空，record 量化的 ∀ᶠ 命题变 ∀（`forall_raise_of_eventually_HNF`）；
  尾相等（`raiseT0_eventually_eq_HNF`）⇒ `∀ B, ∀ᶠ n, T₀ n ≤ …` 型合取不受影响。
* `prefixDt_of_lastDt_HNF`：`EventSlabsDerivative … (Fin.last _)` ⇒ hnotK 要的两条前缀 Dt。
无新顶层 binder；不假设 `hqR`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- `1/2 ≤ 1 − 1/(n+2)`（`_HNF`）。 -/
theorem half_le_thetaCap_HNF (n : ℕ) : (1 : ℝ) / 2 ≤ 1 - 1 / ((n : ℝ) + 2) := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- `1 − 1/(n+2) < 1`（`_HNF`）。 -/
theorem thetaCap_lt_one_HNF (n : ℕ) : 1 - 1 / ((n : ℝ) + 2) < 1 := by
  have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  linarith

/-- **θ₀ ≤ θcap**（`_HNF`）：`θ₀ ≤ 1/2`（R20：`θ₀ = min(1/2, …)`）⇒ `θ₀ ≤ 1 − 1/(n+2)`（∀ n）。 -/
theorem theta0_le_thetaCap_HNF {θ₀ : ℝ} (h : θ₀ ≤ 1 / 2) (n : ℕ) :
    θ₀ ≤ 1 - 1 / ((n : ℝ) + 2) :=
  h.trans (half_le_thetaCap_HNF n)

/-- **cap 不命中对 `(θ, D)` 反单调**（`_HNF`，任一 history / 终点 stage `k` / late records）。 -/
theorem capNot_mono_HNF (K : RetainedCoreHistory.{u}) (k : Fin (K.eventCount + 1))
    {p : CutoffParameters} {T₀ t D D' θ θ' : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (y : (K.stage k).Carrier) (hD : D' ≤ D) (hθ : θ' ≤ θ)
    (hnot : ¬ ∃ (i : Fin K.eventCount) (hi : T₀ ≤ K.time i.succ) (hl : i.succ ≤ k)
      (A : BackwardPointTrace K.toHistory i.succ k hl y)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point i.succ le_rfl hl = ((records i hi).static b).window x ∧ ‖x.val‖ < D + 1 ∧
        t - K.time i.succ ≤ θ * (((records i hi).static b).neck.scale)⁻¹) :
    ¬ ∃ (i : Fin K.eventCount) (hi : T₀ ≤ K.time i.succ) (hl : i.succ ≤ k)
      (A : BackwardPointTrace K.toHistory i.succ k hl y)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point i.succ le_rfl hl = ((records i hi).static b).window x ∧ ‖x.val‖ < D' + 1 ∧
        t - K.time i.succ ≤ θ' * (((records i hi).static b).neck.scale)⁻¹ := by
  rintro ⟨i, hi, hl, A, b, x, h1, h2, h3⟩
  refine hnot ⟨i, hi, hl, A, b, x, h1, by linarith, h3.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hθ
    (inv_nonneg.mpr ((records i hi).static b).neck.scale_pos.le)

/-- **方向（`_HNF`）**：θcap 形（`1 − 1/(n+2)`）⇒ θ₀ 形（`θ₀ ≤ 1/2`）。反向不成立（见头注）。 -/
theorem hnot_theta0_of_thetaCap_HNF (K : RetainedCoreHistory.{u}) (k : Fin (K.eventCount + 1))
    {p : CutoffParameters} {T₀ t D θ₀ : ℝ} (n : ℕ)
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (y : (K.stage k).Carrier) (hθ₀ : θ₀ ≤ 1 / 2)
    (hnot : ¬ ∃ (i : Fin K.eventCount) (hi : T₀ ≤ K.time i.succ) (hl : i.succ ≤ k)
      (A : BackwardPointTrace K.toHistory i.succ k hl y)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point i.succ le_rfl hl = ((records i hi).static b).window x ∧ ‖x.val‖ < D + 1 ∧
        t - K.time i.succ ≤ (1 - 1 / ((n : ℝ) + 2)) * (((records i hi).static b).neck.scale)⁻¹) :
    ¬ ∃ (i : Fin K.eventCount) (hi : T₀ ≤ K.time i.succ) (hl : i.succ ≤ k)
      (A : BackwardPointTrace K.toHistory i.succ k hl y)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point i.succ le_rfl hl = ((records i hi).static b).window x ∧ ‖x.val‖ < D + 1 ∧
        t - K.time i.succ ≤ θ₀ * (((records i hi).static b).neck.scale)⁻¹ :=
  capNot_mono_HNF K k records y le_rfl (theta0_le_thetaCap_HNF hθ₀ n) hnot

/-- **帧搬运（`_HNF`，PROVED）**：K 帧 hnotK（HNOT θ n 形结论逐字：`i.succ ≤ (j n).castSucc`、
`‖x‖ < (n+1)+1`、年龄 `θ n`）⇒ J10 prefix 帧 `hnot`（records := `prefixLateRecords_P6N`，
`θcap n ≤ θ n`、`D n ≤ n + 1`）。 -/
theorem hnot_prefix_of_hnotK_HNF {K : ℕ → RetainedCoreHistory.{u}}
    (j : ∀ n, Fin (K n).eventCount) {p : ℕ → CutoffParameters} {T₀ t θ θcap D : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier)
    (hθ : ∀ n, θcap n ≤ θ n) (hD : ∀ n : ℕ, D n ≤ (n : ℝ) + 1)
    (hnotK : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹) :
    ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θcap n *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
  fun n => capNot_mono_HNF ((K n).prefixAt (j n).castSucc) (Fin.last _) _ (yG n) (hD n) (hθ n)
    ((K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n) (yG n) (hnotK n))

/-- **T₀ 有限前段抬高（`_HNF`）**：`n < N` 处取 `max (T₀ n) (horizon + 1)`，否则 `T₀ n`。 -/
def raiseT0_HNF (K : ℕ → RetainedCoreHistory.{u}) (T₀ : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n < N then max (T₀ n) ((K n).horizon + 1) else T₀ n

theorem le_raiseT0_HNF (K : ℕ → RetainedCoreHistory.{u}) (T₀ : ℕ → ℝ) (N n : ℕ) :
    T₀ n ≤ raiseT0_HNF K T₀ N n := by
  unfold raiseT0_HNF
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem raiseT0_of_le_HNF (K : ℕ → RetainedCoreHistory.{u}) (T₀ : ℕ → ℝ) {N n : ℕ}
    (h : N ≤ n) : raiseT0_HNF K T₀ N n = T₀ n := by
  have h' : ¬ n < N := by omega
  simp only [raiseT0_HNF, h', ↓reduceIte]

theorem raiseT0_eventually_eq_HNF (K : ℕ → RetainedCoreHistory.{u}) (T₀ : ℕ → ℝ) (N : ℕ) :
    ∀ᶠ n in atTop, raiseT0_HNF K T₀ N n = T₀ n :=
  eventually_atTop.mpr ⟨N, fun _ hn => raiseT0_of_le_HNF K T₀ hn⟩

/-- 抬高后 `∀ B, ∀ᶠ n, T₀ n ≤ f B n` 型合取保持（尾相等）。 -/
theorem eventually_raiseT0_le_HNF (K : ℕ → RetainedCoreHistory.{u}) (T₀ : ℕ → ℝ) (N : ℕ)
    {f : ℝ → ℕ → ℝ} (h : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ f B n) :
    ∀ B : ℝ, ∀ᶠ n in atTop, raiseT0_HNF K T₀ N n ≤ f B n := fun B =>
  ((h B).and (raiseT0_eventually_eq_HNF K T₀ N)).mono fun _ hn => hn.2.symm ▸ hn.1

/-- 前段（`n < N`）无事件满足抬高阈值。 -/
theorem not_raiseT0_le_HNF (K : ℕ → RetainedCoreHistory.{u}) (T₀ : ℕ → ℝ) {N n : ℕ}
    (h : n < N) (i : Fin (K n).eventCount) : ¬ raiseT0_HNF K T₀ N n ≤ (K n).time i.succ := by
  intro hle
  have h1 : (K n).time i.succ ≤ (K n).horizon := (K n).toHistory.time_le_horizon_at i.succ
  have h2 : (K n).horizon + 1 ≤ raiseT0_HNF K T₀ N n := by
    simp only [raiseT0_HNF, h, ↓reduceIte]
    exact le_max_right _ _
  linarith

/-- 抬高阈值下的 late records（`_HNF`）：原 records 的限制。 -/
def raiseRecords_HNF {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (N : ℕ) (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)) :
    ∀ n (i : Fin (K n).eventCount), raiseT0_HNF K T₀ N n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n) :=
  fun n i hi => recordsK n i ((le_raiseT0_HNF K T₀ N n).trans hi)

/-- **∀ᶠ → ∀（`_HNF`）**：record 量化命题的 ∀ᶠ 形 ⇒ 抬高阈值下的 ∀ 形（前段空真）。 -/
theorem forall_raise_of_eventually_HNF {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ}
    (P : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ → Prop)
    (h : ∀ᶠ n in atTop, ∀ i hi, P n i hi) :
    ∃ N : ℕ, ∀ n (i : Fin (K n).eventCount) (hi : raiseT0_HNF K T₀ N n ≤ (K n).time i.succ),
      P n i ((le_raiseT0_HNF K T₀ N n).trans hi) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun n i hi => ?_⟩
  by_cases hn : n < N
  · exact absurd hi (not_raiseT0_le_HNF K T₀ hn i)
  · exact hN n (not_lt.mp hn) i _

/-- **前缀 Dt ⇐ 全 slab Dt（`_HNF`）**：`EventSlabsDerivative C Q (Fin.last _)` ⇒ hnotK 的两条前缀 Dt
（slab `< j` 与 slab `j` 的 `(time j⁻, t)`，`t ≤ time j.succ`）。 -/
theorem prefixDt_of_lastDt_HNF (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {C : ℝ≥0} {Q t : ℝ} (h : K.EventSlabsDerivative C Q (Fin.last K.eventCount))
    (ht : t ≤ K.time j.succ) :
    K.EventSlabsDerivative C Q j.castSucc ∧
      (K.toHistory.event j).incoming.DerivativeBoundBefore C Q t :=
  ⟨fun i _ => h i (Fin.castSucc_lt_last i),
    (K.toHistory.event j).incoming.derivativeBoundBefore_mono ht (h j (Fin.castSucc_lt_last j))⟩

end RetainedCoreHistory

/-- consumer（`_HNF`）：θ₀ = 1/4 处，θcap 形 cap 不命中给出 θ₀ 形。 -/
example (K : RetainedCoreHistory.{0}) (k : Fin (K.eventCount + 1)) {p : CutoffParameters}
    {T₀ t D : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (y : (K.stage k).Carrier)
    (hnot : ¬ ∃ (i : Fin K.eventCount) (hi : T₀ ≤ K.time i.succ) (hl : i.succ ≤ k)
      (A : BackwardPointTrace K.toHistory i.succ k hl y)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point i.succ le_rfl hl = ((records i hi).static b).window x ∧ ‖x.val‖ < D + 1 ∧
        t - K.time i.succ ≤
          (1 - 1 / (((3 : ℕ) : ℝ) + 2)) * (((records i hi).static b).neck.scale)⁻¹) :
    ¬ ∃ (i : Fin K.eventCount) (hi : T₀ ≤ K.time i.succ) (hl : i.succ ≤ k)
      (A : BackwardPointTrace K.toHistory i.succ k hl y)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point i.succ le_rfl hl = ((records i hi).static b).window x ∧ ‖x.val‖ < D + 1 ∧
        t - K.time i.succ ≤ (1 / 4) * (((records i hi).static b).neck.scale)⁻¹ :=
  K.hnot_theta0_of_thetaCap_HNF k 3 records y (by norm_num) hnot

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
