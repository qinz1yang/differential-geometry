import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscaleKSepRhoP6HN

/-!
# J6（局部阈值 `Qs_loc`）⇐ (SEP-ρ⁺@Tno) 过去窗 + 未来 records 自动（O-CH11-KTRUNC2c G4c，`_P6KT2c`）

producer 孪生（`P6GapProducers{,Final}LocP6KT2c`）把 `Qs` 换成局部阈值
`Qs_loc n := max ((n+1)/c n) (ρ(Tno n)²)⁻¹`（ρ = profile 半径，`Tno` = 原尺度 seed 时刻 `T_n^orig`，
**不是** `σ`；与 J9 截断点 `tK := Tno`、K 帧 `Tn = Tno / c` 同一阈值）。此时 J6
`(n+1)·max((n+1)/c, Qs_loc) ≤ scale` 按 `max` 幂等即 (SEP-ρ⁺@Tno) 原尺度形
`N·max(N/c, ρ(Tno)⁻²) ≤ S_orig`（`N = n+1`）。本文件把它拆成：
* **单一具名假设 `hpast`**（过去 records，`time i⁺ ≤ Tno`）——(SEP-ρ⁺@Tno) 原尺度形逐字；SEPFIX 的新形经
  本文件唯一 adapter `j6Loc_of_sepRhoPlus_P6KT2c` 的 `hpast` 位接入；
* **未来 records**（`Tno < time i⁺`）自动：`sepRhoPlus_future_sharp_P6KT2c`（HNOT G3
  `sepRhoPlus_future_P6HN` 的锐形：`ρ(0)` 换 `ρ(Tno)`，并用 K 帧选择 `ρ(Tno)² ≤ c/N`，结论与 `c` 无关），
  只需 `recenterConstant·δ(tᵢ) ≤ 1/2` 与 `2N·δ(tᵢ)⁴ ≤ 1`；
* `ρ(Tno)² ≤ c/N` ⇐ hgap 望远镜内既有的 K 帧选择 `R ≤ ρ_K(Tn)⁻²` 与 `N ≤ R`（`rhoSq_le_of_sel_P6KT2c`、
  `sel_orig_of_rescale_P6KT2c`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **未来 record 的 (SEP-ρ⁺) 锐形（`_P6KT2c`，PROVED）**：`σ ≤ tᵢ`、ρ antitone、`ρ(σ)² ≤ c/N`、
`recenterConstant·δ(tᵢ) ≤ 1/2`、`2N·δ(tᵢ)⁴ ≤ 1` ⇒ `N·max(N/c, ρ(σ)⁻²) ≤ scale`（锐形 birth）。 -/
theorem sepRhoPlus_future_sharp_P6KT2c {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hanti : AntitoneOn p.neckRadius (Ici 0))
    {σ N c : ℝ} (hσ0 : 0 ≤ σ) (hσi : σ ≤ H.time i.succ) (hN : 0 < N) (hc : 0 < c)
    (hρc : p.neckRadius σ ^ 2 ≤ c / N)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hδ : 2 * N * p.delta (H.time i.succ) ^ 4 ≤ 1) :
    N * max (N / c) (p.neckRadius σ ^ 2)⁻¹ ≤ (R.static b).neck.scale := by
  have hS := static_scale_gt_birth_P6HN R b hΛδ
  have ht : 0 ≤ H.time i.succ := hσ0.trans hσi
  have hρi := p.neckRadius_pos _ ht
  have hρσ := p.neckRadius_pos _ hσ0
  have hδpos := p.delta_pos _ ht
  have hiσ : p.neckRadius (H.time i.succ) ≤ p.neckRadius σ :=
    hanti (mem_Ici.mpr hσ0) (mem_Ici.mpr ht) hσi
  set a := p.delta (H.time i.succ) ^ 4 with ha
  set ri := p.neckRadius (H.time i.succ) with hri
  set rσ := p.neckRadius σ with hrσ
  have ha0 : 0 < a := by positivity
  have hX : (2 * (p.delta (H.time i.succ) ^ 2 * ri) ^ 2) = 2 * a * ri ^ 2 := by
    rw [ha]
    ring
  rw [hX] at hS
  have hXpos : 0 < 2 * a * ri ^ 2 := by positivity
  have hriσ : ri ^ 2 ≤ rσ ^ 2 := pow_le_pow_left₀ hρi.le hiσ 2
  have h2aN : 2 * a * N ≤ 1 := by linarith
  have hcne : c ≠ 0 := hc.ne'
  have hNne : N ≠ 0 := hN.ne'
  rw [mul_max_of_nonneg _ _ hN.le]
  refine max_le ?_ ?_
  · have h1 : N * (N / c) * (2 * a * ri ^ 2) ≤ 1 := by
      have h3 : N * (N / c) * (2 * a * ri ^ 2) ≤ N * (N / c) * (2 * a * (c / N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hriσ.trans hρc) (by positivity)) (by positivity)
      have h4 : N * (N / c) * (2 * a * (c / N)) = 2 * a * N := by
        field_simp
      linarith
    have h5 : N * (N / c) ≤ (2 * a * ri ^ 2)⁻¹ := by
      rw [show (2 * a * ri ^ 2)⁻¹ = 1 / (2 * a * ri ^ 2) from (one_div _).symm,
        le_div_iff₀ hXpos]
      exact h1
    exact h5.trans hS.le
  · have h1 : N * (rσ ^ 2)⁻¹ * (2 * a * ri ^ 2) ≤ 1 := by
      have hq : ri ^ 2 * (rσ ^ 2)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        exact hriσ
      have h6 : N * (rσ ^ 2)⁻¹ * (2 * a * ri ^ 2) = 2 * a * N * (ri ^ 2 * (rσ ^ 2)⁻¹) := by
        ring
      rw [h6]
      calc 2 * a * N * (ri ^ 2 * (rσ ^ 2)⁻¹) ≤ 2 * a * N * 1 :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ 1 := by linarith
    have h5 : N * (rσ ^ 2)⁻¹ ≤ (2 * a * ri ^ 2)⁻¹ := by
      rw [show (2 * a * ri ^ 2)⁻¹ = 1 / (2 * a * ri ^ 2) from (one_div _).symm,
        le_div_iff₀ hXpos]
      exact h1
    exact h5.trans hS.le

/-- **J6 adapter（`_P6KT2c`，PROVED；SEPFIX 接入点）**：单个 history，records 以 `T₀` 为阈。过去 records
（`time i⁺ ≤ σ`）由**单一具名假设** `hpast`（(SEP-ρ⁺@σ) 原尺度形）付；未来 records 由
`sepRhoPlus_future_sharp_P6KT2c` 付。结论 = J6 在 `Qs_loc := max (N/c) (ρ(σ)²)⁻¹` 处的形
`N·max(N/c, Qs_loc) ≤ scale`（取 `σ := Tno n`、`N := n+1`）。 -/
theorem j6Loc_of_sepRhoPlus_P6KT2c {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {T₀ σ N c : ℝ}
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hanti : AntitoneOn p.neckRadius (Ici 0)) (hσ0 : 0 ≤ σ) (hN : 0 < N) (hc : 0 < c)
    (hρc : p.neckRadius σ ^ 2 ≤ c / N)
    (hpast : ∀ i hi b, H.time i.succ ≤ σ →
      N * max (N / c) (p.neckRadius σ ^ 2)⁻¹ ≤ ((records i hi).static b).neck.scale)
    (hΛδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → σ < H.time i.succ →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → σ < H.time i.succ →
      2 * N * p.delta (H.time i.succ) ^ 4 ≤ 1) :
    ∀ i hi b, N * max (N / c) (max (N / c) (p.neckRadius σ ^ 2)⁻¹) ≤
      ((records i hi).static b).neck.scale := by
  intro i hi b
  rw [← max_assoc, max_self]
  by_cases hiσ : H.time i.succ ≤ σ
  · exact hpast i hi b hiσ
  · have hlt : σ < H.time i.succ := lt_of_not_ge hiσ
    exact sepRhoPlus_future_sharp_P6KT2c (records i hi) b hanti hσ0 hlt.le hN hc hρc
      (hΛδ i hi hlt) (hδ i hi hlt)

/-- `R ≤ c/ρ²`、`N ≤ R`、`ρ, R, N > 0` ⇒ `ρ² ≤ c/N`（`_P6KT2c`）。 -/
theorem rhoSq_le_of_sel_P6KT2c {ρ R c N : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hN : 0 < N)
    (hsel : R ≤ c / ρ ^ 2) (hNR : N ≤ R) : ρ ^ 2 ≤ c / N := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have h1 : R * ρ ^ 2 ≤ c := (le_div_iff₀ hρ2).mp hsel
  have hc : 0 ≤ c := le_trans (by positivity) h1
  have h2 : ρ ^ 2 ≤ c / R := by
    rw [le_div_iff₀ hR]
    linarith
  exact h2.trans (div_le_div_of_nonneg_left hc hN hNR)

/-- K 帧选择（hgap 望远镜 `R ≤ ((q.rescale_P6N c).neckRadius (Tno/c) ^ 2)⁻¹`）⇒ 原尺度 `R ≤ c/ρ(Tno)²`
（`_P6KT2c`；`ρ_K(t) = ρ(c·t)/√c`）。 -/
theorem sel_orig_of_rescale_P6KT2c (q : CutoffParameters) {c : ℝ} (hc : 0 < c) {R Tno : ℝ}
    (h : R ≤ ((q.rescale_P6N c hc).neckRadius (Tno / c) ^ 2)⁻¹) :
    R ≤ c / q.neckRadius Tno ^ 2 := by
  change R ≤ ((q.neckRadius (c * (Tno / c)) / Real.sqrt c) ^ 2)⁻¹ at h
  rw [show c * (Tno / c) = Tno by field_simp, div_pow, Real.sq_sqrt hc.le, inv_div] at h
  exact h

/-- consumer（adapter 形核对）：hgap 望远镜的 K 帧选择 `hQρ`（时刻 `Tn = rescaleTime Tno`）+ `N ≤ R` ⇒
`hρc`（`ρ(Tno)² ≤ c/N`）。 -/
example (Ho : RetainedCoreHistory.{u}) (q : CutoffParameters) {c : ℝ} (hc : 0 < c)
    (Tno : Icc (0 : ℝ) Ho.toHistory.horizon) {R N : ℝ} (hR : 0 < R) (hN : 0 < N) (hNR : N ≤ R)
    (hQρ : R ≤ ((q.rescale_P6N c hc).neckRadius (Ho.rescaleTime_P6X hc Tno) ^ 2)⁻¹) :
    q.neckRadius Tno ^ 2 ≤ c / N :=
  rhoSq_le_of_sel_P6KT2c (q.neckRadius_pos _ Tno.2.1) hR hN
    (sel_orig_of_rescale_P6KT2c q hc hQρ) hNR

/-- consumer（J6 族形）：`hOpen*J` 的 J6 输出形（`Qs := Qs_loc`，`σ := Tno n`，`N := n+1`）逐字。 -/
example {Ho : ℕ → RetainedCoreHistory.{u}} {p : ℕ → CutoffParameters} {T₀ c Tno : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n))
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0)) (hT0 : ∀ n, 0 ≤ Tno n)
    (hc : ∀ n, 0 < c n) (hρc : ∀ n : ℕ, (p n).neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1))
    (hpast : ∀ (n : ℕ) i hi b, (Ho n).time i.succ ≤ Tno n →
      ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) ((p n).neckRadius (Tno n) ^ 2)⁻¹ ≤
        ((recordsK n i hi).static b).neck.scale)
    (hΛδ : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
      Tno n < (Ho n).time i.succ →
        (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2)
    (hδ : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
      Tno n < (Ho n).time i.succ → 2 * ((n : ℝ) + 1) * (p n).delta ((Ho n).time i.succ) ^ 4 ≤ 1) :
    let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) ((p n).neckRadius (Tno n) ^ 2)⁻¹
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
      ((recordsK n i hi).static b).neck.scale :=
  fun n => j6Loc_of_sepRhoPlus_P6KT2c (recordsK n) (hanti n) (hT0 n) (Nat.cast_add_one_pos n)
    (hc n) (hρc n) (hpast n) (hΛδ n) (hδ n)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
