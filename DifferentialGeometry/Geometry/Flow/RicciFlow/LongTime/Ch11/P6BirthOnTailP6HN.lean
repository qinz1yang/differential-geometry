import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoPlusRecentP6SF

/-!
# J6 的因子 N 孪生：cap 出生尺度 ⇐ recent（O-CH11-HNOT-LOCALDT / HNOT-A3 G10，后缀 `_P6HN`）

SEPFIX `j6_on_tail_of_recent_P6SF`（P6SepRhoPlusRecentP6SF:169）给出因子 `n + 1`：
`(n+1)·max((n+1)/c, Qs_loc) ≤ scale`。G9（final 帧 CWW hnotK）的出生前提 `Q_K ≤ Cb n·scale_K`
要因子 `(Cb n)⁻¹`（`Cb` 无下界）。本文件对任意正序列 `N` 给出因子 `M n := max (n+1) (N n)` 版：
* `η n := 1/(2·M n)` ⇒ `2·η²·M ≤ 1`；子列 φ 越过 `max (Tr n) (2·Tδ)`（同 SEPFIX 原证明）；
* `(n+1)/c ≤ ρ(Tno)⁻²` 由 `hρc`（`ρ(Tno)² ≤ c/(n+1)`）吸收，因此 `max ((n+1)/c) (ρ⁻²) = ρ⁻²`，
  再用 `sepRhoPlus'_of_recentSupply_P6SF`（对任意 `N` 成立）取 `N := M n`。
主定理 `birth_on_tail_of_recent_P6HN`；consumer：`N n := (Cb n)⁻¹` 时得到 `Qs_loc ≤ Cb n·scale`
（`qs_le_birth_of_tail_P6HN`），`N := n + 1` 时就是原 J6（`example`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **J6 因子 N 孪生（`_P6HN`，PROVED）**：`max (n+1) (N n)·max((n+1)/c, ρ(Tno)⁻²) ≤ scale`（子列 φ）。 -/
theorem birth_on_tail_of_recent_P6HN {Ho : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
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
        ∀ h, (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius s)
    (N : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (n : ℕ) i hi b,
      max ((n : ℝ) + 1) (N n) * max (((n : ℝ) + 1) / c (φ n))
        (q.neckRadius (Tno (φ n)) ^ 2)⁻¹ ≤
      ((recordsK (φ n) i hi).static b).neck.scale := by
  have hTno : Tendsto Tno atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hNT n]) tendsto_natCast_atTop_atTop
  obtain ⟨Tδ, _, hδlate⟩ := exists_late_recenter_CXW hdelta
  set M : ℕ → ℝ := fun n => max ((n : ℝ) + 1) (N n) with hMdef
  have hM1 : ∀ n : ℕ, 1 ≤ M n := fun n =>
    le_trans (by linarith [Nat.cast_nonneg (α := ℝ) n]) (le_max_left _ _)
  have hMpos : ∀ n, 0 < M n := fun n => lt_of_lt_of_le one_pos (hM1 n)
  let η : ℕ → ℝ := fun n => 1 / (2 * M n)
  have hηpos : ∀ n, 0 < η n := fun n => by have := hMpos n; positivity
  have hηN : ∀ n : ℕ, 2 * η n ^ 2 * M n ≤ 1 := fun n => by
    have hp := hMpos n
    have heq : 2 * η n ^ 2 * M n = 1 / (2 * M n) := by
      dsimp only [η]
      field_simp
    rw [heq, div_le_one (by positivity)]
    linarith [hM1 n]
  choose Tr _hTr0 hTrp using fun n => hrecent (η n) (hηpos n)
  obtain ⟨φ, hφ, hφT⟩ := exists_subseq_ge_P6SF hTno (fun n => max (Tr n) (2 * Tδ))
  refine ⟨φ, hφ, ?_⟩
  intro n i hi b
  have hk := hφT n
  have hTrk : Tr n ≤ Tno (φ n) := (le_max_left _ _).trans hk
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
  have hρ := q.neckRadius_pos (Tno (φ n)) hTno0
  have habs : ((n : ℝ) + 1) / c (φ n) ≤ (q.neckRadius (Tno (φ n)) ^ 2)⁻¹ := by
    rw [div_le_iff₀ (hc (φ n)), inv_mul_eq_div, le_div_iff₀ (pow_pos hρ 2)]
    have := (le_div_iff₀ (Nat.cast_add_one_pos n)).mp hρc'
    linarith
  rw [max_eq_right habs]
  have hti : (Ho (φ n)).time i.succ ≥ max (T₀ (φ n)) (c (φ n) * (σ (φ n) - L (φ n) / R (φ n))) :=
    hi
  have hl : Tno (φ n) ≤ 2 * (Ho (φ n)).time i.succ := hlate.trans (by linarith)
  have hΛδ : q.recenterConstant * q.delta ((Ho (φ n)).time i.succ) ≤ 1 / 2 := by
    apply hδlate
    have := late_of_Ldomain_P6SF (hc (φ n)) (hTn (φ n)) (h2 (φ n)) (hR1 (φ n)) (hL (φ n))
      (le_max_right (T₀ (φ n)) (c (φ n) * (σ (φ n) - L (φ n) / R (φ n)))) |>.le
    linarith [(le_max_right _ _).trans hk, hti, hlate]
  exact sepRhoPlus'_of_recentSupply_P6SF (recordsK (φ n) i hi) b hanti hΛδ (hηpos n).le
    (hηN n) hTno0 hTrk hl (fun s hs hm h => hTrp n s hs (φ n) i hi hm h)

/-- consumer（`_P6HN`）：因子 `M ≥ (Cb)⁻¹` ⇒ 出生尺度 `max((n+1)/c, ρ⁻²) ≤ Cb·scale`（G9 的 birth 形，原尺度）。 -/
theorem qs_le_birth_of_tail_P6HN {Cb M Qs s : ℝ} (hCb : 0 < Cb) (hM : Cb⁻¹ ≤ M)
    (hQs : 0 ≤ Qs) (h : M * Qs ≤ s) : Qs ≤ Cb * s := by
  have h1 : Cb⁻¹ * Qs ≤ s := (mul_le_mul_of_nonneg_right hM hQs).trans h
  have h2 := mul_le_mul_of_nonneg_left h1 hCb.le
  rwa [← mul_assoc, mul_inv_cancel₀ hCb.ne', one_mul] at h2

/-- consumer（`_P6HN`）：`N := n + 1` 时因子就是原 J6 的 `n + 1`。 -/
example (n : ℕ) : max ((n : ℝ) + 1) ((fun m : ℕ => (m : ℝ) + 1) n) = (n : ℝ) + 1 := max_self _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
