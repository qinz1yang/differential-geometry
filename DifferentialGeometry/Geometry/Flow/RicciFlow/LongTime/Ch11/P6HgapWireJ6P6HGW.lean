import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoPlusRecentP6SF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J6LocSepP6KT2c
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapAdaptBudgetKer2P6HA

/-!
# J6 ⇐ SEPFIX recent（无子列：阈值并入 `T₀`；O-CH11-HGAPWIRE，后缀 `_P6HGW`）

hgap 槽收窄 witness 形（`recordsK` 的 static scale = 参考 q-records 的 scale）下，J6
`(n+1)·max((n+1)/c, Qs_loc) ≤ scale` 由 `hpastJ6_of_recent_P6SF` 付：recent 阈值 `Tr n`
（`RecentCutoffSupply_C11S` 取 `η_n = 1/(2(n+1))`）并入 `T₀`（`T₀ n ≤ Tno n`），故对给定 `ind`
的**每个** `n` 成立，不需取子列（R9 的 `ind ∘ φ` 不必用）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- recent 阈值：`η_n = 1/(2(n+1))` 处 `RecentCutoffSupply_C11S` 给出的 `T`。 -/
def recentThr_P6HGW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records) (n : ℕ) : ℝ :=
  Classical.choose (hrcs (1 / (2 * ((n : ℝ) + 1))) (by positivity))

/-- **J6 ⇐ recent（`_P6HGW`，PROVED）**：序列形，witness 收窄（`hsc`），阈值 `recentThr ≤ T₀`、
`lateLambdaThr ≤ T₀`、`T₀ ≤ Tno`。 -/
theorem j6_of_recent_seq_P6HGW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδq : Tendsto q.delta atTop (𝓝 0))
    (ind : ℕ → ℕ) {T₀ c σ L R Tn Tno : ℕ → ℝ}
    (hTr : ∀ n, recentThr_P6HGW hrcs n ≤ T₀ n)
    (hT₀Λ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) (hseed : ∀ n, T₀ n ≤ Tno n)
    (hc : ∀ n, 0 < c n) (hTno : ∀ n, Tno n = c n * Tn n) (hTno0 : ∀ n, 0 ≤ Tno n)
    (h2c : ∀ n, 2 * c n < Tno n) (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (hRρ' : ∀ n, R n ≤ c n * (q.neckRadius (Tno n) ^ 2)⁻¹)
    {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ →
        GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n))
    (hsc : ∀ n i hi b, ((recordsK n i hi).static b).neck.scale =
      ((records (ind n) i).static b).neck.scale) :
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n)
      (max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) ≤
      ((recordsK n i hi).static b).neck.scale := by
  intro n i hi b
  rw [hsc n i hi b, ← max_assoc, max_self]
  have hN : (0 : ℝ) < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  have hR1 : 1 ≤ R n := by
    have := hRr n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hR0 : 0 < R n := lt_of_lt_of_le one_pos hR1
  have hTn : Tn n = Tno n / c n := by
    rw [hTno n]; field_simp [(hc n).ne']
  have hlate : Tno n ≤ 2 * max (T₀ n) (c n * (σ n - L n / R n)) := by
    have := late_of_Ldomain_P6SF (hc n) hTn (h2c n) hR1 (hroom n)
      (le_max_right (T₀ n) (c n * (σ n - L n / R n)))
    linarith
  have hsel : R n ≤ c n / q.neckRadius (Tno n) ^ 2 := by
    rw [div_eq_mul_inv]; exact hRρ' n
  have hρc : q.neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1) :=
    rhoSq_le_of_sel_P6KT2c (q.neckRadius_pos _ (hTno0 n)) hR0 hN hsel (hRr n)
  set η : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hηdef
  have hηpos : 0 < η := by positivity
  have hηN : 2 * η ^ 2 * ((n : ℝ) + 1) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have heq : 2 * η ^ 2 * ((n : ℝ) + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
      rw [hηdef]; field_simp
    rw [heq, div_le_one (by positivity)]
    linarith
  obtain ⟨-, hrec⟩ := Classical.choose_spec (hrcs η (by positivity))
  have hTr' : recentThr_P6HGW hrcs n ≤ Tno n := (hTr n).trans (hseed n)
  have key := hpastJ6_of_recent_P6SF (H := F.tower.history (ind n)) (p := q)
    (T₀ := max (T₀ n) (c n * (σ n - L n / R n))) (σ := Tno n) (N := (n : ℝ) + 1) (c := c n)
    (Tr := recentThr_P6HGW hrcs n) (η := η)
    (fun i' _ => records (ind n) i') hanti (hTno0 n) hN (hc n) hρc hlate hηpos.le hηN hTr'
    (fun i' _ t ht hm h => hrec t ht (ind n) i' hm h)
    (fun i' hi' => lateLambda_of_thr_P6HA q hδq
      ((hT₀Λ n).trans ((le_max_left _ _).trans hi'))) i hi b
  exact key

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
