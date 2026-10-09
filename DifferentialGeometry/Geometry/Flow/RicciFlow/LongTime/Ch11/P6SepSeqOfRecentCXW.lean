import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6YoungCapBirthLateP6EV
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoPlusFixV2P6SF

set_option autoImplicit false

/-!
# Recent supply 实际生产 SEPseq / Actual scale separation from recent supply

`RecentCutoffSupply_C11S` 对任意 real query time 成立，只要求 birth 属于 `[t/2,t]`，
没有 query horizon 条件。`young_cap_birth_late_P6EV` 同时支付该窗口和晚期 recenter。
固定 m 后选 K 和 eta，实际得到原 SEPseq 的双天花板；完全不消费 haccuracy。

所有阈值只依赖实际 fixed F/q/records 和 m，在选择 sequence indices 前已经存在。
SCRS⁺ consumer 仅解包一次，canonical windows、recent 和 late birth 使用同一份 records。
-/

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

private theorem ceiling_absorption_CXW (q : CutoffParameters)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) {t N : ℝ} (ht : 0 ≤ t) (hN : 0 ≤ N) :
    N * max N (q.neckRadius t ^ 2)⁻¹ ≤
      max N (N ^ 2 * q.neckRadius 0 ^ 2) * (q.neckRadius t ^ 2)⁻¹ := by
  have hrt := q.neckRadius_pos t ht
  have hnr := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have hsq := pow_le_pow_left₀ hrt.le hnr 2
  rw [mul_max_of_nonneg _ _ hN]
  refine max_le ?_ ?_
  · rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hrt)).mpr
    calc N * N * q.neckRadius t ^ 2 = N ^ 2 * q.neckRadius t ^ 2 := by ring
      _ ≤ N ^ 2 * q.neckRadius 0 ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg N)
      _ ≤ max N (N ^ 2 * q.neckRadius 0 ^ 2) := le_max_right _ _
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (sq_nonneg _))

/-- 固定 m 的全部 young queries 都满足分离 / Uniform separation for each fixed m. -/
theorem sepRhoPlus_young_of_recent_CXW {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (hcan : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (heps : q.modelAccuracy ≤ 1 / 2) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hlim : Tendsto q.delta atTop (𝓝 0)) (hrecent : RecentCutoffSupply_C11S records) :
    ∀ m : ℕ, ∃ T : ℝ, 0 < T ∧
      ∀ n (i : Fin (F.tower.history n).eventCount)
        (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (t : ℝ),
      T ≤ t → (F.tower.history n).time i.succ ≤ t →
      t - (F.tower.history n).time i.succ ≤
        1 / 4 * ((records n i).static b).neck.scale⁻¹ →
      ((m : ℝ) + 1) * max ((m : ℝ) + 1) (q.neckRadius t ^ 2)⁻¹ ≤
        ((records n i).static b).neck.scale := by
  have hΛ : 0 < q.recenterConstant :=
    lt_of_lt_of_le (by norm_num) q.recenterConstant_ge_four
  have hε : 0 < (1 / 2 : ℝ) / q.recenterConstant := div_pos (by norm_num) hΛ
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  obtain ⟨Ty, _, hy⟩ := young_cap_birth_late_P6EV F q records hcan heps hanti hlim
    (1 / 4) (by norm_num) B
  intro m
  let N : ℝ := (m : ℝ) + 1
  let K : ℝ := max N (N ^ 2 * q.neckRadius 0 ^ 2)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hK : 0 < K := hN.trans_le (le_max_left _ _)
  let η : ℝ := 1 / (2 * (K + 1))
  have hden : 0 < 2 * (K + 1) := by positivity
  have hη : 0 < η := one_div_pos.mpr hden
  have hbudget : 2 * η ^ 2 * K ≤ 1 := by
    have heq : 2 * η ^ 2 * K = 2 * K / (2 * (K + 1)) ^ 2 := by
      dsimp only [η]
      rw [div_pow]
      ring
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith only [sq_nonneg K, hK.le]
  obtain ⟨Tr, hTr, hr⟩ := hrecent η hη
  refine ⟨max Tr Ty, hTr.trans_le (le_max_left _ _), ?_⟩
  intro n i b t ht hupper hage
  have htr : Tr ≤ t := (le_max_left _ _).trans ht
  have hty : Ty ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 ≤ t := (hTr.trans_le htr).le
  obtain ⟨hbirth, hhalf⟩ := hy n i b t hty hage
  have hΛδ : q.recenterConstant * q.delta ((F.tower.history n).time i.succ) ≤ 1 / 2 := by
    have hh := (le_div_iff₀ hΛ).mp (hB _ hbirth).le
    simpa only [mul_comm] using hh
  have hrec : ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t :=
    hr t htr n i ⟨by linarith only [hhalf], hupper⟩
  have hs := sepRhoPlus'_of_recent_P6SF (records n i) b hΛδ
    (q.neckRadius_pos t ht0) hrec hbudget
  exact (ceiling_absorption_CXW q hanti ht0 hN.le).trans hs

/-- 原 SEPseq 全量词形 / Full original sequence shape, with arbitrary observation indices. -/
theorem sepSeq_of_recent_CXW {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (hcan : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (heps : q.modelAccuracy ≤ 1 / 2) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hlim : Tendsto q.delta atTop (𝓝 0)) (hrecent : RecentCutoffSupply_C11S records) :
    ∀ (ν : ℕ → ℕ) (t : ℕ → ℝ), Tendsto t atTop atTop → ∀ m : ℕ,
      ∀ᶠ k in atTop, ∀ (i : Fin (F.tower.history (ν k)).eventCount)
        (b : ((F.tower.history (ν k)).toHistory.event i).RetainedBoundaryIndex),
      (F.tower.history (ν k)).time i.succ ≤ t k →
      t k - (F.tower.history (ν k)).time i.succ ≤
        1 / 4 * ((records (ν k) i).static b).neck.scale⁻¹ →
      ((m : ℝ) + 1) * max ((m : ℝ) + 1) (q.neckRadius (t k) ^ 2)⁻¹ ≤
        ((records (ν k) i).static b).neck.scale := by
  intro ν t ht m
  obtain ⟨T, _, hT⟩ :=
    sepRhoPlus_young_of_recent_CXW F q records hcan heps hanti hlim hrecent m
  filter_upwards [ht.eventually_ge_atTop T] with k hk i b hupper hage
  exact hT (ν k) i b (t k) hk hupper hage

/-- SCRS⁺ 同一次选择给出全部供给 / One SCRS⁺ witness supplies actual SEPseq. -/
theorem sepSeq_of_scrsPlus_CXW {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (h : SameConstructionRetentionSupplyPlus_C11GT6 T) (heps : pB.modelAccuracy ≤ 1 / 2) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : CutoffRecords_C11S F q),
      F.tower = T.toChain.tower ∧
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      q.recenterConstant = pB.recenterConstant ∧
      ∀ (ν : ℕ → ℕ) (t : ℕ → ℝ), Tendsto t atTop atTop → ∀ m : ℕ,
        ∀ᶠ k in atTop, ∀ (i : Fin (F.tower.history (ν k)).eventCount)
          (b : ((F.tower.history (ν k)).toHistory.event i).RetainedBoundaryIndex),
        (F.tower.history (ν k)).time i.succ ≤ t k →
        t k - (F.tower.history (ν k)).time i.succ ≤
          1 / 4 * ((records (ν k) i).static b).neck.scale⁻¹ →
        ((m : ℝ) + 1) * max ((m : ℝ) + 1) (q.neckRadius (t k) ^ 2)⁻¹ ≤
          ((records (ν k) i).static b).neck.scale := by
  obtain ⟨F, q, _, records, hsame, _, _, hprof, hcaps, _⟩ := h
  have hqeps : q.modelAccuracy ≤ 1 / 2 := by
    rw [hsame.2.2.2.2.2.1]
    exact heps
  exact ⟨F, q, records, hsame.1, hsame.2.1, hsame.2.2.2.2.2.2,
    sepSeq_of_recent_CXW F q records hcaps.1 hqeps hprof.2.1 hprof.2.2 hcaps.2.1⟩

end GC.LongTime.Ch11
