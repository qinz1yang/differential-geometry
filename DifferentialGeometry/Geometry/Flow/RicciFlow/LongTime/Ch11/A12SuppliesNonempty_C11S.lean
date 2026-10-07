import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfSuppliesC11S

set_option autoImplicit false

/-!
# O-CH11-SKEL (G3)：供给不是 `False`（非空真检查）

两层检查，0 sorry：
1. **相对非空真 / 无损**：`surgerySupplies_iff_C11S`——`SurgerySupplies_C11S P g` 与 A12 的结论
   **等价**。方向 ⇐ 从任意 profile 读回 S1–S9（取 `q := Hp.parameters`、`α := Hp.largerBallAccuracy`，
   S8 是字段在 `A > 1` 上的限制）。所以供给 bundle 不比 A12 强：它是 `False` 当且仅当 A12 本身假；
   骨架也没有丢信息（任何 A12 的证明都给出全部供给）。
2. **参数层绝对非空**：`sampleParameters_C11S`（δ(t) = 1/(2(t+1))，ρ(t) = 1/(t+1)，scaffold 取
   `StaticCapScaffold.ofCollarLength 1`）同时满足所有**只涉及参数**的供给与适配前提：S1、S2、S4
   （ε = 1/200，C1 = C2 = 1）、S7（对角 α）、S9 的参数级替代 `RecentScaleSupply_C11S` 与半时倍增。
   flow 级供给（S3、S5、S6、S8、S9 的 record 形）的非空真只能由层 1 的等价给出（它们关于构造出的
   flow，没有平凡 flow 可用）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set

namespace GC.LongTime.Ch11

universe u

/-- **方向 ⇐**：A12 的结论 ⇒ 供给 bundle（任何 profile 都给出 S1–S9）。 -/
theorem surgerySupplies_of_conclusion_C11S (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :
    SurgerySupplies_C11S P g := by
  obtain ⟨δ, F, hanti, hdec, ⟨Hp⟩⟩ := h
  rcases Hp with ⟨q, rfl, records, hwin, hrad, eps, heps, hsmall, C1, C2, hC1, hC2, hcan, κ, hκ,
    hκa, hnc, _, _, _, _, _, _, α, hαpos, hαt, hαr, hdiag, hlb, hrcs⟩
  exact ⟨F, q, records, eps, C1, C2, κ, α, ⟨hanti, hdec⟩, hrad, hwin, ⟨heps, hsmall, hC1, hC2⟩,
    hcan, ⟨hκ, hκa, hnc⟩, ⟨hαpos, hαt, hαr, hdiag⟩, fun A hA => hlb A (one_pos.trans hA), hrcs⟩

/-- **供给 ⇔ A12 的结论**（对每个 `P, g`）。 -/
theorem surgerySupplies_iff_C11S {P : OrientedThreeStage.{u}} {g : P.Metric} :
    SurgerySupplies_C11S P g ↔
      ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
        AntitoneOn δ (Ici 0) ∧
        (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
        hasAnalyticAdmissibility F δ :=
  ⟨exists_surgery_with_decaying_accuracy_of_supplies_C11S P g,
    surgerySupplies_of_conclusion_C11S P g⟩

/-- 显式 cutoff 参数：δ(t) = 1/(2(t+1))，ρ(t) = 1/(t+1)，protected 半径 1，scaffold `ofCollarLength 1`。 -/
def sampleParameters_C11S : CutoffParameters where
  delta := fun t => 1 / (2 * (t + 1))
  neckRadius := fun t => 1 / (t + 1)
  protectedRadius := fun _ => 1
  delta_pos := fun t ht => by positivity
  delta_lt_one := fun t ht => by
    rw [div_lt_one (by positivity)]
    linarith
  neckRadius_pos := fun t ht => by positivity
  protectedRadius_pos := fun _ _ => one_pos
  fixed := StaticCapScaffold.ofCollarLength 1 one_pos
  modelRadius := 1
  modelRadius_pos := one_pos
  modelOrder := 0
  modelAccuracy := 1
  modelAccuracy_pos := one_pos
  recenterConstant := 4
  recenterConstant_ge_four := le_rfl

theorem sampleParameters_delta_antitone_C11S :
    AntitoneOn sampleParameters_C11S.delta (Ici 0) := by
  intro s hs t _ hst
  simp only [mem_Ici] at hs
  change 1 / (2 * (t + 1)) ≤ 1 / (2 * (s + 1))
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem sampleParameters_accuracyDecay_C11S :
    AccuracyDecaySupply_C11S sampleParameters_C11S.delta := by
  refine ⟨sampleParameters_delta_antitone_C11S, fun ε hε => ⟨1 / ε, fun t ht => ?_⟩⟩
  have ht0 : 0 < t := lt_trans (by positivity) ht
  have h1 : 1 < t * ε := by rwa [div_lt_iff₀ hε] at ht
  change 1 / (2 * (t + 1)) < ε
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem sampleParameters_radiusAntitone_C11S : RadiusAntitoneSupply_C11S sampleParameters_C11S := by
  intro s hs t _ hst
  simp only [mem_Ici] at hs
  change 1 / (t + 1) ≤ 1 / (s + 1)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem sampleParameters_doubling_C11S : RadiusDoublingSupply_C11S sampleParameters_C11S := by
  refine ⟨2, 0, two_pos, fun t ht u hu => ?_⟩
  have hu0 : 0 ≤ u := by linarith [hu.1]
  change 1 / (u + 1) ≤ 2 * (1 / (t + 1))
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [hu.1]

/-- **参数层非空真**：样本参数同时满足 S1、S2、S4、S7（对角 α）、S9′ 与半时倍增。 -/
theorem sampleParameters_supplies_C11S :
    AccuracyDecaySupply_C11S sampleParameters_C11S.delta ∧
      RadiusAntitoneSupply_C11S sampleParameters_C11S ∧
      CanonicalConstantsSupply_C11S (1 / 200) 1 1 ∧
      LargerBallAccuracySupply_C11S sampleParameters_C11S.delta
        (diagonalAccuracy_C11S sampleParameters_C11S.delta) ∧
      RadiusDoublingSupply_C11S sampleParameters_C11S ∧
      RecentScaleSupply_C11S sampleParameters_C11S :=
  ⟨sampleParameters_accuracyDecay_C11S, sampleParameters_radiusAntitone_C11S,
    ⟨by norm_num, by norm_num, le_rfl, le_rfl⟩,
    largerBallAccuracySupply_diagonal_C11S _ sampleParameters_delta_antitone_C11S,
    sampleParameters_doubling_C11S,
    recentScaleSupply_of_doubling_C11S _ sampleParameters_accuracyDecay_C11S.2
      sampleParameters_doubling_C11S⟩

/-- Consumer：样本参数上 S9′ ⇒ 任意 flow / records 的 S9（`recent_cutoff_smallness`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (records : CutoffRecords_C11S F sampleParameters_C11S) :
    RecentCutoffSupply_C11S records :=
  recentCutoffSupply_of_recentScale_C11S records sampleParameters_supplies_C11S.2.2.2.2.2

end GC.LongTime.Ch11
