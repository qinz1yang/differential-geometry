import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12EnhancedC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12SuppliesNonempty_C11S

set_option autoImplicit false

/-!
# O-CH11-PROF (G3)：与 O-CH11-SKEL 供给骨架的对接（SKEL S1–S9 + 新供给 S10–S19 ⇒ A12′）

同一组数据 `(F, q, records, ε, C1, C2, κ, α)` 上，SKEL 的 S1、S2、S4–S9 与 G1 的 data 级供给
S10–S19（再加常数 `Ctime`）给出 A12′；S3（`canonical_windows`）**被 S10 加强**，不再单列
（`canonicalWindowsSupply_of_linked_C11E`）。profile 用 SKEL 的 `profileOfSupplies_C11S`（原字段）
+ `EnhancedSurgeryProfile_C11E.ofFields`（新字段）；新字段在 `profileOfSupplies_C11S` 上与 data 级
供给**定义等式**（`enhancedFields_profileOfSupplies_iff_C11E` 是 `Iff.rfl`）。

* `exists_surgery_with_decaying_accuracy_enhanced_of_supplies_C11E`：bundle ⇒ A12′ 结论，0 sorry；
* `surgerySupplies_of_enhanced_C11E`：bundle ⇒ SKEL 的 `SurgerySupplies_C11S`（遗忘）；
* `enhancedSurgerySupplies_iff_C11E`：bundle ⇔ A12′ 结论（相对非空真、无损）；
* `sampleEnhancedParameters_C11E`：参数级供给（S1、S2、S12、S18；S4 + S13 取 `ε = εKL70`）同时成立。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## data 级新供给的合取 -/

/-- S10–S19 的合取（同一组数据 + `Ctime`；hprof 常数 = `εProf_C11E`）。 -/
def EnhancedDataSupplies_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (ε C1 C2 : ℝ) (Ctime : ℝ≥0) : Prop :=
  LinkedWindowsSupply_C11E records ∧ TimeDerivativeSupply_C11E F q.neckRadius Ctime ∧
    CollarWindowSupply_C11E.{u} q ∧ ConeEpsilonSupply_C11E ε ∧
    LateLinkedRecordsSupply_C11E F q ∧ LargerBallCanonicalLateSupply_C11E F ε C1 C2 ∧
    StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 ∧ CompatibleCapsSupply_C11E F q records ∧
    ModelConstraintsSupply_C11E q εProf_C11E.{u} ∧ FrontierCollarSupply_C11E F q

/-- S10 加强 S3：linked windows ⇒ `canonical_windows`。 -/
theorem canonicalWindowsSupply_of_linked_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    (h : LinkedWindowsSupply_C11E records) : CanonicalWindowsSupply_C11S records :=
  fun n i b => linkedCanonicalWindow_hasCanonicalWindow_C11E _ (h n i b)

/-- S13 加强 S4 的 `epsilon_small`。 -/
theorem epsilonSmall_of_cone_C11E {ε : ℝ} (h : ConeEpsilonSupply_C11E ε) : ε < 1 / 100 :=
  lt_of_le_of_lt h εKL70_lt_C11E

/-- `εKL70` 就是树内的 `coneAccuracy`（`ST/BoundedCurvatureAtDistanceConstants.lean:23`，定义体逐字同）。 -/
theorem εKL70_eq_coneAccuracy_C11E : εKL70_C11E = coneAccuracy :=
  rfl

/-- S13 的 producer 入口（DIGEST C3）：astra `ClosedBirthConstants.epsilon_cone : ε ≤ coneAccuracy`
直接给出 S13。 -/
theorem coneEpsilonSupply_of_le_coneAccuracy_C11E {ε : ℝ} (h : ε ≤ coneAccuracy) :
    ConeEpsilonSupply_C11E ε :=
  h

/-- 新字段在 SKEL profile 上与 data 级供给定义等式。 -/
theorem enhancedFields_profileOfSupplies_iff_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : CutoffRecords_C11S F q} {eps C1 C2 : ℝ} (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hrad : RadiusAntitoneSupply_C11S q) (hwin : CanonicalWindowsSupply_C11S records)
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F q.neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta α)
    (hrcs : RecentCutoffSupply_C11S records) {Ctime : ℝ≥0} :
    EnhancedFields_C11E (profileOfSupplies_C11S F q records eps C1 C2 κ α hrad hwin hconst hcan
      hnc hacc hLB hrcs) Ctime ↔ EnhancedDataSupplies_C11E F q records eps C1 C2 Ctime :=
  Iff.rfl

/-! ## 供给 ⇒ enhanced profile ⇒ A12′ -/

/-- **供给 ⇒ enhanced profile**（S3 由 S10 推出）。 -/
def enhancedProfileOfSupplies_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (eps C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (Ctime : ℝ≥0) (hrad : RadiusAntitoneSupply_C11S q)
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F q.neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta α)
    (hrcs : RecentCutoffSupply_C11S records)
    (hE : EnhancedDataSupplies_C11E F q records eps C1 C2 Ctime) :
    EnhancedSurgeryProfile_C11E F q.delta :=
  EnhancedSurgeryProfile_C11E.ofFields
    (profileOfSupplies_C11S F q records eps C1 C2 κ α hrad
      (canonicalWindowsSupply_of_linked_C11E hE.1) hconst hcan hnc hacc hLB hrcs) Ctime hE

/-- enhanced 供给 bundle：SKEL 的 S1、S2、S4–S9 与 S10–S19 在同一组数据上。 -/
def EnhancedSurgerySupplies_C11E (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (Ctime : ℝ≥0),
    (AccuracyDecaySupply_C11S q.delta ∧ RadiusAntitoneSupply_C11S q ∧
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ CanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      NoncollapseSupply_C11S F κ ε ∧ LargerBallAccuracySupply_C11S q.delta α ∧
      LargerBallScalarLargeSupply_C11S F q.delta α ∧ RecentCutoffSupply_C11S records) ∧
    EnhancedDataSupplies_C11E F q records ε C1 C2 Ctime

/-- **A12′ 从供给**（0 sorry）：bundle ⇒ `A12EnhancedConclusion_C11E P g`。 -/
theorem exists_surgery_with_decaying_accuracy_enhanced_of_supplies_C11E
    (P : OrientedThreeStage.{u}) (g : P.Metric) (h : EnhancedSurgerySupplies_C11E P g) :
    A12EnhancedConclusion_C11E P g := by
  obtain ⟨F, q, records, eps, C1, C2, κ, α, Ctime,
    ⟨hδ, hrad, hconst, hcan, hnc, hacc, hLB, hrcs⟩, hE⟩ := h
  exact ⟨q.delta, F, hδ.1, hδ.2, ⟨enhancedProfileOfSupplies_C11E F q records eps C1 C2 κ α Ctime
    hrad hconst hcan hnc hacc hLB hrcs hE⟩⟩

/-- 遗忘：enhanced bundle ⇒ SKEL 的 `SurgerySupplies_C11S`（S3 由 S10 给出）。 -/
theorem surgerySupplies_of_enhanced_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (h : EnhancedSurgerySupplies_C11E P g) : SurgerySupplies_C11S P g := by
  obtain ⟨F, q, records, eps, C1, C2, κ, α, _,
    ⟨hδ, hrad, hconst, hcan, hnc, hacc, hLB, hrcs⟩, hE⟩ := h
  exact ⟨F, q, records, eps, C1, C2, κ, α, hδ, hrad, canonicalWindowsSupply_of_linked_C11E hE.1,
    hconst, hcan, hnc, hacc, hLB, hrcs⟩

/-- **方向 ⇐**：A12′ 结论 ⇒ enhanced bundle（任何 enhanced profile 读回全部供给）。 -/
theorem enhancedSurgerySupplies_of_conclusion_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (h : A12EnhancedConclusion_C11E P g) : EnhancedSurgerySupplies_C11E P g := by
  obtain ⟨δ, F, hanti, hdec, ⟨E⟩⟩ := h
  obtain ⟨Hp, Ctime, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := E
  rcases Hp with ⟨q, rfl, records, _, hrad, eps, heps, hsmall, C1, C2, hC1, hC2, hcan, κ, hκ,
    hκa, hnc, _, _, _, _, _, _, α, hαpos, hαt, hαr, hdiag, hlb, hrcs⟩
  exact ⟨F, q, records, eps, C1, C2, κ, α, Ctime,
    ⟨⟨hanti, hdec⟩, hrad, ⟨heps, hsmall, hC1, hC2⟩, hcan, ⟨hκ, hκa, hnc⟩,
      ⟨hαpos, hαt, hαr, hdiag⟩, fun A hA => hlb A (one_pos.trans hA), hrcs⟩,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- **enhanced bundle ⇔ A12′ 结论**（对每个 `P g`）：bundle 不比 A12′ 强、骨架无损。 -/
theorem enhancedSurgerySupplies_iff_C11E {P : OrientedThreeStage.{u}} {g : P.Metric} :
    EnhancedSurgerySupplies_C11E P g ↔ A12EnhancedConclusion_C11E P g :=
  ⟨exists_surgery_with_decaying_accuracy_enhanced_of_supplies_C11E P g,
    enhancedSurgerySupplies_of_conclusion_C11E⟩

/-- consumer：enhanced bundle ⇒ A12（经 A12′ 投影，与 SKEL 的路径给出同一结论）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (h : EnhancedSurgerySupplies_C11E P g) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  exists_surgery_with_decaying_accuracy_of_enhanced_C11E
    (exists_surgery_with_decaying_accuracy_enhanced_of_supplies_C11E P g h)

/-! ## 参数层绝对非空 -/

/-- 样本参数：δ、ρ 同 SKEL 样本；collar = P3 的常数 `A*`、`modelRadius = capWindowRadius + 1`、
`modelOrder = 2`、`modelAccuracy = εProf`。 -/
def sampleEnhancedParameters_C11E.{v} : CutoffParameters where
  delta := fun t => 1 / (2 * (t + 1))
  neckRadius := fun t => 1 / (t + 1)
  protectedRadius := fun _ => 1
  delta_pos := fun t ht => by positivity
  delta_lt_one := fun t ht => by
    rw [div_lt_one (by positivity)]
    linarith
  neckRadius_pos := fun t ht => by positivity
  protectedRadius_pos := fun _ _ => one_pos
  fixed := StaticCapScaffold.ofCollarLength (exists_collarLength_P3_C11E.{v}).choose
    (exists_collarLength_P3_C11E.{v}).choose_spec.choose
  modelRadius := capWindowRadius_C11E + 1
  modelRadius_pos := by
    have := DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E
    positivity
  modelOrder := 2
  modelAccuracy := εProf_C11E.{v}
  modelAccuracy_pos := εProf_pos_C11E.{v}
  recenterConstant := 4
  recenterConstant_ge_four := le_rfl

/-- **参数层非空真**：样本参数同时满足 S1、S2、S12（P3）、S18（hprof），常数 `ε = εKL70` 同时满足
S4（`C1 = C2 = 1`）与 S13（P4）。 -/
theorem sampleEnhancedParameters_supplies_C11E :
    AccuracyDecaySupply_C11S sampleEnhancedParameters_C11E.{u}.delta ∧
      RadiusAntitoneSupply_C11S sampleEnhancedParameters_C11E.{u} ∧
      CollarWindowSupply_C11E.{u} sampleEnhancedParameters_C11E.{u} ∧
      ModelConstraintsSupply_C11E sampleEnhancedParameters_C11E.{u} εProf_C11E.{u} ∧
      CanonicalConstantsSupply_C11S εKL70_C11E 1 1 ∧ ConeEpsilonSupply_C11E εKL70_C11E := by
  have hT := DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
  refine ⟨sampleParameters_accuracyDecay_C11S, sampleParameters_radiusAntitone_C11S,
    ⟨(exists_collarLength_P3_C11E.{u}).choose_spec.choose_spec.2, le_rfl⟩,
    ⟨le_rfl, le_rfl, ?_⟩, ⟨εKL70_pos_C11E, εKL70_lt_C11E, le_rfl, le_rfl⟩, le_rfl⟩
  change DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd + 1 ≤
    capWindowRadius_C11E + 1
  unfold capWindowRadius_C11E
  linarith

end GC.LongTime.Ch11
