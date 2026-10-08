import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopPBaseC11GT3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsAccuracyCXCA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ConstantsTableC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AncientWitnessDecoupledP6P

/-!
# B1：joint 定理的 `ε ≤ epsW` 门槛——闭项 `epsW_CXOU2` 与 Γ 选取处的 accuracy cap（CX-OUTER2，后缀 `_CXOU2`）

* `epsW_CXOU2 : ℝ := (ancientWitness_decoupled_P6P).choose`（只依赖 universe；与 `p6CoarseC_C11GT6`
  的 `ηout` 常数同源于该定理的 `∃ epsW`，见 `P6CoarseJointCXOU2`）。
* 事实更正（相对 lead 16:1x 裁定的措辞）：Γ 的 `epsilon` **不经 reserve 选取**——v6fwd 里 `Γ` 来自
  `hpbase_of_provider_C11GT3 P g`（`A12GapTopV6FwdC11GT6.lean:423`），其 `∃ Γ` 位于 `∀ εReserve` **之前**，
  Γ 本身由 `exists_closedBirthConstants_strong_C12X`（`A12GapTopPBaseC11GT3.lean:52–53`）在首次 ε 选取处给出。
  因此「reserve 取含 epsW 的最小值」（`epsilon0_C11FR` 模式）作用的是 `pB.modelAccuracy`，够不到 `Γ.epsilon`。
  正确插入点 = Γ 选取本身：已有 `exists_closedBirthConstants_strong_accuracy_CXCA`（`εP6` cap 先于 C）。
  本文件把 GT3 的 `hpbase` provider 换成 CXCA 版，得 `Γ.epsilon ≤ εcap`（取 `εcap := epsW_CXOU2`）。
* `joint_gates_of_closedBirth_CXOU2`：`Γ.epsilon ≤ εStrong ∧ Γ.epsilon ≤ epsW_CXOU2` ⇒
  joint 定理的全部 ε 门槛。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **闭项 `epsW`**：`ancientWitness_decoupled_P6P` 的 `∃ epsW` 的 choice（只依赖 universe）。 -/
def epsW_CXOU2 : ℝ := (ObservedHistory.ancientWitness_decoupled_P6P.{u}).choose

theorem epsW_CXOU2_pos : 0 < epsW_CXOU2.{u} :=
  (ObservedHistory.ancientWitness_decoupled_P6P.{u}).choose_spec.1

/-- **Γ 选取处的 accuracy cap（collar 保留版）**：`exists_blockSteps_byPointCollar_C11GT3` 的 CXCA 版，
多一条 `C.epsilon ≤ εcap`（`εcap` 先于 `C`）。 -/
theorem exists_blockSteps_byPointCollarAcc_CXOU2 (Dstar : ℝ) (hDstar : 0 < Dstar) (cMax : ℝ)
    (hcMax : 0 < cMax) (εcap : ℝ) (hεcap : 0 < εcap) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ εStrong_C12X.{u} ∧ C.epsilon ≤ εcap ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (εReserve : ℝ), 0 < εReserve →
    ∃ (pBase : CutoffParameters) (prepared : ClosedBirthPreparedClass pBase C P g 1),
      prepared.parameters = pBase ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality Dstar εReserve ∧
      collarAdmitsAllOrders_C11E.{u} pBase.fixed.collarLength pBase.fixed.collar_pos ∧
      ∀ j : ℕ, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεcap', hεs, ⟨-, A, hA, hfix, hcol⟩, prepareClass,
      analytic, -⟩ := exists_closedBirthConstants_strong_accuracy_CXCA.{u} Dstar 1 εcap hDstar
      one_pos hεcap
  refine ⟨Cdist, hCdist, C, hεs, hεcap', fun P g εReserve hεReserve => ?_⟩
  obtain ⟨Qzero, hQzero, zeroBound, prepareInitial⟩ :=
    exists_prepared_closed_birth_class_before_quality_with_distance_scalars_with_reserve_quality
      Dstar εReserve hDstar hεReserve Cdist fixed recenter prepareClass
      C.epsilon C.C1 C.C2 C.C1s C.C2s C.Cs C.tauMin C.Cbirth C.Ctime C.Cgrad C.epsilon_pos
      ⟨C.C1_ge_one, C.C2_ge_one, C.C1s_ge_one, C.C2s_ge_one, C.tauMin_pos, hεs⟩ analytic P g
  obtain ⟨pBase, δb, ρb, εClass, κClass, κ, qcan, qs, Qbirth, Qall,
    hDReserve, hεReserveBound, hmReserve, hscaleReserve, hStrong,
    hfixed, hrc, hδb, hρb, hεClass, hεClass11, hκClass, hκ,
    hqcan, hqs, hqsC, hQbirth, hQall, hQallPos,
    hcap, hrec, extension, control⟩ := prepareInitial 1 one_pos
  obtain ⟨C1h, C2h, qh, hC1h, hC2h, hC1hb, hC2hb, hqh, hStrongV⟩ := hStrong
  let prepared : ClosedBirthPreparedClass pBase C P g 1 := {
    parameters := pBase
    deltaBound := δb
    radiusBound := ρb
    epsilonClass := εClass
    kappaClass := κClass
    kappa := κ
    qcan := qcan
    qs := qs
    Qzero := Qzero
    Qbirth := Qbirth
    Qall := Qall
    fixed_eq := rfl
    recenter_eq := rfl
    deltaBound_pos := hδb
    radiusBound_pos := hρb
    epsilonClass_pos := hεClass
    epsilonClass_small := hεClass11
    kappaClass_pos := hκClass
    kappa_pos := hκ
    qcan_pos := hqcan
    qcan_le_qs := hqs
    qs_le := hqsC
    Qzero_pos := hQzero
    Qbirth_ge := hQbirth
    Qall_eq := hQall
    Qall_pos := hQallPos
    modelRadius_bound := hcap
    recenter_bound := hrec
    zero_bound := zeroBound
    extension := extension.forget
    control := control
    epsilon_strong := hεs
    C1strong := C1h
    C2strong := C2h
    qStrong := qh
    C1strong_ge_one := hC1h
    C2strong_ge_one := hC2h
    C1strong_le := hC1hb
    C2strong_le := hC2hb
    qs_le_qStrong := hqh
    strongControl := hStrongV }
  have hprep : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist := by
    rw [hfixed, hrc]
    exact prepareClass
  have hcollar : collarAdmitsAllOrders_C11E.{u} pBase.fixed.collarLength
      pBase.fixed.collar_pos := by
    subst hfixed
    exact collarAdmitsAllOrders_of_fixed_ofCollarLength_C11PB
      ⟨A, hA, hfix, collarAdmitsAllOrders_of_staticCollarAdmits_C11PB hcol⟩
  exact ⟨pBase, prepared, rfl, extension,
    ⟨hDReserve, hεReserveBound, hmReserve, hscaleReserve⟩, hcollar,
    blockSteps_of_astra_C11W5 Dstar εReserve hDstar hεReserve Cdist cMax hcMax hprep analytic⟩

/-- **`hpbase`，strong + accuracy cap 形**：`hpbase_strong_C11GT3` 逐字，`∃ Γ` 之后多 `Γ.epsilon ≤ εcap`。 -/
theorem hpbase_accuracy_CXOU2 (P : OrientedThreeStage.{u}) (g : P.Metric) (εcap : ℝ)
    (hεcap : 0 < εcap) :
    ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ εcap ∧
      ∀ εReserve : ℝ, 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j := by
  have hD : 0 < capWindowRadius_C11E + 1 := by
    have hte := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E
    positivity
  obtain ⟨Cdist, -, C, hεs, hεc, hmake⟩ :=
    exists_blockSteps_byPointCollarAcc_CXOU2.{u} (capWindowRadius_C11E + 1) hD 1 one_pos εcap hεcap
  exact ⟨Cdist, C, hεs, hεc, fun ε hε => hmake P g ε hε⟩

/-- **`hpbase` 取 `εcap := epsW_CXOU2`**：v6fwd:423 的 `hpbase_of_provider_C11GT3 P g` 的替换形，多
`Γ.epsilon ≤ epsW_CXOU2.{u}`（连同 `Γ.epsilon ≤ εStrong_C12X`）。 -/
theorem hpbase_epsW_CXOU2 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), Γ.epsilon ≤ εStrong_C12X.{u} ∧
      Γ.epsilon ≤ epsW_CXOU2.{u} ∧
      ∀ εReserve : ℝ, 0 < εReserve →
      ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
        prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j :=
  hpbase_accuracy_CXOU2 P g epsW_CXOU2.{u} epsW_CXOU2_pos.{u}

/-- joint 定理（`canonicalLateCore_of_jointD_P6CK`）的全部 ε 门槛由 Γ 的两条 accuracy 给出。 -/
theorem joint_gates_of_closedBirth_CXOU2 {Γ : ClosedBirthConstants}
    (hs : Γ.epsilon ≤ εStrong_C12X.{u}) (hW : Γ.epsilon ≤ epsW_CXOU2.{u}) :
    0 < Γ.epsilon ∧ Γ.epsilon < 1 / 11 ∧ Γ.epsilon ≤ epsW_CXOU2.{u} ∧
      Γ.epsilon ≤ crossingWindowNeckAccuracy.{u} ∧ Γ.epsilon ≤ crossingNeckAccuracy.{u} ∧
      Γ.epsilon ≤ coneAccuracy := by
  obtain ⟨h11, hw, hn, hc⟩ := p6_accuracy_hyps_of_strong_C12X.{u} hs
  exact ⟨Γ.epsilon_pos, h11, hW, hw, hn, hc⟩

/-- consumer：`hpbase_epsW_CXOU2` 给出的 Γ 满足 joint 的全部 ε 门槛。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Γ : ClosedBirthConstants, 0 < Γ.epsilon ∧ Γ.epsilon < 1 / 11 ∧
      Γ.epsilon ≤ epsW_CXOU2.{u} ∧ Γ.epsilon ≤ crossingWindowNeckAccuracy.{u} ∧
      Γ.epsilon ≤ crossingNeckAccuracy.{u} ∧ Γ.epsilon ≤ coneAccuracy := by
  obtain ⟨-, Γ, hs, hW, -⟩ := hpbase_epsW_CXOU2.{u} P g
  exact ⟨Γ, joint_gates_of_closedBirth_CXOU2 hs hW⟩

end GC.LongTime.Ch11
