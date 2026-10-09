import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedDistanceP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalizedTransferP6ST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistoryRescale_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery

/-!
# `hcen` 的 history 层 adapter（O-CH11-STAB4 G4′，后缀 `_P6ST4`）

HREST2 G3 rev1（`Ch11/P6HbdLateP6HB.lean` `hbd_stage_late_P6HB` 的 binder `hcen`）已加前件
`RegularCrossing p' q` 与种子 terminal footprint（SFP：`o ↦ o'` crossing、`o` / `o'` 与 seed trace 点 HEq、
`d⁺ = ofReal d`、`17(d+1) < 16r`、terminal 球紧且 ⊆ surviving）。本文件证明该槽**逐字**（0 binder）：
* `edist_heq_P6ST4`：stage / metric / 点的 HEq 下 `riemannianEDistOf` 相等；
* `activeStage_eq_succ_of_time_P6ST4`、`stageMetric_heq_output_P6ST4`（`σ = time i.succ` 处
  `stageMetric (activeStage σ) σ ≍ (event i).outputMetric`，`stageMetric_initial` + `event_output`）；
* `hcen_history_P6ST4`（单 history）：G4 `seedDist_seq_le_P6ST4` + slab HEq
  （`stageMetric_slab_heq_P6ST2`）；
* **`hcen_slot_P6ST4`**：结论 = `hcen` 槽逐字（tower `rescale_P6N` 量化）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- stage / metric / 点的 HEq 下 Riemannian 距离相等。 -/
theorem edist_heq_P6ST4 {A B : OrientedThreeStage.{u}} (hAB : A = B) {gA : A.Metric}
    {gB : B.Metric} (hg : HEq gA gB) {a a' : A.Carrier} {b b' : B.Carrier} (ha : HEq a b)
    (ha' : HEq a' b') :
    riemannianEDistOf (I := ThreeModel) gA a a' = riemannianEDistOf (I := ThreeModel) gB b b' := by
  subst hAB
  cases eq_of_heq hg
  cases eq_of_heq ha
  cases eq_of_heq ha'
  rfl

namespace ObservedHistory

/-- `σ = time i.succ` ⇒ `activeStage σ = i.succ`。 -/
theorem activeStage_eq_succ_of_time_P6ST4 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (σ : Icc (0 : ℝ) H.horizon) (hσ : (σ : ℝ) = H.time i.succ) : H.activeStage σ = i.succ :=
  H.activeStage_eq_of_maximal σ i.succ (le_of_eq hσ.symm)
    (fun _ hk => H.time_strictMono.le_iff_le.mp (hk.trans (le_of_eq hσ)))

/-- `σ = time i.succ` 处 `stageMetric (activeStage σ) σ ≍ (event i).outputMetric`。 -/
theorem stageMetric_heq_output_P6ST4 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (σ : Icc (0 : ℝ) H.horizon) (hσ : (σ : ℝ) = H.time i.succ) :
    HEq (H.stageMetric (H.activeStage σ) σ) (H.event i).outputMetric := by
  refine (stageMetric_heq_of_idx_P6S2 H (H.activeStage_eq_succ_of_time_P6ST4 i σ hσ) σ).trans
    (heq_of_eq ?_)
  rw [hσ, H.stageMetric_initial, H.event_output]

/-- **`hcen`（单 history）**：crossing `p' ↦ q`、`HEq y q` + SFP ⇒ `D.v n` 上 eventually
`d_{stageMetric}(seed_t, z) ≤ d_{stageMetric}(seed_σ, y) + η`（`t = D.v n`、`HEq z p'`）。 -/
theorem hcen_history_P6ST4 (H : ObservedHistory.{u}) {ε C1f C2f m : ℝ} {kk : ℕ}
    {Tn aSeed : Icc (0 : ℝ) H.horizon} {haT : aSeed ≤ Tn} {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
    (y : (H.stageAt σ).Carrier) (hσ : (σ : ℝ) = H.time i.succ)
    (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier) (hyq : HEq y q)
    (hcp : (H.event i).RegularCrossing p' q)
    (hSFP : ∃ (o : (H.stage i.castSucc).Carrier) (o' : (H.stage i.succ).Carrier)
      (hco : (H.event i).RegularCrossing o o') (r d : ℝ),
      (∀ (t : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ t) (hvt : t ≤ Tn),
        H.time i.castSucc ≤ t → (t : ℝ) < H.time i.succ →
        HEq (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
          (H.activeStage_mono hvt)) o) ∧
      HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
        (H.activeStage_mono hsT)) o' ∧
      0 ≤ d ∧ riemannianEDistOf (I := ThreeModel) (H.event i).outputMetric o' q =
        ENNReal.ofReal d ∧ 17 * (d + 1) < 16 * r ∧
      IsCompact (riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
        ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r) ∧
      Subtype.val '' riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
        ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r ⊆
          interior (Subtype.val '' (H.event i).old))
    (D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
      (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
      riemannianEDistOf (H.stageMetric (H.activeStage t) t)
          (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) z ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal η := by
  obtain ⟨o, o', hco, r, d, hot, hoσ, hd0, hd, hr, hK, hKold⟩ := hSFP
  have hev := (H.event i).seedDist_seq_le_P6ST4 hco hcp hd0 hd hr hK hKold D.v_mem
    D.v_tendsto hη
  have hRHS : riemannianEDistOf (I := ThreeModel) (H.stageMetric (H.activeStage σ) σ)
      (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y =
      riemannianEDistOf (I := ThreeModel) (H.event i).outputMetric o' q :=
    edist_heq_P6ST4 (congrArg H.stage (H.activeStage_eq_succ_of_time_P6ST4 i σ hσ))
      (H.stageMetric_heq_output_P6ST4 i σ hσ) hoσ hyq
  filter_upwards [hev] with n hn t z ht hz hav hvt
  have ht0 : H.time i.castSucc ≤ t := by
    rw [ht]
    exact (D.v_mem n).1.le
  have ht1 : (t : ℝ) < H.time i.succ := by
    rw [ht]
    exact (D.v_mem n).2
  have hmet : HEq (H.stageMetric (H.activeStage t) t)
      ((H.event i).incoming.flow.base.metric (D.v n)) := by
    have h2 : (H.event i).incoming.flow.base.metric (t : ℝ) =
        (H.event i).incoming.flow.base.metric (D.v n) := by rw [ht]
    exact (stageMetric_slab_heq_P6ST2 i ht0 ht1).trans (heq_of_eq h2)
  rw [edist_heq_P6ST4 (congrArg H.stage (H.activeStage_eq_castSucc_P6ST2 i t ht0 ht1)) hmet
    (hot t hav hvt ht0 ht1) hz, hRHS]
  exact hn

end ObservedHistory

/-- **`hcen` 槽（`P6HbdLateP6HB.lean` `hbd_stage_late_P6HB`，rev1）逐字**：tower 量化版，0 binder。 -/
theorem hcen_slot_P6ST4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ε C1 C2 : ℝ) (Ctime : NNReal) (C1f C2f m : ℝ) (kk : ℕ) :
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier), (σ : ℝ) = H.time i.succ →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
        (H.event i).RegularCrossing p' q →
        (∃ (o : (H.stage i.castSucc).Carrier) (o' : (H.stage i.succ).Carrier)
          (hco : (H.event i).RegularCrossing o o') (r d : ℝ),
          (∀ (t : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ t) (hvt : t ≤ Tn),
            H.time i.castSucc ≤ t → (t : ℝ) < H.time i.succ →
            HEq (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) o) ∧
          HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) o' ∧
          0 ≤ d ∧ riemannianEDistOf (I := ThreeModel) (H.event i).outputMetric o' q =
            ENNReal.ofReal d ∧ 17 * (d + 1) < 16 * r ∧
          IsCompact (riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
            ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r) ∧
          Subtype.val '' riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
            ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r ⊆
              interior (Subtype.val '' (H.event i).old)) →
        ∀ (D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) (η : ℝ), 0 < η →
        ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
          (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
          riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
                (H.activeStage_mono hvt)) z ≤
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hsT)) y +
              ENNReal.ofReal η := by
  intro nn cc hcc H Tn aSeed haT pT seedTrace i σ hsT has y hσ _ p' q hyq hcp hSFP D η hη
  exact H.hcen_history_P6ST4 (haT := haT) seedTrace i σ hsT has y hσ p' q hyq hcp hSFP D hη

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
