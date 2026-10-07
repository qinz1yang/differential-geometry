import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.IncomingEventWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedStagePropagation

/-!
# S-CH11-FIX11 patched-at-path `IncomingStageWeightedRestart`

来源：donor `IncomingStageWeightedRestart.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；下游模块对本路径 `open private … from`，
所以修补文本就放在原路径（patched-at-path）。只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 陈述里的 `ℝ≥0`（`Cderiv`）需要 `open scoped NNReal`（donor 漏开，`LE Type / OfNat Type 0` ×3 及其级联
  "Unknown identifier traced_weighted_minimum_restarts_on_fixed_incoming_stage" / "No goals"）→ 在已有
  的 `open scoped` 行补上 `NNReal`；
* `(hsmall.and ((Ioo_mem_nhdsGT hkd).and (Ioo_mem_nhdsGT hkx))).exists`：`Ioo_mem_nhdsGT` 的类型是
  集合成员 `Ioo k d ∈ 𝓝[>] k`，`.and` 字段记号不适用（"Invalid field `and`: … `Exists.and`"）→ 先
  `have hd1 : ∀ᶠ a in 𝓝[>] k, a ∈ Ioo k d := Ioo_mem_nhdsGT hkd`（`hd2` 同）；
* `huscF.mono (show Ioi k ⊆ Ici k from fun _ h => h.le)`（`h.le` 在成员位上类型不对）→
  `huscF.mono Ioi_subset_Ici_self`；
* `apply (mul_le_mul_right (mul_pos …)).mp`（本树 `mul_le_mul_right` 是单调性引理）→
  `apply le_of_mul_le_mul_right ?_ (mul_pos …)`；
* calc 末步 `field_simp` 已关目标，多余 `ring` "No goals"（坑 xiii）→ 删；
* `haveI : NeBot … := …`（命题用 `have`，`linter.style.haveILetI`）→ `have`；
* 8 个陈述 binder `hf` / `hl` 不被引用 → `_hf` / `_hl`。
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

open private weighted_infimum_antitone_on_fixed_regular_stage from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedStagePropagation

private theorem antitoneOn_Icc_of_right_usc_and_guarded_entry_strips
    (f : ℝ → ℝ) (k b d guard : ℝ)
    (hkb : k < b) (hkd : k < d) (hdb : d ≤ b)
    (husc : UpperSemicontinuousWithinAt f (Ici k) k)
    (hgap : f k < guard)
    (hstrips : ∀ a ∈ Ioo k d, f a < guard → AntitoneOn f (Icc a b)) :
    AntitoneOn f (Icc k b) := by
  have : NeBot (𝓝[>] k) := nhdsGT_neBot_of_exists_gt ⟨b, hkb⟩
  have huscRight : UpperSemicontinuousWithinAt f (Ioi k) k :=
    husc.mono Ioi_subset_Ici_self
  have hsmall : ∀ᶠ a in 𝓝[>] k, f a < guard := huscRight guard hgap
  have hbound (w : ℝ) (hw : w ∈ Ioc k b) : f w ≤ f k := by
    have hcomp : ∀ᶠ a in 𝓝[>] k, f w ≤ f a := by
      filter_upwards [hsmall, Ioo_mem_nhdsGT hkd, Ioo_mem_nhdsGT hw.1]
        with a haSmall had haw
      exact hstrips a had haSmall
        ⟨le_rfl, had.2.le.trans hdb⟩ ⟨haw.2.le, hw.2⟩ haw.2.le
    exact huscRight.frequently (f w) hcomp.frequently
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with hxk | hkx
  · subst x
    rcases eq_or_lt_of_le hy.1 with hyk | hky
    · subst y
      exact le_rfl
    · exact hbound y ⟨hky, hy.2⟩
  · have hd1 : ∀ᶠ a in 𝓝[>] k, a ∈ Ioo k d := Ioo_mem_nhdsGT hkd
    have hd2 : ∀ᶠ a in 𝓝[>] k, a ∈ Ioo k x := Ioo_mem_nhdsGT hkx
    obtain ⟨a, haSmall, had, hax⟩ := (hsmall.and (hd1.and hd2)).exists
    exact hstrips a had haSmall
      ⟨hax.2.le, hx.2⟩ ⟨hax.2.le.trans hxy, hy.2⟩ hxy

private theorem traced_weighted_minimum_restarts_on_fixed_incoming_stage
    (a₀ : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hSupportAt :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0)
    (k b : ℝ) (hk : 0 < k) (hkb : k < b)
    (hbhalf : b ^ 2 ≤ r ^ 2 / 2)
    (eventIndex : Fin H.eventCount) (hfSeed : H.activeStage aSeed ≤ eventIndex.castSucc)
    (hl : eventIndex.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time eventIndex.succ)
    {Dcap εcap : ℝ} {ncap : ℕ}
    (S : ∀ c : (H.event eventIndex).RetainedBoundaryIndex,
      (H.event eventIndex).PresentedStaticCap parameters.fixed Dcap ncap εcap c)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : εcap ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < Dcap)
    (O z : (H.event eventIndex).old)
    (hOin : O.val.val = seedTrace.point eventIndex.castSucc hfSeed (eventIndex.castSucc_le_succ.trans hl))
    (hO : ∀ c, (H.event eventIndex).oldOutput O ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ c, (H.event eventIndex).oldOutput z ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (L : ℝ)
    (hinside : riemannianEDistOf (H.event eventIndex).outputMetric
        ((H.event eventIndex).oldOutput O) ((H.event eventIndex).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost eventIndex.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x
      ((H.event eventIndex).oldOutput z) = (L : WithTop ℝ))
    (hcontact : H.physicalWeightedCost eventIndex.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
        ((H.event eventIndex).oldOutput O) ((H.event eventIndex).oldOutput z) =
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A k)
    (hclockEnd : H.time eventIndex.castSucc < t.val - b ^ 2) :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : eventIndex.castSucc ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ b ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), eventIndex.castSucc ≤ i.castSucc → i.succ ≤ H.activeStage t →
        D * r ≤ nodeA i) →
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun w => (M w).untopD 0
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    f k ≤ 2 * r →
    (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
    AntitoneOn f (Icc k b) ∧
    (∀ w ∈ Icc k b,
      m w ≤ Real.exp (C * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r) *
        (w / k) * m k ∧
      m w ≤ 2 * r * w * Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r)) := by
  classical
  intro C D nodeA nodeE nodeR nodeQ nodeRho hnode hfit M m f hclosed
  have hkhalf : k ^ 2 < r ^ 2 / 2 := by
    have hsq := mul_pos (sub_pos.mpr hkb) (add_pos (hk.trans hkb) hk)
    nlinarith only [hsq, hbhalf]
  obtain ⟨hfiniteK, hmkpos, hright, husc⟩ :=
    H.traced_physical_weighted_minimum_right_control_of_event_window_data
      parameters records a₀ ha₀ hfixed hscalar t p x r A k hr hk hkhalf hT
      aSeed hSeedTime hSeedClock seedTrace eventIndex hfSeed hl hevent
      S hcanonical hε hD O z hOin hO hz L hinside hcost hcontact
  have huscF : UpperSemicontinuousWithinAt f (Ici k) k := husc C
  obtain ⟨d₀, hkd₀, _, hnear⟩ := hright 1 (by norm_num)
  let d : ℝ := min d₀ b
  have hkd : k < d := lt_min hkd₀ hkb
  have hdb : d ≤ b := min_le_right _ _
  have hfiniteEntry (a : ℝ) (ha : a ∈ Ioo k d) : M a ≠ ⊤ :=
    (hnear a ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩).2.2.2.1
  let guard : ℝ := 2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2)
  have hcancelGuard : Real.exp (C / 2 + 32 / Real.sqrt 2) *
      Real.exp (-C / 2 - 32 / Real.sqrt 2) = 1 := by
    rw [← Real.exp_add,
      show (C / 2 + 32 / Real.sqrt 2) + (-C / 2 - 32 / Real.sqrt 2) = 0 by ring,
      Real.exp_zero]
  have hguard : 2 * r < guard := by
    have hformula : guard = 2 * r + 2 * r * Real.exp (-C / 2 - 32 / Real.sqrt 2) := by
      dsimp only [guard, D]
      calc
        2 * r * (Real.exp (C / 2 + 32 / Real.sqrt 2) + 1) *
            Real.exp (-C / 2 - 32 / Real.sqrt 2) =
            2 * r * (Real.exp (C / 2 + 32 / Real.sqrt 2) *
              Real.exp (-C / 2 - 32 / Real.sqrt 2)) +
              2 * r * Real.exp (-C / 2 - 32 / Real.sqrt 2) := by ring
        _ = 2 * r + 2 * r * Real.exp (-C / 2 - 32 / Real.sqrt 2) := by
          rw [hcancelGuard, mul_one]
    rw [hformula]
    exact lt_add_of_pos_right _ (mul_pos (mul_pos (by norm_num) hr) (Real.exp_pos _))
  have hgap : f k < guard := hclosed.trans_lt hguard
  have hstrip (a : ℝ) (ha : a ∈ Ioo k d) (hsmall : f a < guard) :
      (∀ w ∈ Icc a b, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w < 2 * r * w * D) ∧
        AntitoneOn f (Icc a b) := by
    have ha0 : 0 < a := hk.trans ha.1
    have hab : a ≤ b := ha.2.le.trans hdb
    have hclock (w : ℝ) (hw : w ∈ Icc a b) :
        t.val - w ^ 2 ∈ Ioo (H.time eventIndex.castSucc)
          (H.stageEndTime eventIndex.castSucc) := by
      have hw0 : 0 < w := ha0.trans_le hw.1
      have hwb : w ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hw0.le hw.2 2
      have hkw : k < w := ha.1.trans_le hw.1
      have hkwSq := mul_pos (sub_pos.mpr hkw) (add_pos hw0 hk)
      rw [H.stageEndTime_castSucc]
      constructor
      · linarith only [hclockEnd, hwb]
      · nlinarith only [hevent, hkwSq]
    have hentry : WithTop.map
        (fun value : ℝ => Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * value / a) (M a) <
        (guard : WithTop ℝ) := by
      obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp (hfiniteEntry a ha)
      rw [← hvalue, WithTop.map_coe]
      apply WithTop.coe_lt_coe.mpr
      simpa only [f, m, ← hvalue, WithTop.untopD_coe] using hsmall
    have hs := weighted_infimum_antitone_on_fixed_regular_stage
      a₀ Cderiv ha₀ request H parameters records hfixed hscalar
      t p x r A hr hA hT aSeed hSeedTime hSeedClock seedTrace hSupportAt
      eventIndex.castSucc hfSeed (eventIndex.castSucc_le_succ.trans hl)
      a b ha0 hab hbhalf hclock nodeA nodeE nodeR nodeQ nodeRho hnode hfit hentry
    exact ⟨hs.1, hs.2.2.1⟩
  have hfanti : AntitoneOn f (Icc k b) :=
    antitoneOn_Icc_of_right_usc_and_guarded_entry_strips f k b d guard hkb hkd hdb
      huscF hgap (fun a ha hsmall => (hstrip a ha hsmall).2)
  have hsmallNear : ∀ᶠ a in 𝓝[>] k, f a < guard :=
    (huscF.mono Ioi_subset_Ici_self) guard hgap
  have hall (w : ℝ) (hw : w ∈ Icc k b) : M w ≠ ⊤ ∧ 0 ≤ m w := by
    rcases eq_or_lt_of_le hw.1 with hkw | hkw
    · subst w
      exact ⟨hfiniteK, hmkpos.le⟩
    · obtain ⟨a, hsmall, ha⟩ :=
        (hsmallNear.and (Ioo_mem_nhdsGT (lt_min hkd hkw))).exists
      have had : a ∈ Ioo k d := ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩
      have haw : a ≤ w := (ha.2.trans_le (min_le_right _ _)).le
      have hs := (hstrip a had hsmall).1 w ⟨haw, hw.2⟩
      exact ⟨hs.1, hs.2.1⟩
  refine ⟨hall, hfanti, ?_⟩
  intro w hw
  have hw0 : 0 < w := hk.trans_le hw.1
  have hh := hfanti ⟨le_rfl, hkb.le⟩ hw hw.1
  constructor
  · change Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w ≤
      Real.exp (-C * k ^ 2 / r ^ 2 - 32 * k / r) * m k / k at hh
    have hmul := (div_le_div_iff₀ hw0 hk).mp hh
    have hexp : Real.exp (C * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r) *
        Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) =
        Real.exp (-C * k ^ 2 / r ^ 2 - 32 * k / r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    apply le_of_mul_le_mul_right ?_
      (mul_pos (Real.exp_pos (-C * w ^ 2 / r ^ 2 - 32 * w / r)) hk)
    calc
      m w * (Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * k) =
          (Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w) * k := by ring
      _ ≤ (Real.exp (-C * k ^ 2 / r ^ 2 - 32 * k / r) * m k) * w := hmul
      _ = (Real.exp (C * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r) * (w / k) * m k) *
          (Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * k) := by
        rw [← hexp]
        field_simp [hk.ne']
  · have hbound : f w ≤ 2 * r := hh.trans hclosed
    have hscaled : Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w ≤ 2 * r * w :=
      (div_le_iff₀ hw0).mp hbound
    have hcancel : Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) *
        Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) = 1 := by
      rw [← Real.exp_add, show (C * w ^ 2 / r ^ 2 + 32 * w / r) +
        (-C * w ^ 2 / r ^ 2 - 32 * w / r) = 0 by ring, Real.exp_zero]
    have hmul := mul_le_mul_of_nonneg_left hscaled
      (Real.exp_pos (C * w ^ 2 / r ^ 2 + 32 * w / r)).le
    have hm : m w ≤ Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) * (2 * r * w) := by
      simpa only [← mul_assoc, hcancel, one_mul] using hmul
    simpa only [mul_comm] using hm

theorem traced_weighted_minimum_restarts_on_incoming_stage_without_loss
    (a₀ c : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hSupport :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ c →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p,
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      H.time (H.activeStage t) < t.val →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0)
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hrecenter : parameters.recenterConstant ≤ c)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val)
    (hseed : H.isParabolicallyRmControlledBall t p r)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hpole : H.time (H.activeStage t) < t.val)
    (k b : ℝ) (hk : 0 < k) (hkb : k < b)
    (hbhalf : b ^ 2 ≤ r ^ 2 / 2)
    (eventIndex : Fin H.eventCount) (hfSeed : H.activeStage aSeed ≤ eventIndex.castSucc)
    (hl : eventIndex.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time eventIndex.succ)
    {Dcap εcap : ℝ} {ncap : ℕ}
    (S : ∀ c : (H.event eventIndex).RetainedBoundaryIndex,
      (H.event eventIndex).PresentedStaticCap parameters.fixed Dcap ncap εcap c)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : εcap ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < Dcap)
    (O z : (H.event eventIndex).old)
    (hOin : O.val.val = seedTrace.point eventIndex.castSucc hfSeed (eventIndex.castSucc_le_succ.trans hl))
    (hO : ∀ c, (H.event eventIndex).oldOutput O ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ c, (H.event eventIndex).oldOutput z ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (L : ℝ)
    (hinside : riemannianEDistOf (H.event eventIndex).outputMetric
        ((H.event eventIndex).oldOutput O) ((H.event eventIndex).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost eventIndex.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x
      ((H.event eventIndex).oldOutput z) = (L : WithTop ℝ))
    (hcontact : H.physicalWeightedCost eventIndex.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
        ((H.event eventIndex).oldOutput O) ((H.event eventIndex).oldOutput z) =
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A k)
    (hclockEnd : H.time eventIndex.castSucc < t.val - b ^ 2) :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : eventIndex.castSucc ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ b ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), eventIndex.castSucc ≤ i.castSucc → i.succ ≤ H.activeStage t →
        D * r ≤ nodeA i) →
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun w => (M w).untopD 0
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    f k ≤ 2 * r →
    (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
    AntitoneOn f (Icc k b) ∧
    (∀ w ∈ Icc k b,
      m w ≤ Real.exp (C * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r) *
        (w / k) * m k ∧
      m w ≤ 2 * r * w * Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r)) := by
  refine traced_weighted_minimum_restarts_on_fixed_incoming_stage a₀ Cderiv ha₀ request
    H parameters records hfixed hscalar t p x r A hr hA hT
    aSeed hSeedTime hSeedClock seedTrace ?_ k b hk hkb hbhalf
    eventIndex hfSeed hl hevent S hcanonical hε hD O z hOin hO hz L hinside hcost hcontact
    hclockEnd
  intro _C _D a has hat v hv hhalf hclock hpast
  exact hSupport H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock hpole hpast

theorem traced_weighted_minimum_restarts_on_incoming_stage_without_loss_at_closed_poles
    (a₀ c : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hSupport :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ c →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p,
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0)
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hrecenter : parameters.recenterConstant ≤ c)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val)
    (hseed : H.isParabolicallyRmControlledBall t p r)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (k b : ℝ) (hk : 0 < k) (hkb : k < b)
    (hbhalf : b ^ 2 ≤ r ^ 2 / 2)
    (eventIndex : Fin H.eventCount) (hfSeed : H.activeStage aSeed ≤ eventIndex.castSucc)
    (hl : eventIndex.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time eventIndex.succ)
    {Dcap εcap : ℝ} {ncap : ℕ}
    (S : ∀ c : (H.event eventIndex).RetainedBoundaryIndex,
      (H.event eventIndex).PresentedStaticCap parameters.fixed Dcap ncap εcap c)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : εcap ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < Dcap)
    (O z : (H.event eventIndex).old)
    (hOin : O.val.val = seedTrace.point eventIndex.castSucc hfSeed (eventIndex.castSucc_le_succ.trans hl))
    (hO : ∀ c, (H.event eventIndex).oldOutput O ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ c, (H.event eventIndex).oldOutput z ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (L : ℝ)
    (hinside : riemannianEDistOf (H.event eventIndex).outputMetric
        ((H.event eventIndex).oldOutput O) ((H.event eventIndex).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost eventIndex.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x
      ((H.event eventIndex).oldOutput z) = (L : WithTop ℝ))
    (hcontact : H.physicalWeightedCost eventIndex.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
        ((H.event eventIndex).oldOutput O) ((H.event eventIndex).oldOutput z) =
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A k)
    (hclockEnd : H.time eventIndex.castSucc < t.val - b ^ 2) :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : eventIndex.castSucc ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ b ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), eventIndex.castSucc ≤ i.castSucc → i.succ ≤ H.activeStage t →
        D * r ≤ nodeA i) →
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun w => (M w).untopD 0
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    f k ≤ 2 * r →
    (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
    AntitoneOn f (Icc k b) ∧
    (∀ w ∈ Icc k b,
      m w ≤ Real.exp (C * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r) *
        (w / k) * m k ∧
      m w ≤ 2 * r * w * Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r)) := by
  refine traced_weighted_minimum_restarts_on_fixed_incoming_stage a₀ Cderiv ha₀ request
    H parameters records hfixed hscalar t p x r A hr hA hT
    aSeed hSeedTime hSeedClock seedTrace ?_ k b hk hkb hbhalf
    eventIndex hfSeed hl hevent S hcanonical hε hD O z hOin hO hz L hinside hcost hcontact
    hclockEnd
  intro _C _D a has hat v hv hhalf hclock hpast
  exact hSupport H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock hpast

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
