import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalDistanceUpperLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

/-!
# S-CH11-FIX8 port of astra `EventWeightedContinuation`（`PortC11P`）

来源：donor `EventWeightedContinuation.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `hpost`：`simp only [physicalWeightedCost, hpostMetric, hinside, ite_true, hcost, …]` 里 `hinside`
  讲 `(H.event i).outputMetric`，目标里是 let 变量 `E`（`E := H.event i`），simp 不 zeta-delta，
  四个 simp 参数都 unused、`if` 没化简 → 先把 `hinside` / `hcost` 用 `E` 重述为
  `hins` / `hcostE`（defeq 转型），simp 里换用它们；
* 三处 `add_le_add_right`（本树左右约定相反）→ `add_le_add … le_rfl`；
* `E.terminal.eventually_ambient_edist_le (E.oldTerminal O) …`：本树的字段记法把
  `(E.oldTerminal O)` 填给显式参数 `G`（`IncomingSlab`）→ 写成
  `OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ambient_edist_le _ E.terminal …`。

原路径 `EventWeightedContinuation` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem exists_weighted_upper_neighborhood
    (r A k C D η : ℝ)
    (harg : D / r - A * (1 - 2 * k ^ 2 / r ^ 2) < 1 / 10)
    (hpositive : 0 < 2 * k * C + 2 * r * k) (hη : 0 < η) :
    ∃ e : ℝ, 0 < e ∧ ∃ d : ℝ, k < d ∧ ∀ v ∈ Ioo k d,
      (D + e) / r - A * (1 - 2 * v ^ 2 / r ^ 2) < 1 / 10 ∧
      0 < 2 * v * (C + e) + 2 * r * v ∧
      DifferentialGeometry.Analysis.SingularBarrier.value
          ((D + e) / r - A * (1 - 2 * v ^ 2 / r ^ 2)) *
          (2 * v * (C + e) + 2 * r * v) <
        DifferentialGeometry.Analysis.SingularBarrier.value
          (D / r - A * (1 - 2 * k ^ 2 / r ^ 2)) *
          (2 * k * C + 2 * r * k) + η := by
  let arg : ℝ × ℝ → ℝ := fun z =>
    (D + z.1) / r - A * (1 - 2 * z.2 ^ 2 / r ^ 2)
  let factor : ℝ × ℝ → ℝ := fun z => 2 * z.2 * (C + z.1) + 2 * r * z.2
  let envelope : ℝ × ℝ → ℝ := fun z =>
    DifferentialGeometry.Analysis.SingularBarrier.value (arg z) * factor z
  have harg0 : arg (0, k) < 1 / 10 := by
    simpa only [arg, add_zero] using harg
  have hfactor0 : 0 < factor (0, k) := by
    simpa only [factor, add_zero] using hpositive
  have hargContinuous : Continuous arg := by dsimp only [arg]; fun_prop
  have hfactorContinuous : Continuous factor := by dsimp only [factor]; fun_prop
  have hphi : ContinuousAt DifferentialGeometry.Analysis.SingularBarrier.value
      (arg (0, k)) :=
    DifferentialGeometry.Analysis.SingularBarrier.contDiffOn.continuousOn.continuousAt
      (isOpen_Iio.mem_nhds harg0)
  have henvelope : ContinuousAt envelope (0, k) :=
    (hphi.comp hargContinuous.continuousAt).mul hfactorContinuous.continuousAt
  have hnear : ∀ᶠ z in 𝓝 ((0, k) : ℝ × ℝ),
      arg z < 1 / 10 ∧ 0 < factor z ∧ envelope z < envelope (0, k) + η :=
    (hargContinuous.continuousAt.eventually (Iio_mem_nhds harg0)).and
      ((hfactorContinuous.continuousAt.eventually (Ioi_mem_nhds hfactor0)).and
        (henvelope.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hη))))
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ / 2, half_pos hδ, k + δ / 2, by linarith, ?_⟩
  intro v hv
  have hd : dist ((δ / 2, v) : ℝ × ℝ) (0, k) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [sub_zero, abs_of_pos (half_pos hδ), abs_of_pos (sub_pos.mpr hv.1)]
    exact max_lt (by linarith) (by linarith [hv.2])
  simpa only [arg, factor, envelope, add_zero] using hδnear hd

theorem ObservedHistory.exists_physicalWeightedCost_lt_after_event_of_outside_canonical_cap_windows
    (H : ObservedHistory.{u})
    (i : Fin H.eventCount) (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B r A k b C : ℝ}
    (hr : 0 < r) (hk : 0 < k) (hkb : k < b)
    (hevent : T - k ^ 2 = H.time i.succ)
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ c : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap fixed D m ε c)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    (O z : (H.event i).old)
    (hO : ∀ c, (H.event i).oldOutput O ∉ (S c).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ c, (H.event i).oldOutput z ∉ (S c).window ''
      {x : standardCapWindow D | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hinside : riemannianEDistOf (H.event i).outputMetric
        ((H.event i).oldOutput O) ((H.event i).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost i.succ last hl T B 0 k p
      ((H.event i).oldOutput z) = (C : WithTop ℝ))
    (hpositive : 0 < 2 * k * C + 2 * r * k) :
    ∀ η : ℝ, 0 < η → ∃ d : ℝ, k < d ∧ d ≤ b ∧
      ∀ v ∈ Ioo k d,
        H.physicalWeightedCost i.castSucc last (i.castSucc_le_succ.trans hl)
            T B r A v p O.val.val z.val.val <
          H.physicalWeightedCost i.succ last hl T B r A k p
            ((H.event i).oldOutput O) ((H.event i).oldOutput z) + (η : WithTop ℝ) := by
  classical
  let E := H.event i
  let Dplus := riemannianEDistOf E.outputMetric (E.oldOutput O) (E.oldOutput z)
  let Dreal : ℝ := Dplus.toReal
  have hfinite : Dplus ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinside.le
  have hDnonneg : 0 ≤ Dreal := ENNReal.toReal_nonneg
  have hDreal : ENNReal.ofReal Dreal = Dplus := ENNReal.ofReal_toReal hfinite
  have harg : Dreal / r - A * (1 - 2 * k ^ 2 / r ^ 2) < 1 / 10 := by
    have hdist := ENNReal.toReal_lt_of_lt_ofReal hinside
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    dsimp only [Dreal, Dplus, E]
    nlinarith only [hdist]
  have hpostMetric : H.stageMetric i.succ (T - k ^ 2) = E.outputMetric := by
    rw [hevent, H.stageMetric_initial]
    exact (H.event_output i).symm
  have hpost : H.physicalWeightedCost i.succ last hl T B r A k p
        (E.oldOutput O) (E.oldOutput z) =
      ((DifferentialGeometry.Analysis.SingularBarrier.value
          (Dreal / r - A * (1 - 2 * k ^ 2 / r ^ 2)) *
          (2 * k * C + 2 * r * k) : ℝ) : WithTop ℝ) := by
    have hins : riemannianEDistOf E.outputMetric (E.oldOutput O) (E.oldOutput z) <
        ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) := hinside
    have hcostE : H.regularizedCost i.succ last hl T B 0 k p (E.oldOutput z) =
        (C : WithTop ℝ) := hcost
    simp only [ObservedHistory.physicalWeightedCost, hpostMetric, hins,
      ite_true, hcostE, WithTop.map_coe, Dreal, Dplus]
  have hterminal := E.oldTerminal_edist_le_of_outside_canonical_cap_windows
    S hOld hcanonical hε hD O z hO hz
  have hterminalFinite :
      riemannianEDistOf E.terminal.metric (E.oldTerminal O) (E.oldTerminal z) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite hterminal
  intro η hη
  obtain ⟨e, he, dweight, hkweight, hweight⟩ :=
    exists_weighted_upper_neighborhood r A k C Dreal η harg hpositive hη
  obtain ⟨t₀, ht₀, hlimit⟩ :=
    OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ambient_edist_le _
      E.terminal (E.oldTerminal O) (E.oldTerminal z) hterminalFinite e he
  have htime : ∀ᶠ v in 𝓝 k, t₀ < T - v ^ 2 := by
    have hc : ContinuousAt (fun v : ℝ => T - v ^ 2) k := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (by simpa only [hevent] using ht₀.2))
  obtain ⟨daction, hkaction, _, haction⟩ :=
    H.exists_regularizedCost_lt_after_event i last hl (u := 0) hkb hevent
      (by simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hupper)
      hscalar p z hcost e he
  have hnear : ∀ᶠ v in 𝓝[>] k,
      H.physicalWeightedCost i.castSucc last (i.castSucc_le_succ.trans hl)
          T B r A v p O.val.val z.val.val <
        H.physicalWeightedCost i.succ last hl T B r A k p
          (E.oldOutput O) (E.oldOutput z) + (η : WithTop ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT hkweight, Ioo_mem_nhdsGT hkaction,
      htime.filter_mono nhdsWithin_le_nhds] with v hvweight hvaction hvtime
    have hv : 0 < v := hk.trans hvweight.1
    have hbefore : T - v ^ 2 < H.time i.succ := by
      have hprod := mul_pos (sub_pos.mpr hvweight.1) (add_pos hv hk)
      nlinarith only [hprod, hevent]
    have hdistIncoming : riemannianEDistOf (H.stageMetric i.castSucc (T - v ^ 2))
        O.val.val z.val.val ≤ ENNReal.ofReal (Dreal + e) := by
      have ht := hlimit (T - v ^ 2) ⟨hvtime, hbefore⟩
      have hb := ht.trans (add_le_add hterminal le_rfl)
      rw [ObservedHistory.stageMetric_castSucc_apply]
      rw [ENNReal.ofReal_add hDnonneg he.le, hDreal]
      simpa only [E.oldTerminal_eq O, E.oldTerminal_eq z] using hb
    have hdistReal :
        (riemannianEDistOf (H.stageMetric i.castSucc (T - v ^ 2))
          O.val.val z.val.val).toReal ≤ Dreal + e :=
      ENNReal.toReal_le_of_le_ofReal (add_nonneg hDnonneg he.le) hdistIncoming
    obtain ⟨hargUpper, hfactorUpper, henvelope⟩ := hweight v hvweight
    have hcutoff : Dreal + e < r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10) := by
      have hh := (div_lt_iff₀ hr).mp ((sub_lt_iff_lt_add).mp hargUpper)
      nlinarith only [hh]
    have hcutoffPos : 0 < r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10) :=
      (add_pos_of_nonneg_of_pos hDnonneg he).trans hcutoff
    have hinsideV : riemannianEDistOf (H.stageMetric i.castSucc (T - v ^ 2))
        O.val.val z.val.val <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) :=
      hdistIncoming.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hcutoffPos).mpr hcutoff)
    let argV :=
      (riemannianEDistOf (H.stageMetric i.castSucc (T - v ^ 2))
        O.val.val z.val.val).toReal / r - A * (1 - 2 * v ^ 2 / r ^ 2)
    have hargLe : argV ≤ (Dreal + e) / r - A * (1 - 2 * v ^ 2 / r ^ 2) :=
      sub_le_sub_right (div_le_div_of_nonneg_right hdistReal hr.le) _
    have hargV : argV < 1 / 10 := hargLe.trans_lt hargUpper
    have hphiPos := DifferentialGeometry.Analysis.SingularBarrier.pos hargV
    have hphiLe := DifferentialGeometry.Analysis.SingularBarrier.monotoneOn
      hargV hargUpper hargLe
    have hcostLt := haction v hvaction
    have hcostFinite : H.regularizedCost i.castSucc last
        (i.castSucc_le_succ.trans hl) T B 0 v p z.val.val ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hcostLt.le
    obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hcostFinite
    have hcostEq : H.regularizedCost i.castSucc last
        (i.castSucc_le_succ.trans hl) T B 0 v p z.val.val = (L : WithTop ℝ) := hL.symm
    have hLupper : L < C + e := by
      rw [hcostEq] at hcostLt
      exact WithTop.coe_lt_coe.mp hcostLt
    have hfactorLe : 2 * v * L + 2 * r * v ≤ 2 * v * (C + e) + 2 * r * v :=
      add_le_add (mul_le_mul_of_nonneg_left hLupper.le (by positivity : (0 : ℝ) ≤ 2 * v))
        le_rfl
    have hvalue : H.physicalWeightedCost i.castSucc last
        (i.castSucc_le_succ.trans hl) T B r A v p O.val.val z.val.val =
        ((DifferentialGeometry.Analysis.SingularBarrier.value argV *
          (2 * v * L + 2 * r * v) : ℝ) : WithTop ℝ) := by
      simp only [ObservedHistory.physicalWeightedCost, hinsideV, ite_true,
        hcostEq, WithTop.map_coe, argV]
    rw [hvalue, hpost, ← WithTop.coe_add]
    apply WithTop.coe_lt_coe.mpr
    calc
      DifferentialGeometry.Analysis.SingularBarrier.value argV *
          (2 * v * L + 2 * r * v) ≤
          DifferentialGeometry.Analysis.SingularBarrier.value argV *
            (2 * v * (C + e) + 2 * r * v) :=
        mul_le_mul_of_nonneg_left hfactorLe hphiPos.le
      _ ≤ DifferentialGeometry.Analysis.SingularBarrier.value
          ((Dreal + e) / r - A * (1 - 2 * v ^ 2 / r ^ 2)) *
            (2 * v * (C + e) + 2 * r * v) :=
        mul_le_mul_of_nonneg_right hphiLe hfactorUpper.le
      _ < _ := henvelope
  obtain ⟨d, hkd, hd⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hkb).mp hnear
  refine ⟨min d b, lt_min hkd hkb, min_le_right _ _, ?_⟩
  intro v hv
  exact hd ⟨hv.1, hv.2.trans_le (min_le_left _ _)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
