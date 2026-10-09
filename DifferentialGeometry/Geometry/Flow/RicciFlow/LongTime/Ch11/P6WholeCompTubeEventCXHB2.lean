import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WholeCompNeckCXHB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransEventCXHT
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSpatialNeck

/-!
# CX-HTUBE2 G2：event 层 whole-component cut-tube 不交 + 无条件 htube 的移除（`_CXHB2`）

* **`cutTubeDisjoint_of_wholeComponent_CXHB2`**（D-6 的局部 exclusion，positive / round 两支）：
  `Rc : GeometricCutoffRecord H i pp`，`∀ j, Rc.delta j ≤ eps`，`eps < 1/11`，
  `eps · (10 · C1w · √C2w) ≤ 1`，`v → s⁻`，frequently 在 `(v n, p')` 有 positive / round
  `(η, C1w, C2w)` witness ⇒ `∀ j, Disjoint (comp p') (range (tube j))`（即固定点的 (P)）。
  三组接口事实：
  (1) 拓扑 / 索引识别：`Rc.eventually_exists_spatialNeck`（树内）给 `g(t)` 的 spatial `eps`-neck，
      `nk.map (q.1, q.2) = tube j q`，故 `range (tube j) ⊆ nk.map '' (S² × (-eps⁻¹, eps⁻¹))`
      （`|q.2| ≤ 2 < 11 < eps⁻¹`）；相交 ⇒ 包含 = G1 `slab_subset_component_CXHB2`。
  (2) 同度量几何：neck 就在 `g(v n)` 里（backward neck → preterminal 的度量 / 中心 / 尺度识别由
      `IncomingBackwardNeck.eventually_exists_normalizedNeck` 完成，中心 = `(Rc.neck j).center`，
      尺度 = `R_{g(v n)}(center)` 自身，故比较常数 `B = 1`）；ambient 距离下界 = G1。
  (3) δ-smallness：本定理把它作为显式数值前提；tower 层的 records 供给见 G3 合同。
* **`htrans_event_record_CXHB2`**：`htrans_event_CXHT` 的孪生——无条件 `htube` 换成
  `Rc` + δ-smallness（`eps · (10 C1₁ √C2₁) ≤ 1`）。证明：反设 eventually 有 witness，类型鸽笼
  给 frequently positive ∨ round，由上一定理得 `htube`，再调 `htrans_event_CXHT` 矛盾。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- **whole-component 局部 cut-tube 不交（positive / round 两支）**。 -/
theorem cutTubeDisjoint_of_wholeComponent_CXHB2 (Rc : GeometricCutoffRecord H i pp)
    {eps η C1w C2w : ℝ} (heps : eps < 1 / 11) (hdelta : ∀ j, Rc.delta j ≤ eps)
    (hsmall : eps * (10 * C1w * Real.sqrt C2w) ≤ 1)
    {p' : (H.stage i.castSucc).Carrier} {v : ℕ → ℝ}
    (hvt : Tendsto v atTop (𝓝[<] H.time i.succ))
    (hW : ∃ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
      ((H.event i).incoming.flow.base.metric (v n)) η C1w C2w p',
      (∃ wh d sc, W.alternative = .positive wh d sc) ∨ ∃ wh R, W.alternative = .round wh R) :
    ∀ j, Disjoint (connectedComponent p')
      (Set.range ((H.event i).transition.trace.tubes.tube j)) := by
  intro j
  have hev := hvt.eventually (Rc.eventually_exists_spatialNeck heps hdelta)
  obtain ⟨n, ⟨W, hW⟩, hnk⟩ := (hW.and_eventually hev).exists
  obtain ⟨nk, -, hmap⟩ := hnk j
  have hi : (11 : ℝ) < eps⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) nk.eps_pos]
    linarith
  refine (disjoint_slab_of_wholeComponent_CXHB2 W
    (domain_eq_component_of_posOrRound_CXHB2 W hW) nk hsmall).mono_right ?_
  rintro _ ⟨z, rfl⟩
  refine ⟨(z.1, z.2.val), ⟨mem_univ _, ?_, ?_⟩, hmap z⟩ <;> linarith [z.2.2.1, z.2.2.2]

end GeometricCutoffRecord

namespace ObservedHistory

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- **`htrans` event 层孪生（无条件 `htube` 移除）**：`Rc` + δ-smallness 代替 `htube`。 -/
theorem htrans_event_record_CXHB2 (Rc : GeometricCutoffRecord H i pp) {eps : ℝ}
    (heps : eps < 1 / 11) (hdelta : ∀ j, Rc.delta j ≤ eps)
    {p : (H.stage i.castSucc).Carrier} {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing p q)
    {ε C1f C2f m : ℝ} {kk : ℕ} (D : (H.event i).BufferedFootprintData_P6ST2 p q ε C1f C2f m kk)
    {η₁ C1₁ C2₁ C1 C2 : ℝ} (hε : 0 < ε) (hη₁ : 0 < η₁)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2)
    (hδ : eps * (10 * C1₁ * Real.sqrt C2₁) ≤ 1)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
      W.capTubeHasNeckChart ε) :
    ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
      ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p, W.capTubeHasNeckChart η₁ := by
  have hlt : neckModelTolerance (ε / 2) < 1 / 11 := by
    have := neckModelTolerance_le (ε / 2)
    linarith [D.ηout_lt]
  have hA := MetricCutCapEvent.frequently_not_fineMargin_P6ST2 D
    (le_refl (neckModelTolerance (ε / 2))) h1 h2 hnot
  intro hev
  have hev' : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
      ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p, W.capTubeHasNeckChart η₁ :=
    hev.mono fun n hn => not_not.mp hn
  have hposround : ∃ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
      ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p,
      (∃ wh d sc, W.alternative = .positive wh d sc) ∨ ∃ wh R, W.alternative = .round wh R := by
    refine (hA.and_eventually hev').mono fun n ⟨hbad, W, hW⟩ => ⟨W, ?_⟩
    exact alt_posOrRound_of_not_fineMarginGood_CXHT
      (g := (H.event i).incoming.flow.base.metric (D.v n)) hη (by linarith) hC1f hC2f hm hm'
      hbad W hW
  have hvt : Tendsto D.v atTop (𝓝[<] H.time i.succ) :=
    tendsto_nhdsWithin_iff.mpr ⟨D.v_tendsto, Eventually.of_forall fun n => (D.v_mem n).2⟩
  have htube := Rc.cutTubeDisjoint_of_wholeComponent_CXHB2 heps hdelta hδ hvt hposround
  exact MetricCutCapEvent.htrans_event_CXHT hcross htube D hε hη₁ hη hsmall hC1₁ hC2₁ hC1f hC2f
    hm hm' h1 h2 hnot hev

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
