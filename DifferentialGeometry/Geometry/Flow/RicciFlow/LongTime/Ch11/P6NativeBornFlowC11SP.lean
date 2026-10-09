import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

/-!
# born patch 的公共 flow（O-CH11-NATIVE-BORN G2 = SL2-c-ii，后缀 `_C11SP`）

hBorn 的第二个引理。patch `B(w, ρ)` 上每点 alive（从 `a` 起、Rm ≤ K 的 trace）或 born（从 `v ≤ u*`
起、Rm ≤ K 的 trace），则整块从 `u*` 起 traced：
* `exists_max_bornTime_C11SP`：born 点有限多种 event ⇒ 取 born 时刻最大的 `(x*, e*)`（`Finset.exists_max_image`）；
* `bornPatch_isTracedRegion_C11SP`：trace 截到 `u*`（`restrictFirst` + `isRmBoundedBy.restrictFirst`）⇒
  `isTracedRegion t w ρ (t − u*) K`；深度 `t − u*` 无下界；
* `bornPatch_commonFlow_C11SP`：再用 `exists_common_flow_with_compact_neighborhood_of_isTracedRegion`，
  并把它的 `a` 认成 `u*`，得到 SPINE-B G7 `exists_reset_shi_commonFlow_C11SP` 的全部输入
  （`U / f / hf / S / IsSolutionOn / hmetric / hRm / hterminal`），外加 `f j x = B.point j`（trace 唯一性
  `BackwardPointTrace.point_unique`），这样 G3 能把 G7 的初始 jets 位置认成 born 点 cap window 的点。
HANDOVER v3 估计 (ii) 约 400–700 行；实际树内 `exists_common_flow_of_isTracedRegion` 已跨任意多个
event 拼好公共 flow，这里只剩截断与识别。
-/

noncomputable section

open Set Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G2c（PROVED）**：born 点所属 event 有限 ⇒ 存在 born 时刻最大的 `(x*, e*)`。 -/
theorem exists_max_bornTime_C11SP (H : ObservedHistory.{u}) {α : Type*} (X : Set α)
    (Ev : α → Fin H.eventCount → Prop) (hne : ∃ x ∈ X, ∃ e, Ev x e) :
    ∃ x ∈ X, ∃ e, Ev x e ∧ ∀ x' ∈ X, ∀ e', Ev x' e' → H.time e'.succ ≤ H.time e.succ := by
  classical
  let s : Finset (Fin H.eventCount) := Finset.univ.filter fun e => ∃ x ∈ X, Ev x e
  have hs : s.Nonempty := by
    obtain ⟨x, hx, e, he⟩ := hne
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, he⟩⟩
  obtain ⟨e, hes, hmax⟩ := s.exists_max_image (fun e => H.time e.succ) hs
  obtain ⟨-, x, hx, hex⟩ := Finset.mem_filter.mp hes
  refine ⟨x, hx, e, hex, fun x' hx' e' he' => hmax e' ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x', hx', he'⟩

/-- **G2a（PROVED）**：patch 上逐点 alive（从 `a`）或 born（从 `v ≤ u*`）且 Rm ≤ K ⇒
从 `u*` 起的 traced region，深度 `t − u*`。 -/
theorem bornPatch_isTracedRegion_C11SP (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (w : (H.stageAt t).Carrier) {ρ K : ℝ} (hρ : 0 < ρ)
    (a ustar : Icc (0 : ℝ) H.horizon) (hat : a ≤ t) (hau : a ≤ ustar) (hut : ustar ≤ t)
    (hlt : (ustar : ℝ) < t)
    (hall : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) w ρ,
      (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
          B.isRmBoundedBy (hat := hat) K) ∨
      ∃ (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t), v ≤ ustar ∧
        ∃ B : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt) x,
          B.isRmBoundedBy (hat := hvt) K) :
    H.isTracedRegion t w ρ ((t : ℝ) - ustar) K := by
  refine ⟨hρ, sub_pos.mpr hlt, ustar, hut, by ring, fun x hx => ?_⟩
  rcases hall x hx with ⟨B, hB⟩ | ⟨v, hvt, hvu, B, hB⟩
  · exact ⟨B.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut),
      BackwardPointTrace.isRmBoundedBy.restrictFirst B hB hau hut⟩
  · exact ⟨B.restrictFirst (H.activeStage_mono hvu) (H.activeStage_mono hut),
      BackwardPointTrace.isRmBoundedBy.restrictFirst B hB hvu hut⟩

/-- **G2（PROVED）**：born patch 在 `[u*, t]` 上的公共 flow，形状 = G7
`exists_reset_shi_commonFlow_C11SP` 的输入；另给 `f j x = B.point j`（任意 trace `B`）。 -/
theorem bornPatch_commonFlow_C11SP (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (w : (H.stageAt t).Carrier) {ρ K : ℝ} (hρ : 0 < ρ)
    (a ustar : Icc (0 : ℝ) H.horizon) (hat : a ≤ t) (hau : a ≤ ustar) (hut : ustar ≤ t)
    (hlt : (ustar : ℝ) < t)
    (hall : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) w ρ,
      (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
          B.isRmBoundedBy (hat := hat) K) ∨
      ∃ (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t), v ≤ ustar ∧
        ∃ B : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt) x,
          B.isRmBoundedBy (hat := hvt) K) :
    ∃ U : TopologicalSpace.Opens (H.stageAt t).Carrier,
      (U : Set (H.stageAt t).Carrier) =
        riemannianBallOf (H.stageMetric (H.activeStage t) t) w ρ ∧
      ∃ f : (j : H.StageInterval (H.activeStage ustar) (H.activeStage t)) → U →
          (H.stage j.val).Carrier,
        ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
          (∀ (x : U) (B : BackwardPointTrace H (H.activeStage ustar) (H.activeStage t)
              (H.activeStage_mono hut) x.val) (j : H.StageInterval (H.activeStage ustar)
                (H.activeStage t)), f j x = B.point j.val j.property.1 j.property.2) ∧
          ∃ S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed ustar.val t.val hut),
            IsSolutionOn S ∧
            (∀ j : H.StageInterval (H.activeStage ustar) (H.activeStage t),
              ∀ v ∈ Icc ustar.val t.val, v ∈ H.stageDomain j.val →
                S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
            (∀ v ∈ Icc ustar.val t.val, ∀ x : U,
              normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2) ∧
            S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U := by
  have htr := bornPatch_isTracedRegion_C11SP H t w hρ a ustar hat hau hut hlt hall
  obtain ⟨a', hat', ha', U, hU, f, hf, -, hcross, hlast, S, hS, hmetric, hRm, hcurrent, -⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_isTracedRegion t w htr
  have hEq : a' = ustar := Subtype.ext (by rw [ha']; ring)
  subst hEq
  refine ⟨U, hU, f, hf, ?_, S, hS, hmetric, hRm, hcurrent t ⟨hat', le_rfl⟩ (H.activeStage_mem t)⟩
  intro x B j
  let T : BackwardPointTrace H (H.activeStage a') (H.activeStage t) (H.activeStage_mono hut)
      x.val :=
    { point := fun k hk1 hk2 => f ⟨k, hk1, hk2⟩ x
      endpoint_eq := hlast x
      crossing := fun i hi hl => hcross i hi hl x }
  exact BackwardPointTrace.point_unique T B j.val j.property.1 j.property.2

/-- consumer：G2c 选出最大 born 时刻后，G2 的输出逐项喂 SPINE-B G7 的前提（类型对齐检查）。 -/
example (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (w : (H.stageAt t).Carrier) {ρ K : ℝ} (hρ : 0 < ρ)
    (a ustar : Icc (0 : ℝ) H.horizon) (hat : a ≤ t) (hau : a ≤ ustar) (hut : ustar ≤ t)
    (hlt : (ustar : ℝ) < t)
    (halive : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) w ρ,
      ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
          B.isRmBoundedBy (hat := hat) K) :
    ∃ U : TopologicalSpace.Opens (H.stageAt t).Carrier,
      ∃ f : (j : H.StageInterval (H.activeStage ustar) (H.activeStage t)) → U →
          (H.stage j.val).Carrier,
        ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
          ∃ S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed ustar.val t.val hut),
            IsSolutionOn S ∧
            (∀ j : H.StageInterval (H.activeStage ustar) (H.activeStage t),
              ∀ v ∈ Icc ustar.val t.val, v ∈ H.stageDomain j.val →
                S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) := by
  obtain ⟨U, -, f, hf, -, S, hS, hmetric, -, -⟩ := bornPatch_commonFlow_C11SP H t w hρ a ustar
    hat hau hut hlt fun x hx => Or.inl (halive x hx)
  exact ⟨U, f, hf, S, hS, hmetric⟩

end GC.LongTime.Ch11
