import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryNoShortcutDisjC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonDefs

/-!
# O-CH11-NATIVE-SHORT G3：`hdisj` 对 `GeometricCutoffRecord` 的 static cap 成立（`_C11SP`）

(D4′) 链剩下的 binder `hdisj`（不同 `RetainedBoundaryIndex` 的 cap window 不相交）对**一般** `S` 不可导：
`StaticCapWitness` 只在 `‖x‖ ≤ fixed.deepRadius` 处（`window_deep`）把 `window` 绑到 `capChart`，collar
半径处没有字段把 `window` 连到 `retained` / neck；不同 `b` 的 `(S b).neck` 之间也没有关联。
对 `S = G.static`（`G : GeometricCutoffRecord H i parameters`，下游 NATIVE-CC 用的正是
`(records e).static`）则**完整的 hdisj（不需 `‖z‖ ≤ TE + 10`）成立**：
* `witness.cover`：window 点 = retained collar 点或 cap 点；`retained_eq` / `cap_eq` 推到 presentation；
* cap/cap：`Capping.cap_disjoint`；retained/cap：`Capping.core_cap_intersection` ⇒ 是 `b'` 的
  core 边界球点 = `tube b'.1.1` 的点（`tube_eq` + `tube_in_buffer`）= record neck `b'.1.1` 的 chart 点；
* retained 点 = static neck chart 点（`retained_point_eq`，`neckRetainedCollar ⊆ neckBuffer`）=
  record neck `b.1.1` 的 chart 点（`staticNeckChart_eq_neckChart`）；
* `buffer_disjoint` ⇒ `b.1.1 = b'.1.1`，`retainedBoundary_side_eq` ⇒ `b = b'`。
（模板：`GeometricCutoffRecord.staticNeckPoint_range_disjoint`，ComparisonSupportRegion.lean:90。）
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D η : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- window 点在 presentation 下要么是 retained collar 的 core 点，要么是 cap `b.1` 的点。 -/
theorem window_mem_cases_C11SP (S : E.PresentedStaticCap fixed D m η b)
    (y : standardCapWindow D) :
    (∃ r : neckRetainedCollar S.delta, E.transition.trace.presentation
        (E.transition.trace.capping.coreInclusion (S.retainedPoint r).1) =
          Sum.inl (S.window y)) ∨
      ∃ k : ThreeBall, E.transition.trace.presentation (E.transition.trace.capping.cap b.1 k) =
        Sum.inl (S.window y) := by
  have hmem : S.witness.window y ∈ Set.range S.witness.retained ∪ Set.range S.witness.cap := by
    rw [S.witness.cover]
    exact Set.mem_univ _
  rcases hmem with ⟨r, hr⟩ | ⟨k, hk⟩
  · refine Or.inl ⟨r, ?_⟩
    rw [S.retained_eq r, hr]
    rfl
  · refine Or.inr ⟨k, ?_⟩
    rw [S.cap_eq k, hk]
    rfl

end MetricCutCapEvent.PresentedStaticCap

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

/-- static cap 的 retained collar 点落在 record neck `b.1.1` 的 chart 像里。 -/
theorem retainedPoint_mem_neck_C11SP (b : (H.event i).RetainedBoundaryIndex)
    (r : neckRetainedCollar (G.static b).delta) :
    ∃ w, ((G.neck b.1.1).chart w).1 = ((G.static b).retainedPoint r).1.1 := by
  have hr : r.1 ∈ neckBuffer (G.static b).delta := by
    have := inv_pos.mpr (G.static b).neck.delta_pos
    constructor <;> linarith [r.2.1, r.2.2]
  have h := G.staticNeckChart_eq_neckChart b ⟨r.1, hr⟩
  exact ⟨_, h.symm.trans ((G.static b).retained_point_eq r hr).symm⟩

/-- core 边界球点落在 record neck `β.1` 的 chart 像里。 -/
theorem coreBoundarySphere_mem_neck_C11SP (β : (H.event i).transition.trace.tubes.Boundary)
    (ζ : Sphere 2) :
    ∃ w, ((G.neck β.1).chart w).1 =
      ((H.event i).transition.trace.tubes.coreBoundarySphere β ζ).1 := by
  have h := G.tube_eq β.1 (ζ, TubeSystem.boundaryLevel β.2)
    (G.tube_in_buffer β.1 (ζ, TubeSystem.boundaryLevel β.2))
  exact ⟨_, h.symm⟩

/-- **G3（PROVED）**：record 的不同 retained 边界的 static cap window 两两不交（全 window，无半径限制）。 -/
theorem static_window_ne_C11SP {b b' : (H.event i).RetainedBoundaryIndex} (hbb : b ≠ b')
    (y z : standardCapWindow parameters.modelRadius) :
    (G.static b).window y ≠ (G.static b').window z := by
  intro heq
  have hidx : b.1.1 ≠ b'.1.1 := by
    intro hidx
    have hb : (H.event i).RetainedBoundary (b.1.1, b.1.2) := b.2
    have hside : b.1.2 = b'.1.2 := G.retainedBoundary_side_eq (α := b'.1.1) (hidx ▸ hb) b'.2
    exact hbb (Subtype.ext (Prod.ext hidx hside))
  have hb1 : b.1 ≠ b'.1 := fun h => hbb (Subtype.ext h)
  have hnk : ∀ w w', ((G.neck b.1.1).chart w).1 ≠ ((G.neck b'.1.1).chart w').1 := by
    intro w w' h
    exact Set.disjoint_left.mp (G.buffer_disjoint hidx) (Set.mem_range_self w)
      ⟨w', Subtype.ext h.symm⟩
  have hP := (H.event i).transition.trace.presentation.injective
  have hC := (H.event i).transition.trace.capping.coreEmbedding.injective
  rcases (G.static b).window_mem_cases_C11SP y with ⟨r, hr⟩ | ⟨k, hk⟩ <;>
    rcases (G.static b').window_mem_cases_C11SP z with ⟨r', hr'⟩ | ⟨k', hk'⟩
  · have hAB : (H.event i).transition.trace.presentation
          ((H.event i).transition.trace.capping.coreInclusion ((G.static b).retainedPoint r).1) =
        (H.event i).transition.trace.presentation
          ((H.event i).transition.trace.capping.coreInclusion
            ((G.static b').retainedPoint r').1) := by
      rw [hr, heq, hr']
    have h1 := hC (hP hAB)
    obtain ⟨w, hw⟩ := G.retainedPoint_mem_neck_C11SP b r
    obtain ⟨w', hw'⟩ := G.retainedPoint_mem_neck_C11SP b' r'
    exact hnk w w' (hw.trans ((congrArg Subtype.val h1).trans hw'.symm))
  · have h1 : (H.event i).transition.trace.capping.coreInclusion
        ((G.static b).retainedPoint r).1 = (H.event i).transition.trace.capping.cap b'.1 k' :=
      hP (by rw [hr, heq, hk'])
    have hmem : (H.event i).transition.trace.capping.coreInclusion
        ((G.static b).retainedPoint r).1 ∈
          Set.range (H.event i).transition.trace.capping.coreInclusion ∩
            Set.range ((H.event i).transition.trace.capping.cap b'.1) :=
      ⟨⟨_, rfl⟩, ⟨k', h1.symm⟩⟩
    rw [(H.event i).transition.trace.capping.core_cap_intersection] at hmem
    obtain ⟨ζ, hζ⟩ := hmem
    have h2 := hC hζ
    obtain ⟨w, hw⟩ := G.retainedPoint_mem_neck_C11SP b r
    obtain ⟨w', hw'⟩ := G.coreBoundarySphere_mem_neck_C11SP b'.1 ζ
    exact hnk w w' (hw.trans ((congrArg Subtype.val h2).symm.trans hw'.symm))
  · have h1 : (H.event i).transition.trace.capping.coreInclusion
        ((G.static b').retainedPoint r').1 = (H.event i).transition.trace.capping.cap b.1 k :=
      hP (by rw [hr', ← heq, hk])
    have hmem : (H.event i).transition.trace.capping.coreInclusion
        ((G.static b').retainedPoint r').1 ∈
          Set.range (H.event i).transition.trace.capping.coreInclusion ∩
            Set.range ((H.event i).transition.trace.capping.cap b.1) :=
      ⟨⟨_, rfl⟩, ⟨k, h1.symm⟩⟩
    rw [(H.event i).transition.trace.capping.core_cap_intersection] at hmem
    obtain ⟨ζ, hζ⟩ := hmem
    have h2 := hC hζ
    obtain ⟨w, hw⟩ := G.coreBoundarySphere_mem_neck_C11SP b.1 ζ
    obtain ⟨w', hw'⟩ := G.retainedPoint_mem_neck_C11SP b' r'
    exact hnk w w' (hw.trans ((congrArg Subtype.val h2).trans hw'.symm))
  · have hAB : (H.event i).transition.trace.presentation
          ((H.event i).transition.trace.capping.cap b.1 k) =
        (H.event i).transition.trace.presentation
          ((H.event i).transition.trace.capping.cap b'.1 k') := by
      rw [hk, heq, hk']
    have h1 := hP hAB
    exact Set.disjoint_left.mp ((H.event i).transition.trace.capping.cap_disjoint hb1)
      ⟨k, rfl⟩ ⟨k', h1.symm⟩

/-- **G3（PROVED）`hdisj`**：A2 G6 / G2 consumer 的 `hdisj` binder 在 `S = G.static` 处逐字成立。 -/
theorem hdisj_C11SP : ∀ b b' : (H.event i).RetainedBoundaryIndex, b ≠ b' →
    ∀ y z : standardCapWindow parameters.modelRadius,
      ‖z.val‖ ≤ StandardCap.transitionEnd + 10 → (G.static b).window y ≠ (G.static b').window z :=
  fun _ _ hbb y z _ => G.static_window_ne_C11SP hbb y z

end GeometricCutoffRecord

namespace ObservedHistory

/-- **G3 consumer（PROVED，0 合同 binder）**：record 情形的 (D4′) buffer no-shortcut 乘性形。
前提只剩结构性的：record `G`、`hcan`（canonical window）、参数界 `hε`、`hD`、crossing / 端点分类、`δ`。
结论 = G2 consumer 在 `S = G.static`、`Dc = modelRadius` 处的实例（`C_buf = max (1 + 4·(22/c)) Cs`）。 -/
theorem surgery_no_shortcut_buffer_of_record_C11SP (H : ObservedHistory.{u})
    (e : Fin H.eventCount) {params : CutoffParameters} (G : GeometricCutoffRecord H e params)
    (hcan : ∀ b, (G.static b).hasCanonicalWindow) (hε : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    {pm qm : (H.stage e.castSucc).Carrier} {pp qp : (H.stage e.succ).Carrier}
    (hp : (H.event e).RegularCrossing pm pp) (hq : (H.event e).RegularCrossing qm qp)
    (hpb : (∀ b, pp ∉ (G.static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (G.static b₀).window x = pp)
    (hqb : (∀ b, qp ∉ (G.static b).window ''
        {y : standardCapWindow params.modelRadius | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (G.static b₀).window x = qp)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] H.time e.succ,
      riemannianEDistOf (H.stageMetric e.castSucc t) pm qm ≤
        ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
            (StandardCap.transitionEnd + 11) ^ 2)))
          (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))) *
          riemannianEDistOf (H.stageMetric e.succ (H.time e.succ)) pp qp + ENNReal.ofReal δ :=
  surgery_no_shortcut_buffer_of_disj_C11SP H e G.static G.old_eq_retained hcan hε hD
    G.hdisj_C11SP hp hq hpb hqb hδ

end ObservedHistory

/-- NATIVE-CC 的 `hdisj` 槽（`pairEDist_window_of_largeCap_count_C11SP`，records 族形）由 G3 直接填。 -/
example {H : ObservedHistory.{u}} {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params) :
    ∀ (e : Fin H.eventCount) (b b' : (H.event e).RetainedBoundaryIndex), b ≠ b' →
      ∀ y z : standardCapWindow params.modelRadius,
        ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records e).static b).window y ≠ ((records e).static b').window z :=
  fun e => (records e).hdisj_C11SP

/-- records 族的 `hshort′`（G1 history 形，records 实例）由 G1 + G3 直接填，无 binder。 -/
example {H : ObservedHistory.{u}} {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hε : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius) (e : Fin H.eventCount) :=
  ObservedHistory.hshort_of_collar_history_C11SP H e (records e).static
    (records e).old_eq_retained (hcan e) hε hD (records e).hdisj_C11SP

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
