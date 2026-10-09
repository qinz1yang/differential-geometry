import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

/-!
# CX-HTUBE G1：`htube` 由 `GeometricCutoffRecord` 推不出——它在有切口的 event 上逐字为假（`_CXHB`）

CX-HTRANS 的 `htube` binder（event 形）：
`∀ p' q, RegularCrossing p' q → ∀ j, Disjoint (connectedComponent p') (range (tubes.tube j))`。
这里 `connectedComponent p'` 是 incoming stage 整个 carrier（切除之前的流形）里的拓扑分支。

本文件的结论（数学 + 形式化）：
* `exists_retainedSide_CXHB`：record 的 `one_retained_side` ⇒ 每个 tube 有一侧是 retained。
* `protected_component_meets_tube_CXHB`：record 的 `retained_meets_protected` +
  `protected_interior` ⇒ 每个 tube `α` 都与某个 protected 点 `x`（terminal regular open、在 core 里、
  `R ≤ r_prot⁻²`、在 retained 集的内部）的 `connectedComponent` 相交。
* `htube_forces_noCrossing_CXHB`：若 `htube` 成立，则上述 protected 点都不是 `RegularCrossing`。
* `cutTubeDisjoint_iff_noCut_CXHB`：在桥 `hPC`（protected 点是 regular crossing；数学上成立，因为
  protected 点在 retained 集内部、远离 tube 中段，从而在 `old` 的内部）之下，
  `htube ↔ IsEmpty tubes.Index`——即 `htube` 恰好等价于"该 event 没有切口"。

所以目标 `cutTubeDisjoint_of_record_CXHB` 的逐字形不可证（对任何真正切了 neck 的 event 为假），
状态 BLOCKED；repair target 见 DELIVERIES 块（branch-local 的 tube 不交性：只在 positive / round
whole-component 分支里用，由 witness 的 `radius_upper` / `scalar_bounds` 与 record 的 δ-neck 长度
（需 `pp.delta ≤ c/(C1·√C2)` 一类 smallness）推出）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- record 的 `one_retained_side`：每个 tube 恰有一侧 retained（这里只要存在）。 -/
theorem exists_retainedSide_CXHB (Rc : GeometricCutoffRecord H i pp)
    (α : (H.event i).transition.trace.tubes.Index) :
    ∃ b : Bool, (H.event i).RetainedBoundary (α, b) := by
  by_cases h : (H.event i).RetainedBoundary (α, true)
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    by_contra h'
    exact h ((Rc.one_retained_side α).mpr h')

/-- **每个 cut tube 都落在某个 protected retained 点的 `connectedComponent` 里（相交）**。 -/
theorem protected_component_meets_tube_CXHB (Rc : GeometricCutoffRecord H i pp)
    (α : (H.event i).transition.trace.tubes.Index) :
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      x.1 ∈ (H.event i).transition.trace.tubes.core ∧
      metricScalarAt (H.event i).terminal.metric x ≤
        ((pp.protectedRadius (H.time i.succ)) ^ 2)⁻¹ ∧
      x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore) ∧
      ¬ Disjoint (connectedComponent x.1)
        (Set.range ((H.event i).transition.trace.tubes.tube α)) := by
  obtain ⟨b, hb⟩ := Rc.exists_retainedSide_CXHB α
  obtain ⟨y⟩ : Nonempty (Sphere 2) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  let T := (H.event i).transition.trace.tubes
  obtain ⟨z, hzdef⟩ : ∃ z : T.core, z = T.coreBoundarySphere (α, b) y := ⟨_, rfl⟩
  have hz : z ∈ (H.event i).transition.trace.retainedCore := hzdef ▸ hb y
  obtain ⟨x, hx, hmk, hsc⟩ := Rc.retained_meets_protected (ConnectedComponents.mk z) ⟨z, rfl, hz⟩
  refine ⟨x, hx, hsc, Rc.protected_interior x hsc, ?_⟩
  have h1 : (⟨x.1, hx⟩ : T.core) ∈ connectedComponent z :=
    ConnectedComponents.coe_eq_coe'.mp hmk
  have h2 : x.1 ∈ connectedComponent z.1 :=
    continuous_subtype_val.image_connectedComponent_subset z ⟨_, h1, rfl⟩
  rw [← connectedComponent_eq h2]
  refine Set.not_disjoint_iff.mpr ⟨z.1, mem_connectedComponent, ?_⟩
  subst hzdef
  exact ⟨(y, TubeSystem.boundaryLevel b), rfl⟩

/-- **`htube` ⇒ protected 点都不是 regular crossing**（record 下 `htube` 的真实代价）。 -/
theorem htube_forces_noCrossing_CXHB (Rc : GeometricCutoffRecord H i pp)
    (htube : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
      (H.event i).RegularCrossing p' q → ∀ j,
      Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j)))
    (α : (H.event i).transition.trace.tubes.Index) :
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      x.1 ∈ (H.event i).transition.trace.tubes.core ∧
      metricScalarAt (H.event i).terminal.metric x ≤
        ((pp.protectedRadius (H.time i.succ)) ^ 2)⁻¹ ∧
      x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore) ∧
      ∀ q, ¬ (H.event i).RegularCrossing x.1 q := by
  obtain ⟨x, hx, hsc, hint, hmeet⟩ := Rc.protected_component_meets_tube_CXHB α
  exact ⟨x, hx, hsc, hint, fun q hc => hmeet (htube x.1 q hc α)⟩

/-- **`htube ↔ 无切口`**：在桥 `hPC`（protected 点是 regular crossing）之下，CX-HTRANS 的 `htube`
（event 形，逐字）恰好等价于 `IsEmpty tubes.Index`。 -/
theorem cutTubeDisjoint_iff_noCut_CXHB (Rc : GeometricCutoffRecord H i pp)
    (hPC : ∀ x : (H.event i).incoming.terminalRegularOpen,
      x.1 ∈ (H.event i).transition.trace.tubes.core →
      metricScalarAt (H.event i).terminal.metric x ≤
        ((pp.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
      x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore) →
      ∃ q, (H.event i).RegularCrossing x.1 q) :
    (∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
      (H.event i).RegularCrossing p' q → ∀ j,
      Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j))) ↔
      IsEmpty (H.event i).transition.trace.tubes.Index := by
  constructor
  · intro htube
    refine ⟨fun α => ?_⟩
    obtain ⟨x, hx, hsc, hint, hno⟩ := Rc.htube_forces_noCrossing_CXHB htube α
    obtain ⟨q, hq⟩ := hPC x hx hsc hint
    exact hno q hq
  · intro hE _ _ _ j
    exact (IsEmpty.false j).elim

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
