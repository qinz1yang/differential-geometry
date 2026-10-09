import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryNeckSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapPersistence

/-!
# R3（G3′，第 1 部分）：event 的切割系统把 pre-surgery slice 分成存活侧与其余（S-A14-SURGERY-2）

对 event `i`（`E := H.event i`，`X := (H.stage i.castSucc).Carrier`）与 retained boundary `b`，
`static b` 的 neck 坐标 `z_s`（`z_s = 0` 是切割球面，`z_s ≥ 0` 是 unchanged 侧）给出 slab

  `neckSlab_SG2 R b S := {x | ∃ y : neckBuffer δ_b, y.1.2 ∈ S ∧ (chart y).1 = x}`。

`Σ_b := neckSlab R b {50}`、`N_b := neckSlab R b (Icc 0 50)`。本文件用**整个切割系统**（所有
retained boundary 同时、实际的 `retainedCore` piece 标记，不假定单个球面分离）证明：

* **T1**（`retained_frontier_SG2`）：`retainedCore` 在 `X` 里的边界点都落在某个 retained boundary 球面
  `{z_s = 0}`；
* **`exists_event_separation_SG2`**：存在紧集 `K ⊆ {RegularCrossing 源点}` 与开集 `U ⊆ interior K`、
  开集 `V`，`U ∩ V = ∅`，`X ∖ ⋃_b Σ_b ⊆ U ∪ V`；且 `RegularCrossing` 源点只要不落在任何 `N_b` 里就在 `U` 里
  （`γ_s ⊆ U` 的判据：几何输入只剩 "`γ_s` 不碰 `N_b`"）。

抽象部分 `exists_slab_separation_SG2` 是纯拓扑引理（闭集 `Rt`、有限族 slab）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Abstract

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]

/-- **抽象分离**：`Rt` 闭；`A b` 闭、`O b` 开、`A b ⊆ O b ∪ S b`；`Rt ∩ O b ⊆ A b`；`Rt` 的边界点落在某个
`A b ∩ O b`。则 `U := Rt ∖ ⋃ A` 开、`U ⊆ interior (Rt ∖ ⋃ O)`、`Rt ∖ ⋃ O` 闭且 `⊆ interior Rt`、
`closure U ⊆ U ∪ ⋃ S`。 -/
theorem exists_slab_separation_SG2 {Rt : Set X} (hRt : IsClosed Rt) {A O S : ι → Set X}
    (hA : ∀ b, IsClosed (A b)) (hO : ∀ b, IsOpen (O b)) (hAO : ∀ b, A b ⊆ O b ∪ S b)
    (hRO : ∀ b, Rt ∩ O b ⊆ A b) (hfr : ∀ x ∈ Rt, x ∉ interior Rt → ∃ b, x ∈ A b ∩ O b) :
    IsOpen (Rt \ ⋃ b, A b) ∧ IsClosed (Rt \ ⋃ b, O b) ∧ Rt \ ⋃ b, O b ⊆ interior Rt ∧
      Rt \ ⋃ b, A b ⊆ interior (Rt \ ⋃ b, O b) ∧
      closure (Rt \ ⋃ b, A b) ⊆ (Rt \ ⋃ b, A b) ∪ ⋃ b, S b := by
  have hUint : Rt \ ⋃ b, A b ⊆ interior Rt := by
    rintro x ⟨hxR, hxA⟩
    by_contra hx
    obtain ⟨b, hb⟩ := hfr x hxR hx
    exact hxA (mem_iUnion.2 ⟨b, hb.1⟩)
  have hUopen : IsOpen (Rt \ ⋃ b, A b) := by
    have : Rt \ ⋃ b, A b = interior Rt \ ⋃ b, A b := by
      ext x
      exact ⟨fun h => ⟨hUint h, h.2⟩, fun h => ⟨interior_subset h.1, h.2⟩⟩
    rw [this]
    exact isOpen_interior.sdiff (isClosed_iUnion_of_finite hA)
  have hKclosed : IsClosed (Rt \ ⋃ b, O b) := hRt.sdiff (isOpen_iUnion hO)
  have hKint : Rt \ ⋃ b, O b ⊆ interior Rt := by
    rintro x ⟨hxR, hxO⟩
    by_contra hx
    obtain ⟨b, hb⟩ := hfr x hxR hx
    exact hxO (mem_iUnion.2 ⟨b, hb.2⟩)
  have hUK : Rt \ ⋃ b, A b ⊆ Rt \ ⋃ b, O b := by
    rintro u ⟨huR, huA⟩
    refine ⟨huR, fun huO => ?_⟩
    obtain ⟨b, hb⟩ := mem_iUnion.1 huO
    exact huA (mem_iUnion.2 ⟨b, hRO b ⟨huR, hb⟩⟩)
  refine ⟨hUopen, hKclosed, hKint, interior_maximal hUK hUopen, ?_⟩
  intro x hx
  have hxR : x ∈ Rt := closure_minimal (fun u hu => hu.1) hRt hx
  by_cases hxU : x ∈ Rt \ ⋃ b, A b
  · exact Or.inl hxU
  · right
    obtain ⟨b, hxA⟩ := mem_iUnion.1 (by_contra fun h => hxU ⟨hxR, h⟩ : x ∈ ⋃ b, A b)
    by_cases hxS : x ∈ S b
    · exact mem_iUnion.2 ⟨b, hxS⟩
    · have hxO : x ∈ O b := (hAO b hxA).resolve_right hxS
      obtain ⟨u, huO, huU⟩ := mem_closure_iff.1 hx (O b) (hO b) hxO
      exact absurd (mem_iUnion.2 ⟨b, hRO b ⟨huU.1, huO⟩⟩) huU.2

end Abstract

section Event

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- retained boundary `b` 的 static neck 坐标 `z_s ∈ S` 的点集（`X = (H.stage i.castSucc).Carrier`）。 -/
def neckSlab_SG2 (R : GeometricCutoffRecord H i p) (b : (H.event i).RetainedBoundaryIndex)
    (S : Set ℝ) : Set (H.stage i.castSucc).Carrier :=
  {x | ∃ y : neckBuffer (R.static b).delta, y.1.2 ∈ S ∧ ((R.static b).neck.chart y).1 = x}

theorem isOpen_neckSlab_SG2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {S : Set ℝ} (hS : IsOpen S) :
    IsOpen (neckSlab_SG2 R b S) := by
  have h1 : IsOpen {y : neckBuffer (R.static b).delta | y.1.2 ∈ S} :=
    hS.preimage (continuous_snd.comp continuous_subtype_val)
  have h2 : neckSlab_SG2 R b S =
      Subtype.val '' ((R.static b).neck.chart '' {y | y.1.2 ∈ S}) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h2]
  exact (H.event i).incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _
    ((neck_chart_isOpenEmbedding_SG (R.static b).neck).isOpenMap _ h1)

theorem isCompact_neckSlab_SG2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {S : Set ℝ} (hS : IsCompact S)
    (hSb : S ⊆ Ioo (-((R.static b).delta)⁻¹ - 1) (((R.static b).delta)⁻¹ + 1)) :
    IsCompact (neckSlab_SG2 R b S) := by
  have himg : Subtype.val '' {y : neckBuffer (R.static b).delta | y.1.2 ∈ S} =
      (univ : Set (Sphere 2)) ×ˢ S := by
    ext ⟨v, z⟩
    constructor
    · rintro ⟨y, hy, hyv⟩
      rw [← hyv]
      exact ⟨mem_univ _, hy⟩
    · rintro ⟨-, hz⟩
      exact ⟨⟨(v, z), (hSb hz).1, (hSb hz).2⟩, hz, rfl⟩
  have hc : IsCompact {y : neckBuffer (R.static b).delta | y.1.2 ∈ S} := by
    refine Topology.IsInducing.subtypeVal.isCompact_iff.2 ?_
    exact himg ▸ isCompact_univ.prod hS
  have h2 : neckSlab_SG2 R b S =
      (fun y => ((R.static b).neck.chart y).1) '' {y | y.1.2 ∈ S} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h2]
  exact hc.image (continuous_subtype_val.comp (R.static b).neck.chart.continuous)

/-- 切割球面 `z_s = 0` 之下（removed band `-2 < z_s < 0`）的点不在 `core` 里。 -/
theorem neckSlab_below_not_mem_core_SG2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {x : (H.stage i.castSucc).Carrier}
    (hx : x ∈ neckSlab_SG2 R b (Ioo (-2) 0)) :
    x ∉ (H.event i).transition.trace.tubes.core := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hbuf := R.recenter_in_buffer b y
  have hchart := R.recenter_chart b y hbuf
  have hlevel : -1 < (if b.1.2 then (1 : ℝ) else -1) * (1 + y.1.2) ∧
      (if b.1.2 then (1 : ℝ) else -1) * (1 + y.1.2) < 1 := by
    split_ifs <;> constructor <;> linarith [hy.1, hy.2]
  have hIcc : (if b.1.2 then (1 : ℝ) else -1) * (1 + y.1.2) ∈ Icc (-2 : ℝ) 2 :=
    ⟨by linarith [hlevel.1], by linarith [hlevel.2]⟩
  intro hcore
  refine hcore (mem_iUnion.2 ⟨b.1.1, (y.1.1, ⟨_, hIcc⟩), hlevel, ?_⟩)
  rw [hchart]
  exact R.tube_eq b.1.1 (y.1.1, ⟨_, hIcc⟩) hbuf

/-- `Σ_b = {z_s = 50}` 在原 neck `neck b.1.1` 的坐标里是 `z = ±51`（`recenter_chart`；符号 = `b.1.2`）。
S-W-NECK 的 band `{|z ∓ 51| < 20}` 就是围绕它的 band。 -/
theorem neckSlab_fifty_eq_orig_SG2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hcol : 50 < ((R.static b).delta)⁻¹) :
    neckSlab_SG2 R b {50} = {x | ∃ y' : neckBuffer (R.delta b.1.1),
      y'.1.2 = (if b.1.2 then (1 : ℝ) else -1) * 51 ∧ ((R.neck b.1.1).chart y').1 = x} := by
  have key : ∀ (w w' : neckBuffer (R.delta b.1.1)), w.1 = w'.1 →
      ((R.neck b.1.1).chart w).1 = ((R.neck b.1.1).chart w').1 := fun w w' h => by
    rw [Subtype.ext h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hbuf := R.recenter_in_buffer b y
    refine ⟨⟨_, hbuf⟩, ?_, ?_⟩
    · have h50 : y.1.2 = 50 := hy
      change (if b.1.2 then (1 : ℝ) else -1) * (1 + y.1.2) = _
      rw [h50]
      norm_num
    · rw [R.recenter_chart b y hbuf]
  · rintro ⟨y', hy', rfl⟩
    have hδ : 0 < (R.static b).delta := (R.static b).neck.delta_pos
    have hmem : ((y'.1.1, (50 : ℝ)) : NeckCylinder) ∈ neckBuffer (R.static b).delta := by
      have := inv_pos.mpr hδ
      constructor <;> simp only <;> linarith
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    rw [R.recenter_chart b ⟨_, hmem⟩ (R.recenter_in_buffer b ⟨_, hmem⟩)]
    refine key _ _ (Prod.ext rfl ?_)
    change (if b.1.2 then (1 : ℝ) else -1) * (1 + 50) = y'.1.2
    rw [hy']
    ring

/-- **T1**：`val '' old = val '' retainedCore` 在 `X` 里的边界点都落在某个 retained boundary 的
切割球面 `{z_s = 0}`（整个切割系统；`retainedCore` 是 `core` 的 clopen piece 并）。 -/
theorem retained_frontier_SG2 (R : GeometricCutoffRecord H i p)
    {x : (H.stage i.castSucc).Carrier} (hx : x ∈ Subtype.val '' (H.event i).old)
    (hnot : x ∉ interior (Subtype.val '' (H.event i).old)) :
    ∃ b : (H.event i).RetainedBoundaryIndex, x ∈ neckSlab_SG2 R b {0} := by
  classical
  have : CompactSpace (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.core_compact
  have hold : ∀ q : (H.event i).transition.trace.tubes.core,
      q ∈ (H.event i).old ↔ q ∈ (H.event i).transition.trace.retainedCore := fun q => by
    rw [R.old_eq_retained]
  obtain ⟨q₀, hq₀, rfl⟩ := hx
  by_cases hcb : ∃ a, (q₀ : (H.stage i.castSucc).Carrier) ∈
      (H.event i).transition.trace.tubes.tube a ''
        {z : TubeDomain | -1 ≤ z.2.1 ∧ z.2.1 ≤ 1}
  · obtain ⟨a, z, ⟨hz1, hz2⟩, hzq⟩ := hcb
    have hq0core : (q₀ : (H.stage i.castSucc).Carrier) ∈
        (H.event i).transition.trace.tubes.core := q₀.2
    have hlev : z.2.1 = 1 ∨ z.2.1 = -1 := by
      by_contra hne
      push Not at hne
      exact hq0core (mem_iUnion.2 ⟨a, z, ⟨lt_of_le_of_ne hz1 (Ne.symm hne.2),
        lt_of_le_of_ne hz2 hne.1⟩, hzq⟩)
    obtain ⟨side, hside⟩ : ∃ side : Bool, z.2 = TubeSystem.boundaryLevel side := by
      rcases hlev with h | h
      · exact ⟨true, Subtype.ext (by simp [TubeSystem.boundaryLevel, h])⟩
      · exact ⟨false, Subtype.ext (by simp [TubeSystem.boundaryLevel, h])⟩
    have hz2' : z.2.1 = if side then (1 : ℝ) else -1 := by
      have := congrArg Subtype.val hside
      cases side <;> simpa [TubeSystem.boundaryLevel] using this
    have hsph : (H.event i).transition.trace.tubes.coreBoundarySphere (a, side) z.1 = q₀ := by
      apply Subtype.ext
      change (H.event i).transition.trace.tubes.tube a (z.1, TubeSystem.boundaryLevel side) = _
      rw [← hside]
      exact hzq
    have hret : (H.event i).RetainedBoundary (a, side) := by
      have h0 : (H.event i).transition.trace.tubes.coreBoundarySphere (a, side) z.1 ∈
          (H.event i).transition.trace.retainedCore := by
        rw [hsph]
        exact (hold _).1 hq₀
      intro y'
      exact CutCapTopology.capRetained_coreBoundarySphere_mem_retainedCore _ (a, side)
        (CutCapTopology.capRetained_of_coreBoundarySphere_mem_retainedCore _ (a, side) z.1 h0) y'
    have hδ : 0 < (R.static ⟨(a, side), hret⟩).delta :=
      (R.static ⟨(a, side), hret⟩).neck.delta_pos
    have hmem : ((z.1, (0 : ℝ)) : NeckCylinder) ∈
        neckBuffer (R.static ⟨(a, side), hret⟩).delta := by
      have := inv_pos.mpr hδ
      constructor <;> simp only <;> linarith
    refine ⟨⟨(a, side), hret⟩, ⟨(z.1, 0), hmem⟩, rfl, ?_⟩
    have hbuf := R.recenter_in_buffer ⟨(a, side), hret⟩ ⟨(z.1, 0), hmem⟩
    have hchart := R.recenter_chart ⟨(a, side), hret⟩ ⟨(z.1, 0), hmem⟩ hbuf
    have hE := R.tube_eq a z (R.tube_in_buffer a z)
    have key : ∀ (w w' : neckBuffer (R.delta a)), w.1 = w'.1 →
        ((R.neck a).chart w).1 = ((R.neck a).chart w').1 := fun w w' h => by
      rw [Subtype.ext h]
    rw [hchart, ← hzq, hE]
    refine key _ _ ?_
    ext
    · rfl
    · simp [hz2']
  · exfalso
    apply hnot
    have hclosedBand : ∀ a, IsClosed ((H.event i).transition.trace.tubes.tube a ''
        {z : TubeDomain | -1 ≤ z.2.1 ∧ z.2.1 ≤ 1}) := by
      intro a
      have hc : IsCompact {z : TubeDomain | -1 ≤ z.2.1 ∧ z.2.1 ≤ 1} :=
        ((isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).inter
          (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const)).isCompact
      exact (hc.image ((H.event i).transition.trace.tubes.tube a).continuous).isClosed
    have hWopen : IsOpen (⋃ a, (H.event i).transition.trace.tubes.tube a ''
        {z : TubeDomain | -1 ≤ z.2.1 ∧ z.2.1 ≤ 1})ᶜ :=
      (isClosed_iUnion_of_finite hclosedBand).isOpen_compl
    have hretOpen : IsOpen (H.event i).transition.trace.retainedCore := by
      have : (H.event i).transition.trace.retainedCore =
          (fun q : (H.event i).transition.trace.tubes.core =>
            (H.event i).transition.trace.presentation
              ((H.event i).transition.trace.capping.coreInclusion q)) ⁻¹' range Sum.inl :=
        Set.ext fun q => ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
      rw [this]
      exact isClopen_range_inl.isOpen.preimage
        ((H.event i).transition.trace.presentation.continuous.comp
          (H.event i).transition.trace.capping.coreInclusion.continuous)
    have hZclosed : IsClosed (Subtype.val ''
        {q : (H.event i).transition.trace.tubes.core |
          q ∉ (H.event i).transition.trace.retainedCore}) :=
      ((hretOpen.isClosed_compl.isCompact).image continuous_subtype_val).isClosed
    have hxW : (q₀ : (H.stage i.castSucc).Carrier) ∈
        (⋃ a, (H.event i).transition.trace.tubes.tube a ''
          {z : TubeDomain | -1 ≤ z.2.1 ∧ z.2.1 ≤ 1})ᶜ := fun h => hcb (mem_iUnion.1 h)
    have hxZ : (q₀ : (H.stage i.castSucc).Carrier) ∉ Subtype.val ''
        {q : (H.event i).transition.trace.tubes.core |
          q ∉ (H.event i).transition.trace.retainedCore} := by
      rintro ⟨q, hq, hqq⟩
      have : q = q₀ := Subtype.ext hqq
      subst this
      exact hq ((hold _).1 hq₀)
    refine interior_maximal ?_ (hWopen.sdiff hZclosed) ⟨hxW, hxZ⟩
    rintro w ⟨hwW, hwZ⟩
    have hwcore : w ∈ (H.event i).transition.trace.tubes.core := by
      intro hw
      obtain ⟨a, z, ⟨h1, h2⟩, hzw⟩ := mem_iUnion.1 hw
      exact hwW (mem_iUnion.2 ⟨a, z, ⟨h1.le, h2.le⟩, hzw⟩)
    refine ⟨⟨w, hwcore⟩, ?_, rfl⟩
    exact (hold ⟨w, hwcore⟩).2 (by_contra fun hq => hwZ ⟨_, hq, rfl⟩)

/-- `interior (val '' old)` 的点是 `RegularCrossing` 的源点（`R.retained_terminal` 给出 `terminalRegularOpen`
成员资格）。 -/
theorem regularCrossing_of_mem_interior_SG2 (R : GeometricCutoffRecord H i p)
    {x : (H.stage i.castSucc).Carrier}
    (hx : x ∈ interior (Subtype.val '' (H.event i).old)) :
    ∃ q, (H.event i).RegularCrossing x q := by
  obtain ⟨q, hq, rfl⟩ := interior_subset hx
  have hq' : q ∈ (H.event i).transition.trace.retainedCore := R.old_eq_retained ▸ hq
  obtain ⟨w, -, -, hcross⟩ := (H.event i).exists_oldTerminal_eq_of_mem_interior_old
    ⟨q.1, R.retained_terminal q hq'⟩ hx
  exact ⟨_, hcross⟩

/-- `RegularCrossing` 的源点在 `val '' old` 里。 -/
theorem mem_image_old_of_regularCrossing_SG2 {x : (H.stage i.castSucc).Carrier}
    {q : (H.stage i.succ).Carrier} (hq : (H.event i).RegularCrossing x q) :
    x ∈ Subtype.val '' (H.event i).old := by
  obtain ⟨w, -, hw, -⟩ := hq
  exact ⟨w.1, w.2, hw⟩

/-- **R3（event 层）**：晚期 event（所有 retained boundary 的 `δ_s⁻¹ > 100`）。存在紧集 `K`（其点都是
`RegularCrossing` 的源点）、开集 `U ⊆ interior K`、开集 `V`，`U ∩ V = ∅`，
`X ∖ ⋃_b Σ_b ⊆ U ∪ V`（`Σ_b = {z_s = 50}`）；并且 `RegularCrossing` 源点只要不落在任何
`N_b = {0 ≤ z_s ≤ 50}` 里就在 `U` 里（`γ_s ⊆ U` 的判据）。 -/
theorem exists_event_separation_SG2 (R : GeometricCutoffRecord H i p)
    (hcol : ∀ b : (H.event i).RetainedBoundaryIndex, 100 < ((R.static b).delta)⁻¹) :
    ∃ K U V : Set (H.stage i.castSucc).Carrier,
      IsCompact K ∧ (∀ x ∈ K, ∃ q, (H.event i).RegularCrossing x q) ∧
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ⊆ interior K ∧
      (∀ x, (∀ b, x ∉ neckSlab_SG2 R b {50}) → x ∈ U ∪ V) ∧
      (∀ x, (∃ q, (H.event i).RegularCrossing x q) →
        (∀ b, x ∉ neckSlab_SG2 R b (Icc 0 50)) → x ∈ U) := by
  classical
  have hRtc : IsCompact (Subtype.val '' (H.event i).old) :=
    (H.event i).old_compact.image continuous_subtype_val
  have hbuf : ∀ (b : (H.event i).RetainedBoundaryIndex) (S : Set ℝ), S ⊆ Icc (-2) 50 →
      S ⊆ Ioo (-((R.static b).delta)⁻¹ - 1) (((R.static b).delta)⁻¹ + 1) :=
    fun b S hS z hz => by
      have h1 := hcol b
      have h2 := hS hz
      constructor <;> linarith [h2.1, h2.2]
  obtain ⟨hUo, hKc, hKint, hUK, hcl⟩ := exists_slab_separation_SG2
    (ι := (H.event i).RetainedBoundaryIndex) hRtc.isClosed
    (A := fun b => neckSlab_SG2 R b (Icc 0 50)) (O := fun b => neckSlab_SG2 R b (Ioo (-2) 50))
    (S := fun b => neckSlab_SG2 R b {50})
    (fun b => (isCompact_neckSlab_SG2 R b isCompact_Icc
      (hbuf b _ fun z hz => ⟨by linarith [hz.1], hz.2⟩)).isClosed)
    (fun b => isOpen_neckSlab_SG2 R b isOpen_Ioo)
    (fun b x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hy.2.lt_or_eq with h | h
      · exact Or.inl ⟨y, ⟨by linarith [hy.1], h⟩, rfl⟩
      · exact Or.inr ⟨y, h, rfl⟩)
    (fun b x hx => by
      obtain ⟨hxR, y, hy, rfl⟩ := hx
      by_cases h0 : 0 ≤ y.1.2
      · exact ⟨y, ⟨h0, hy.2.le⟩, rfl⟩
      · exfalso
        obtain ⟨q, -, hq⟩ := hxR
        have hcore : ((R.static b).neck.chart y).1 ∈
            (H.event i).transition.trace.tubes.core := hq ▸ q.2
        exact neckSlab_below_not_mem_core_SG2 R b ⟨y, ⟨hy.1, lt_of_not_ge h0⟩, rfl⟩ hcore)
    (fun x hx hnot => by
      obtain ⟨b, hb⟩ := retained_frontier_SG2 R hx hnot
      obtain ⟨y, hy, hyx⟩ := hb
      have hy0 : y.1.2 = 0 := hy
      exact ⟨b, ⟨y, ⟨hy0.ge, by linarith⟩, hyx⟩, ⟨y, ⟨by linarith, by linarith⟩, hyx⟩⟩)
  refine ⟨Subtype.val '' (H.event i).old \ ⋃ b, neckSlab_SG2 R b (Ioo (-2) 50),
    Subtype.val '' (H.event i).old \ ⋃ b, neckSlab_SG2 R b (Icc 0 50),
    (closure (Subtype.val '' (H.event i).old \ ⋃ b, neckSlab_SG2 R b (Icc 0 50)))ᶜ,
    hRtc.of_isClosed_subset hKc sdiff_subset, ?_, hUo, isClosed_closure.isOpen_compl,
    disjoint_left.2 fun x hxU hxV => hxV (subset_closure hxU), hUK, ?_, ?_⟩
  · exact fun x hx => regularCrossing_of_mem_interior_SG2 R (hKint hx)
  · intro x hx
    by_cases hxc : x ∈ closure (Subtype.val '' (H.event i).old \
        ⋃ b, neckSlab_SG2 R b (Icc 0 50))
    · left
      rcases hcl hxc with h | h
      · exact h
      · obtain ⟨b, hb⟩ := mem_iUnion.1 h
        exact absurd hb (hx b)
    · exact Or.inr hxc
  · intro x ⟨q, hq⟩ hnot
    exact ⟨mem_image_old_of_regularCrossing_SG2 hq, fun h => by
      obtain ⟨b, hb⟩ := mem_iUnion.1 h
      exact hnot b hb⟩

end Event

end GC.LongTime.CuspP1
