import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.A12FullConsumerC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore

set_option autoImplicit false

/-!
# O-C12X-RFCA (T2)：RFC-a 是每个 cutoff record 的定理（后缀 `_C12X`）

RFC-a（`[FROZEN] CH12-S105`，record 子句 `FrontierCollarClause_C11E R`）：event 旧输出
`range (H.event i).oldOutput` 的 frontier 落在某个 retained boundary 的 retained collar
（`z' ≤ 1`）里。这里对**任意** `R : GeometricCutoffRecord H i pp` 证明它，不用 linked window、
accuracy、radius、order 任何前提：

* `oldOutput` 的值域紧（`old_compact`），故闭，frontier 点 `y = oldOutput x`；
* 若 `x` 不在任何 tube 的像里：`Capping.exhaustive` + `core_cap_intersection` + core 紧（
  `SmoothCutCapTransition.core_compact`）给出 `N` 中开集 `(⋃ cap 像 ∪ coreInclusion '' (tube 像))ᶜ`，
  经 `presentation`（同胚）与 `old_contains_outside` 得 `y ∈ interior (range oldOutput)`，矛盾；
* 若 `x = tube α (u, z)`：core 条件给 `|z| ≥ 1`；取 `s := (z ≥ 1)`、`t := |z| - 1 ∈ [0, 1]`。
  strip `tube α (S² × ±[1, 2])` 连通、`retainedCore` 在 core 里既开又闭
  （`CutCapTopology.isClopen_retainedCore`）⇒ boundary `(α, s)` retained；
  `c := (u, t)` 在 `neckRetainedCollar (R.static b).delta` 里（static neck 的 `delta < 1`），
  `retained_point_eq` + `recenter_chart` + `tube_eq` 给 `retainedPoint c = x`，
  `retained_eq` + `oldOutput_eq` + `Sum.inl` 单射给 `inclusion (retained c) = y`。

推论：`FrontierCollarSupplyFull_C11F F q`（ch12 终端 `hRFCa` binder 的 ch11 版）、弱形
`FrontierCollarSupply_C11E F q` 对所有 `F q` 无条件成立；A12′ v2 ⇔ PROF 形 A12′
（`a12EnhancedFull_iff_C12X`：MERGE U1 的"全称形加强"不加内容）；链级 consumer 的 `hext`
少掉 S19（`a12EnhancedFull_of_chain_noRFCa_C12X`，余 7 项）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter TopologicalSpace
open scoped Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## event 级：不在 tube 里的旧点映到 `range oldOutput` 的内部 -/

/-- tube 坐标 `|z| ≥ 1` 的点在 core 里（`boundarySphere_mem_core` 的推广）。 -/
private theorem rfca_tube_mem_core {M : Type*} [TopologicalSpace M] (T : TubeSystem M)
    (α : T.Index) (w : TubeDomain) (hw : 1 ≤ |(w.2 : ℝ)|) : T.tube α w ∈ T.core := by
  intro hm
  obtain ⟨a, z, hz, heq⟩ := by
    simpa only [mem_iUnion, TubeSystem.removedBand, mem_image] using hm
  have ha : a = α := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne) (Set.mem_range_self z) ⟨w, heq.symm⟩
  subst ha
  have hcoord : (z.2 : ℝ) = w.2 := congrArg (fun z : TubeDomain => (z.2 : ℝ))
    ((T.embedding a).injective heq)
  rw [← hcoord] at hw
  exact absurd hw (not_le.mpr (abs_lt.mpr hz))

/-- 不在任何 tube 像里的旧点：`oldOutput x` 是 `range oldOutput` 的内点。 -/
private theorem rfca_mem_interior {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (x : E.old)
    (hx : ∀ α w, E.transition.trace.tubes.tube α w ≠ x.1.1) :
    E.oldOutput x ∈ interior (range E.oldOutput) := by
  have : CompactSpace E.transition.trace.tubes.core := E.transition.core_compact
  have : CompactSpace ThreeBall := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : Set E.transition.trace.tubes.core :=
    Subtype.val ⁻¹' ⋃ α, range (E.transition.trace.tubes.tube α)
  have hK : IsClosed K := by
    refine IsClosed.preimage continuous_subtype_val (isClosed_iUnion_of_finite fun α => ?_)
    exact (isCompact_range (E.transition.trace.tubes.tube α).continuous).isClosed
  let C : Set E.capped.Carrier := (⋃ b, range (E.transition.trace.capping.cap b)) ∪
    E.transition.trace.capping.coreInclusion '' K
  have hC : IsClosed C := by
    refine IsClosed.union (isClosed_iUnion_of_finite fun b => ?_) ?_
    · exact (isCompact_range (E.transition.trace.capping.cap b).continuous).isClosed
    · exact (hK.isCompact.image E.transition.trace.capping.coreInclusion.continuous).isClosed
  have hxC : E.transition.trace.capping.coreInclusion x.1 ∉ C := by
    rintro (hcap | ⟨z, hzK, hz⟩)
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hcap
      have hmem : E.transition.trace.capping.coreInclusion x.1 ∈
          range E.transition.trace.capping.coreInclusion ∩
            range (E.transition.trace.capping.cap b) := ⟨mem_range_self _, hb⟩
      rw [E.transition.trace.capping.core_cap_intersection b] at hmem
      obtain ⟨y, hy⟩ := hmem
      have hy' : E.transition.trace.capping.coreInclusion
          (E.transition.trace.tubes.coreBoundarySphere b y) =
            E.transition.trace.capping.coreInclusion x.1 := hy
      exact hx b.1 _ (congrArg Subtype.val
        (E.transition.trace.capping.coreEmbedding.injective hy'))
    · have hzx : z = x.1 := E.transition.trace.capping.coreEmbedding.injective hz
      rw [hzx] at hzK
      obtain ⟨α, w, hw⟩ := mem_iUnion.mp hzK
      exact hx α w hw
  have hV : IsOpen (Sum.inl ⁻¹' (E.transition.trace.presentation '' Cᶜ) : Set Q.Carrier) :=
    (E.transition.trace.presentation.isOpenMap _ hC.isOpen_compl).preimage continuous_inl
  refine mem_interior.mpr ⟨_, ?_, hV, ⟨_, hxC, E.oldOutput_eq x⟩⟩
  rintro q ⟨n, hn, hnq⟩
  have hn' : n ∈ range E.transition.trace.capping.coreInclusion := by
    have hu : n ∈ range E.transition.trace.capping.coreInclusion ∪
        ⋃ b, range (E.transition.trace.capping.cap b) := by
      rw [E.transition.trace.capping.exhaustive]
      exact mem_univ n
    rcases hu with h | h
    · exact h
    · exact absurd (Or.inl h) hn
  obtain ⟨z, rfl⟩ := hn'
  have hzK : z ∉ K := fun h => hn (Or.inr ⟨z, h, rfl⟩)
  have hold : z ∈ E.old := E.old_contains_outside z ⟨q, hnq⟩
    fun α hα => hzK (mem_iUnion.mpr ⟨α, image_subset_range _ _ hα⟩)
  refine ⟨⟨z, hold⟩, ?_⟩
  have h := E.oldOutput_eq ⟨z, hold⟩
  rw [hnq] at h
  exact (Sum.inl_injective h).symm

/-! ## record 级：tube 里的旧点在 retained collar 的 `z' ≤ 1` 部分 -/

section Record

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- side `s` 上 tube `α` 的点 `tube α (u, ±(1 + t))`（`t ∈ [0, 1]`）若是旧点 `x`，则 boundary
`(α, s)` retained，且 `oldOutput x` 是 static cap `(α, s)` 的 retained collar 点 `(u, t)`。 -/
private theorem rfca_side (R : GeometricCutoffRecord H i pp) (x : (H.event i).old)
    (α : (H.event i).transition.trace.tubes.Index) (s : Bool) (u : Sphere 2) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : (if s then (1 : ℝ) else -1) * (1 + t) ∈ Icc (-2 : ℝ) 2)
    (hw : (H.event i).transition.trace.tubes.tube α (u, ⟨_, hz⟩) = x.1.1) :
    ∃ (b : (H.event i).RetainedBoundaryIndex)
      (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 ∧
        (R.static b).inclusion ((R.static b).witness.retained c) = (H.event i).oldOutput x := by
  have hlev : ∀ r : Icc (0 : ℝ) 1, (if s then (1 : ℝ) else -1) * (1 + r) ∈ Icc (-2 : ℝ) 2 := by
    rintro ⟨r, hr0, hr1⟩
    cases s
    · change (-1 : ℝ) * (1 + r) ∈ Icc (-2 : ℝ) 2
      constructor <;> linarith
    · change (1 : ℝ) * (1 + r) ∈ Icc (-2 : ℝ) 2
      constructor <;> linarith
  have habs : ∀ r : Icc (0 : ℝ) 1, 1 ≤ |(if s then (1 : ℝ) else -1) * (1 + r)| := by
    rintro ⟨r, hr0, hr1⟩
    cases s
    · change 1 ≤ |(-1 : ℝ) * (1 + r)|
      rw [abs_of_nonpos (by linarith)]
      linarith
    · change 1 ≤ |(1 : ℝ) * (1 + r)|
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hret : (H.event i).RetainedBoundary (α, s) := by
    intro y
    let φ : Sphere 2 × Icc (0 : ℝ) 1 → (H.event i).transition.trace.tubes.core := fun p =>
      ⟨(H.event i).transition.trace.tubes.tube α (p.1, ⟨_, hlev p.2⟩),
        rfca_tube_mem_core _ α _ (habs p.2)⟩
    have hφ : Continuous φ := by
      refine continuous_induced_rng.2 (((H.event i).transition.trace.tubes.tube α).continuous.comp'
        (continuous_fst.prodMk (Continuous.subtype_mk ?_ _)))
      exact continuous_const.mul (continuous_const.add (continuous_subtype_val.comp continuous_snd))
    have : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
        (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
    have : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
    have hsub := (isPreconnected_range hφ).subset_isClopen
      (CutCapTopology.isClopen_retainedCore (H.event i).transition.trace)
      ⟨x.1, ⟨(u, ⟨t, ht0, ht1⟩), Subtype.ext hw⟩, (H.event i).old_retained x.2⟩
    have hy := hsub ⟨(y, ⟨0, le_rfl, zero_le_one⟩), rfl⟩
    have heq : (H.event i).transition.trace.tubes.coreBoundarySphere (α, s) y =
        φ (y, ⟨0, le_rfl, zero_le_one⟩) := by
      refine Subtype.ext (congrArg ((H.event i).transition.trace.tubes.tube α)
        (Prod.ext rfl (Subtype.ext ?_)))
      cases s <;> simp [TubeSystem.boundaryLevel]
    rw [heq]
    exact hy
  let b : (H.event i).RetainedBoundaryIndex := ⟨(α, s), hret⟩
  have hδ := (R.static b).neck.delta_pos
  have hinv : 1 < (R.static b).delta⁻¹ := (one_lt_inv₀ hδ).mpr (R.static b).neck.delta_lt_one
  let c : neckRetainedCollar (R.static b).delta := ⟨(u, t), ht0, by linarith⟩
  have hc : c.1 ∈ neckBuffer (R.static b).delta := by
    change -(R.static b).delta⁻¹ - 1 < t ∧ t < (R.static b).delta⁻¹ + 1
    constructor <;> linarith
  have hx2 : (c.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + c.1.2)) ∈
      neckBuffer (R.delta b.1.1) := R.tube_in_buffer α (u, ⟨_, hz⟩)
  have hpt : ((R.static b).retainedPoint c).1 = x.1 := by
    apply Subtype.ext
    rw [(R.static b).retained_point_eq c hc, R.recenter_chart b ⟨c.1, hc⟩ hx2]
    exact (R.tube_eq α (u, ⟨_, hz⟩) hx2).symm.trans hw
  refine ⟨b, c, ht1, ?_⟩
  have h1 := (R.static b).retained_eq c
  rw [hpt, (H.event i).oldOutput_eq x] at h1
  exact (Sum.inl_injective h1).symm

/-- **RFC-a 对每个 cutoff record 成立**（`[FROZEN] CH12-S105` 的 record 子句；无任何前提）。 -/
theorem frontierCollarClause_C12X (R : GeometricCutoffRecord H i pp) :
    FrontierCollarClause_C11E R := by
  intro y hy
  have : CompactSpace (H.event i).old := isCompact_iff_compactSpace.mp (H.event i).old_compact
  obtain ⟨x, rfl⟩ :=
    (isCompact_range (H.event i).oldOutput.continuous).isClosed.frontier_subset hy
  by_cases htube : ∃ (α : (H.event i).transition.trace.tubes.Index) (w : TubeDomain),
      (H.event i).transition.trace.tubes.tube α w = x.1.1
  · obtain ⟨α, ⟨u, z, hz⟩, hw⟩ := htube
    have hcore : ¬ ((-1 : ℝ) < z ∧ z < 1) := fun hlt =>
      x.1.2 (mem_iUnion.mpr ⟨α, (u, ⟨z, hz⟩), hlt, hw⟩)
    rcases le_or_gt 1 z with h1 | h1
    · have hz' : (if true then (1 : ℝ) else -1) * (1 + (z - 1)) ∈ Icc (-2 : ℝ) 2 := by
        change (1 : ℝ) * (1 + (z - 1)) ∈ Icc (-2 : ℝ) 2
        constructor <;> linarith [hz.1, hz.2]
      refine rfca_side R x α true u (z - 1) (by linarith) (by linarith [hz.2]) hz' ?_
      refine Eq.trans ?_ hw
      refine congrArg _ (Prod.ext rfl (Subtype.ext ?_))
      change (1 : ℝ) * (1 + (z - 1)) = z
      ring
    · have hz1 : z ≤ -1 := by
        by_contra h
        exact hcore ⟨by linarith, h1⟩
      have hz' : (if false then (1 : ℝ) else -1) * (1 + (-z - 1)) ∈ Icc (-2 : ℝ) 2 := by
        change (-1 : ℝ) * (1 + (-z - 1)) ∈ Icc (-2 : ℝ) 2
        constructor <;> linarith [hz.1, hz.2]
      refine rfca_side R x α false u (-z - 1) (by linarith) (by linarith [hz.1]) hz' ?_
      refine Eq.trans ?_ hw
      refine congrArg _ (Prod.ext rfl (Subtype.ext ?_))
      change (-1 : ℝ) * (1 + (-z - 1)) = z
      ring
  · exact absurd (rfca_mem_interior (H.event i) x fun α w h => htube ⟨α, w, h⟩) hy.2

end Record

/-! ## 供给：全称形 / 弱形 / profile 级 -/

/-- **S19′ 无条件**：ch12 `hRFCa` binder 的 ch11 版对所有 `F q` 成立。 -/
theorem frontierCollarSupplyFull_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) :
    FrontierCollarSupplyFull_C11F F q :=
  fun _ _ _ _ _ _ _ _ _ _ R _ => frontierCollarClause_C12X R

/-- **S19 无条件**（PROF 弱形）。 -/
theorem frontierCollarSupply_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) : FrontierCollarSupply_C11E F q :=
  frontierCollarSupply_of_full_C11F (frontierCollarSupplyFull_C12X F q)

/-- profile 级 RFC-a 全称形（任意 profile）。 -/
theorem rfcaFull_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    RFCaFull_C11F Hp :=
  frontierCollarSupplyFull_C12X F Hp.parameters

/-! ## A12′ v2 ⇔ PROF 形 -/

/-- PROF 形 enhanced admissibility ⇒ v2（RFC-a 全称形无条件）。 -/
theorem hasEnhancedAdmissibilityFull_of_enhanced_C12X {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (h : hasEnhancedAdmissibility_C11E F δ) : hasEnhancedAdmissibilityFull_C11F F δ :=
  let ⟨E⟩ := h
  ⟨E.toFull_C12X (rfcaFull_C12X _)⟩

/-- v2 admissibility ⇔ PROF 形。 -/
theorem hasEnhancedAdmissibilityFull_iff_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} :
    hasEnhancedAdmissibilityFull_C11F F δ ↔ hasEnhancedAdmissibility_C11E F δ :=
  ⟨hasEnhancedAdmissibility_of_full_C11F, hasEnhancedAdmissibilityFull_of_enhanced_C12X⟩

/-- **A12′ v2 ⇔ A12′（PROF 形）**：MERGE U1 的全称形字段不加内容。 -/
theorem a12EnhancedFull_iff_C12X {P : OrientedThreeStage.{u}} {g : P.Metric} :
    A12EnhancedFullConclusion_C11F P g ↔ A12EnhancedConclusion_C11E P g :=
  ⟨a12EnhancedConclusion_of_full_C11F, fun ⟨δ, F, ha, hd, hE⟩ =>
    ⟨δ, F, ha, hd, hasEnhancedAdmissibilityFull_of_enhanced_C12X hE⟩⟩

/-! ## 链级：`hext` 去掉 S19 -/

/-- **A12′ v2 从链（S19 已供）**：`a12EnhancedFull_of_chain_C12X` 的 `hext` 去掉末项
（RFC-a 全称形由 `frontierCollarSupplyFull_C12X` 给）；余 astra 不给的 7 项：
S8、S10、S11、S14、S15、S16、S17。 -/
theorem a12EnhancedFull_of_chain_noRFCa_C12X {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hext : ∃ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g,
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
        (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
        F.tower = S.tower ∧ ε = C.epsilon ∧
        (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
          q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
        CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
        AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
        HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
        (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
          (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
        Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
        LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) ∧
        LinkedWindowsSupply_C11E records ∧ TimeDerivativeSupply_C11E F q.neckRadius C.Ctime ∧
        LateLinkedRecordsSupply_C11E F q ∧ LargerBallCanonicalLateSupply_C11E F ε C1 C2 ∧
        StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 ∧
        CompatibleCapsSupply_C11E F q records) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19⟩ := hext
  exact a12EnhancedFull_of_chain_C12X hP3 hprof ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    frontierCollarSupplyFull_C12X F q⟩

end GC.LongTime.Ch11
