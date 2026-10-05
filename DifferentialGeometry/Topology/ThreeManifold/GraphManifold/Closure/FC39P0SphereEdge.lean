import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereEdgeBase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Regression
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertFields2

/-!
# FC39 producer, packet P0 (gate 1), §7.3: the S³ edge kind, components and link

Task-47 draft §7.3 / §7.9 row "edge base / component / end registry" for the S³ inhabitant
(disposition D10), on the edge bundle `sphereEdgeBundle` of `FC39P0SphereEdgeBase.lean`:

* the two actual components of `C₂ = [0, 1] ∪ [3, 4]` (`connectedComponentIn_edgeCbase`), their
  parametrizations `edgeInterval b t = t + shift b` (smooth embeddings of `[0, 1]`), the four
  endpoints `0, 1, 3, 4` in bijection with `Fin 2 × Bool`, no circle component;
* the whole products: the polar disk handles `cycleS3Handle false` (south cap) and
  `cycleS3Handle true` (north cap), each image the WHOLE inverse image of its component, every
  slice the whole disk and its rim the whole rim (`sphereEdgeModels`);
* the new edge link of the layer of these two handles (`sphereEdgeLink`), and the concrete
  regression test A of the draft (§6.1, the north handle registered twice): the old dry
  `EdgeLink` holds, the old S4 / S9 conclusions fail, and the new contract rejects the layer
  (`sphereRegressionA`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

local instance diskChartsEdge_FC39P0b : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## The interval components of `C₂` -/

theorem mem_Ioo_of_Icc_FC39P0b (t : Icc (0 : ℝ) 1) : t.val ∈ Ioo (-1 / 2 : ℝ) (3 / 2) :=
  ⟨by linarith [t.2.1], by linarith [t.2.2]⟩

/-- The parametrization `t ↦ t + shift b` of the component of the side `b`. -/
def edgeInterval (b : Bool) (t : Icc (0 : ℝ) 1) : edgeBaseOpens :=
  edgeBasePoint b t.val (mem_Ioo_of_Icc_FC39P0b t)

theorem edgeBaseCoord_interval (b : Bool) (t : Icc (0 : ℝ) 1) :
    edgeBaseCoord (edgeInterval b t) = t.val + edgeShift b :=
  edgeBaseCoord_basePoint b _

theorem edgeBase_ext {c c' : edgeBaseOpens} (h : edgeBaseCoord c = edgeBaseCoord c') : c = c' :=
  Subtype.ext (edgeLineEquiv.symm.injective h)

theorem continuous_edgeInterval (b : Bool) : Continuous (edgeInterval b) :=
  (edgeLineEquiv.continuous.comp (continuous_subtype_val.add continuous_const)).subtype_mk _

theorem range_edgeInterval (b : Bool) :
    range (edgeInterval b) = edgeBaseCoord ⁻¹' Icc (edgeShift b) (edgeShift b + 1) := by
  ext c
  constructor
  · rintro ⟨t, rfl⟩
    rw [mem_preimage, edgeBaseCoord_interval]
    constructor <;> linarith [t.2.1, t.2.2]
  · intro hc
    have ht : edgeBaseCoord c - edgeShift b ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hc.1], by linarith [hc.2]⟩
    refine ⟨⟨_, ht⟩, edgeBase_ext ?_⟩
    rw [edgeBaseCoord_interval]
    ring

theorem edgeCbase_eq : edgeCbase = range (edgeInterval false) ∪ range (edgeInterval true) := by
  rw [range_edgeInterval, range_edgeInterval]
  ext c
  simp only [edgeCbase, edgeCbaseReal, edgeShift, mem_preimage, mem_union, Bool.false_eq_true,
    ite_false, ite_true]
  norm_num

theorem range_edgeInterval_subset (b : Bool) : range (edgeInterval b) ⊆ edgeCbase := by
  rw [edgeCbase_eq]
  cases b
  exacts [subset_union_left, subset_union_right]

/-- The translation `t ↦ t + shift b` as a diffeomorphism `ℝ ≃ ℝ¹`. -/
def edgeLineDiffeo (b : Bool) : Diffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ E1 ∞ where
  toFun t := edgeLineEquiv (t + edgeShift b)
  invFun v := edgeLineEquiv.symm v - edgeShift b
  left_inv t := by simp
  right_inv v := by simp
  contMDiff_toFun := (edgeLineEquiv.contDiff.comp (contDiff_id.add contDiff_const)).contMDiff
  contMDiff_invFun := (edgeLineEquiv.symm.contDiff.sub contDiff_const).contMDiff

theorem isSmoothEmbedding_edgeLine (b : Bool) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞
      fun t : Icc (0 : ℝ) 1 => edgeLineEquiv (t.val + edgeShift b) := by
  have himm : IsImmersion (𝓡∂ 1) (𝓡 1) ∞
      (edgeLineDiffeo b ∘ fun t : Icc (0 : ℝ) 1 => t.val) :=
    (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)).isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
      ((edgeLineDiffeo b).isLocalDiffeomorph.isLocalDiffeomorphOn _) (by simp)
  refine ⟨himm, (Continuous.isClosedEmbedding himm.contMDiff.continuous ?_).isEmbedding⟩
  intro t t' h
  have h' := edgeLineEquiv.injective h
  exact Subtype.ext (add_right_cancel h')

/-- **The component parametrizations are smooth embeddings of `[0, 1]`.** -/
theorem isSmoothEmbedding_edgeInterval (b : Bool) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (edgeInterval b) :=
  isSmoothEmbedding_codRestrict_opens (isSmoothEmbedding_edgeLine b) edgeBaseOpens
    fun t => (edgeInterval b t).2

theorem isPreconnected_range_edgeInterval (b : Bool) : IsPreconnected (range (edgeInterval b)) := by
  have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  exact isPreconnected_range (continuous_edgeInterval b)

theorem mem_range_edgeInterval_of_lt {c : edgeBaseOpens} (hc : c ∈ edgeCbase)
    (h : edgeBaseCoord c < 2) : c ∈ range (edgeInterval false) := by
  rw [range_edgeInterval, mem_preimage]
  rcases hc with hc | hc
  · simpa [edgeShift] using hc
  · exfalso
    linarith [hc.1]

theorem mem_range_edgeInterval_of_gt {c : edgeBaseOpens} (hc : c ∈ edgeCbase)
    (h : 2 < edgeBaseCoord c) : c ∈ range (edgeInterval true) := by
  rw [range_edgeInterval, mem_preimage]
  rcases hc with hc | hc
  · exfalso
    linarith [hc.2]
  · simp only [edgeShift, ite_true]
    norm_num
    exact hc

/-- **The actual components of `C₂`** are the two intervals. -/
theorem connectedComponentIn_edgeCbase {b : Bool} {c : edgeBaseOpens}
    (hc : c ∈ range (edgeInterval b)) :
    connectedComponentIn edgeCbase c = range (edgeInterval b) := by
  have hcC : c ∈ edgeCbase := range_edgeInterval_subset b hc
  refine Subset.antisymm ?_
    ((isPreconnected_range_edgeInterval b).subset_connectedComponentIn hc
      (range_edgeInterval_subset b))
  have hUV : Disjoint (edgeBaseCoord ⁻¹' Iio 2) (edgeBaseCoord ⁻¹' Ioi 2) :=
    Set.disjoint_left.2 fun x (h1 : edgeBaseCoord x < 2) (h2 : 2 < edgeBaseCoord x) =>
      lt_asymm h1 h2
  have hcov : connectedComponentIn edgeCbase c ⊆
      edgeBaseCoord ⁻¹' Iio 2 ∪ edgeBaseCoord ⁻¹' Ioi 2 := by
    intro x hx
    rcases connectedComponentIn_subset _ _ hx with h | h
    · exact Or.inl (show edgeBaseCoord x < 2 by linarith [h.2])
    · exact Or.inr (show 2 < edgeBaseCoord x by linarith [h.1])
  have hcmem := mem_connectedComponentIn hcC
  rw [range_edgeInterval, mem_preimage] at hc
  rcases isPreconnected_connectedComponentIn.subset_or_subset
    (isOpen_Iio.preimage continuous_edgeBaseCoord) (isOpen_Ioi.preimage continuous_edgeBaseCoord)
    hUV hcov with h | h
  · cases b
    · intro x hx
      exact mem_range_edgeInterval_of_lt (connectedComponentIn_subset _ _ hx) (h hx)
    · exfalso
      have := h hcmem
      simp only [edgeShift, ite_true] at hc
      exact absurd (show edgeBaseCoord c < 2 from this) (by linarith [hc.1])
  · cases b
    · exfalso
      have := h hcmem
      simp only [edgeShift, Bool.false_eq_true, ite_false] at hc
      exact absurd (show 2 < edgeBaseCoord c from this) (by linarith [hc.2])
    · intro x hx
      exact mem_range_edgeInterval_of_gt (connectedComponentIn_subset _ _ hx) (h hx)

/-- The actual component of the interval `i` (`0` south, `1` north). -/
def edgeComponent (i : Fin 2) : ActualComponent edgeCbase :=
  ⟨range (edgeInterval (finTwoEquiv i)), edgeInterval (finTwoEquiv i) (iccEnd false),
    range_edgeInterval_subset _ ⟨_, rfl⟩, (connectedComponentIn_edgeCbase ⟨_, rfl⟩).symm⟩

/-- The component registry (two intervals, no circle). -/
def edgeComponentFun : Fin 2 ⊕ Fin 0 → ActualComponent edgeCbase
  | .inl i => edgeComponent i
  | .inr j => j.elim0

theorem edgeComponentFun_bijective : Bijective edgeComponentFun := by
  constructor
  · rintro (i | i) (j | j) h
    · have h1 := congrArg Subtype.val h
      have hm : edgeInterval (finTwoEquiv i) (iccEnd false) ∈
          (edgeComponentFun (.inl j)).1 := by
        rw [← h1]
        exact ⟨_, rfl⟩
      change edgeInterval _ _ ∈ range (edgeInterval (finTwoEquiv j)) at hm
      rw [range_edgeInterval, mem_preimage, edgeBaseCoord_interval] at hm
      fin_cases i <;> fin_cases j <;>
        first | rfl | norm_num [finTwoEquiv, edgeShift, iccEnd] at hm
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  · rintro ⟨C, x, hx, rfl⟩
    rw [edgeCbase_eq] at hx
    rcases hx with hx | hx
    · exact ⟨.inl 0, Subtype.ext (connectedComponentIn_edgeCbase hx).symm⟩
    · exact ⟨.inl 1, Subtype.ext (connectedComponentIn_edgeCbase hx).symm⟩

/-! ## The four endpoints -/

theorem edgeInterval_end_mem_frontier (i : Fin 2) (e : Bool) :
    edgeInterval (finTwoEquiv i) (iccEnd e) ∈ frontier edgeCbase := by
  rw [mem_frontier_edgeCbase, edgeBaseCoord_interval]
  fin_cases i <;> cases e <;> norm_num [finTwoEquiv, edgeShift, iccEnd]

/-- The endpoint registry. -/
def edgeEndFun (a : Fin 2 × Bool) : {c : edgeBaseOpens // c ∈ frontier edgeCbase} :=
  ⟨edgeInterval (finTwoEquiv a.1) (iccEnd a.2), edgeInterval_end_mem_frontier a.1 a.2⟩

theorem edgeEndFun_bijective : Bijective edgeEndFun := by
  constructor
  · rintro ⟨i, e⟩ ⟨j, e'⟩ h
    have h1 := congrArg (fun c => edgeBaseCoord c.1) h
    simp only [edgeEndFun, edgeBaseCoord_interval] at h1
    fin_cases i <;> fin_cases j <;> cases e <;> cases e' <;>
      simp [finTwoEquiv, edgeShift, iccEnd] at h1 ⊢ <;> norm_num at h1
  · rintro ⟨c, hc⟩
    have hc' := mem_frontier_edgeCbase.1 hc
    have key : ∀ (i : Fin 2) (e : Bool),
        edgeBaseCoord c = (iccEnd e).val + edgeShift (finTwoEquiv i) →
          ∃ a, edgeEndFun a = ⟨c, hc⟩ := fun i e h =>
      ⟨(i, e), Subtype.ext (edgeBase_ext (by
        change edgeBaseCoord (edgeInterval (finTwoEquiv i) (iccEnd e)) = edgeBaseCoord c
        rw [edgeBaseCoord_interval, h]))⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hc'
    rcases hc' with h | h | h | h
    · exact key 0 false (by simp [h, finTwoEquiv, edgeShift, iccEnd])
    · exact key 0 true (by simp [h, finTwoEquiv, edgeShift, iccEnd])
    · exact key 1 false (by simp [h, finTwoEquiv, edgeShift, iccEnd])
    · refine key 1 true ?_
      simp [h, finTwoEquiv, edgeShift, iccEnd]
      norm_num

/-! ## The whole products: the two polar disk handles -/

theorem diskRim_iff_FC39P0b {x : ClosedCell 2} : x ∈ diskRim ↔ ‖x.val‖ = 1 := by
  have h := congrArg (x ∈ ·)
    (DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1)
  exact Iff.of_eq h

theorem handle_box (w : ClosedCell 2) (t : Icc (0 : ℝ) 1) : (w.val, t.val) ∈ edgeBox :=
  ⟨mem_ball_zero_iff.2 (by linarith [w.2]), mem_Ioo_of_Icc_FC39P0b t⟩

theorem cycleS3Handle_map (b : Bool) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1) :
    (cycleS3Handle b).map (w, t) = cycleHandleChart b (w.val, t.val) :=
  rfl

theorem edgeShift_mem_Icc_iff {b b' : Bool} {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    t + edgeShift b' ∈ Icc (edgeShift b) (edgeShift b + 1) ↔ b' = b ∧ t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro h
    cases b <;> cases b' <;>
      simp only [edgeShift, Bool.false_eq_true, ite_false, ite_true, add_zero, zero_add,
        mem_Icc] at h ⊢
    · exact ⟨trivial, h.1, h.2⟩
    · exfalso
      linarith [h.1, h.2, ht.1, ht.2]
    · exfalso
      linarith [h.1, h.2, ht.1, ht.2]
    · exact ⟨trivial, by linarith [h.1], by linarith [h.2]⟩
  · rintro ⟨rfl, h⟩
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The image of the handle `b` is the WHOLE inverse image of its component.** -/
theorem range_cycleS3Handle_eq (b : Bool) :
    range (cycleS3Handle b).map =
      Subtype.val '' {x : edgeSource | edgeProj x ∈ range (edgeInterval b) ∧ edgeHeight x ≤ 1} := by
  have h := image_val_edgeSource
    (fun s => edgeLineEquiv.symm s ∈ Icc (edgeShift b) (edgeShift b + 1)) (· ≤ 1)
  beta_reduce at h
  have hset : {x : edgeSource | edgeProj x ∈ range (edgeInterval b) ∧ edgeHeight x ≤ 1} =
      {x : edgeSource | edgeLineEquiv.symm (edgeProjE x.val) ∈
        Icc (edgeShift b) (edgeShift b + 1) ∧ edgeHeightR x.val ≤ 1} := by
    rw [range_edgeInterval]
    rfl
  rw [hset, h]
  ext y
  simp only [mem_iUnion, mem_image, mem_range]
  constructor
  · rintro ⟨⟨w, t⟩, rfl⟩
    refine ⟨b, (w.val, t.val), ⟨handle_box w t, ?_, ?_⟩, rfl⟩
    · rw [ContinuousLinearEquiv.symm_apply_apply]
      exact (edgeShift_mem_Icc_iff (mem_Ioo_of_Icc_FC39P0b t)).2 ⟨rfl, t.2⟩
    · nlinarith [w.2, norm_nonneg w.val]
  · rintro ⟨b', p, ⟨hp, hI, hR⟩, rfl⟩
    rw [ContinuousLinearEquiv.symm_apply_apply] at hI
    obtain ⟨rfl, ht⟩ := (edgeShift_mem_Icc_iff hp.2).1 hI
    exact ⟨(⟨p.1, by nlinarith [norm_nonneg p.1]⟩, ⟨p.2, ht⟩), rfl⟩

theorem cycleS3Handle_proj (b : Bool) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1) :
    ∃ hx : (cycleS3Handle b).map (w, t) ∈ edgeSource,
      edgeProj ⟨(cycleS3Handle b).map (w, t), hx⟩ = edgeInterval b t :=
  ⟨chart_mem_edgeSource (handle_box w t), Subtype.ext (edgeProjE_chart (handle_box w t))⟩

theorem cycleS3Handle_disk (b : Bool) (t : Icc (0 : ℝ) 1) :
    range (fun w => (cycleS3Handle b).map (w, t)) =
      Subtype.val '' {x : edgeSource | edgeProj x = edgeInterval b t ∧ edgeHeight x ≤ 1} :=
  (edge_disk_eq b (mem_Ioo_of_Icc_FC39P0b t)).symm

theorem cycleS3Handle_rim (b : Bool) (t : Icc (0 : ℝ) 1) :
    (fun w => (cycleS3Handle b).map (w, t)) '' diskRim =
      Subtype.val '' {x : edgeSource | edgeProj x = edgeInterval b t ∧ edgeHeight x = 1} := by
  refine Eq.trans ?_ (image_val_edgeSource_fibre b (mem_Ioo_of_Icc_FC39P0b t) (· = 1)).symm
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : ‖w.val‖ = 1 := diskRim_iff_FC39P0b.1 hw
    exact ⟨w.val, ⟨by linarith, by rw [h1]; norm_num⟩, rfl⟩
  · rintro ⟨w, ⟨-, hw⟩, rfl⟩
    have h1 : ‖w‖ = 1 :=
      (pow_left_inj₀ (norm_nonneg w) zero_le_one two_ne_zero).1 (by rw [hw]; norm_num)
    exact ⟨⟨w, h1.le⟩, diskRim_iff_FC39P0b.2 h1, rfl⟩

/-! ## The component export and the new edge link -/

/-- **The component export of the S³ edge bundle** (§1.1): two interval components, four
endpoints, the polar disk handles as whole products, no circle component. -/
def sphereEdgeModels : EdgeComponentModels sphereEdgeBundle where
  intervalCount := 2
  circleCount := 0
  componentEquiv := Equiv.ofBijective edgeComponentFun edgeComponentFun_bijective
  intervalBase i := edgeInterval (finTwoEquiv i)
  intervalBase_embedding _ := isSmoothEmbedding_edgeInterval _
  intervalBase_range _ := rfl
  circleBase j := j.elim0
  circleBase_embedding j := j.elim0
  circleBase_range j := j.elim0
  endpointEquiv := Equiv.ofBijective edgeEndFun edgeEndFun_bijective
  endpointEquiv_apply _ _ := rfl
  intervalTriv i := cycleS3Handle (finTwoEquiv i)
  intervalTriv_range _ := range_cycleS3Handle_eq _
  intervalTriv_proj _ w t := cycleS3Handle_proj _ w t
  intervalTriv_disk _ t := cycleS3Handle_disk _ t
  intervalTriv_rim _ t := cycleS3Handle_rim _ t
  circleTriv j := j.elim0
  circleTriv_smooth j := j.elim0
  circleTriv_mfderiv j := j.elim0
  circleTriv_injective j := j.elim0
  circleTriv_range j := j.elim0
  circleTriv_proj j := j.elim0
  circleTriv_disk j := j.elim0
  circleTriv_rim j := j.elim0

/-- The edge layer of the S³ inhabitant: the south and the north polar disk handle. -/
def sphereEdgeLayer : EdgeLayer sphereW where
  handleCount := 2
  handle i := cycleS3Handle (finTwoEquiv i)
  edgeCircleCount := 0
  edgeCircle j := j.elim0

/-- **The new edge link of the S³ inhabitant** (§1.2). -/
def sphereEdgeLink : EdgeComponentsLink sphereEdgeBundle sphereEdgeModels sphereEdgeLayer where
  handleEquiv := Equiv.refl _
  circleEquiv := Equiv.refl _
  handle_whole h := sphereEdgeModels.intervalTriv_range h
  circle_whole j := j.elim0
  handle_proj h := sphereEdgeModels.intervalTriv_proj h
  handle_disk h := sphereEdgeModels.intervalTriv_disk h
  handle_rim h := sphereEdgeModels.intervalTriv_rim h
  circle_proj j := j.elim0
  circle_disk j := j.elim0
  circle_rim j := j.elim0

/-! ## Regression test A on S³ (draft §6.1) -/

/-- The north polar disk handle of the S³ edge layer. -/
def sphereNorthHandle : Fin sphereEdgeLayer.handleCount :=
  (1 : Fin 2)

theorem sphereEdgeLayer_north : sphereEdgeLayer.handle sphereNorthHandle = cycleS3Handle true :=
  rfl

/-- **Regression test A, concrete (S³, the north handle registered twice).** The old dry
`EdgeLink` holds for the duplicated layer, the old S4 (cover) and S9 (handle ends) conclusions
fail, and the new contract has no registration of the duplicated layer. -/
theorem sphereRegressionA :
    DryEdgeLink sphereEdgeBundle (sphereEdgeLayer.duplicate sphereNorthHandle) ∧
      (∀ (V : VertexLayer sphereW) (circ : CircleRegion sphereW),
        ¬ CoverLayer sphereW V (sphereEdgeLayer.duplicate sphereNorthHandle) circ) ∧
      (∀ {n : ℕ} {E : BoundaryTori sphereW n} (V : VertexLayer sphereW)
        {circ : CircleRegion sphereW} {S : SeamLayer sphereW V circ} {O : PortLayer sphereW E V}
        (F : FaceLayer sphereW E V S O),
          IsEmpty (HandleEndLayer sphereW V (sphereEdgeLayer.duplicate sphereNorthHandle) F)) ∧
      IsEmpty (EdgeComponentsLink sphereEdgeBundle sphereEdgeModels
        (sphereEdgeLayer.duplicate sphereNorthHandle)) :=
  regressionA sphereEdgeLink sphereNorthHandle

/-- The two handles of the S³ edge layer have disjoint images and four pairwise disjoint end
disks (derived from the component registration, `FC39P0Edges.lean`). -/
theorem sphereEdgeLayer_disjoint :
    (Pairwise fun h h' : Fin sphereEdgeLayer.handleCount =>
        Disjoint (range (sphereEdgeLayer.handle h).map) (range (sphereEdgeLayer.handle h').map)) ∧
      Pairwise fun a b : Fin sphereEdgeLayer.handleCount × Bool =>
        Disjoint ((sphereEdgeLayer.handle a.1).endDisk a.2)
          ((sphereEdgeLayer.handle b.1).endDisk b.2) :=
  ⟨sphereEdgeLink.handle_ranges_disjoint_of_components,
    sphereEdgeLink.endDisks_disjoint_of_components⟩

end GC.GraphManifold.Assembly.FC39P0
