import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeBaseSTR
import DifferentialGeometry.Topology.Manifold.Interval.Immersion

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G2 part 5: the edge bundle of the rows and its component models

`edgeBundle_STR Z = edgeBundle74 A D F` is the actual restriction of the edge stage to
`edgeBaseOpen = ⊤`. Its closed base `C₂ = {0 ≤ t ≤ 1}` has ONE interval component and no circle
component; `edgeComponentModels_STR Z : EdgeComponentModels (edgeBundle_STR Z)` registers it: the
interval parametrization `t ↦ t`, the two endpoints `t = 0, 1` and the whole `D² × [0, 1]` handle.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_ModelsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_ModelsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable (Z : ZeroDomains Wc)

/-- **The edge bundle of the rows**: the actual restriction of the edge stage to `⊤`. -/
abbrev edgeBundle_STR : EdgeBundle Wc :=
  edgeBundle74 (stageGeometry_STR Z) (cutChoice_STR Z) (edgeFacts_STR Z)

theorem disk_eq_STR (c : Base1_STR) :
    (edgeBundle_STR Z).disk c = fibreSet_STR ((c.val : EuclideanSpace ℝ (Fin 1)) 0) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hc, hh⟩, rfl⟩
    have hy : x.val ∈ edgeParent_STR := (stageGeometry_STR Z).edge.restrictParent_le _ x.2
    refine ⟨hy, ?_, hh⟩
    have h0 : (edgeProj_STR ⟨x.val, hy⟩) 0 = (c.val : EuclideanSpace ℝ (Fin 1)) 0 :=
      congrArg (fun k => (k.val : EuclideanSpace ℝ (Fin 1)) 0) hc
    rw [edgeProj_val_STR] at h0
    exact h0
  · rintro ⟨hy, ht, h1⟩
    refine ⟨⟨y, (stageGeometry_STR Z).edge.mem_restrictParent_of hy trivial⟩, ⟨?_, h1⟩, rfl⟩
    apply Subtype.ext
    change edgeProj_STR ⟨y, hy⟩ = c.val
    rw [edgeProj_eq_single_STR hy, ht]
    ext i
    fin_cases i
    simp

theorem rim_eq_STR (c : Base1_STR) :
    (edgeBundle_STR Z).rim c = rimSet_STR ((c.val : EuclideanSpace ℝ (Fin 1)) 0) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hc, hh⟩, rfl⟩
    have hy : x.val ∈ edgeParent_STR := (stageGeometry_STR Z).edge.restrictParent_le _ x.2
    refine ⟨hy, ?_, hh⟩
    have h0 : (edgeProj_STR ⟨x.val, hy⟩) 0 = (c.val : EuclideanSpace ℝ (Fin 1)) 0 :=
      congrArg (fun k => (k.val : EuclideanSpace ℝ (Fin 1)) 0) hc
    rw [edgeProj_val_STR] at h0
    exact h0
  · rintro ⟨hy, ht, h1⟩
    refine ⟨⟨y, (stageGeometry_STR Z).edge.mem_restrictParent_of hy trivial⟩, ⟨?_, h1⟩, rfl⟩
    apply Subtype.ext
    change edgeProj_STR ⟨y, hy⟩ = c.val
    rw [edgeProj_eq_single_STR hy, ht]
    ext i
    fin_cases i
    simp


/-! ## The one interval component -/

theorem isPreconnected_cbase_STR :
    IsPreconnected (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := by
  rw [cbase_eq_STR]
  exact coordHomeo_STR.isPreconnected_preimage.mpr isPreconnected_Icc

/-- The point `t = 0` of the edge base. -/
def cbasePoint_STR : Base1_STR := ⟨EuclideanSpace.single (0 : Fin 1) 0, trivial⟩

theorem cbasePoint_mem_STR : cbasePoint_STR ∈ (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := by
  simp [cbasePoint_STR, edgeC2_STR]

/-- The unique component of `C₂`. -/
def cbaseComp_STR : ActualComponent (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) :=
  ActualComponent.of cbasePoint_mem_STR

theorem cbaseComp_val_STR :
    cbaseComp_STR.1 = (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) :=
  isPreconnected_cbase_STR.connectedComponentIn cbasePoint_mem_STR

theorem actualComponent_eq_STR (C : ActualComponent (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR)) :
    C = cbaseComp_STR := by
  apply Subtype.ext
  obtain ⟨x, hx, hC⟩ := C.2
  rw [hC, cbaseComp_val_STR]
  exact isPreconnected_cbase_STR.connectedComponentIn hx

/-- The component equivalence of the models. -/
def componentEquiv_STR :
    (Fin 1 ⊕ Fin 0) ≃ ActualComponent (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) where
  toFun _ := cbaseComp_STR
  invFun _ := Sum.inl 0
  left_inv s := by
    rcases s with i | j
    · exact congrArg Sum.inl (Subsingleton.elim _ _)
    · exact j.elim0
  right_inv C := (actualComponent_eq_STR C).symm

/-- The interval parametrization `t ↦ (t)` of the closed edge base. -/
def intervalBase_STR (t : Icc (0 : ℝ) 1) : Base1_STR :=
  ⟨EuclideanSpace.single (0 : Fin 1) t.val, trivial⟩

theorem intervalBase_embedding_STR :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ intervalBase_STR := by
  have h := (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
    (n := ∞)).continuousLinearEquiv_comp e1_STR.symm
  have h2 := h.diffeomorph_comp
    (openDiffeomorphOfForall (I := 𝓡 1)
      (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))) (fun _ => trivial)).symm
  exact h2

theorem intervalBase_range_STR :
    range intervalBase_STR = (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := by
  ext c
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.2.1, t.2.2⟩
  · intro hc
    refine ⟨⟨(c.val : EuclideanSpace ℝ (Fin 1)) 0, hc⟩, ?_⟩
    apply Subtype.ext
    change EuclideanSpace.single (0 : Fin 1) ((c.val : EuclideanSpace ℝ (Fin 1)) 0) = c.val
    ext i
    fin_cases i
    simp


theorem eq_single_STR (v : EuclideanSpace ℝ (Fin 1)) :
    v = EuclideanSpace.single (0 : Fin 1) (v 0) := by
  ext i
  fin_cases i
  simp

theorem endpoint_mem_frontier_STR (b : Bool) :
    intervalBase_STR (iccEnd b) ∈ frontier (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := by
  rw [frontier_cbase_STR]
  cases b
  · left
    simp [intervalBase_STR, iccEnd]
  · right
    simp [intervalBase_STR, iccEnd]

/-- The two endpoints of the edge base. -/
def endpointEquiv_STR : (Fin 1 × Bool) ≃
    {c : Base1_STR // c ∈ frontier (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR)} where
  toFun p := ⟨intervalBase_STR (iccEnd p.2), endpoint_mem_frontier_STR p.2⟩
  invFun e := (0, decide ((e.1.val : EuclideanSpace ℝ (Fin 1)) 0 = 1))
  left_inv := by
    rintro ⟨i, b⟩
    refine Prod.ext (Subsingleton.elim _ _) ?_
    cases b
    · simp [intervalBase_STR, iccEnd]
    · simp [intervalBase_STR, iccEnd]
  right_inv := by
    rintro ⟨c, hc⟩
    have he : c ∈ {c : Base1_STR | (c.val : EuclideanSpace ℝ (Fin 1)) 0 = 0 ∨
        (c.val : EuclideanSpace ℝ (Fin 1)) 0 = 1} := by
      rw [← frontier_cbase_STR]
      exact hc
    apply Subtype.ext
    apply Subtype.ext
    change EuclideanSpace.single (0 : Fin 1) (iccEnd (decide
      ((c.val : EuclideanSpace ℝ (Fin 1)) 0 = 1))).val = c.val
    rcases he with h0 | h1
    · have hne : ¬ (c.val : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
        rw [h0]
        norm_num
      rw [decide_eq_false hne]
      rw [eq_single_STR c.val, h0]
      simp [iccEnd]
    · rw [decide_eq_true h1]
      rw [eq_single_STR c.val, h1]
      simp [iccEnd]


theorem wholeComponent_eq_STR :
    (edgeBundle_STR Z).wholeComponent cbaseComp_STR = handleSet_STR := by
  ext y
  constructor
  · rintro ⟨x, ⟨hc, hh⟩, rfl⟩
    have hy : x.val ∈ edgeParent_STR := (stageGeometry_STR Z).edge.restrictParent_le _ x.2
    have hc' : (stageGeometry_STR Z).edge.restrictProj (cutChoice_STR Z).edgeBaseOpen x ∈
        (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := by
      rw [← cbaseComp_val_STR]
      exact hc
    refine ⟨hy, ?_, hh⟩
    have h0 : (edgeProj_STR ⟨x.val, hy⟩) 0 ∈ Icc (0 : ℝ) 1 := hc'
    rw [edgeProj_val_STR] at h0
    exact h0
  · rintro ⟨hy, ht, h1⟩
    refine ⟨⟨y, (stageGeometry_STR Z).edge.mem_restrictParent_of hy trivial⟩, ⟨?_, h1⟩, rfl⟩
    rw [cbaseComp_val_STR]
    change (edgeProj_STR ⟨y, hy⟩) ∈ edgeC2_STR
    rw [edgeProj_eq_single_STR hy]
    simpa [edgeC2_STR] using ht

/-- **The component models of the edge bundle**: one interval component `[0, 1]`, no circle
component. -/
def edgeComponentModels_STR : EdgeComponentModels (edgeBundle_STR Z) where
  intervalCount := 1
  circleCount := 0
  componentEquiv := componentEquiv_STR
  intervalBase _ := intervalBase_STR
  intervalBase_embedding _ := intervalBase_embedding_STR
  intervalBase_range _ := intervalBase_range_STR.trans cbaseComp_val_STR.symm
  circleBase j := j.elim0
  circleBase_embedding j := j.elim0
  circleBase_range j := j.elim0
  endpointEquiv := endpointEquiv_STR
  endpointEquiv_apply _ _ := rfl
  intervalTriv _ := edgeHandle_STR
  intervalTriv_range _ := by
    change range handleMap_STR = _
    rw [range_handleMap_STR]
    exact (wholeComponent_eq_STR Z).symm
  intervalTriv_proj _ w t := by
    have hp := rho2_handleEuclid_lt_STR (w, t)
    have hy : handleMap_STR (w, t) ∈ edgeParent_STR := edgeToW_mem_parent_STR hp
    refine ⟨(stageGeometry_STR Z).edge.mem_restrictParent_of hy trivial, ?_⟩
    apply Subtype.ext
    change edgeProj_STR ⟨handleMap_STR (w, t), hy⟩ = EuclideanSpace.single (0 : Fin 1) t.val
    rw [edgeProj_eq_single_STR hy]
    congr 1
    change tOf_STR (sphereSecond (edgeToW_STR (handleEuclid_STR (w, t))).val) = t.val
    rw [tOf_edgeToW_STR hp]
    simp [handleEuclid_apply_STR, cellPt_STR]
  intervalTriv_disk _ t := by
    rw [disk_eq_STR]
    change range (fun w : ClosedCell 2 => edgeToW_STR (cellPt_STR w t.val)) = _
    rw [range_edgeSlice_STR]
    rfl
  intervalTriv_rim _ t := by
    rw [rim_eq_STR]
    change (fun w : ClosedCell 2 => edgeToW_STR (cellPt_STR w t.val)) '' diskRim = _
    rw [slice_rim_STR]
    rfl
  circleTriv j := j.elim0
  circleTriv_smooth j := j.elim0
  circleTriv_mfderiv j := j.elim0
  circleTriv_injective j := j.elim0
  circleTriv_range j := j.elim0
  circleTriv_proj j := j.elim0
  circleTriv_disk j := j.elim0
  circleTriv_rim j := j.elim0

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
