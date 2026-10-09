import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeBundle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CliffordBlocks

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_RegistryX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_RegistryX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance
local instance cellCharts_RegistryX135 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  Handle.closedCellChartedSpaceSucc 1
local instance cellSmooth_RegistryX135 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  Handle.closedCellIsManifold 1

theorem radialBaseComponent_univ (C : radialEdgeBundle.EdgeBaseComponent) : C.val = univ := by
  obtain ⟨x, hx, he⟩ := C.property
  change C.val = connectedComponentIn (univ : Set Circle) x at he
  exact he.trans ((connectedComponentIn_univ (show Circle from x)).trans
    (PreconnectedSpace.connectedComponent_eq_univ (show Circle from x)))

def radialBaseComponent : radialEdgeBundle.EdgeBaseComponent :=
  ActualComponent.of (x := (1 : Circle)) (mem_univ _)

def radialComponentEquiv : (Fin 0 ⊕ Fin 1) ≃ radialEdgeBundle.EdgeBaseComponent where
  toFun := fun _ => radialBaseComponent
  invFun := fun _ => .inr 0
  left_inv := by
    intro i
    cases i with
    | inl i => exact i.elim0
    | inr i => exact Subsingleton.elim _ _
  right_inv := by
    intro C
    apply Subtype.ext
    rw [radialBaseComponent_univ, radialBaseComponent_univ]

instance radialEdgeEndEmpty : IsEmpty radialEdgeBundle.EdgeEnd :=
  ⟨fun p => by
    have hp : p.val ∈ frontier (univ : Set Circle) := p.property
    have hf : frontier (univ : Set Circle) = ∅ := frontier_univ
    have hm : (show Circle from p.val) ∈ (∅ : Set Circle) := hf ▸ hp
    exact Set.notMem_empty _ hm⟩

def radialEndpointEquiv : (Fin 0 × Bool) ≃ radialEdgeBundle.EdgeEnd :=
  Equiv.equivOfIsEmpty _ _

def radialCircleTriv (q : ClosedCell 2 × Circle) : carrier.Carrier :=
  edgeToCarrier (edgeClosedCellProduct q)

theorem radialCircleTriv_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) ∞ radialCircleTriv :=
  edgeToCarrier_smooth.comp edgeClosedCellProduct.contMDiff

theorem radialCircleTriv_injective : Injective radialCircleTriv :=
  edgeToCarrier_injective.comp edgeClosedCellProduct.injective

theorem radialCircleTriv_mfderiv (q : ClosedCell 2 × Circle) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) radialCircleTriv q) := by
  have hd := (edgeClosedCellProduct.mfderivToContinuousLinearEquiv (by simp) q).bijective
  have hcomp := (edgeToCarrier_mfderiv (edgeClosedCellProduct q)).comp hd
  have hc := mfderiv_comp q (edgeToCarrier_smooth.mdifferentiableAt (by simp))
    (edgeClosedCellProduct.contMDiff.mdifferentiableAt (by simp))
  exact hc.symm ▸ hcomp

theorem radialCircleTriv_fibre (c : Circle) (x : ClosedCell 2) :
    radialCircleTriv (x, c) = edgeFibreAt c x := by
  apply Subtype.ext
  change (edgeClosedCellProduct (x, c)).val = (edgeCoreFibreAt c x).val
  rw [edgeCoreFibreAt_product]

theorem radialCircleTriv_height (q : ClosedCell 2 × Circle) :
    height (radialCircleTriv q) =
      ‖(GC.Seifert.unitDiscClosedCell.{0}.symm q.1).down.val‖ ^ 2 / 4 - 1 :=
  edgeHalfCarrier_height (GC.Seifert.unitDiscClosedCell.{0}.symm q.1, q.2)

theorem radialCircleTriv_boundary (c : Circle) {x : ClosedCell 2} :
    x ∈ diskRim ↔ height (radialCircleTriv (x, c)) = -(3 / 4 : ℝ) := by
  have hi := (GC.Seifert.unitDiscClosedCell.{0}.symm.isLocalDiffeomorph x).isBoundaryPoint_iff
    (by simp)
  rw [radialCircleTriv_height]
  change (𝓡∂ 2).IsBoundaryPoint x ↔ _
  rw [hi, GC.Seifert.unitDisc_isBoundaryPoint_iff]
  constructor <;> intro h <;> linarith

theorem radialCircleTriv_range :
    range radialCircleTriv = {p : carrier.Carrier | height p ≤ -(3 / 4 : ℝ)} := by
  rw [← edgeToCarrier_range]
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨edgeClosedCellProduct q, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨z, rfl⟩ := edgeClosedCellProduct.surjective q
    exact ⟨z, rfl⟩

theorem radialWholeComponent (C : radialEdgeBundle.EdgeBaseComponent) :
    radialEdgeBundle.wholeComponent C =
      {p : carrier.Carrier | height p ≤ -(3 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨q, ⟨hc, hh⟩, rfl⟩
    exact hh
  · intro hh
    have hi : height p < 0 := hh.trans_lt (by norm_num : -(3 / 4 : ℝ) < 0)
    refine ⟨⟨p, hi⟩, ⟨?_, hh⟩, rfl⟩
    rw [radialBaseComponent_univ]
    exact mem_univ _

theorem radialCircleTriv_proj (x : ClosedCell 2) (c : Circle) :
    ∃ hx : radialCircleTriv (x, c) ∈ radialEdgeBundle.source,
      radialEdgeBundle.proj ⟨radialCircleTriv (x, c), hx⟩ = c := by
  rw [radialCircleTriv_fibre]
  refine ⟨?_, edgeLongitude_fibre c x⟩
  exact (edgeCoreFibreAt_height c x).trans_lt (by norm_num : -(3 / 4 : ℝ) < 0)

theorem radialCircleTriv_disk (c : Circle) :
    range (fun x => radialCircleTriv (x, c)) = radialEdgeBundle.disk c := by
  have he : (fun x => radialCircleTriv (x, c)) = edgeFibreAt c :=
    funext (radialCircleTriv_fibre c)
  rw [he, edgeFibreAt_range]
  ext p
  constructor
  · rintro ⟨hc, hh⟩
    have hi : height p < 0 := hh.trans_lt (by norm_num : -(3 / 4 : ℝ) < 0)
    exact ⟨⟨p, hi⟩, ⟨hc, hh⟩, rfl⟩
  · rintro ⟨q, ⟨hc, hh⟩, rfl⟩
    exact ⟨hc, hh⟩

theorem radialCircleTriv_rim (c : Circle) :
    (fun x => radialCircleTriv (x, c)) '' diskRim = radialEdgeBundle.rim c := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hs, hproj⟩ := radialCircleTriv_proj x c
    exact ⟨⟨radialCircleTriv (x, c), hs⟩,
      ⟨hproj, (radialCircleTriv_boundary c (x := x)).mp hx⟩, rfl⟩
  · rintro ⟨q, ⟨hc, hh⟩, rfl⟩
    have hqd : q.val ∈ radialEdgeBundle.disk c := ⟨q, ⟨hc, hh.le⟩, rfl⟩
    rw [← radialCircleTriv_disk] at hqd
    obtain ⟨x, hx⟩ := hqd
    refine ⟨x, ?_, hx⟩
    apply (radialCircleTriv_boundary c (x := x)).mpr
    exact (congrArg height hx).trans hh

def radialEdgeComponentModels : EdgeComponentModels radialEdgeBundle where
  intervalCount := 0
  circleCount := 1
  componentEquiv := radialComponentEquiv
  intervalBase i := i.elim0
  intervalBase_embedding i := i.elim0
  intervalBase_range i := i.elim0
  circleBase _ := id
  circleBase_embedding _ := (Diffeomorph.refl (𝓡 1) Circle ∞).isSmoothEmbedding
  circleBase_range _ := by rw [radialBaseComponent_univ]; exact range_id
  endpointEquiv := radialEndpointEquiv
  endpointEquiv_apply i := i.elim0
  intervalTriv i := i.elim0
  intervalTriv_range i := i.elim0
  intervalTriv_proj i := i.elim0
  intervalTriv_disk i := i.elim0
  intervalTriv_rim i := i.elim0
  circleTriv _ := radialCircleTriv
  circleTriv_smooth _ := radialCircleTriv_smooth
  circleTriv_mfderiv _ := radialCircleTriv_mfderiv
  circleTriv_injective _ := radialCircleTriv_injective
  circleTriv_range _ := by rw [radialWholeComponent]; exact radialCircleTriv_range
  circleTriv_proj _ := radialCircleTriv_proj
  circleTriv_disk _ := radialCircleTriv_disk
  circleTriv_rim _ := radialCircleTriv_rim

end GC.GraphManifold.Assembly.FC39P0.X135Radial
