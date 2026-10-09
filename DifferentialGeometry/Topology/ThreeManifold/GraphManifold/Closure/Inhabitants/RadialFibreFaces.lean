import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialRimBase

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_FibreFacesX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_FibreFacesX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialFibrePoint (b : radialCircleBase) : radialCircleDomain :=
  radialCircleProduct.symm (b, (1 : Circle))

theorem radialFibrePoint_projection (b : radialCircleBase) :
    radialCircleProjection (radialFibrePoint b) = b :=
  congrArg Prod.fst (radialCircleProduct.apply_symm_apply (b, (1 : Circle)))

theorem radialFibrePoint_mem (b : radialCircleBase) :
    (radialFibrePoint b).val ∈ radialCircleBundle.fibre b :=
  ⟨radialFibrePoint b, radialFibrePoint_projection b, rfl⟩

theorem radial_fibre_height (b : radialCircleBase) (p : carrier.Carrier)
    (hp : p ∈ radialCircleBundle.fibre b) : height p = 1 - 2 * ‖b.val.val‖ ^ 2 := by
  obtain ⟨q, hq, rfl⟩ := hp
  have hproj : radialCircleProjection q = b := hq
  have hh := radialCircleProjection_height q
  rw [hproj] at hh
  exact hh

theorem radial_fibre_level_iff {b : radialCircleBase} {t : ℝ} :
    radialCircleBundle.fibre b ⊆ {p | height p = t} ↔ 1 - 2 * ‖b.val.val‖ ^ 2 = t := by
  constructor
  · intro h
    have ht := h (radialFibrePoint_mem b)
    change height (radialFibrePoint b).val = t at ht
    rw [radial_fibre_height b _ (radialFibrePoint_mem b)] at ht
    exact ht
  · intro ht p hp
    change height p = t
    exact (radial_fibre_height b p hp).trans ht

theorem radial_fibre_horizontal_iff {b : radialCircleBase} {F : radialSlims.ResidualFace} :
    radialCircleBundle.fibre b ⊆ radialSlims.residualSet F ↔
      ‖b.val.val‖ ^ 2 = (3 / 4 : ℝ) := by
  rw [radial_residual_height, radial_fibre_level_iff]
  constructor <;> intro h <;> linarith

theorem radial_wholeVertical_height (C : radialEdgeBundle.EdgeBaseComponent) :
    radialEdgeBundle.wholeVertical C = {p | height p = -(3 / 4 : ℝ)} := by
  unfold EdgeBundle.wholeVertical
  rw [radialBaseComponent_univ]
  exact radial_vertical_height

theorem radial_fibre_vertical_iff {b : radialCircleBase}
    {C : radialEdgeBundle.EdgeBaseComponent} :
    radialCircleBundle.fibre b ⊆ radialEdgeBundle.wholeVertical C ↔
      ‖b.val.val‖ ^ 2 = (7 / 8 : ℝ) := by
  rw [radial_wholeVertical_height, radial_fibre_level_iff]
  constructor <;> intro h <;> linarith

theorem radial_newEnd_unique (e : radialSlims.NewEnd) : e = radialNewEnd := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact @Subsingleton.elim (Fin 1) inferInstance _ _
  · exact radialSlim_new_true e

theorem radial_residual_unique (F : radialSlims.ResidualFace) : F = radialResidualFace := by
  cases F with
  | inl F =>
    have hf := radial_neighbour_unique F.val
    have hn := F.property radialSharedEnd
    rw [hf] at hn
    exact (hn rfl).elim
  | inr e => exact congrArg Sum.inr (radial_newEnd_unique e)

theorem radial_component_unique (C : radialEdgeBundle.EdgeBaseComponent) :
    C = radialBaseComponent := by
  apply Subtype.ext
  rw [radialBaseComponent_univ, radialBaseComponent_univ]

def radialFaceEquiv : Fin 2 ≃ CircleFaceLabel radialSlims.ResidualFace
    radialEdgeBundle.EdgeBaseComponent where
  toFun l := if l = 0 then .horizontal radialResidualFace else .vertical radialBaseComponent
  invFun f := match f with
    | .horizontal _ => 0
    | .vertical _ => 1
  left_inv := by
    intro l
    fin_cases l <;> rfl
  right_inv := by
    intro f
    cases f with
    | horizontal F =>
      have hf := radial_residual_unique F
      subst F
      rfl
    | vertical C =>
      have hc := radial_component_unique C
      subst C
      rfl

theorem radial_fibre_face_iff {l : Fin 2} {b : radialCircleBase} :
    radialCircleBundle.fibre b ⊆ circleFaceSet radialSlims radialEdgeBundle
      (radialFaceEquiv l) ↔ radialCircleDefining l b = 0 := by
  fin_cases l
  · change radialCircleBundle.fibre b ⊆ radialSlims.residualSet radialResidualFace ↔
      (3 / 4 : ℝ) - ‖b.val.val‖ ^ 2 = 0
    rw [radial_fibre_horizontal_iff]
    constructor <;> intro h <;> linarith
  · change radialCircleBundle.fibre b ⊆ radialEdgeBundle.wholeVertical radialBaseComponent ↔
      ‖b.val.val‖ ^ 2 - (7 / 8 : ℝ) = 0
    rw [radial_fibre_vertical_iff]
    constructor <;> intro h <;> linarith

end GC.GraphManifold.Assembly.FC39P0.X135Radial
