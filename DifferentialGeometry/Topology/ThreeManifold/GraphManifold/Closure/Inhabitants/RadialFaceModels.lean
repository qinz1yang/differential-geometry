import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialVertexSeams
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesParams

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_FaceModelsX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_FaceModelsX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

theorem radialCuspEndCarrier_embedding (b : Bool) :
    Topology.IsEmbedding (fun t => cuspToCarrier (cuspEnd b t)) := by
  have hi : Injective (cuspEnd b) := by
    intro t u h
    exact congrArg Prod.fst (cuspProduct.injective h)
  exact ((cuspToCarrier_smooth.continuous.comp (cuspEnd_continuous b)).isClosedEmbedding
    (cuspToCarrier_injective.comp hi)).isEmbedding

def radialCuspFaceHomeo (b : Bool) :
    {p : carrier.Carrier | height p = if b then -(1 / 4 : ℝ) else 0} ≃ₜ Torus :=
  ((radialCuspEndCarrier_embedding b).toHomeomorph.trans
    (Homeomorph.setCongr (cuspEnd_map_range b))).symm

theorem radialSlimEndCarrier_embedding (b : Bool) :
    Topology.IsEmbedding (fun t => slimToCarrier (slimEnd b t)) := by
  have hi : Injective (slimEnd b) := by
    intro t u h
    exact congrArg Prod.fst (slimProduct.injective h)
  have hc : Continuous (slimEnd b) :=
    slimProduct.continuous.comp (continuous_id.prodMk continuous_const)
  exact ((slimToCarrier_smooth.continuous.comp hc).isClosedEmbedding
    (slimToCarrier_injective.comp hi)).isEmbedding

def radialSlimFaceHomeo (b : Bool) :
    {p : carrier.Carrier | height p = if b then -(1 / 2 : ℝ) else -(1 / 4 : ℝ)} ≃ₜ Torus :=
  ((radialSlimEndCarrier_embedding b).toHomeomorph.trans
    (Homeomorph.setCongr (slimEnd_map_range b))).symm

theorem radialSharedParam_source (t : Torus) : (t, (0 : ℝ)) ∈ radialSharedCollar.source := by
  rw [radialSharedCollar_source]
  constructor <;> norm_num

theorem radialSharedParam_smooth : ContMDiff torusModel carrier.model ∞
    (fun t : Torus => radialSharedCollar (t, 0)) := by
  intro t
  exact (radialSharedCollar.contMDiffOn_toFun.contMDiffAt
    (radialSharedCollar.open_source.mem_nhds (radialSharedParam_source t))).comp t
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt

theorem radialSharedParam_embedding : IsSmoothEmbedding torusModel carrier.model ∞
    (fun t : Torus => radialSharedCollar (t, 0)) := by
  have hi : Injective (fun t : Torus => radialSharedCollar (t, 0)) := by
    intro t u h
    exact congrArg Prod.fst (radialSharedCollar.injOn (radialSharedParam_source t)
      (radialSharedParam_source u) h)
  have he := (radialSharedParam_smooth.continuous.isClosedEmbedding hi).isEmbedding
  have hincl : IsSmoothEmbedding torusModel signedCollarModel ∞
      (fun t : Torus => (t, (0 : ℝ))) := Manifold.isSmoothEmbedding_prodMk_const _
  apply isSmoothEmbedding_of_interior_GSF carrier radialSharedParam_smooth he
  · intro t
    change Injective (mfderiv torusModel (𝓡∂ 3)
      (fun t : Torus => radialSharedCollar (t, 0)) t)
    have hloc := radialSharedCollar.isLocalDiffeomorphAt signedCollarModel (𝓡∂ 3) ∞
      (radialSharedParam_source t)
    have ho : Injective (mfderiv signedCollarModel (𝓡∂ 3) radialSharedCollar (t, 0)) := by
      change Injective (hloc.mfderivToContinuousLinearEquiv (by simp))
      exact (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
    have hm : MDifferentiableAt signedCollarModel (𝓡∂ 3) radialSharedCollar (t, 0) :=
      (radialSharedCollar.contMDiffOn_toFun.contMDiffAt
        (radialSharedCollar.open_source.mem_nhds (radialSharedParam_source t))).mdifferentiableAt
          (by simp)
    have hc := mfderiv_comp t hm (hincl.contMDiff.mdifferentiableAt (by simp))
    exact hc.symm ▸ ho.comp (hincl.isImmersion.mfderiv_injective (by simp) t)
  · intro t
    exact radialSharedCollar_interior (radialSharedCollar.map_source (radialSharedParam_source t))

theorem radialCusp_boundary_height : (radialVertices.vertex (0 : Fin 2)).boundaryImage =
    {p | height p = (0 : ℝ)} ∪ {p | height p = -(1 / 4 : ℝ)} := by
  change cuspToCarrier '' (𝓡∂ 3).boundary cuspSet = _
  rw [cusp_boundary_eq_ends, image_union, ← range_comp, ← range_comp]
  change range (fun t => cuspToCarrier (cuspEnd false t)) ∪
    range (fun t => cuspToCarrier (cuspEnd true t)) = _
  exact congrArg₂ (fun A B : Set carrier.Carrier => A ∪ B)
    (cuspEnd_map_range false) (cuspEnd_map_range true)

theorem radialSlim_boundary_height : (radialVertices.vertex (1 : Fin 2)).boundaryImage =
    {p | height p = -(1 / 4 : ℝ)} ∪ {p | height p = -(1 / 2 : ℝ)} := by
  have hb : (𝓡∂ 3).boundary slimSet = range (slimEnd false) ∪ range (slimEnd true) := by
    rw [slimEnd_range false, slimEnd_range true]
    ext p
    change (𝓡∂ 3).IsBoundaryPoint p ↔ cliffordHeight p.val = -(1 / 4 : ℝ) ∨
      cliffordHeight p.val = -(1 / 2 : ℝ)
    exact slim_boundary_iff.trans or_comm
  change slimToCarrier '' (𝓡∂ 3).boundary slimSet = _
  rw [hb, image_union, ← range_comp, ← range_comp]
  change range (fun t => slimToCarrier (slimEnd false t)) ∪
    range (fun t => slimToCarrier (slimEnd true t)) = _
  exact congrArg₂ (fun A B : Set carrier.Carrier => A ∪ B)
    (slimEnd_map_range false) (slimEnd_map_range true)

theorem radialCuspSideData : ∃ ψ : Torus → cuspSet,
    IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ ψ ∧ range ψ = (cuspModelFace true).val ∧
      ∀ t, cuspToCarrier (ψ t) = radialSharedCollar (t, 0) := by
  apply exists_sideParam_torus_GSF cuspPiece (cuspModelFace true) radialSharedParam_embedding
  · change range (fun t : Torus => radialSharedCollar (t, 0)) =
      cuspToCarrier '' range (cuspEnd true)
    rw [← range_comp]
    have hc : range (fun t => cuspToCarrier (cuspEnd true t)) =
        {p | height p = -(1 / 4 : ℝ)} := cuspEnd_map_range true
    exact radialSharedCollar_zero.trans hc.symm
  · rintro p ⟨t, rfl⟩
    exact radialSharedCollar_interior (radialSharedCollar.map_source (radialSharedParam_source t))

theorem radialSlimSideData : ∃ ψ : Torus → slimSet,
    IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ ψ ∧ range ψ = (slimModelFace false).val ∧
      ∀ t, slimToCarrier (ψ t) = radialSharedCollar (t, 0) := by
  apply exists_sideParam_torus_GSF slimPiece (slimModelFace false) radialSharedParam_embedding
  · change range (fun t : Torus => radialSharedCollar (t, 0)) =
      slimToCarrier '' range (slimEnd false)
    rw [← range_comp]
    have hs : range (fun t => slimToCarrier (slimEnd false t)) =
        {p | height p = -(1 / 4 : ℝ)} := slimEnd_map_range false
    exact radialSharedCollar_zero.trans hs.symm
  · rintro p ⟨t, rfl⟩
    exact radialSharedCollar_interior (radialSharedCollar.map_source (radialSharedParam_source t))

def radialCuspSideParam : Torus → cuspSet := Classical.choose radialCuspSideData

def radialSlimSideParam : Torus → slimSet := Classical.choose radialSlimSideData

theorem radialCuspSideParam_embedding :
    IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ radialCuspSideParam :=
  (Classical.choose_spec radialCuspSideData).1

theorem radialSlimSideParam_embedding :
    IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ radialSlimSideParam :=
  (Classical.choose_spec radialSlimSideData).1

theorem radialCuspSideParam_range : range radialCuspSideParam = (cuspModelFace true).val :=
  (Classical.choose_spec radialCuspSideData).2.1

theorem radialSlimSideParam_range : range radialSlimSideParam = (slimModelFace false).val :=
  (Classical.choose_spec radialSlimSideData).2.1

theorem radialCuspSideParam_map (t : Torus) :
    cuspToCarrier (radialCuspSideParam t) = radialSharedCollar (t, 0) :=
  (Classical.choose_spec radialCuspSideData).2.2 t

theorem radialSlimSideParam_map (t : Torus) :
    slimToCarrier (radialSlimSideParam t) = radialSharedCollar (t, 0) :=
  (Classical.choose_spec radialSlimSideData).2.2 t

end GC.GraphManifold.Assembly.FC39P0.X135Radial
