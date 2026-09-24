import DifferentialGeometry.Topology.Homology.LocalCharts
import DifferentialGeometry.Topology.Homology.RelativeZeroNaturality

noncomputable section

open CategoryTheory ContinuousMap Module Set

universe u

namespace DifferentialGeometry.Topology

theorem integralLocalHomologyOpenPartialHomeomorphIso_zero_vertex
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) :
    (integralLocalHomologyOpenPartialHomeomorphIso 0 e x hx).hom.hom
      (integralAbsoluteToRelative 0 ({x}ᶜ : Set X)
        (integralZeroChainClass (integralVertexChain x))) =
    integralAbsoluteToRelative 0 ({e x}ᶜ : Set Y)
      (integralZeroChainClass (integralVertexChain (e x))) := by
  let a : e.source := ⟨x, hx⟩
  let z := integralAbsoluteToRelative 0 ({a}ᶜ : Set e.source)
    (integralZeroChainClass (integralVertexChain a))
  let J := integralLocalHomologyNeighborhoodIso 0 x e.source e.open_source hx
  let g : C(e.source, Y) := ⟨fun y => e y, e.continuousOn.domRestrict⟩
  have hg : MapsTo g ({a}ᶜ : Set e.source) ({e x}ᶜ : Set Y) := by
    intro y hy heq
    exact hy (Subtype.ext (e.injOn y.property hx heq))
  have hJ : J.hom.hom z = integralAbsoluteToRelative 0 ({x}ᶜ : Set X)
      (integralZeroChainClass (integralVertexChain x)) :=
    integralRelativeHomologyMap_zero_vertex (singularSubspaceInclusion e.source)
      (neighborhoodPointComplement_mapsTo x e.source hx) a
  have hn := LinearMap.congr_fun
    (integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
      0 e x e.source e.open_source hx Subset.rfl) z
  change (integralLocalHomologyOpenPartialHomeomorphIso 0 e x hx).hom.hom
      (J.hom.hom z) = integralRelativeHomologyMap 0 g hg z at hn
  calc
    _ = (integralLocalHomologyOpenPartialHomeomorphIso 0 e x hx).hom.hom
        (J.hom.hom z) := congrArg _ hJ.symm
    _ = integralRelativeHomologyMap 0 g hg z := hn
    _ = _ := integralRelativeHomologyMap_zero_vertex g hg a

end DifferentialGeometry.Topology
