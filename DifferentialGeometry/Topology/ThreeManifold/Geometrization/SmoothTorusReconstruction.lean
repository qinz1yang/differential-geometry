import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
namespace GC.Endpoint
universe u

def ReversesBoundaryOrientation (C : CompactCarrier)
    (l r : Torus × EuclideanHalfSpace 1 → C.Carrier) : Prop :=
  ∀ t : Torus,
    ∃ L : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ]
        TangentSpace C.model (l (t, halfZero)),
    ∃ R : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ]
        TangentSpace C.model (r (t, halfZero)),
      (∀ v, L v = mfderiv halfCollarModel C.model l (t, halfZero) v) ∧
      (∀ v, R v = mfderiv halfCollarModel C.model r (t, halfZero) v) ∧
      Orientation.map (Fin 3) L.symm (C.orientation.orientation (l (t, halfZero))) =
        -Orientation.map (Fin 3) R.symm (C.orientation.orientation (r (t, halfZero)))

structure SmoothAssembly {C : CompactCarrier.{u}} (G : TorusGluing C) where
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.Assembled]
  [smooth : IsManifold (𝓡 3) ∞ G.Assembled]
  orientation : ManifoldOrientation (𝓡 3) G.Assembled 3
  quotient_smooth : ContMDiff C.model (𝓡 3) ∞ G.quotientMap
  quotient_oriented : ∀ x : C.Carrier,
    ∃ L : TangentSpace C.model x ≃ₗ[ℝ] TangentSpace (𝓡 3) (G.quotientMap x),
      (∀ v, L v = mfderiv C.model (𝓡 3) G.quotientMap x v) ∧
      Orientation.map (Fin 3) L (C.orientation.orientation x) =
        orientation.orientation (G.quotientMap x)
  boundary_reversing : ∀ i, ReversesBoundaryOrientation C (G.leftCollar i)
    (fun p => G.rightCollar i (G.matching i p.1, p.2))
  interiorImage : TopologicalSpace.Opens G.Assembled
  interiorDiffeomorph : C.interior ≃ₘ⟮C.model, 𝓡 3⟯ interiorImage
  interior_map : ∀ x : C.interior,
    (interiorDiffeomorph x).val = G.quotientMap x.val
  seam : Fin G.count →
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) G.Assembled ∞
  seam_source : ∀ i, (seam i).source = signedCollarSource
  seam_zero : ∀ i t, seam i (t, 0) = G.torusMap i t
  seam_positive : ∀ i t s (hs : 0 ≤ s), s < 1 →
    seam i (t, s) = G.quotientMap (G.rightCollar i (G.matching i t, halfPoint s hs))
  seam_negative : ∀ i t s (hs : s ≤ 0), -1 < s →
    seam i (t, s) = G.quotientMap (G.leftCollar i (t, halfPoint (-s) (neg_nonneg.mpr hs)))

namespace SmoothAssembly
variable {C : CompactCarrier.{u}} {G : TorusGluing C}

def assembled (A : SmoothAssembly G) : ClosedOrientedManifold.{u} 3 where
  Carrier := G.Assembled
  charts := A.charts
  smooth := A.smooth
  orientation := A.orientation

def Reconstruction (A : SmoothAssembly G) (P : ConnectedClosedOrientedManifold.{u} 3) :=
  ClosedOrientedManifold.OrientedDiffeomorph A.assembled P.toClosedOrientedManifold

def torusInPrime (A : SmoothAssembly G) {P : ConnectedClosedOrientedManifold.{u} 3}
    (r : A.Reconstruction P) (i : Fin G.count) : C(Torus, P.Carrier) :=
  (show C(G.Assembled, P.Carrier) from ⟨r.val, r.val.continuous⟩).comp (G.torusMap i)

def Incompressible (A : SmoothAssembly G) {P : ConnectedClosedOrientedManifold.{u} 3}
    (r : A.Reconstruction P) : Prop :=
  ∀ i : Fin G.count, ∀ x : Torus,
    Function.Injective (FundamentalGroup.map (A.torusInPrime r i) x)

theorem torusInPrime_smooth (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (i : Fin G.count) :
    ContMDiff torusModel (𝓡 3) ∞ (A.torusInPrime r i) := by
  let := A.charts
  let := A.smooth
  have hs (t : Torus) : (t, (0 : ℝ)) ∈ (A.seam i).source := by
    rw [A.seam_source]
    exact ⟨by norm_num, by norm_num⟩
  have hc : ContMDiff torusModel (𝓡 3) ∞ (fun t => A.seam i (t, 0)) :=
    (A.seam i).contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) hs
  have ht : ContMDiff torusModel (𝓡 3) ∞ (G.torusMap i) := by
    simpa only [A.seam_zero] using hc
  exact r.val.contMDiff.comp ht

theorem torusInPrime_isEmbedding (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (i : Fin G.count) :
    _root_.Topology.IsEmbedding (A.torusInPrime r i) :=
  r.val.toHomeomorph.isEmbedding.comp (G.torusMap_isEmbedding i)

def primeSeam (A : SmoothAssembly G) {P : ConnectedClosedOrientedManifold.{u} 3}
    (r : A.Reconstruction P) (i : Fin G.count) :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) P.Carrier ∞ :=
  by
    let := A.charts
    exact (A.seam i).trans r.val.toPartialDiffeomorph

theorem primeSeam_source (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (i : Fin G.count) :
    (A.primeSeam r i).source = signedCollarSource := by
  change (A.seam i).source ∩ (A.seam i) ⁻¹' Set.univ = _
  simpa using A.seam_source i

theorem primeSeam_zero (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P)
    (i : Fin G.count) (t : Torus) :
    A.primeSeam r i (t, 0) = A.torusInPrime r i t := by
  change r.val (A.seam i (t, 0)) = r.val (G.torusMap i t)
  rw [A.seam_zero]

end SmoothAssembly
end GC.Endpoint
