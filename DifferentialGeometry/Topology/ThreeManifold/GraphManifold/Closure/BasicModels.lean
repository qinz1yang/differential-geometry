import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.OnePiece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlockAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Flatten

/-!
Actual raw certificates for the solid torus, the annulus product, and the filled Mobius model.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem solidTorusCarrier_connected : ConnectedSpace solidTorusCarrier.{u}.Carrier :=
  solidTorusDiscCircle.toHomeomorph.connectedSpace_iff.mpr inferInstance

theorem solidTorus_boundary_eq : solidTorusCarrier.{u}.model.boundary
    solidTorusCarrier.{u}.Carrier = solidTorusBoundary.image := by
  change (𝓡∂ 3).boundary solidTorusSet.{u} = solidTorusBoundary.image
  ext y
  change (𝓡∂ 3).IsBoundaryPoint y ↔ y ∈ solidTorusBoundary.image
  rw [solidTorus_isBoundaryPoint_iff]
  constructor
  · intro hy
    have hfirst : sphereFirst y.val ≠ 0 := by
      have hnorm := norm_sphereFirst_sq_eq y.val
      rw [hy] at hnorm
      intro hz
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    have hyt : y ∈ solidTorusCollar.{u}.target := hfirst
    have hh : (solidTorusCollar.{u}.symm y).2 = halfZero := by
      apply Subtype.ext
      ext i
      rw [Subsingleton.elim i 0]
      change -cliffordHeight y.val = 0
      rw [hy, neg_zero]
    have he : solidTorusCollar.{u} ((solidTorusCollar.{u}.symm y).1, halfZero) = y := by
      rw [← hh, Prod.mk.eta]
      exact solidTorusCollar.{u}.right_inv hyt
    refine mem_iUnion.mpr ⟨⟨0, Nat.one_pos⟩, ?_⟩
    exact ⟨(solidTorusCollar.{u}.symm y).1, he⟩
  · intro hy
    obtain ⟨i, t, ht⟩ := mem_iUnion.mp hy
    rw [← ht]
    exact cliffordHeight_solidTorusCollar_zero t

def solidTorusRawPresentation : RawGraphPresentation solidTorusCarrier.{u} :=
  letI := solidTorusCarrier_connected.{u}
  singlePieceRawPresentation solidTorusCarrier solidTorusFibration solidTorusBoundary
    solidTorus_boundary_eq

theorem solidTorusRawPresentation_counts :
    solidTorusRawPresentation.{u}.components.count = 1 ∧
    solidTorusRawPresentation.{u}.pairing.count = 0 ∧
    solidTorusRawPresentation.{u}.externalCount = 1 := ⟨rfl, rfl, rfl⟩

def annulusRawPresentation : RawGraphPresentation annulusCircleCarrier.{u} :=
  annulusCirclePresentation.withFibration fun i =>
    Fin.cases annulusCirclePiece.fibration (fun j => j.elim0) i

theorem annulusRawPresentation_counts :
    annulusRawPresentation.{u}.components.count = 1 ∧
    annulusRawPresentation.{u}.pairing.count = 0 ∧
    annulusRawPresentation.{u}.externalCount = 2 := ⟨rfl, rfl, rfl⟩

def twistedIBundleRawPresentation : RawGraphPresentation mobiusBundleCarrier.{u} :=
  mobiusTwistedIBundle.toRaw

theorem twistedIBundleRawPresentation_counts :
    twistedIBundleRawPresentation.{u}.components.count = 3 ∧
    twistedIBundleRawPresentation.{u}.pairing.count = 2 ∧
    twistedIBundleRawPresentation.{u}.externalCount = 1 := ⟨rfl, rfl, rfl⟩

end GC.GraphManifold
