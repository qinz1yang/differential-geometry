import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSide

/-!
# The side data of a mixed split (statement of the ledger item N4 in mixed form)

Lane MS (design `handoffs/20261004-design-ms-mixed-split.md` §1.2, §2; lead decision of
2026-10-04). `MixedStage.SideData` is the text of `ElementaryPresentation.SideData`
(`Seifert/MoveSplitCappedSide.lean`) with the elementary presentation replaced by a mixed stage:
for a split seam `j` on side `b` of `σ` with a split datum `S` (standard
products of `V` and `H`, `MixedSplitCharts`), a spherical capping `K` of `Q` along a tube system `T`
and a tube `a`, the two capped solid tori over the round disc, their ports among the host
circles other than `hostSide`, their holonomies, smoothness, bijective differentials,
injectivity, the collar formula through the host chart of `S` at height `δ₂ s`, the cap and core
covering clauses over the split region `V ∪ H` (`InSplitRegion`) and the boundary clause.

`ExistsMixedSideData` is the statement of N4 for mixed stages: for a linear split seam of a mixed
stage, any split datum and any capping along its split tube, the side data exist for every small
`δ₂`. It is the only definition of a statement in this file; it is consumed as an explicit
hypothesis by the MixedSplit producer and is the target of lane N2f's second tier. Its elementary
instance through `MixedStage.ofElementary` is the hypothesis `hN4` of
`GraphManifold/PrimeStructureSideDataProved`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

namespace MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} (S : σ.SplitData h)
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index)

def InSplitRegion (y : σ.toTorus.cutCarrier.Carrier) : Prop :=
  y ∈ σ.toTorus.components.piece (σ.seamPiece j b) ∨
    y ∈ σ.toTorus.components.piece (σ.hostPiece j b)

structure SideData (δ₂ : ℝ) where
  port : Bool → Fin 3
  port_ne : ∀ t, port t ≠ σ.hostSide h
  port_false_ne_true : port false ≠ port true
  holonomy : Bool → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  solid : Bool → (discPlanarBase.{u} 1).surface.Carrier × Circle → N.Carrier
  smooth : ∀ t, ContMDiff ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
    (𝓡 3) ∞ (solid t)
  mfderiv_bijective : ∀ t q, Function.Bijective (mfderiv
    ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)) (𝓡 3) (solid t) q)
  injective : ∀ t, Function.Injective (solid t)
  collar : ∀ t (p : Torus) (s : ℝ) (hs : 0 ≤ s), s < 1 →
    solid t ((discPlanarBase.{u} 1).collar 0 (p.1, halfPoint s hs), p.2) =
      SplitTube.coreMap K (σ.hostMap S (planarCollarFormula 3 (port t)
        (((holonomy t p).1 : ℂ), δ₂ * s), (holonomy t p).2))
  cap_mem : ∀ t w, ∃ q, solid t q = K.cap (a, t) w
  core_mem : ∀ y : σ.toTorus.cutCarrier.Carrier, σ.InSplitRegion (j := j) (b := b) y →
    σ.toTorus.cutMap y ∈ T.core → ∃ t q, solid t q = SplitTube.coreMap K (σ.toTorus.cutMap y)
  image : ∀ t q, (∃ w, solid t q = K.cap (a, t) w) ∨ ∃ y : σ.toTorus.cutCarrier.Carrier,
    σ.InSplitRegion (j := j) (b := b) y ∧ σ.toTorus.cutMap y ∈ T.core ∧
      solid t q = SplitTube.coreMap K (σ.toTorus.cutMap y)
  boundary_of_eq : ∀ q q', solid false q = solid true q' →
    ElementaryPresentation.OnSolidBoundary q ∧ ElementaryPresentation.OnSolidBoundary q'

end MixedStage

def ExistsMixedSideData : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (σ : MixedStage Q)
    {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b)
    (S : σ.SplitData h) (hlin : σ.IsLinearSeam j)
    {T : SphericalTubeSystem Q.toClosedOrientedManifold} (_ : T = σ.splitSeamTube S hlin)
    {N : ClosedOrientedManifold.{u} 3}
    (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index),
      ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (σ.SideData S K a δ₂)

end GC.Seifert.RelativeNormalization
