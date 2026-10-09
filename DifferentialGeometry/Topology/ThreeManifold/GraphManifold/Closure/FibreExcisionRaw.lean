import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRestriction
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreBaseExcision
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcision
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreSaturatedTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.OnePiece
import DifferentialGeometry.Topology.Embedding.Lift

/-!
The same saturated regular-fibre tube gives an actual punctured fibred carrier and a single-piece
raw presentation, retaining the excision boundary collar literally on its entire half-source.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem pullbackRange_complement {C : CompactCarrier.{u}}
    (F : CircleFibration C ⊤) (B : CompactSurface.{u})
    (b : C(B.Carrier, F.base.Carrier)) (hb : Injective b)
    (hsm : ContMDiff (SurfaceModel.model B.kind) (SurfaceModel.model F.base.kind) ∞ b)
    (hbij : ∀ y, Bijective (mfderiv (SurfaceModel.model B.kind)
      (SurfaceModel.model F.base.kind) b y))
    (V : Set F.base.Carrier) (hV : range b = Vᶜ) :
    range (F.fibreRestrictionInclusion B b hb hsm hbij) =
      {x : C.Carrier | F.projection ⟨x, trivial⟩ ∈ V}ᶜ := by
  rw [F.fibreRestrictionInclusion_range, hV]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

private def fibreExcisionComparison {C : CompactCarrier.{u}}
    (F : CircleFibration C ⊤) (B : CompactSurface.{u})
    (b : C(B.Carrier, F.base.Carrier))
    (hb : IsSmoothEmbedding (SurfaceModel.model B.kind)
      (SurfaceModel.model F.base.kind) ∞ b)
    (hbij : ∀ y, Bijective (mfderiv (SurfaceModel.model B.kind)
      (SurfaceModel.model F.base.kind) b y))
    (K : CompactCarrier.{u}) (ι : K.Carrier → C.Carrier)
    (hι : IsSmoothEmbedding K.model C.model ∞ ι)
    (hrange : range ι = range (F.fibreRestrictionInclusion B b hb.isEmbedding.injective
      hb.contMDiff hbij)) :
    K.Carrier ≃ₘ⟮K.model,
      (F.fibreRestrictionCarrier B b hb.isEmbedding.injective hb.contMDiff hbij).model⟯
      (F.fibreRestrictionCarrier B b hb.isEmbedding.injective hb.contMDiff hbij).Carrier := by
  let R := F.fibreRestrictionCarrier B b hb.isEmbedding.injective hb.contMDiff hbij
  let r := F.fibreRestrictionInclusion B b hb.isEmbedding.injective hb.contMDiff hbij
  have hi (x : K.Carrier) : F.projection ⟨ι x, trivial⟩ ∈ range b := by
    have hx : ι x ∈ range r := hrange ▸ mem_range_self x
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact y.property
  let e : K.Carrier → R.Carrier := fun x => ⟨⟨ι x, trivial⟩, hi x⟩
  have hs : range r ⊆ range ι := by rw [hrange]
  let g := hι.lift r hs
  have hg : ContMDiff R.model K.model ∞ g :=
    hι.contMDiff_lift
      (F.fibreRestrictionInclusion_smooth B b hb.isEmbedding.injective hb.contMDiff hbij) hs
  refine
    { toFun := e
      invFun := g
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := hg }
  · intro x
    apply hι.isEmbedding.injective
    exact hι.comp_lift hs (e x)
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hι.comp_lift hs y
  · exact F.fibreRestrictionLift_smooth B b hb.isEmbedding.injective hb.contMDiff hbij
      hb ι hι.contMDiff (fun x => trivial) hi

theorem exists_fibredExcisionRaw
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CircleFibration (NoCuts.carrier M) ⊤) :
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
        (PlaneLift.{u} × Circle) M.Carrier ∞,
    {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source ∧
    ∃ (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier)
      (G : RawGraphPresentation K),
      K.kind = .withBoundary ∧
      IsSmoothEmbedding K.model (𝓡 3) ∞ ι ∧
      range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Function.Bijective (mfderiv K.model (𝓡 3) ι x)) ∧
      (∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
        D.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
          M.orientation.orientation (ι x)) ∧
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 ∧
      ∀ (i : Fin G.externalCount) (p : Torus × EuclideanHalfSpace 1),
        p ∈ halfCollarSource →
        ι (G.external.collar i p) =
          φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  let C := NoCuts.carrier M
  let : SecondCountableTopology M.Carrier := C.secondCountable
  obtain ⟨β, φ, hβ, hsource, hφI, hβI, hproj, htarget, hclosed, hopen⟩ :=
    F.exists_saturatedRegularFibreTube
  have hφ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source := by
    intro p hp
    rw [hsource]
    exact ⟨hβ hp, mem_univ p.2⟩
  obtain ⟨B, b, γ, hBk, hbrange, hb, hbij, hγsource, hγ, hBboundary⟩ :=
    F.exists_fibreBaseExcision rfl β hβ hβI
  obtain ⟨K, ι, E, hKk, hι, hιrange, hKboundary, hιbij, hιO, hE⟩ :=
    CircleFibration.exists_fibreExcision_of_tube φ hφ M.orientation
  let R := F.fibreRestrictionCarrier B b hb.isEmbedding.injective hb.contMDiff hbij
  let r := F.fibreRestrictionInclusion B b hb.isEmbedding.injective hb.contMDiff hbij
  have hrange : range ι = range r := by
    rw [hιrange, hopen]
    exact (pullbackRange_complement F B b hb.isEmbedding.injective hb.contMDiff hbij
      (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1}) hbrange).symm
  let e : K.Carrier ≃ₘ⟮K.model, R.model⟯ R.Carrier :=
    fibreExcisionComparison F B b hb hbij K ι hι hrange
  let : ConnectedSpace K.Carrier := e.symm.surjective.connectedSpace e.symm.continuous
  let et : (⊤ : TopologicalSpace.Opens K.Carrier) ≃ₘ⟮K.model, R.model⟯
      (⊤ : TopologicalSpace.Opens R.Carrier) :=
    (topOpensDiffeomorph (I := K.model) K.Carrier).trans
      (e.trans (topOpensDiffeomorph (I := R.model) R.Carrier).symm)
  let H := (F.fibreRestriction B b hb.isEmbedding.injective hb.contMDiff hbij).ofDiffeomorph et
  let G := singlePieceRawPresentation K H E hKboundary
  refine ⟨φ, hφ, K, ι, G, hKk, hι, hιrange, hιbij, hιO, rfl, rfl, rfl, ?_⟩
  intro i p hp
  let k : Fin 1 := i
  change ι (E.collar k p) = _
  have hk : k = 0 := Subsingleton.elim k 0
  rw [hk]
  exact hE p.1 p.2 hp

end GC.GraphManifold
