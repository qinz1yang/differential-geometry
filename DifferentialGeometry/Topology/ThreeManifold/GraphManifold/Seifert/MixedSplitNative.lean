import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitFixed
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitSystem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativePieceAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ContractClosed

/-!
# The native pieces, sides and seams of a mixed split

Lane MS, tier MS4 (design `handoffs/20261004-design-ms-mixed-split.md` §3.3). Fix side data `D`
and capping conditions `hC` of a split seam `j` on side `b` of a mixed stage `σ`, and the fixed
presentation `capTorus D hC = σ.fixedCapPresentation (capReparam D) δ₂` (`MixedSplitFixed`). Its
cut system of kind `.withBoundary` (`capCut`, Lane BA's `cutSystemOfKind`) supplies the passive
pieces: every old piece other than the solid torus `V` and the host `H` with its actual compact
component carrier and the half collars of the fixed presentation. The capped manifold receives
these pieces through the core (`capMap`, `SplitTube.coreMap K` after the cut map), and the two
capped solid tori of `D` over the regular model `cutModelPiece 1` of the round disc.

The sides of the surviving seams `c ≠ j` are those of the fixed presentation on passive pieces
and the unique port of a capped solid torus on a host port (`capSide`, as lane N2c's
`cappedSide`); `recover` reads them back as sides of the old presentation, so `capSide` is a
bijection onto the ports (`capSide_bijective`). The seam charts are the fixed seams read through
the core (`capSeam`), exact on the passive sides (`capSeam_neg`, `capSeam_pos`, from the cut
system) and on the host ports through `solid_collar_eq_fixed`.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {S : σ.SplitData h}
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N T} {a : T.Index} {δ₂ : ℝ}
  (D : σ.SideData S K a δ₂) (hC : σ.CappedConditions S a δ₂)

abbrev capTorus : TorusPresentation (NoCuts.carrier Q) :=
  σ.fixedCapPresentation (capReparam D) hC.pos hC.le_one

theorem capTorus_kind : (capTorus D hC).cutCarrier.kind = .withBoundary :=
  TorusPresentation.kind_eq_withBoundary_of_pairing_count_pos _ (Fin.pos j)

abbrev capCut : EmbeddedCutSystem (NoCuts.carrier Q) .withBoundary :=
  (capTorus D hC).cutSystemOfKind .withBoundary (capTorus_kind D hC)

instance capCutTop (k : Fin σ.toTorus.components.count) :
    TopologicalSpace ((capCut D hC).Piece k) :=
  (capCut D hC).topology k

instance capCutCharts (k : Fin σ.toTorus.components.count) :
    ChartedSpace CarrierModel.withBoundary.Space ((capCut D hC).Piece k) :=
  (capCut D hC).charts k

instance capCutManifold (k : Fin σ.toTorus.components.count) :
    IsManifold CarrierModel.withBoundary.model ∞ ((capCut D hC).Piece k) :=
  (capCut D hC).manifold k

def passivePt {k : Fin σ.toTorus.components.count} (q : (capCut D hC).Piece k) :
    (capTorus D hC).cutCarrier.Carrier :=
  Subtype.val (show ↥((capTorus D hC).components.piece k) from q)

theorem passivePt_mem {k : Fin σ.toTorus.components.count} (q : (capCut D hC).Piece k) :
    passivePt D hC q ∈ (capTorus D hC).components.piece k :=
  Subtype.property (show ↥((capTorus D hC).components.piece k) from q)

theorem capCut_map {k : Fin σ.toTorus.components.count} (q : (capCut D hC).Piece k) :
    (capCut D hC).map k q = σ.toTorus.cutMap (passivePt D hC q) := rfl

variable (σ j b) in
abbrev CapPiece : Type :=
  {k : Fin σ.toTorus.components.count // k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b} ⊕ Bool

variable (σ j) in
abbrev CapSeam : Type := {c : Fin σ.toTorus.pairing.count // c ≠ j}

def discTheta :
    ((discPlanarBase.{u} 1).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1), 𝓡∂ 3⟯ cutModelPiece.{u} 1 :=
  (discPlanarBase.{u} 1).cutModelTrivialization (by simp)

def capPart : CapPiece σ j b → Type u
  | .inl k => (capCut D hC).Piece k.1
  | .inr _ => cutModelPiece.{u} 1

instance capPartTop : ∀ i, TopologicalSpace (capPart D hC i)
  | .inl k => (capCut D hC).topology k.1
  | .inr _ => inferInstanceAs (TopologicalSpace (cutModelPiece.{u} 1))

instance capPartCharts : ∀ i, ChartedSpace CarrierModel.withBoundary.Space (capPart D hC i)
  | .inl k => (capCut D hC).charts k.1
  | .inr _ => inferInstanceAs (ChartedSpace (EuclideanHalfSpace 3) (cutModelPiece.{u} 1))

instance capPartManifold : ∀ i, IsManifold CarrierModel.withBoundary.model ∞ (capPart D hC i)
  | .inl k => (capCut D hC).manifold k.1
  | .inr _ => inferInstanceAs (IsManifold (𝓡∂ 3) ∞ (cutModelPiece.{u} 1))

instance capPartCompact : ∀ i, CompactSpace (capPart D hC i)
  | .inl k => (capCut D hC).compact k.1
  | .inr _ => discTheta.toHomeomorph.compactSpace

instance capPartT2 : ∀ i, T2Space (capPart D hC i)
  | .inl k => (capCut D hC).hausdorff k.1
  | .inr _ => inferInstanceAs (T2Space (cutModelPiece.{u} 1))

instance capPartSecond : ∀ i, SecondCountableTopology (capPart D hC i)
  | .inl k => (capCut D hC).secondCountable k.1
  | .inr _ => inferInstanceAs (SecondCountableTopology (cutModelPiece.{u} 1))

instance capPartConnected : ∀ i, ConnectedSpace (capPart D hC i)
  | .inl k => (capCut D hC).connected k.1
  | .inr _ => discTheta.toHomeomorph.surjective.connectedSpace discTheta.continuous

def capMap : ∀ i, capPart D hC i → N.Carrier
  | .inl k => fun q => SplitTube.coreMap K ((capCut D hC).map k.1 q)
  | .inr t => fun q => D.solid t (discTheta.symm q)

def capTorusCount : CapPiece σ j b → ℕ
  | .inl k => (capCut D hC).torusCount k.1
  | .inr _ => 1

def capCollar : ∀ i, Fin (capTorusCount D hC i) →
    PartialDiffeomorph halfCollarModel CarrierModel.withBoundary.model
      (Torus × EuclideanHalfSpace 1) (capPart D hC i) ∞
  | .inl k => (capCut D hC).collar k.1
  | .inr _ => fun _ => trivCollar ((discPlanarBase.{u} 1).collar 0) discTheta

theorem capMap_inl (k : {k : Fin σ.toTorus.components.count //
    k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b}) (q : capPart D hC (.inl k)) :
    capMap D hC (.inl k) q = SplitTube.coreMap K (σ.toTorus.cutMap
      (passivePt D hC (show (capCut D hC).Piece k.1 from q))) := rfl

theorem passive_core (k : {k : Fin σ.toTorus.components.count //
    k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b}) (q : (capCut D hC).Piece k.1) :
    σ.toTorus.cutMap (passivePt D hC q) ∈ T.core ∧
      ∀ b' z, T.boundarySphere b' z ≠ σ.toTorus.cutMap (passivePt D hC q) :=
  hC.piece k.1 k.2.1 k.2.2 _ (passivePt_mem D hC q)

theorem isLocalDiffeomorphAt_coreMap_passive (k : {k : Fin σ.toTorus.components.count //
    k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b}) (q : (capCut D hC).Piece k.1) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (SplitTube.coreMap K)
      (σ.toTorus.cutMap (passivePt D hC q)) :=
  SplitTube.isLocalDiffeomorphAt_coreMap K ⟨_, (passive_core D hC k q).1⟩
    (SplitTube.isInteriorPoint_of_forall_ne K ⟨_, (passive_core D hC k q).1⟩
      (passive_core D hC k q).2)

theorem passive_smooth (k : {k : Fin σ.toTorus.components.count //
    k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b}) :
    ContMDiff CarrierModel.withBoundary.model (𝓡 3) ∞
      (fun q : (capCut D hC).Piece k.1 => SplitTube.coreMap K ((capCut D hC).map k.1 q)) :=
  fun q => (isLocalDiffeomorphAt_coreMap_passive D hC k q).contMDiffAt.comp q
    (((capCut D hC).smooth k.1) q)

theorem passive_mfderiv_bijective (k : {k : Fin σ.toTorus.components.count //
    k ≠ σ.seamPiece j b ∧ k ≠ σ.hostPiece j b}) (q : (capCut D hC).Piece k.1) :
    Bijective (mfderiv CarrierModel.withBoundary.model (𝓡 3)
      (fun q : (capCut D hC).Piece k.1 => SplitTube.coreMap K ((capCut D hC).map k.1 q)) q) := by
  have hcm := isLocalDiffeomorphAt_coreMap_passive D hC k q
  have hm : ContMDiffAt CarrierModel.withBoundary.model (𝓡 3) ∞ ((capCut D hC).map k.1) q :=
    ((capCut D hC).smooth k.1) q
  have hc := mfderiv_comp (f := (capCut D hC).map k.1) (g := SplitTube.coreMap K) q
    (hcm.mdifferentiableAt (by simp)) (hm.mdifferentiableAt (by simp))
  change Bijective (mfderiv CarrierModel.withBoundary.model (𝓡 3)
    (SplitTube.coreMap K ∘ (capCut D hC).map k.1) q)
  rw [hc, ContinuousLinearMap.coe_comp]
  exact (bijective_mfderiv_of_isLocalDiffeomorphAt hcm).comp
    ((capCut D hC).mfderiv_bijective k.1 q)

theorem capMap_smooth : ∀ i, ContMDiff CarrierModel.withBoundary.model (𝓡 3) ∞ (capMap D hC i)
  | .inl k => passive_smooth D hC k
  | .inr t => (D.smooth t).comp discTheta.symm.contMDiff

theorem capMap_mfderiv_bijective :
    ∀ i q, Bijective (mfderiv CarrierModel.withBoundary.model (𝓡 3) (capMap D hC i) q)
  | .inl k, q => passive_mfderiv_bijective D hC k q
  | .inr t, q => mfderiv_comp_diffeomorph_symm_bijective discTheta.symm (D.smooth t) q
      (D.mfderiv_bijective t _)

theorem capCollar_source : ∀ i l, (capCollar D hC i l).source = halfCollarSource
  | .inl k, l => (capCut D hC).collar_source k.1 l
  | .inr _, _ => trivCollar_source ((discPlanarBase.{u} 1).source_eq 0) _

theorem capCollar_disjoint :
    ∀ i, Pairwise fun l l' => Disjoint (capCollar D hC i l).target (capCollar D hC i l').target
  | .inl k => (capCut D hC).collar_disjoint k.1
  | .inr _ => fun l l' hll' => absurd (Subsingleton.elim (α := Fin 1) l l') hll'

theorem capCollar_inr_apply (t : Bool) (l : Fin 1) (p : Torus × EuclideanHalfSpace 1) :
    capCollar D hC (.inr t) l p =
      discTheta ((discPlanarBase.{u} 1).collar 0 (p.1.1, p.2), p.1.2) :=
  trivCollar_apply _ _ p

theorem capCollar_boundary_exhausted : ∀ i, CarrierModel.withBoundary.model.boundary
    (capPart D hC i) = ⋃ l, range fun t => capCollar D hC i l (t, halfZero)
  | .inl k => (capCut D hC).boundary_exhausted k.1
  | .inr t => by
    ext x
    have hx : (𝓡∂ 3).IsBoundaryPoint x ↔ ((SurfaceModel.model
        (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)).IsBoundaryPoint (discTheta.symm x) := by
      rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
        ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, not_iff_not]
      exact (discTheta.symm.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)
    change (𝓡∂ 3).IsBoundaryPoint x ↔ _
    rw [hx]
    change discTheta.symm x ∈ ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod
      (𝓡 1)).boundary _ ↔ _
    rw [ModelWithCorners.boundary_of_boundaryless_right,
      (discPlanarBase.{u} 1).boundary_exhausted]
    constructor
    · rintro ⟨hb, -⟩
      obtain ⟨l, t', ht⟩ := mem_iUnion.1 hb
      refine mem_iUnion.2 ⟨⟨0, Nat.one_pos⟩, (t', (discTheta.symm x).2), ?_⟩
      have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      change discTheta ((discPlanarBase.{u} 1).collar 0 (t', halfZero), (discTheta.symm x).2) = x
      rw [show (discPlanarBase.{u} 1).collar 0 (t', halfZero) = (discTheta.symm x).1 from ht,
        Prod.mk.eta]
      exact discTheta.apply_symm_apply x
    · rintro hx'
      obtain ⟨l, p, rfl⟩ := mem_iUnion.1 hx'
      refine ⟨mem_iUnion.2 ⟨0, p.1, ?_⟩, mem_univ _⟩
      change (discPlanarBase.{u} 1).collar 0 (p.1, halfZero) =
        (discTheta.symm (discTheta ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero), p.2))).1
      exact (congrArg Prod.fst (discTheta.symm_apply_apply
        ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero), p.2))).symm

end GC.Seifert.RelativeNormalization.MixedStage
