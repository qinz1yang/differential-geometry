import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitNativeSystem
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationPassive
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationModels
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationInitial

/-!
# The mixed stages on the capped components

Lane MS, tier MS5 (design `handoffs/20261004-design-ms-mixed-split.md` §3.5, review 30 §5.3, §6.1).
A product certificate of a piece of a `MixedClosedSystem` is a planar base, an INTRINSIC
diffeomorphism of the product onto the piece, a port bijection and the collar equation
(`MixedClosedSystem.ProductCert`); it survives restriction to a component and becomes Codex X45's
`RelativeCapNativeProduct` of the reindexed cut system (`ProductCert.toNative`).

For the capped system of a mixed split every non-frozen piece has one (`capCert`): a passive
product piece the product of the fixed presentation (the stage's own product, shrunk by `δ₂`;
the reparametrisation is the identity on its sides, `capProduct`) followed by the recast onto
the native piece, a capped solid torus the intrinsic model `discTheta : D² × S¹ ≃ cutModelPiece 1`
(its map into the capped manifold is `D.solid t ∘ discTheta⁻¹`). A frozen piece carries the old
hyperbolic geometry on its old component carrier together with the recast onto the native piece
(`capPart_frozen_geom`). `capStage c` is the mixed stage of the component `c`: the presentation of
the restricted cut system, frozen pieces the passive frozen pieces, protected seams exactly the
surviving old protected seams, product pieces from `capCert` through X45's `.piece`, hyperbolic
geometries through the transport of X45's `Build`, and every side of a frozen piece protected
because it is an old side of an old frozen piece (`capStage_left_prot`, `capStage_right_prot`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace MixedClosedSystem

variable {kind : CarrierModel}

structure ProductCert {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (P : MixedClosedSystem.{u} M kind) (i : P.Piece)
    (k : ℕ) where
  base : PlanarBase.{u} k
  map : (base.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model base.surface.kind).prod (𝓡 1),
    kind.model⟯ P.Part i
  port : Fin k ≃ Fin (P.torusCount i)
  collar : ∀ l p, p ∈ halfCollarSource →
    P.collar i (port l) p = map (base.collar l (p.1.1, p.2), p.1.2)

def ProductCert.restrict {N : ClosedOrientedManifold.{u} 3}
    {P : MixedClosedSystem.{u} N.Carrier kind}
    {K : ConnectedComponents N.Carrier} {hK : ∃ i, P.pieceComp i = K}
    {i : (P.restrict K hK).Piece} {k : ℕ} (C : P.ProductCert i.1 k) :
    (P.restrict K hK).ProductCert i k :=
  ⟨C.base, C.map, C.port, C.collar⟩

def ProductCert.toNative {A : ConnectedClosedOrientedManifold.{u} 3}
    {P : MixedClosedSystem.{u} A.Carrier kind} {z : Fin P.toCutSystem.count} {k : ℕ}
    (C : P.ProductCert (P.pieceEquiv z) k) : RelativeCapNativeProduct P.toCutSystem z k :=
  ⟨C.base, C.map, C.port, C.collar⟩

theorem pieceEquiv_portEquiv_symm_fst {A : ConnectedClosedOrientedManifold.{u} 3}
    (P : MixedClosedSystem.{u} A.Carrier kind) (x : Σ i, Fin (P.torusCount i)) :
    P.pieceEquiv (P.portEquiv.symm x).1 = x.1 :=
  congrArg Sigma.fst (P.portEquiv.apply_symm_apply x)

theorem pieceEquiv_side_fst {A : ConnectedClosedOrientedManifold.{u} 3}
    (P : MixedClosedSystem.{u} A.Carrier kind) (d : Fin P.toCutSystem.seamCount) (β : Bool) :
    P.pieceEquiv (P.toCutSystem.side d β).1 = (P.side (P.seamEquiv d) β).1 :=
  P.pieceEquiv_portEquiv_symm_fst _

end MixedClosedSystem

namespace RelativeNormalization

theorem recastDiffeomorph_apply (D : CompactCarrier.{u}) (k : CarrierModel) (h : D.kind = k)
    (x : (recastCarrier D k h).Carrier) : (recastDiffeomorph D k h x : D.Carrier) = x := by
  cases D
  subst h
  rfl

namespace MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {S : σ.SplitData h}
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N T} {a : T.Index} {δ₂ : ℝ}
  (D : σ.SideData S K a δ₂) (hC : σ.CappedConditions S a δ₂)

instance capSystemTop (i : CapPiece σ j b) : TopologicalSpace ((capSystem D hC).Part i) :=
  capPartTop D hC i

instance capSystemCharts (i : CapPiece σ j b) :
    ChartedSpace CarrierModel.withBoundary.Space ((capSystem D hC).Part i) :=
  capPartCharts D hC i

instance capSystemTop' (i : (capSystem D hC).Piece) : TopologicalSpace ((capSystem D hC).Part i) :=
  capPartTop D hC i

instance capSystemCharts' (i : (capSystem D hC).Piece) :
    ChartedSpace CarrierModel.withBoundary.Space ((capSystem D hC).Part i) :=
  capPartCharts D hC i

variable (σ j b) in
def capKind : CapPiece σ j b → ℕ
  | .inl k => σ.kind k.1
  | .inr _ => 1

variable (σ j b) in
def capFrozen : CapPiece σ j b → Prop
  | .inl k => k.1 ∈ σ.frozen
  | .inr _ => False

def passiveRecast (k : Fin σ.toTorus.components.count) :
    (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k).Carrier ≃ₘ⟮
      (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k).model,
      CarrierModel.withBoundary.model⟯ (capCut D hC).Piece k :=
  (recastDiffeomorph ((capTorus D hC).Component k) .withBoundary (capTorus_kind D hC)).symm

theorem passivePt_passiveRecast (k : Fin σ.toTorus.components.count)
    (x : (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k).Carrier) :
    passivePt D hC (passiveRecast D hC k x) = x.val := by
  have e1 := recastDiffeomorph_apply ((capTorus D hC).Component k) .withBoundary
    (capTorus_kind D hC) (passiveRecast D hC k x)
  exact congrArg Subtype.val (e1.symm.trans ((recastDiffeomorph ((capTorus D hC).Component k)
    .withBoundary (capTorus_kind D hC)).apply_symm_apply x))

theorem capReparam_of_owned {k : Fin σ.toTorus.components.count} (hkH : k ≠ σ.hostPiece j b)
    (s : σ.toTorus.OwnedSide k) : capReparam D s.val = Diffeomorph.refl torusModel Torus ∞ := by
  obtain ⟨c, β, hcβ⟩ := σ.exists_seamSide_eq s.val
  have hp : σ.seamPiece c β = k := by rw [← σ.sidePiece_seamSide, hcβ]; exact s.2
  rw [← hcβ, capReparam_seamSide, sideTwist_of_not_host D c (fun he => hkH (hp.symm.trans he))]

def capProduct (k : Fin σ.toTorus.components.count) (hkH : k ≠ σ.hostPiece j b)
    (hk : k ∉ σ.frozen) : ProductFibredPiece (capTorus D hC) k (σ.kind k) :=
  (σ.toTorus.reparam (capReparam D)).shrinkPiece k (σ.piece k hk).base
    ((σ.piece k hk).port.trans (σ.toTorus.reparamOwnedSide (capReparam D) k))
    (σ.piece k hk).trivialization hC.pos hC.le_one fun l p hp _ => by
      have hcol : σ.toTorus.pieceCollar k ((σ.piece k hk).port l)
          (capReparam D ((σ.piece k hk).port l).val p.1, p.2) =
          (σ.piece k hk).trivialization ((σ.piece k hk).base.collar l (p.1.1, p.2), p.1.2) := by
        rw [capReparam_of_owned D hkH ((σ.piece k hk).port l)]
        exact (σ.piece k hk).collar_eq l p hp
      exact Subtype.ext ((TorusPresentation.pieceCollar_apply _ _ _ hp).trans
        ((congrArg (fun c => c p) (TorusPresentation.reparam_sideCollar σ.toTorus (capReparam D)
          ((σ.piece k hk).port l).val)).trans
          ((TorusPresentation.pieceCollar_apply σ.toTorus k ((σ.piece k hk).port l)
            (p := (capReparam D ((σ.piece k hk).port l).val p.1, p.2)) hp).symm.trans
              (congrArg Subtype.val hcol))))

def passivePort (k : Fin (capTorus D hC).components.count) (hkH : k ≠ σ.hostPiece j b)
    (hk : k ∉ σ.frozen) : Fin (σ.kind k) ≃ Fin ((capCut D hC).torusCount k) :=
  (capProduct D hC k hkH hk).port.trans (Fintype.equivFin _)

theorem passive_collar_val (k : Fin (capTorus D hC).components.count)
    (hkH : k ≠ σ.hostPiece j b) (hk : k ∉ σ.frozen) (l : Fin (σ.kind k))
    (p : Torus × EuclideanHalfSpace 1) :
    passivePt D hC ((capCut D hC).collar k (passivePort D hC k hkH hk l) p) =
      ((capTorus D hC).pieceCollar k ((capProduct D hC k hkH hk).port l) p).val := by
  refine (congrArg Subtype.val (recastPD_apply ((capTorus D hC).Component k)
    .withBoundary (capTorus_kind D hC) _ p)).trans ?_
  change ((capTorus D hC).pieceCollar k ((Fintype.equivFin _).symm
    ((Fintype.equivFin _) ((capProduct D hC k hkH hk).port l))) p).val = _
  rw [Equiv.symm_apply_apply]

def capCert : ∀ i : CapPiece σ j b, ¬ capFrozen σ j b i →
    (capSystem D hC).ProductCert i (capKind σ j b i)
  | .inl k, hk =>
    { base := (capProduct D hC k.1 k.2.2 hk).base
      map := show _ ≃ₘ⟮_, CarrierModel.withBoundary.model⟯ (capCut D hC).Piece k.1 from
        (capProduct D hC k.1 k.2.2 hk).trivialization.trans (passiveRecast D hC k.1)
      port := passivePort D hC k.1 k.2.2 hk
      collar := fun l p hp => by
        apply Subtype.ext
        refine (passive_collar_val D hC k.1 k.2.2 hk l p).trans ?_
        refine Eq.trans ?_ (passivePt_passiveRecast D hC k.1 _).symm
        exact congrArg Subtype.val ((capProduct D hC k.1 k.2.2 hk).collar_eq l p hp) }
  | .inr t, _ =>
    { base := discPlanarBase.{u} 1
      map := discTheta
      port := Equiv.refl (Fin 1)
      collar := fun l p _ => by
        have hl : l = ⟨0, Nat.one_pos⟩ := Fin.ext (by
          have := l.isLt
          change l.val < 1 at this
          change l.val = 0
          omega)
        subst hl
        exact capCollar_inr_apply D hC t 0 p }

theorem capKind_mem : ∀ i : CapPiece σ j b, ¬ capFrozen σ j b i →
    capKind σ j b i ∈ ({1, 2, 3} : Finset ℕ)
  | .inl k, hk => σ.kind_mem k.1 hk
  | .inr _, _ => by simp [capKind]

theorem capPart_frozen_geom : ∀ i : CapPiece σ j b, capFrozen σ j b i →
    ∃ (C : CompactCarrier.{u})
      (_ : C.Carrier ≃ₘ⟮C.model, CarrierModel.withBoundary.model⟯ (capSystem D hC).Part i)
      (g : C.InteriorGeometry ⊤),
      letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior ⊤)
      letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior ⊤)
      g.model = .hyperbolic
  | .inl k, hk => by
    obtain ⟨g, hg⟩ := σ.hyperbolic k.1 hk
    obtain ⟨g', hg'⟩ := relativeCapComponentHyperbolicProfile σ.toTorus k.1 g hg
    exact ⟨componentCarrier σ.toTorus.cutCarrier σ.toTorus.components k.1,
      passiveRecast D hC k.1, g', hg'⟩
  | .inr _, hf => hf.elim

theorem capSide_frozen_prot (c' : CapSeam σ j) (β : Bool)
    (hf : capFrozen σ j b (capSide D hC c' β).1) : c'.1 ∈ σ.prot := by
  by_cases hH : σ.seamPiece c'.1 β = σ.hostPiece j b
  · rw [capSide_of_host D hC c' hH] at hf
    exact hf.elim
  · rw [capSide_of_not_host D hC c' hH] at hf
    change ((capCut D hC).side c'.1 β).1 ∈ σ.frozen at hf
    rw [capCut_side_fst] at hf
    cases β
    · exact σ.right_prot c'.1 hf
    · exact σ.left_prot c'.1 hf

open Classical in
def capStage (c : ConnectedComponents N.Carrier) : MixedStage (N.component c) where
  toTorus := (capCutSystem D hC c).toTorusPresentation
  prot := Finset.univ.filter fun d => ((capComponentSystem D hC c).seamEquiv d).1.1 ∈ σ.prot
  frozen := Finset.univ.filter fun z =>
    capFrozen σ j b ((capComponentSystem D hC c).pieceEquiv z).1
  hyperbolic z hz := by
    obtain ⟨C, e, g, hg⟩ := capPart_frozen_geom D hC _ (Finset.mem_filter.mp hz).2
    let e' : C.Carrier ≃ₘ⟮C.model, (relativeCapNativePieceCarrier (capCutSystem D hC c) z).model⟯
        (relativeCapNativePieceCarrier (capCutSystem D hC c) z).Carrier := e
    exact relativeCapHyperbolicProfile (pieceInteriorCongr
      ((topOpensDiffeomorph (I := C.model) C.Carrier).trans
        (e'.trans (relativeCapNativePieceDiffeomorph (capCutSystem D hC c) z)))).symm g hg
  kind z := capKind σ j b ((capComponentSystem D hC c).pieceEquiv z).1
  kind_mem z hz := capKind_mem _ fun hf => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩)
  piece z hz := (MixedClosedSystem.ProductCert.toNative (MixedClosedSystem.ProductCert.restrict
    (capCert D hC _ fun hf => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩)))).piece
  left_prot d hd := by
    have hf := (Finset.mem_filter.mp hd).2
    have e := MixedClosedSystem.pieceEquiv_side_fst (capComponentSystem D hC c) d true
    have hf' : capFrozen σ j b ((capComponentSystem D hC c).side
        ((capComponentSystem D hC c).seamEquiv d) true).1.1 := by
      rw [← e]
      exact hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, capSide_frozen_prot D hC _ true hf'⟩
  right_prot d hd := by
    have hf := (Finset.mem_filter.mp hd).2
    have e := MixedClosedSystem.pieceEquiv_side_fst (capComponentSystem D hC c) d false
    have hf' : capFrozen σ j b ((capComponentSystem D hC c).side
        ((capComponentSystem D hC c).seamEquiv d) false).1.1 := by
      rw [← e]
      exact hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, capSide_frozen_prot D hC _ false hf'⟩

end MixedStage

end RelativeNormalization

end GC.Seifert
