import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleBallVertex
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimQuadrantProducer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# FC42 sphere recursion, packet S4 (group G1): pieces and vertices along a new map; restriction to a
component carrier

Lane ASM-SPH2 (review 40 §2.4 "third layer", §2.5 "restriction along an actual clopen component").

* `PieceEmbedding.ofMap`, `ZeroModel.ofMap`, `SlimFibre.ofMap`, `SlimModel.ofMap`,
  `ClosedZeroPiece.ofMap`, `Vertex.ofMap`: the same piece manifold and the same model, with a new map
  into another carrier (`image_ofMap`, `boundaryImage_ofMap`, `IsBall.ofMap`, `ofMap_ne_closedZero`).
* Restriction to `componentCarrier Q DQ i`: `componentRestrict` (codomain restriction of a map with
  range in the piece), `PieceEmbedding.toComponent`, `Vertex.toComponent`, `EdgeHandle.toComponent`,
  `EdgeCirclePiece.toComponent`, `SphereSeam.toComponent`, `TorusSeam.toComponent`; interior points of
  the component (`mem_componentInterior_iff`), interiors of preimages, the component of a point
  (`pointComp`, `subset_piece_pointComp`), the homeomorphism `val ⁻¹' A ≃ₜ A`.
* `OpenPartialHomeomorph`: images of interiors inside the source.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASMSPH2R : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASMSPH2R : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-! ## The same piece and model with a new map -/

section OfMap

variable {W W' : CompactCarrier.{u}}

/-- The same piece manifold with a new embedding into another carrier. -/
def PieceEmbedding.ofMap (P : PieceEmbedding W) (g : P.Piece → W'.Carrier)
    (hs : ContMDiff (𝓡∂ 3) W'.model ∞ g) (hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q))
    (hi : Injective g) : PieceEmbedding W' where
  Piece := P.Piece
  map := g
  smooth := hs
  mfderiv_bijective := hb
  injective := hi

/-- The same zero model on the re-embedded piece. -/
def ZeroModel.ofMap {P : PieceEmbedding W} {g : P.Piece → W'.Carrier}
    {hs : ContMDiff (𝓡∂ 3) W'.model ∞ g} {hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q)}
    {hi : Injective g} : ZeroModel P → ZeroModel (P.ofMap g hs hb hi)
  | .ball e => .ball e
  | .solidTorus e => .solidTorus e
  | .twistedIBundle e => .twistedIBundle e
  | .puncturedRP3 c f hf hr => .puncturedRP3 c f hf hr

/-- The same slim fibre on the re-embedded piece. -/
def SlimFibre.ofMap {P : PieceEmbedding W} {g : P.Piece → W'.Carrier}
    {hs : ContMDiff (𝓡∂ 3) W'.model ∞ g} {hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q)}
    {hi : Injective g} {p : P.Piece → Circle} : SlimFibre P p → SlimFibre (P.ofMap g hs hb hi) p
  | .sphere f hf hr => .sphere f hf hr
  | .torus f hf hr => .torus f hf hr

/-- The same slim model on the re-embedded piece. -/
def SlimModel.ofMap {P : PieceEmbedding W} {g : P.Piece → W'.Carrier}
    {hs : ContMDiff (𝓡∂ 3) W'.model ∞ g} {hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q)}
    {hi : Injective g} : SlimModel P → SlimModel (P.ofMap g hs hb hi)
  | .sphereInterval e => .sphereInterval e
  | .torusInterval e => .torusInterval e
  | .overCircle p hp hsub fibre hclosed => .overCircle p hp hsub fibre.ofMap hclosed

/-- The same closed zero piece with a new map. -/
def ClosedZeroPiece.ofMap (C : ClosedZeroPiece W) (g : C.piece.Piece → W'.Carrier)
    (hs : ContMDiff (𝓡∂ 3) W'.model ∞ g) (hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q))
    (hi : Injective g) : ClosedZeroPiece W' where
  piece := C.piece.ofMap g hs hb hi
  boundary_empty := C.boundary_empty
  Q := C.Q
  metric := C.metric
  nonneg := C.nonneg
  ident := C.ident

/-- **The same vertex (piece manifold and model) with a new map into another carrier.** -/
def Vertex.ofMap : (v : Vertex W) → (g : v.piece.Piece → W'.Carrier) →
    ContMDiff (𝓡∂ 3) W'.model ∞ g → (∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q)) →
    Injective g → Vertex W'
  | .zero P m, g, hs, hb, hi => .zero (P.ofMap g hs hb hi) m.ofMap
  | .closedZero C, g, hs, hb, hi => .closedZero (C.ofMap g hs hb hi)
  | .slim P m, g, hs, hb, hi => .slim (P.ofMap g hs hb hi) m.ofMap
  | .cuspCore P e, g, hs, hb, hi => .cuspCore (P.ofMap g hs hb hi) e

namespace Vertex

theorem image_ofMap (v : Vertex W) (g : v.piece.Piece → W'.Carrier)
    (hs : ContMDiff (𝓡∂ 3) W'.model ∞ g) (hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q))
    (hi : Injective g) : (v.ofMap g hs hb hi).image = range g := by
  cases v <;> rfl

theorem boundaryImage_ofMap (v : Vertex W) (g : v.piece.Piece → W'.Carrier)
    (hs : ContMDiff (𝓡∂ 3) W'.model ∞ g) (hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q))
    (hi : Injective g) :
    (v.ofMap g hs hb hi).boundaryImage = g '' (𝓡∂ 3).boundary v.piece.Piece := by
  cases v <;> rfl

theorem IsBall.ofMap {v : Vertex W} (h : v.IsBall) (g : v.piece.Piece → W'.Carrier)
    (hs : ContMDiff (𝓡∂ 3) W'.model ∞ g) (hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q))
    (hi : Injective g) : (v.ofMap g hs hb hi).IsBall := by
  obtain ⟨P, e, rfl⟩ := h
  exact ⟨P.ofMap g hs hb hi, e, rfl⟩

theorem ofMap_ne_closedZero {v : Vertex W} (hv : ∀ C, v ≠ .closedZero C)
    (g : v.piece.Piece → W'.Carrier) (hs : ContMDiff (𝓡∂ 3) W'.model ∞ g)
    (hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q)) (hi : Injective g)
    (C' : ClosedZeroPiece W') : v.ofMap g hs hb hi ≠ .closedZero C' := by
  cases v with
  | zero P m => intro h; cases h
  | closedZero C => exact absurd rfl (hv C)
  | slim P m => intro h; cases h
  | cuspCore P e => intro h; cases h

end Vertex

end OfMap

/-! ## Images of interiors under an open partial homeomorphism -/

theorem OpenPartialHomeomorph.image_interior_of_subset_source {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {A : Set X} (hA : A ⊆ e.source) :
    e '' interior A = interior (e '' A) := by
  apply Subset.antisymm
  · exact interior_maximal (image_mono interior_subset)
      (e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hA))
  · intro y hy
    have hyT : interior (e '' A) ⊆ e.target := fun z hz => by
      obtain ⟨x, hx, rfl⟩ := interior_subset hz
      exact e.map_source (hA hx)
    have hopen : IsOpen (e.symm '' interior (e '' A)) :=
      e.symm.isOpen_image_of_subset_source isOpen_interior hyT
    have hsub : e.symm '' interior (e '' A) ⊆ A := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := interior_subset hz
      rw [e.left_inv (hA hx)]
      exact hx
    refine ⟨e.symm y, interior_maximal hsub hopen ⟨y, hy, rfl⟩, e.right_inv (hyT hy)⟩

/-! ## Restriction to a component carrier -/

section Component

variable {Q : CompactCarrier.{u}} (DQ : Q.Components) (i : Fin DQ.count)

/-- The codomain restriction of a map whose range lies in the piece `i`. -/
def componentRestrict {M : Type*} (f : M → Q.Carrier) (h : range f ⊆ (DQ.piece i : Set Q.Carrier)) :
    M → (GC.Topology.componentCarrier Q DQ i).Carrier :=
  fun q => ⟨f q, h ⟨q, rfl⟩⟩

variable {DQ i}

@[simp]
theorem componentRestrict_val {M : Type*} {f : M → Q.Carrier}
    {h : range f ⊆ (DQ.piece i : Set Q.Carrier)} (q : M) :
    (componentRestrict DQ i f h q).val = f q :=
  rfl

theorem range_componentRestrict {M : Type*} {f : M → Q.Carrier}
    (h : range f ⊆ (DQ.piece i : Set Q.Carrier)) :
    range (componentRestrict DQ i f h) = Subtype.val ⁻¹' range f := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩

theorem image_componentRestrict {M : Type*} {f : M → Q.Carrier}
    (h : range f ⊆ (DQ.piece i : Set Q.Carrier)) (A : Set M) :
    componentRestrict DQ i f h '' A = Subtype.val ⁻¹' (f '' A) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨q, hq, Subtype.ext hqx⟩

theorem componentRestrict_injective {M : Type*} {f : M → Q.Carrier}
    (h : range f ⊆ (DQ.piece i : Set Q.Carrier)) (hf : Injective f) :
    Injective (componentRestrict DQ i f h) :=
  fun _ _ hqq' => hf (congrArg Subtype.val hqq')

section Smooth

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

theorem contMDiff_componentRestrict {f : M → Q.Carrier}
    (h : range f ⊆ (DQ.piece i : Set Q.Carrier)) (hf : ContMDiff IM Q.model ∞ f) :
    ContMDiff IM (GC.Topology.componentCarrier Q DQ i).model ∞ (componentRestrict DQ i f h) :=
  (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff (J := Q.model) (DQ.piece i)
    (componentRestrict DQ i f h)).mp hf

theorem mfderiv_componentRestrict {f : M → Q.Carrier}
    (h : range f ⊆ (DQ.piece i : Set Q.Carrier)) (q : M) :
    mfderiv IM (GC.Topology.componentCarrier Q DQ i).model (componentRestrict DQ i f h) q =
      mfderiv IM Q.model f q :=
  (mfderiv_subtypeVal_comp (J := Q.model) (DQ.piece i) (componentRestrict DQ i f h) q).symm

theorem bijective_mfderiv_componentRestrict {f : M → Q.Carrier}
    (h : range f ⊆ (DQ.piece i : Set Q.Carrier)) {q : M}
    (hq : Bijective (mfderiv IM Q.model f q)) :
    Bijective (mfderiv IM (GC.Topology.componentCarrier Q DQ i).model
      (componentRestrict DQ i f h) q) := by
  rw [mfderiv_componentRestrict]
  exact hq

end Smooth

/-- Interior points of the component carrier are the interior points of `Q` in the piece. -/
theorem mem_componentInterior_iff {x : (GC.Topology.componentCarrier Q DQ i).Carrier} :
    x ∈ (GC.Topology.componentCarrier Q DQ i).interior ↔ x.val ∈ Q.interior :=
  ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := Q.model) (u := DQ.piece i)

theorem preimage_val_subset_componentInterior {A : Set Q.Carrier} (hA : A ⊆ Q.interior) :
    (Subtype.val ⁻¹' A : Set (GC.Topology.componentCarrier Q DQ i).Carrier) ⊆
      (GC.Topology.componentCarrier Q DQ i).interior :=
  fun _ hx => mem_componentInterior_iff.mpr (hA hx)

/-- The interior of a preimage in the (open) piece is the preimage of the interior. -/
theorem interior_preimage_val (A : Set Q.Carrier) :
    interior (Subtype.val ⁻¹' A : Set (GC.Topology.componentCarrier Q DQ i).Carrier) =
      Subtype.val ⁻¹' interior A :=
  ((DQ.piece i).isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    continuous_subtype_val A).symm

/-- The homeomorphism between a preimage in the piece and the set itself. -/
def preimageValHomeomorph {A : Set Q.Carrier} (hA : A ⊆ (DQ.piece i : Set Q.Carrier)) :
    ((Subtype.val : DQ.piece i → Q.Carrier) ⁻¹' A) ≃ₜ A where
  toFun x := ⟨x.val.val, x.2⟩
  invFun y := ⟨⟨y.val, hA y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-! ### Pieces, vertices, handles, edge circles and seams in the component -/

/-- **A piece of `Q` inside the piece `i`, as a piece of the component carrier.** -/
def PieceEmbedding.toComponent (P : PieceEmbedding Q) (h : range P.map ⊆ (DQ.piece i : Set Q.Carrier)) :
    PieceEmbedding (GC.Topology.componentCarrier Q DQ i) :=
  P.ofMap (componentRestrict DQ i P.map h) (contMDiff_componentRestrict h P.smooth)
    (fun q => bijective_mfderiv_componentRestrict h (P.mfderiv_bijective q))
    (componentRestrict_injective h P.injective)

theorem PieceEmbedding.range_toComponent (P : PieceEmbedding Q)
    (h : range P.map ⊆ (DQ.piece i : Set Q.Carrier)) :
    range (P.toComponent h).map = Subtype.val ⁻¹' range P.map :=
  range_componentRestrict h

theorem PieceEmbedding.toComponent_map_val (P : PieceEmbedding Q)
    (h : range P.map ⊆ (DQ.piece i : Set Q.Carrier)) (q : P.Piece) :
    ((P.toComponent h).map q).val = P.map q :=
  rfl

theorem Vertex.range_piece_subset {v : Vertex Q} (h : v.image ⊆ (DQ.piece i : Set Q.Carrier)) :
    range v.piece.map ⊆ (DQ.piece i : Set Q.Carrier) := by
  rw [← Vertex.image_eq_range_piece]
  exact h

/-- **A vertex of `Q` inside the piece `i`, as a vertex of the component carrier.** -/
def Vertex.toComponent (v : Vertex Q) (h : v.image ⊆ (DQ.piece i : Set Q.Carrier)) :
    Vertex (GC.Topology.componentCarrier Q DQ i) :=
  v.ofMap (componentRestrict DQ i v.piece.map (Vertex.range_piece_subset h))
    (contMDiff_componentRestrict _ v.piece.smooth)
    (fun q => bijective_mfderiv_componentRestrict _ (v.piece.mfderiv_bijective q))
    (componentRestrict_injective _ v.piece.injective)

theorem Vertex.image_toComponent (v : Vertex Q) (h : v.image ⊆ (DQ.piece i : Set Q.Carrier)) :
    (v.toComponent h).image = Subtype.val ⁻¹' v.image := by
  rw [Vertex.toComponent, Vertex.image_ofMap, range_componentRestrict, Vertex.image_eq_range_piece]

theorem Vertex.boundaryImage_toComponent (v : Vertex Q)
    (h : v.image ⊆ (DQ.piece i : Set Q.Carrier)) :
    (v.toComponent h).boundaryImage = Subtype.val ⁻¹' v.boundaryImage := by
  rw [Vertex.toComponent, Vertex.boundaryImage_ofMap, image_componentRestrict]
  rfl

theorem Vertex.IsBall.toComponent {v : Vertex Q} (hv : v.IsBall)
    (h : v.image ⊆ (DQ.piece i : Set Q.Carrier)) : (v.toComponent h).IsBall :=
  hv.ofMap _ _ _ _

theorem Vertex.toComponent_ne_closedZero {v : Vertex Q} (hv : ∀ C, v ≠ .closedZero C)
    (h : v.image ⊆ (DQ.piece i : Set Q.Carrier))
    (C' : ClosedZeroPiece (GC.Topology.componentCarrier Q DQ i)) : v.toComponent h ≠ .closedZero C' :=
  Vertex.ofMap_ne_closedZero hv _ _ _ _ C'

/-- **A handle of `Q` inside the piece `i`, in the component carrier.** -/
def EdgeHandle.toComponent (H : EdgeHandle Q) (h : range H.map ⊆ (DQ.piece i : Set Q.Carrier)) :
    EdgeHandle (GC.Topology.componentCarrier Q DQ i) where
  map := componentRestrict DQ i H.map h
  smooth := contMDiff_componentRestrict h H.smooth
  mfderiv_bijective p := bijective_mfderiv_componentRestrict h (H.mfderiv_bijective p)
  injective := componentRestrict_injective h H.injective
  interior := by
    rw [range_componentRestrict]
    exact preimage_val_subset_componentInterior H.interior

theorem EdgeHandle.toComponent_map_val (H : EdgeHandle Q)
    (h : range H.map ⊆ (DQ.piece i : Set Q.Carrier)) (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    ((H.toComponent h).map p).val = H.map p :=
  rfl

theorem EdgeHandle.range_toComponent (H : EdgeHandle Q)
    (h : range H.map ⊆ (DQ.piece i : Set Q.Carrier)) :
    range (H.toComponent h).map = Subtype.val ⁻¹' range H.map :=
  range_componentRestrict h

theorem EdgeHandle.endDisk_toComponent (H : EdgeHandle Q)
    (h : range H.map ⊆ (DQ.piece i : Set Q.Carrier)) (b : Bool) :
    (H.toComponent h).endDisk b = Subtype.val ⁻¹' H.endDisk b := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- **An edge-circle piece of `Q` inside the piece `i`, in the component carrier.** -/
def EdgeCirclePiece.toComponent (P : EdgeCirclePiece Q)
    (h : range P.piece.map ⊆ (DQ.piece i : Set Q.Carrier)) :
    EdgeCirclePiece (GC.Topology.componentCarrier Q DQ i) where
  piece := P.piece.toComponent h
  proj := P.proj
  proj_smooth := P.proj_smooth
  proj_submersion := P.proj_submersion
  boundary_submersion := P.boundary_submersion
  fibre := P.fibre
  fibre_embedding := P.fibre_embedding
  fibre_range := P.fibre_range
  interior := by
    rw [PieceEmbedding.range_toComponent]
    exact preimage_val_subset_componentInterior P.interior

theorem EdgeCirclePiece.range_toComponent (P : EdgeCirclePiece Q)
    (h : range P.piece.map ⊆ (DQ.piece i : Set Q.Carrier)) :
    range (P.toComponent h).piece.map = Subtype.val ⁻¹' range P.piece.map :=
  PieceEmbedding.range_toComponent _ h

theorem EdgeCirclePiece.image_boundary_toComponent (P : EdgeCirclePiece Q)
    (h : range P.piece.map ⊆ (DQ.piece i : Set Q.Carrier)) :
    (P.toComponent h).piece.map '' {q | (𝓡∂ 3).IsBoundaryPoint q} =
      Subtype.val ⁻¹' (P.piece.map '' {q | (𝓡∂ 3).IsBoundaryPoint q}) :=
  image_componentRestrict h _

variable (DQ i) in
theorem nonempty_piece : Nonempty (DQ.piece i) :=
  (DQ.connected i).toNonempty

/-- **A sphere seam of `Q` inside the piece `i`, in the component carrier.** -/
def SphereSeam.toComponent (S : SphereSeam Q) (h : S.collar.target ⊆ (DQ.piece i : Set Q.Carrier)) :
    SphereSeam (GC.Topology.componentCarrier Q DQ i) where
  collar := codRestrictOpens (J := Q.model) S.collar (DQ.piece i) (nonempty_piece DQ i)
  source_eq := (codRestrictOpens_source _ _ _ h).trans S.source_eq
  target_interior := by
    rw [codRestrictOpens_target]
    exact preimage_val_subset_componentInterior S.target_interior

theorem SphereSeam.toComponent_collar_val (S : SphereSeam Q)
    (h : S.collar.target ⊆ (DQ.piece i : Set Q.Carrier)) {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ S.collar.source) : ((S.toComponent h).collar p).val = S.collar p :=
  codRestrictOpens_apply S.collar (DQ.piece i) _ (h (S.collar.map_source hp))

theorem SphereSeam.toComponent_collar_target (S : SphereSeam Q)
    (h : S.collar.target ⊆ (DQ.piece i : Set Q.Carrier)) :
    (S.toComponent h).collar.target = Subtype.val ⁻¹' S.collar.target :=
  codRestrictOpens_target S.collar (DQ.piece i) _

/-- **A torus seam of `Q` inside the piece `i`, in the component carrier.** -/
def TorusSeam.toComponent (T : TorusSeam Q) (h : T.collar.target ⊆ (DQ.piece i : Set Q.Carrier)) :
    TorusSeam (GC.Topology.componentCarrier Q DQ i) where
  collar := codRestrictOpens (J := Q.model) T.collar (DQ.piece i) (nonempty_piece DQ i)
  source_eq := (codRestrictOpens_source _ _ _ h).trans T.source_eq
  target_interior := by
    rw [codRestrictOpens_target]
    exact preimage_val_subset_componentInterior T.target_interior

theorem TorusSeam.toComponent_collar_val (T : TorusSeam Q)
    (h : T.collar.target ⊆ (DQ.piece i : Set Q.Carrier)) {p : Torus × ℝ}
    (hp : p ∈ T.collar.source) : ((T.toComponent h).collar p).val = T.collar p :=
  codRestrictOpens_apply T.collar (DQ.piece i) _ (h (T.collar.map_source hp))

theorem TorusSeam.toComponent_collar_target (T : TorusSeam Q)
    (h : T.collar.target ⊆ (DQ.piece i : Set Q.Carrier)) :
    (T.toComponent h).collar.target = Subtype.val ⁻¹' T.collar.target :=
  codRestrictOpens_target T.collar (DQ.piece i) _

end Component

/-! ## The component of a point -/

section PointComp

variable {Q : CompactCarrier.{u}} (DQ : Q.Components)

/-- The component containing a point. -/
def pointComp (x : Q.Carrier) : Fin DQ.count :=
  (mem_iUnion.mp (DQ.covers ▸ mem_univ x)).choose

theorem mem_pointComp (x : Q.Carrier) : x ∈ DQ.piece (pointComp DQ x) :=
  (mem_iUnion.mp (DQ.covers ▸ mem_univ x)).choose_spec

variable {DQ}

theorem pointComp_eq_of_mem {x : Q.Carrier} {j : Fin DQ.count} (hx : x ∈ DQ.piece j) :
    pointComp DQ x = j := by
  by_contra hne
  exact Set.disjoint_left.mp (DQ.disjoint hne) (mem_pointComp DQ x) hx

theorem pointComp_eq_iff {x : Q.Carrier} {j : Fin DQ.count} : pointComp DQ x = j ↔ x ∈ DQ.piece j :=
  ⟨fun h => h ▸ mem_pointComp DQ x, pointComp_eq_of_mem⟩

/-- A preconnected set lies in the component of each of its points. -/
theorem subset_piece_pointComp {S : Set Q.Carrier} (hS : IsPreconnected S) {x : Q.Carrier}
    (hx : x ∈ S) : S ⊆ DQ.piece (pointComp DQ x) :=
  hS.subset_isClopen ⟨DQ.closed _, (DQ.piece _).isOpen⟩ ⟨x, hx, mem_pointComp DQ x⟩

theorem pointComp_eq_of_isPreconnected {S : Set Q.Carrier} (hS : IsPreconnected S) {x y : Q.Carrier}
    (hx : x ∈ S) (hy : y ∈ S) : pointComp DQ y = pointComp DQ x :=
  pointComp_eq_of_mem (subset_piece_pointComp hS hx hy)

end PointComp

end GC.GraphManifold.Assembly
