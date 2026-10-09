import DifferentialGeometry.Geometry.Collapse.LatePieceGeometry
import DifferentialGeometry.Geometry.Collapse.CutMetricTransport
import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# Cut pieces: the boundary distance and the cut-piece map on the interior (A7 CPI, T1–T2)

Let `D : TorusDecomposition M` cut a connected closed oriented 3-manifold `M` into pieces and let
`W = D.component i` be a piece, with its cut-piece map
`cutPieceMap D i : W.Carrier → M.Carrier` (`Geometry/Collapse/LatePieceGeometry.lean:12`).

* T1 (any compact carrier `W` and metric `g`): the distance to the boundary
  (`distanceToBoundary`, `Geometry/Collapse/CuspBoundary.lean:57`) is `1`-Lipschitz in `ℝ≥0∞`,
  `distanceToBoundary_le_add`, and a Riemannian ball whose radius is at most the distance of its
  centre to the boundary misses the boundary, `riemannianBallOf_disjoint_boundary`, i.e. it lies
  in the manifold interior, `riemannianBallOf_subset_interior`.
* T2: on the interior `W°` of the piece the cut-piece map is an injective `C^∞` local
  diffeomorphism (`isLocalDiffeomorph_cutPieceInteriorMap`, `injective_cutPieceInteriorMap`,
  `isLocalDiffeomorphAt_cutPieceMap`, `injOn_cutPieceMap_interior`). It is packaged as a partial
  diffeomorphism `cutPiecePartialDiffeomorph D i` whose underlying function is `cutPieceMap D i`
  itself and whose source is `W°`.

Proof of T2. An interior point of the piece is an interior point of the cut carrier
(`ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val`, the piece being open), and on the
interior of the cut carrier the quotient map is the interior diffeomorphism of the smooth
assembly (`SmoothAssembly.interior_map`,
`Topology/ThreeManifold/Geometrization/SmoothTorusReconstruction.lean:37–40`). Hence on `W°` the
cut-piece map is the composite of four local diffeomorphisms: the open inclusion of `W°` into the
interior of the cut carrier, `interiorDiffeomorph`, the open inclusion of `interiorImage`, and the
reconstruction diffeomorphism; each is injective. (The same factorisation for a closed piece is
lane A6's `isLocalDiffeomorph_cutPieceMap_of_closed`, `Geometry/Collapse/ClosedCutComponent.lean`.)
No assumption on the seams is made: the boundary points of the piece are simply excluded.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology
open Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-! ## T1: the distance to the boundary -/

section Boundary

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- The distance to the boundary is at most the distance to a given boundary point. -/
theorem distanceToBoundary_le_riemannianEDistOf {p q : W.Carrier}
    (hq : q ∈ W.model.boundary W.Carrier) :
    distanceToBoundary W g p ≤ riemannianEDistOf g p q :=
  iInf_le (fun b : W.model.boundary W.Carrier => riemannianEDistOf g p b) ⟨q, hq⟩

/-- T1. The distance to the boundary is `1`-Lipschitz for the Riemannian distance (in `ℝ≥0∞`;
both sides are `⊤` when the boundary is empty). -/
theorem distanceToBoundary_le_add (p q : W.Carrier) :
    distanceToBoundary W g p ≤ distanceToBoundary W g q + riemannianEDistOf g p q := by
  unfold distanceToBoundary
  rw [ENNReal.iInf_add]
  refine iInf_mono fun b => ?_
  calc riemannianEDistOf g p b ≤ riemannianEDistOf g p q + riemannianEDistOf g q b :=
        riemannianEDistOf_triangle g p q b
    _ = riemannianEDistOf g q b + riemannianEDistOf g p q := add_comm _ _

/-- T1. A Riemannian ball whose radius is at most the distance of its centre to the boundary
misses the boundary. -/
theorem riemannianBallOf_disjoint_boundary {p : W.Carrier} {r : ℝ}
    (hr : ENNReal.ofReal r ≤ distanceToBoundary W g p) :
    Disjoint (riemannianBallOf g p r) (W.model.boundary W.Carrier) := by
  rw [Set.disjoint_left]
  intro x hx hxb
  have hlt : riemannianEDistOf g p x < ENNReal.ofReal r := hx
  exact (lt_irrefl _) ((distanceToBoundary_le_riemannianEDistOf W g hxb).trans_lt
    (hlt.trans_le hr))

/-- T1, interior form: such a ball lies in the manifold interior of `W`. -/
theorem riemannianBallOf_subset_interior {p : W.Carrier} {r : ℝ}
    (hr : ENNReal.ofReal r ≤ distanceToBoundary W g p) :
    riemannianBallOf g p r ⊆ W.model.interior W.Carrier := by
  intro x hx
  rw [← W.model.compl_boundary]
  exact Set.disjoint_left.mp (riemannianBallOf_disjoint_boundary W g hr) hx

/-- T1, closed balls of smaller radius: for `0 ≤ L < r` the closed ball of radius `L` lies in
the manifold interior. -/
theorem riemannianClosedBallOf_subset_interior {p : W.Carrier} {r L : ℝ} (hL : 0 ≤ L)
    (hLr : L < r) (hr : ENNReal.ofReal r ≤ distanceToBoundary W g p) :
    riemannianClosedBallOf g p L ⊆ W.model.interior W.Carrier := by
  intro x hx
  apply riemannianBallOf_subset_interior W g hr
  have hle : riemannianEDistOf g p x ≤ ENNReal.ofReal L := hx
  exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hL.trans_lt hLr)).mpr hLr)

end Boundary

/-! ## An injective local diffeomorphism on an open set is a partial diffeomorphism -/

section OfInjOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]

/-- A map that is smooth on an open set `s`, injective on `s`, and whose restriction to `s` is a
local diffeomorphism, is a partial diffeomorphism with source `s`, target `f '' s`, and underlying
function `f` itself (the inverse is `Function.invFunOn f s`). -/
def partialDiffeomorphOfInjOn [Nonempty X] (f : X → Y) (s : TopologicalSpace.Opens X)
    (hf : ContMDiffOn I J ∞ f s) (hF : IsLocalDiffeomorph I J ∞ (fun x : s => f x))
    (hinj : InjOn f s) : PartialDiffeomorph I J X Y ∞ where
  toFun := f
  invFun := Function.invFunOn f s
  source := s
  target := f '' s
  map_source' x hx := ⟨x, hx, rfl⟩
  map_target' y hy := Function.invFunOn_mem hy
  left_inv' x hx := hinj.leftInvOn_invFunOn hx
  right_inv' y hy := Function.invFunOn_eq hy
  open_source := s.isOpen
  open_target := by
    have hr : Set.range (fun x : s => f x) = f '' s := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [← hr]
    exact hF.isOpen_range
  contMDiffOn_toFun := hf
  contMDiffOn_invFun := by
    rintro y ⟨x₀, hx₀, rfl⟩
    let z₀ : s := ⟨x₀, hx₀⟩
    have hz := hF z₀
    have hinv : ContMDiffAt J I ∞ (fun y => (hz.localInverse y : X)) (f x₀) :=
      contMDiff_subtype_val.contMDiffAt.comp (f x₀) hz.contMDiffAt_localInverse
    refine (hinv.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hz.localInverse.open_source.mem_nhds hz.localInverse_mem_source] with y hy
    have hright : f (hz.localInverse y : X) = y := hz.localInverse_right_inv hy
    have hmem : ∃ x ∈ (s : Set X), f x = y := ⟨_, (hz.localInverse y).property, hright⟩
    exact hinj (Function.invFunOn_mem hmem) (hz.localInverse y).property
      ((Function.invFunOn_eq hmem).trans hright.symm)

@[simp]
theorem coe_partialDiffeomorphOfInjOn [Nonempty X] (f : X → Y) (s : TopologicalSpace.Opens X)
    (hf : ContMDiffOn I J ∞ f s) (hF : IsLocalDiffeomorph I J ∞ (fun x : s => f x))
    (hinj : InjOn f s) : ⇑(partialDiffeomorphOfInjOn f s hf hF hinj) = f := rfl

@[simp]
theorem partialDiffeomorphOfInjOn_source [Nonempty X] (f : X → Y)
    (s : TopologicalSpace.Opens X)
    (hf : ContMDiffOn I J ∞ f s) (hF : IsLocalDiffeomorph I J ∞ (fun x : s => f x))
    (hinj : InjOn f s) : (partialDiffeomorphOfInjOn f s hf hF hinj).source = s := rfl

@[simp]
theorem partialDiffeomorphOfInjOn_target [Nonempty X] (f : X → Y)
    (s : TopologicalSpace.Opens X)
    (hf : ContMDiffOn I J ∞ f s) (hF : IsLocalDiffeomorph I J ∞ (fun x : s => f x))
    (hinj : InjOn f s) : (partialDiffeomorphOfInjOn f s hf hF hinj).target = f '' s := rfl

end OfInjOn

/-! ## T2: the cut-piece map on the interior of the piece -/

section CutPiece

variable {M : ConnectedClosedOrientedManifold.{u} 3}

/-- An interior point of a cut piece is an interior point of the cut carrier. -/
theorem val_mem_carrier_interior (D : TorusDecomposition M) (i : Fin D.components.count)
    {x : D.components.piece i}
    (hx : x ∈ (D.component i).model.interior (D.component i).Carrier) :
    x.val ∈ D.carrier.interior := by
  have hxi : D.carrier.model.IsInteriorPoint x := hx
  exact D.carrier.model.isInteriorPoint_iff_isInteriorPoint_val.mp hxi

/-- The cut-piece map restricted to the interior `W°` of the piece. -/
def cutPieceInteriorMap (D : TorusDecomposition M) (i : Fin D.components.count) :
    (D.component i).interior → M.Carrier :=
  fun x => cutPieceMap D i x.val

/-- On the interior of the piece the cut-piece map factors through the interior diffeomorphism
of the smooth assembly. -/
theorem cutPieceInteriorMap_eq (D : TorusDecomposition M) (i : Fin D.components.count)
    (x : (D.component i).interior) :
    cutPieceInteriorMap D i x =
      D.reconstruction.val
        (D.reconstructionAtlas.interiorDiffeomorph
          ⟨(x.val : D.components.piece i).val, val_mem_carrier_interior D i x.property⟩).val := by
  rw [D.reconstructionAtlas.interior_map]
  rfl

/-- T2. On the interior of the piece the cut-piece map is a `C^∞` local diffeomorphism. -/
theorem isLocalDiffeomorph_cutPieceInteriorMap (D : TorusDecomposition M)
    (i : Fin D.components.count) :
    IsLocalDiffeomorph (D.component i).model (𝓡 3) ∞ (cutPieceInteriorMap D i) := by
  let := D.reconstructionAtlas.charts
  have hint : ∀ x : (D.component i).interior,
      ((x.val : D.components.piece i).val : D.carrier.Carrier) ∈ D.carrier.interior :=
    fun x => val_mem_carrier_interior D i x.property
  have hvv : IsLocalDiffeomorph (D.component i).model D.carrier.model ∞
      (fun x : (D.component i).interior => ((x.val : D.components.piece i).val)) :=
    have h1 : IsLocalDiffeomorph (D.component i).model (D.component i).model ∞
        (Subtype.val : (D.component i).interior → (D.component i).Carrier) :=
      isLocalDiffeomorph_subtype_val _
    have h2 : IsLocalDiffeomorph (D.component i).model D.carrier.model ∞
        (fun x : (D.component i).Carrier => (x : D.components.piece i).val) :=
      isLocalDiffeomorph_subtype_val (I := D.carrier.model) (D.components.piece i)
    isLocalDiffeomorph_comp h2 h1
  have hι : IsLocalDiffeomorph (D.component i).model D.carrier.model ∞
      (fun x : (D.component i).interior =>
        (⟨(x.val : D.components.piece i).val, hint x⟩ : D.carrier.interior)) := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict (V := D.carrier.interior) hint (hvv x)
  have hΦ := D.reconstructionAtlas.interiorDiffeomorph.isLocalDiffeomorph
  have hval : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : D.reconstructionAtlas.interiorImage → D.boundary.Assembled) :=
    isLocalDiffeomorph_subtype_val _
  have hr := D.reconstruction.val.isLocalDiffeomorph
  have hcomp := isLocalDiffeomorph_comp hr
    (isLocalDiffeomorph_comp hval (isLocalDiffeomorph_comp hΦ hι))
  have heq : (⇑D.reconstruction.val ∘ Subtype.val ∘ ⇑D.reconstructionAtlas.interiorDiffeomorph ∘
      fun x : (D.component i).interior =>
        (⟨(x.val : D.components.piece i).val, hint x⟩ : D.carrier.interior)) =
        cutPieceInteriorMap D i := by
    funext x
    exact (cutPieceInteriorMap_eq D i x).symm
  rw [← heq]
  exact hcomp

/-- T2. On the interior of the piece the cut-piece map is injective. -/
theorem injective_cutPieceInteriorMap (D : TorusDecomposition M) (i : Fin D.components.count) :
    Function.Injective (cutPieceInteriorMap D i) := by
  intro x y hxy
  rw [cutPieceInteriorMap_eq D i x, cutPieceInteriorMap_eq D i y] at hxy
  have h1 := D.reconstruction.val.injective hxy
  have h2 := D.reconstructionAtlas.interiorDiffeomorph.injective (Subtype.ext h1)
  have h3 : (x.val : D.components.piece i).val = (y.val : D.components.piece i).val :=
    congrArg (fun z : D.carrier.interior => z.val) h2
  exact Subtype.ext (Subtype.ext h3)

/-- T2. At every interior point of the piece the cut-piece map is a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_cutPieceMap (D : TorusDecomposition M)
    (i : Fin D.components.count) {x : (D.component i).Carrier}
    (hx : x ∈ (D.component i).interior) :
    IsLocalDiffeomorphAt (D.component i).model (𝓡 3) ∞ (cutPieceMap D i) x := by
  have hval := isLocalDiffeomorph_subtype_val (I := (D.component i).model)
    (D.component i).interior ⟨x, hx⟩
  exact isLocalDiffeomorphAt_of_comp (isLocalDiffeomorph_cutPieceInteriorMap D i ⟨x, hx⟩) hval

instance (D : TorusDecomposition M) (i : Fin D.components.count) :
    Nonempty (D.component i).Carrier :=
  (D.components.connected i).toNonempty

/-- T2, packaged. The cut-piece map as a partial diffeomorphism with source the interior of the
piece; its underlying function is `cutPieceMap D i` (`coe_cutPiecePartialDiffeomorph`). -/
def cutPiecePartialDiffeomorph (D : TorusDecomposition M) (i : Fin D.components.count) :
    PartialDiffeomorph (D.component i).model (𝓡 3) (D.component i).Carrier M.Carrier ∞ :=
  partialDiffeomorphOfInjOn (cutPieceMap D i) (D.component i).interior
    (contMDiff_cutPieceMap D i).contMDiffOn (isLocalDiffeomorph_cutPieceInteriorMap D i)
    (injOn_cutPieceMap_interior D i)

@[simp]
theorem coe_cutPiecePartialDiffeomorph (D : TorusDecomposition M) (i : Fin D.components.count) :
    ⇑(cutPiecePartialDiffeomorph D i) = cutPieceMap D i := rfl

@[simp]
theorem cutPiecePartialDiffeomorph_source (D : TorusDecomposition M)
    (i : Fin D.components.count) :
    (cutPiecePartialDiffeomorph D i).source = (D.component i).interior := rfl

theorem mem_cutPiecePartialDiffeomorph_source_iff {D : TorusDecomposition M}
    {i : Fin D.components.count} {x : (D.component i).Carrier} :
    x ∈ (cutPiecePartialDiffeomorph D i).source ↔
      x ∈ (D.component i).model.interior (D.component i).Carrier := Iff.rfl

end CutPiece

end DifferentialGeometry.Geometry.Collapse
