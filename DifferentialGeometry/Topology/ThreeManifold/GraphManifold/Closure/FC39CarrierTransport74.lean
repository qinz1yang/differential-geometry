import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertRestrict
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# Draft 74, D74-6: transport of FC39 row objects along ONE carrier diffeomorphism (primitive T0)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G13. Draft 74 §2.2–2.3 (D74-6): the closed rows are
built on `W.Carrier`, every chain object is carried by the ONE diffeomorphism `M.ψ` (sets pushed
forward, functions pulled back by `ψ⁻¹`). The primitive first:

* `PieceEmbedding.mapCarrier74 e P` (`e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier`): the same
  piece manifold with the map `e ∘ P.map` (through the tree's `PieceEmbedding.ofMap`; the
  differential of a diffeomorphism is bijective, `mfderiv_diffeo_bijective_R74`), and its
  closed-route form `PieceEmbedding.ofComp74` (`map = e ∘ j` for a piece `j : Q → N` into the
  model manifold `N` and `e = M.ψ : N ≃ W.Carrier`; draft 74 §2.2 `map_i = M.ψ ∘ Ψ_i ∘ j_i`);
* transport of the attached sets and functions: `range_mapCarrier74`,
  `pieceBoundary_mapCarrier74` (model boundary image), `image_interior_R74`,
  `image_frontier_R74`, `image_closure_R74`, `relInt_image_R74` (§5.7 relative interior),
  `preimage_symm_R74` (whole fibres / sublevels of a pulled-back function are the images),
  `contMDiff_comp_symm_R74`, `mfderiv_comp_symm_ne_zero_R74` (defining functions stay smooth and
  regular), `image_interior_carrier_R74` (`e(int W₀) = int W₁`, so interior-supported opens stay
  interior; D74-6: the boundary of `W₁` is never inferred from `BoundaryTori.empty`);
* models: `ZeroModel` / `ClosedZeroPiece` / `SlimModel` carried by the tree's `ofMap`;
* first package of `FC39RowsV2.transport74` ("pieces"): **`ZeroDomains.mapCarrier74 e Z`**
  (pieces, disjointness, ratio functions `Z.ratio i ∘ e⁻¹`, near sets `e(near i)`, regularity,
  `pieceBoundary = {ratio = 0}`, `range = {ratio ≤ 0}`, models), with `range` / `ratio` /
  `near` identities `ZeroDomains.mapCarrier74_range`, `…_ratio`, `…_near`.
NOT in this group (D74-6 packages, next): `SlimPiecesV2`, `CuspCores`, `EdgeBundle`,
`EdgeComponentModels`, `CircleBundle` (bundle half) and `JunctionsV2`, `LabelledCornerTubes`
(faces / junctions / tubes); the target boundary tori must be the transported ports, never an
arbitrary `E₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

variable {W₀ W₁ : CompactCarrier.{u}}

/-- The differential of a diffeomorphism is bijective at every point. -/
theorem mfderiv_diffeo_bijective_R74 {EN HN EN' HN' : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] [NormedAddCommGroup EN'] [NormedSpace ℝ EN']
    [TopologicalSpace HN'] {I : ModelWithCorners ℝ EN HN} {I' : ModelWithCorners ℝ EN' HN'}
    {N N' : Type*} [TopologicalSpace N] [ChartedSpace HN N] [TopologicalSpace N']
    [ChartedSpace HN' N'] (e : N ≃ₘ⟮I, I'⟯ N') (x : N) : Bijective (mfderiv I I' e x) := by
  have h := (e.mfderivToContinuousLinearEquiv (by simp) x).bijective
  rwa [← ContinuousLinearEquiv.coe_coe, Diffeomorph.mfderivToContinuousLinearEquiv_coe] at h

/-- **D74-6, closed-route form**: a compact connected piece `Q` immersed injectively into a
manifold `N` by `j` (bijective differential), followed by a diffeomorphism `e : N ≃ W.Carrier`
(e.g. `M.ψ`), is a piece embedding of `W` with map `e ∘ j` (draft 74 §2.2:
`map_i = M.ψ ∘ Ψ_i ∘ j_i`). -/
def PieceEmbedding.ofComp74 {W : CompactCarrier.{u}} {EN HN : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {I : ModelWithCorners ℝ EN HN} {N : Type*}
    [TopologicalSpace N] [ChartedSpace HN N] (Q : Type u) [TopologicalSpace Q]
    [ChartedSpace (EuclideanHalfSpace 3) Q] [IsManifold (𝓡∂ 3) ∞ Q] [CompactSpace Q] [T2Space Q]
    [SecondCountableTopology Q] [ConnectedSpace Q] (j : Q → N) (hj : ContMDiff (𝓡∂ 3) I ∞ j)
    (hjb : ∀ q, Bijective (mfderiv (𝓡∂ 3) I j q)) (hji : Injective j)
    (e : N ≃ₘ⟮I, W.model⟯ W.Carrier) : PieceEmbedding W where
  Piece := Q
  map := e ∘ j
  smooth := e.contMDiff.comp hj
  mfderiv_bijective q := by
    have hd : MDifferentiableAt (𝓡∂ 3) I j q := (hj q).mdifferentiableAt (by simp)
    have he : MDifferentiableAt I W.model e (j q) := e.mdifferentiable (by simp) _
    rw [mfderiv_comp q he hd]
    exact (mfderiv_diffeo_bijective_R74 e (j q)).comp (hjb q)
  injective := e.injective.comp hji

/-- The closed-route piece has range `e(range j)` and model boundary image `e(j(∂Q))`. -/
theorem PieceEmbedding.ofComp74_range {W : CompactCarrier.{u}} {EN HN : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {I : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (Q : Type u) [TopologicalSpace Q] [ChartedSpace (EuclideanHalfSpace 3) Q]
    [IsManifold (𝓡∂ 3) ∞ Q] [CompactSpace Q] [T2Space Q] [SecondCountableTopology Q]
    [ConnectedSpace Q] (j : Q → N) (hj : ContMDiff (𝓡∂ 3) I ∞ j)
    (hjb : ∀ q, Bijective (mfderiv (𝓡∂ 3) I j q)) (hji : Injective j)
    (e : N ≃ₘ⟮I, W.model⟯ W.Carrier) :
    range (PieceEmbedding.ofComp74 Q j hj hjb hji e).map = e '' range j ∧
      FC39P0.pieceBoundary (PieceEmbedding.ofComp74 Q j hj hjb hji e) =
        e '' (j '' (𝓡∂ 3).boundary Q) :=
  ⟨range_comp e j, image_comp e j _⟩

/-- `e ∘ P.map` is smooth with bijective differential and injective. -/
theorem mapCarrier74_facts (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (P : PieceEmbedding W₀) :
    ContMDiff (𝓡∂ 3) W₁.model ∞ (e ∘ P.map) ∧
      (∀ q, Bijective (mfderiv (𝓡∂ 3) W₁.model (e ∘ P.map) q)) ∧ Injective (e ∘ P.map) := by
  refine ⟨e.contMDiff.comp P.smooth, fun q => ?_, e.injective.comp P.injective⟩
  have hd : MDifferentiableAt (𝓡∂ 3) W₀.model P.map q := P.mdifferentiable_map q
  have he : MDifferentiableAt W₀.model W₁.model e (P.map q) := e.mdifferentiable (by simp) _
  rw [mfderiv_comp q he hd]
  exact (mfderiv_diffeo_bijective_R74 e (P.map q)).comp (P.mfderiv_bijective q)

/-- **D74-6 primitive**: the piece transported along the carrier diffeomorphism `e`. -/
def PieceEmbedding.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (P : PieceEmbedding W₀) : PieceEmbedding W₁ :=
  P.ofMap (e ∘ P.map) (mapCarrier74_facts e P).1 (mapCarrier74_facts e P).2.1
    (mapCarrier74_facts e P).2.2

section Primitive

variable (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)

/-- The transported piece map is `e ∘ P.map`. -/
theorem PieceEmbedding.mapCarrier74_map (P : PieceEmbedding W₀) :
    (P.mapCarrier74 e).map = e ∘ P.map :=
  rfl

/-- `range` is transported. -/
theorem PieceEmbedding.range_mapCarrier74 (P : PieceEmbedding W₀) :
    range (P.mapCarrier74 e).map = e '' range P.map :=
  range_comp e P.map

/-- The model boundary image is transported. -/
theorem PieceEmbedding.pieceBoundary_mapCarrier74 (P : PieceEmbedding W₀) :
    FC39P0.pieceBoundary (P.mapCarrier74 e) = e '' FC39P0.pieceBoundary P :=
  image_comp e P.map _

end Primitive

section Generic

variable {EN HN EN' HN' : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
  {I : ModelWithCorners ℝ EN HN} {I' : ModelWithCorners ℝ EN' HN'} {N N' : Type*}
  [TopologicalSpace N] [ChartedSpace HN N] [TopologicalSpace N'] [ChartedSpace HN' N']
  (e : N ≃ₘ⟮I, I'⟯ N')

/-- Interiors are transported. -/
theorem image_interior_R74 (A : Set N) : e '' interior A = interior (e '' A) :=
  e.toHomeomorph.image_interior A

/-- Frontiers are transported. -/
theorem image_frontier_R74 (A : Set N) : e '' frontier A = frontier (e '' A) :=
  e.toHomeomorph.image_frontier A

/-- Closures are transported. -/
theorem image_closure_R74 (A : Set N) : e '' closure A = closure (e '' A) :=
  e.toHomeomorph.image_closure A

/-- Relative interiors (§5.7) are transported. -/
theorem relInt_image_R74 (A S : Set N) :
    FC39P0.relInt (e '' A) (e '' S) = e '' FC39P0.relInt A S := by
  ext y
  change y ∈ Subtype.val '' interior (Subtype.val ⁻¹' (e '' S) : Set (e '' A)) ↔
    y ∈ e '' (Subtype.val '' interior (Subtype.val ⁻¹' S : Set A))
  rw [mem_image_interior_preimage_val_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, O, hO, hxO, hOA⟩
    refine ⟨x, mem_image_interior_preimage_val_iff.mpr ⟨hx, e ⁻¹' O, hO.preimage e.continuous,
      hxO, fun z hz => ?_⟩, rfl⟩
    obtain ⟨z', hz', hzz⟩ := hOA ⟨hz.1, z, hz.2, rfl⟩
    rw [← e.injective hzz]
    exact hz'
  · rintro ⟨x, hx', rfl⟩
    obtain ⟨hx, O, hO, hxO, hOA⟩ := mem_image_interior_preimage_val_iff.mp hx'
    refine ⟨⟨x, hx, rfl⟩, e '' O, e.toHomeomorph.isOpenMap O hO, ⟨x, hxO, rfl⟩, ?_⟩
    rintro _ ⟨⟨z, hzO, rfl⟩, w, hw, hwz⟩
    rw [e.injective hwz] at hw
    exact ⟨z, hOA ⟨hzO, hw⟩, rfl⟩

/-- Whole fibres, sublevels and every other level set of a pulled-back function are the images. -/
theorem preimage_symm_R74 {Y : Type*} (f : N → Y) (T : Set Y) :
    (f ∘ e.symm) ⁻¹' T = e '' (f ⁻¹' T) := by
  ext y
  constructor
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    change f (e.symm (e x)) ∈ T
    rw [e.symm_apply_apply]
    exact hx

end Generic

section Primitive2

variable (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)

/-- The interior of the carrier is transported: `e(int W₀) = int W₁`. -/
theorem image_interior_carrier_R74 :
    e '' (W₀.interior : Set W₀.Carrier) = (W₁.interior : Set W₁.Carrier) :=
  e.image_interior (by simp)

/-- A pulled-back smooth function is smooth. -/
theorem contMDiff_comp_symm_R74 {f : W₀.Carrier → ℝ}
    (hf : ContMDiff W₀.model 𝓘(ℝ, ℝ) ∞ f) : ContMDiff W₁.model 𝓘(ℝ, ℝ) ∞ (f ∘ e.symm) :=
  hf.comp e.symm.contMDiff

/-- A pulled-back smooth function is regular where the original is. -/
theorem mfderiv_comp_symm_ne_zero_R74 {f : W₀.Carrier → ℝ}
    (hf : ContMDiff W₀.model 𝓘(ℝ, ℝ) ∞ f) {y : W₁.Carrier}
    (hy : mfderiv W₀.model 𝓘(ℝ, ℝ) f (e.symm y) ≠ 0) :
    mfderiv W₁.model 𝓘(ℝ, ℝ) (f ∘ e.symm) y ≠ 0 := by
  have hd : MDifferentiableAt W₀.model 𝓘(ℝ, ℝ) f (e.symm y) := hf.mdifferentiableAt (by simp)
  have he : MDifferentiableAt W₁.model W₀.model e.symm y := e.symm.mdifferentiable (by simp) _
  rw [mfderiv_comp y hd he]
  intro h0
  apply hy
  ext v
  obtain ⟨u, rfl⟩ := (mfderiv_diffeo_bijective_R74 e.symm y).2 v
  exact congrArg (fun L => L u) h0

end Primitive2

end GC.GraphManifold.Assembly

namespace GC.GraphManifold.Assembly.FC39P0

variable {W₀ W₁ : CompactCarrier.{u}}

/-- **First package of `FC39RowsV2.transport74`: zero domains along `e`** (pieces, ratio
functions pulled back by `e⁻¹`, near sets pushed forward, models by `ofMap`). -/
def ZeroDomains.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (Z : ZeroDomains W₀) : ZeroDomains W₁ where
  count := Z.count
  piece i := (Z.piece i).mapCarrier74 e
  disjoint i j hij := by
    change Disjoint (range ((Z.piece i).mapCarrier74 e).map)
      (range ((Z.piece j).mapCarrier74 e).map)
    rw [PieceEmbedding.range_mapCarrier74, PieceEmbedding.range_mapCarrier74]
    exact (disjoint_image_iff e.injective).mpr (Z.disjoint hij)
  ratio i := Z.ratio i ∘ e.symm
  near i := ⟨e '' Z.near i, e.toHomeomorph.isOpenMap _ (Z.near i).isOpen⟩
  near_interior i := by
    rw [← image_interior_carrier_R74 e]
    exact image_mono (Z.near_interior i)
  ratio_smooth i := contMDiff_comp_symm_R74 e (Z.ratio_smooth i)
  ratio_regular i y hy :=
    mfderiv_comp_symm_ne_zero_R74 e (Z.ratio_smooth i) (Z.ratio_regular i (e.symm y) hy)
  zero_subset_near i y hy := ⟨e.symm y, Z.zero_subset_near i hy, e.apply_symm_apply y⟩
  boundary_eq i := by
    rw [PieceEmbedding.pieceBoundary_mapCarrier74, Z.boundary_eq i]
    exact (preimage_symm_R74 e (Z.ratio i) {0}).symm
  range_eq i := by
    rw [PieceEmbedding.range_mapCarrier74, Z.range_eq i]
    exact (preimage_symm_R74 e (Z.ratio i) (Iic 0)).symm
  model i := match Z.model i with
    | .inl m => .inl m.ofMap
    | .inr ⟨⟨piece, hbe, Q, metric, nonneg, ident⟩, hC⟩ => .inr
        ⟨ClosedZeroPiece.ofMap ⟨piece, hbe, Q, metric, nonneg, ident⟩ (e ∘ piece.map)
          (mapCarrier74_facts e piece).1 (mapCarrier74_facts e piece).2.1
          (mapCarrier74_facts e piece).2.2, by subst hC; rfl⟩

section ZeroTransport

variable (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) (Z : ZeroDomains W₀)

/-- The transported zero pieces have the transported ranges. -/
theorem ZeroDomains.mapCarrier74_range (i : Fin Z.count) :
    range ((Z.mapCarrier74 e).piece i).map = e '' range (Z.piece i).map :=
  PieceEmbedding.range_mapCarrier74 e (Z.piece i)

/-- The transported ratio is the pulled-back ratio. -/
theorem ZeroDomains.mapCarrier74_ratio (i : Fin Z.count) :
    (Z.mapCarrier74 e).ratio i = Z.ratio i ∘ e.symm :=
  rfl

/-- The transported near set is the image. -/
theorem ZeroDomains.mapCarrier74_near (i : Fin Z.count) :
    ((Z.mapCarrier74 e).near i : Set W₁.Carrier) = e '' Z.near i :=
  rfl

/-- The transported zero union is the image of the zero union (`Z_W = e(Z)`). -/
theorem ZeroDomains.mapCarrier74_union :
    ⋃ i, range ((Z.mapCarrier74 e).piece i).map = e '' ⋃ i, range (Z.piece i).map := by
  rw [image_iUnion]
  exact iUnion_congr fun i => Z.mapCarrier74_range e i

end ZeroTransport

end GC.GraphManifold.Assembly.FC39P0
