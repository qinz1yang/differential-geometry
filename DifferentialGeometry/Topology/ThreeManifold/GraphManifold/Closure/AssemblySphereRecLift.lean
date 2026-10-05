import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecTransport

/-!
# FC42 sphere recursion, packet S2 (second half): lifting the certificate data across the cut

Lane ASM-SPH (review 40 §2.4 "first layer"). Everything goes through ONE map: the transport
`X.transport : W \ Σ ≅ Q \ caps` (and, on the seam sphere itself, the side lifts `X.sideLift j`, which
agree with the transport off `Σ`).

* `liftPiece P j hside`: a piece of `W` that stays on side `j` of the seam (adjacent vertices)
  becomes a piece of the capped carrier, `q ↦ core (sideLift j (P.map q))`; its differential is
  bijective because `fold ∘ sideLift j = id`.
* `liftPieceAway P h`: a piece avoiding `Σ` (non-adjacent vertices, edge-circle pieces),
  `q ↦ transport (P.map q)`; it is `liftPiece` for either side (`liftPiece_map_of_notMem`).
* `liftPartialDiffeomorph φ h = φ.trans transport` for charts whose target avoids `Σ` (rim charts,
  collars), with the same source; `liftSphereSeam`, `liftTorusSeam`: the other seams;
  `liftEdgeHandle`, `liftEdgeCirclePiece`: handles and edge-circle pieces.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASMSPH : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASMSPH : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- An injective endomorphism-shaped continuous linear map between two copies of a
finite-dimensional space is bijective. -/
theorem bijective_of_injective_continuousLinearMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {f : V →L[ℝ] V} (hf : Injective f) :
    Bijective f := by
  have h : Injective f.toLinearMap := hf
  exact ⟨hf, LinearMap.injective_iff_surjective.mp h⟩

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

section General

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- The transport of a smooth map avoiding the seam sphere is smooth. -/
theorem contMDiff_transport_comp {m : M → W.Carrier} (hm : ContMDiff IM W.model ∞ m)
    (h : range m ⊆ S.zeroSphereᶜ) : ContMDiff IM X.Q.model ∞ (X.transport ∘ m) :=
  X.transport.contMDiffOn.comp_contMDiff hm fun q => h ⟨q, rfl⟩

/-- Differential of the transport of a map avoiding the seam sphere. -/
theorem mfderiv_transport_comp_bijective {m : M → W.Carrier}
    (hm : ContMDiff IM W.model ∞ m) (h : range m ⊆ S.zeroSphereᶜ) (q : M)
    (hq : Bijective (mfderiv IM W.model m q)) :
    Bijective (mfderiv IM X.Q.model (X.transport ∘ m) q) := by
  have hsrc : m q ∈ X.transport.source := h ⟨q, rfl⟩
  rw [mfderiv_comp q (X.transport.mdifferentiableAt (by simp) hsrc)
    (hm.mdifferentiableAt (by simp))]
  exact (X.mfderiv_transport_bijective (h ⟨q, rfl⟩)).comp hq

/-- Differential of a side-lifted map composed with the core: bijective when the original map has
bijective differential (the fold undoes the side lift). -/
theorem mfderiv_core_sideLift_comp_bijective
    (hdim : Module.finrank ℝ EM = 3) (j : Fin 2) {m : M → W.Carrier}
    (hm : ContMDiff IM W.model ∞ m)
    (hside : ∀ q p, p ∈ S.collar.source → m q = S.collar p → 0 ≤ cutSideSign j * p.2) (q : M)
    (hq : Bijective (mfderiv IM W.model m q)) :
    Bijective (mfderiv IM X.Q.model (X.capping.core ∘ (X.sideLift j ∘ m)) q) := by
  have hg := X.contMDiff_sideLift_comp j hm hside
  have hgd : MDifferentiableAt IM X.C.model (X.sideLift j ∘ m) q := hg.mdifferentiableAt (by simp)
  have hfold : X.fold ∘ (X.sideLift j ∘ m) = m := funext fun q => X.fold_sideLift j (m q)
  have hchain : mfderiv IM W.model m q =
      (mfderiv X.C.model W.model X.fold ((X.sideLift j ∘ m) q)).comp
        (mfderiv IM X.C.model (X.sideLift j ∘ m) q) := by
    rw [← mfderiv_comp q (X.smooth.mdifferentiableAt (by simp)) hgd, hfold]
  have hinj : Injective (mfderiv IM X.C.model (X.sideLift j ∘ m) q) := by
    intro v w hvw
    apply hq.1
    rw [DFunLike.congr_fun hchain v, DFunLike.congr_fun hchain w]
    exact congrArg (mfderiv X.C.model W.model X.fold ((X.sideLift j ∘ m) q)) hvw
  have hEM : FiniteDimensional ℝ EM := Module.finite_of_finrank_eq_succ hdim
  let L : EM ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hdim, finrank_euclideanSpace_fin])
  have hbij : Bijective (mfderiv IM X.C.model (X.sideLift j ∘ m) q) := by
    let f : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (mfderiv IM X.C.model (X.sideLift j ∘ m) q).comp (L.symm : EuclideanSpace ℝ (Fin 3) →L[ℝ] EM)
    have hf : Injective f := hinj.comp L.symm.injective
    have hfb := bijective_of_injective_continuousLinearMap hf
    refine ⟨hinj, fun w => ?_⟩
    obtain ⟨v, hv⟩ := hfb.2 w
    exact ⟨L.symm v, hv⟩
  rw [mfderiv_comp q (X.capping.core_embedding.contMDiff.mdifferentiableAt (by simp)) hgd]
  exact (X.mfderiv_core_bijective _).comp hbij

end General

/-- **S2.** A piece of `W` that stays on side `j` of the seam, lifted into the capped carrier. -/
def liftPiece (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2) :
    PieceEmbedding X.Q where
  Piece := P.Piece
  map q := X.capping.core (X.sideLift j (P.map q))
  smooth := X.capping.core_embedding.contMDiff.comp (X.contMDiff_sideLift_comp j P.smooth hside)
  mfderiv_bijective q :=
    X.mfderiv_core_sideLift_comp_bijective finrank_euclideanSpace_fin j P.smooth hside q
      (P.mfderiv_bijective q)
  injective := X.core_injective.comp ((X.sideLift_injective j).comp P.injective)

theorem liftPiece_map (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
    (q : P.Piece) :
    (X.liftPiece P j hside).map q = X.capping.core (X.sideLift j (P.map q)) :=
  rfl

theorem liftPiece_map_of_notMem (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
    {q : P.Piece} (hq : P.map q ∉ S.zeroSphere) :
    (X.liftPiece P j hside).map q = X.transport (P.map q) := by
  rw [liftPiece_map, X.sideLift_of_notMem j hq, transport_apply]

/-- The fold undoes the lift: `fold (core⁻¹ (lift q)) = P.map q`. -/
theorem fold_coreInverse_liftPiece (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
    (q : P.Piece) : X.fold (X.coreInverse ((X.liftPiece P j hside).map q)) = P.map q := by
  rw [liftPiece_map, X.coreInverse_core, X.fold_sideLift]

theorem liftPiece_map_of_mem (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
    {q : P.Piece} {z : ClosureSphere.{u}} (hq : P.map q = S.collar (z, 0)) :
    (X.liftPiece P j hside).map q = X.capping.core (X.cutSphere j z) := by
  rw [liftPiece_map, hq, X.sideLift_of_mem]

/-- **S2.** A piece of `W` avoiding the seam sphere, transported into the capped carrier. -/
def liftPieceAway (P : PieceEmbedding W) (h : range P.map ⊆ S.zeroSphereᶜ) : PieceEmbedding X.Q where
  Piece := P.Piece
  map q := X.transport (P.map q)
  smooth := X.contMDiff_transport_comp P.smooth h
  mfderiv_bijective q :=
    X.mfderiv_transport_comp_bijective P.smooth h q (P.mfderiv_bijective q)
  injective q q' hqq' :=
    P.injective (X.transport.toPartialEquiv.injOn (h ⟨q, rfl⟩) (h ⟨q', rfl⟩) hqq')

theorem liftPieceAway_map (P : PieceEmbedding W) (h : range P.map ⊆ S.zeroSphereᶜ) (q : P.Piece) :
    (X.liftPieceAway P h).map q = X.transport (P.map q) :=
  rfl

theorem range_liftPieceAway (P : PieceEmbedding W) (h : range P.map ⊆ S.zeroSphereᶜ) :
    range (X.liftPieceAway P h).map = X.transport '' range P.map := by
  rw [← range_comp]
  rfl

/-- Off the seam sphere, the side lifts of a piece agree with its transport. -/
theorem liftPiece_map_eq_liftPieceAway (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
    (h : range P.map ⊆ S.zeroSphereᶜ) (q : P.Piece) :
    (X.liftPiece P j hside).map q = (X.liftPieceAway P h).map q :=
  X.liftPiece_map_of_notMem P j hside (h ⟨q, rfl⟩)

/-- The transport of an interior point is interior. -/
theorem transport_image_subset_interior {A : Set W.Carrier} (hA : A ⊆ W.interior) :
    X.transport '' A ⊆ X.Q.interior := by
  rintro _ ⟨x, hx, rfl⟩
  exact X.transport_mem_interior (hA hx)

section Charts

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- **S2.** A chart (collar, rim chart) of `W` whose target avoids the seam sphere, carried into the
capped carrier by the transport. -/
def liftPartialDiffeomorph (φ : PartialDiffeomorph IM W.model M W.Carrier ∞)
    (_h : φ.target ⊆ S.zeroSphereᶜ) : PartialDiffeomorph IM X.Q.model M X.Q.Carrier ∞ :=
  φ.trans X.transport

theorem liftPartialDiffeomorph_apply (φ : PartialDiffeomorph IM W.model M W.Carrier ∞)
    (h : φ.target ⊆ S.zeroSphereᶜ) (p : M) :
    X.liftPartialDiffeomorph φ h p = X.transport (φ p) :=
  rfl

theorem liftPartialDiffeomorph_source (φ : PartialDiffeomorph IM W.model M W.Carrier ∞)
    (h : φ.target ⊆ S.zeroSphereᶜ) : (X.liftPartialDiffeomorph φ h).source = φ.source := by
  change φ.source ∩ φ ⁻¹' X.transport.source = φ.source
  exact inter_eq_left.mpr fun p hp => h (φ.map_source hp)

theorem liftPartialDiffeomorph_target (φ : PartialDiffeomorph IM W.model M W.Carrier ∞)
    (h : φ.target ⊆ S.zeroSphereᶜ) :
    (X.liftPartialDiffeomorph φ h).target = X.transport '' φ.target := by
  ext y
  constructor
  · rintro ⟨hy, hy'⟩
    exact ⟨X.transport.symm y, hy', X.transport.toPartialEquiv.right_inv hy⟩
  · rintro ⟨x, hx, rfl⟩
    have hxs : x ∈ X.transport.source := h hx
    refine ⟨X.transport.map_source hxs, ?_⟩
    change X.transport.symm (X.transport x) ∈ φ.target
    have e : X.transport.symm (X.transport x) = x := X.transport.toPartialEquiv.left_inv hxs
    rw [e]
    exact hx

end Charts

/-- **S2.** Another sphere seam whose collar avoids the cut seam sphere, in the capped carrier. -/
def liftSphereSeam (S' : SphereSeam W) (h : S'.collar.target ⊆ S.zeroSphereᶜ) : SphereSeam X.Q where
  collar := X.liftPartialDiffeomorph S'.collar h
  source_eq := (X.liftPartialDiffeomorph_source S'.collar h).trans S'.source_eq
  target_interior := by
    rw [X.liftPartialDiffeomorph_target]
    exact X.transport_image_subset_interior S'.target_interior

theorem liftSphereSeam_collar_apply (S' : SphereSeam W) (h : S'.collar.target ⊆ S.zeroSphereᶜ)
    (p : ClosureSphere.{u} × ℝ) : (X.liftSphereSeam S' h).collar p = X.transport (S'.collar p) :=
  rfl

/-- **S2.** A torus seam whose collar avoids the cut seam sphere, in the capped carrier. -/
def liftTorusSeam (T : TorusSeam W) (h : T.collar.target ⊆ S.zeroSphereᶜ) : TorusSeam X.Q where
  collar := X.liftPartialDiffeomorph T.collar h
  source_eq := (X.liftPartialDiffeomorph_source T.collar h).trans T.source_eq
  target_interior := by
    rw [X.liftPartialDiffeomorph_target]
    exact X.transport_image_subset_interior T.target_interior

theorem liftTorusSeam_collar_apply (T : TorusSeam W) (h : T.collar.target ⊆ S.zeroSphereᶜ)
    (p : Torus × ℝ) : (X.liftTorusSeam T h).collar p = X.transport (T.collar p) :=
  rfl

/-- **S2.** A handle avoiding the seam sphere, in the capped carrier. -/
def liftEdgeHandle (H : EdgeHandle W) (h : range H.map ⊆ S.zeroSphereᶜ) : EdgeHandle X.Q where
  map p := X.transport (H.map p)
  smooth := X.contMDiff_transport_comp H.smooth h
  mfderiv_bijective p := X.mfderiv_transport_comp_bijective H.smooth h p (H.mfderiv_bijective p)
  injective p p' hpp' :=
    H.injective (X.transport.toPartialEquiv.injOn (h ⟨p, rfl⟩) (h ⟨p', rfl⟩) hpp')
  interior := by
    rw [show (range fun p => X.transport (H.map p)) = X.transport '' range H.map from
      (range_comp _ _)]
    exact X.transport_image_subset_interior H.interior

theorem liftEdgeHandle_map (H : EdgeHandle W) (h : range H.map ⊆ S.zeroSphereᶜ)
    (p : ClosedCell 2 × Icc (0 : ℝ) 1) : (X.liftEdgeHandle H h).map p = X.transport (H.map p) :=
  rfl

/-- **S2.** An edge-circle piece avoiding the seam sphere, in the capped carrier. -/
def liftEdgeCirclePiece (P : EdgeCirclePiece W) (h : range P.piece.map ⊆ S.zeroSphereᶜ) :
    EdgeCirclePiece X.Q where
  piece := X.liftPieceAway P.piece h
  proj := P.proj
  proj_smooth := P.proj_smooth
  proj_submersion := P.proj_submersion
  boundary_submersion := P.boundary_submersion
  fibre := P.fibre
  fibre_embedding := P.fibre_embedding
  fibre_range := P.fibre_range
  interior := by
    rw [X.range_liftPieceAway]
    exact X.transport_image_subset_interior P.interior

theorem liftEdgeCirclePiece_map (P : EdgeCirclePiece W) (h : range P.piece.map ⊆ S.zeroSphereᶜ)
    (q : P.piece.Piece) : (X.liftEdgeCirclePiece P h).piece.map q = X.transport (P.piece.map q) :=
  rfl

end SphereCutCapped

end GC.GraphManifold.Assembly
