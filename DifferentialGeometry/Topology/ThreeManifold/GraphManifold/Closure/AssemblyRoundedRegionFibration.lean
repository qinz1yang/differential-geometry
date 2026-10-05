import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModelApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.OnePiece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

/-!
# FC42 packet T2b: the circle fibration of a rounded region piece and its Raw presentation

Review 40 §3.1 steps 3–5 and §3.2. For the piece `P_j = roundedRegionPiece j` over the rounded base
component `B_j = roundedBaseSurface j` (T1a, T2a):

* `roundedRegionProj j : P_j → B_j`, the bundle projection (the projection of the circle region,
  restricted), smooth (`contMDiff_roundedRegionProj`), with `∂P_j = π_j⁻¹(∂B_j)`
  (`roundedRegionPiece_boundary_eq`);
* `roundedTrivialization j b`: the ACTUAL trivialization `R.trivialization (ι b)` of the circle
  region restricted to the part of `P_j` over the preimage in `B_j` of its base neighbourhood — a
  diffeomorphism `π_j⁻¹(N_b) ≃ N_b × S¹` over `π_j`;
* `roundedRegionFibration j : CircleFibration P_j.toCarrier ⊤` with base `B_j`. No orientability of the
  base is assumed, and the base may be closed;
* `roundedRegionRawPresentation j E hb`: the single-piece Raw presentation
  (`singlePieceRawPresentation`, `Closure/OnePiece.lean`) for any family `E` of boundary tori of the
  piece exhausting `∂P_j` (the constructor's own input; the tori are produced in T3);
  `rawPiece_of_roundedRegionPiece_of_boundary_eq_empty`: for a closed base component the Raw piece in
  the `hpiece` format of B3 with no further input.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W) (j : ConnectedComponents R.roundedBase)

/-! ## Points of a piece -/

/-- A point of the piece `P_j`, as a point of the domain of the circle region. -/
def roundedPieceDomain (q : (R.roundedRegionPiece j).Piece) : R.domain :=
  R.roundedTotalDomain (show R.roundedPieceOpens j from q).1

theorem roundedPieceDomain_val (q : (R.roundedRegionPiece j).Piece) :
    (R.roundedPieceDomain j q : W.Carrier) = (R.roundedRegionPiece j).map q :=
  rfl

theorem contMDiff_roundedPieceDomain :
    ContMDiff (𝓡∂ 3) W.model ∞ (R.roundedPieceDomain j) :=
  (ContMDiff.subtypeVal_comp_iff R.domain _).mp (R.roundedRegionPiece j).smooth

variable {R j} in
/-- Smooth maps into a piece are the maps whose composition with the piece map is smooth. -/
theorem contMDiff_roundedPiece_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {f : X → (R.roundedRegionPiece j).Piece} :
    ContMDiff J (𝓡∂ 3) ∞ f ↔ ContMDiff J W.model ∞ ((R.roundedRegionPiece j).map ∘ f) := by
  change ContMDiff J (𝓡∂ 3) ∞ (show X → R.roundedPieceOpens j from f) ↔ _
  rw [← ContMDiff.subtypeVal_comp_iff (R.roundedPieceOpens j), contMDiff_roundedTotal_iff]
  rfl

theorem proj_mem_range_of_mem_piece (q : (R.roundedRegionPiece j).Piece) :
    R.proj (R.roundedPieceDomain j q) ∈ range (R.roundedBaseIncl j) :=
  roundedTotalProj_mem_component_iff.mp (show R.roundedPieceOpens j from q).2

/-- A point of the domain over `B_j`, as a point of the piece `P_j`. -/
def roundedPieceOfDomain (y : R.domain) (hy : R.proj y ∈ range (R.roundedBaseIncl j)) :
    (R.roundedRegionPiece j).Piece :=
  show R.roundedPieceOpens j from
    ⟨R.roundedTotalOfDomain y (by
        obtain ⟨b, hb⟩ := hy
        rw [← hb]
        exact R.rounding_roundedBaseIncl_le j b),
      roundedTotalProj_mem_component_iff.mpr hy⟩

theorem map_roundedPieceOfDomain (y : R.domain) (hy : R.proj y ∈ range (R.roundedBaseIncl j)) :
    (R.roundedRegionPiece j).map (R.roundedPieceOfDomain j y hy) = y :=
  rfl

theorem roundedPieceDomain_roundedPieceOfDomain (y : R.domain)
    (hy : R.proj y ∈ range (R.roundedBaseIncl j)) :
    R.roundedPieceDomain j (R.roundedPieceOfDomain j y hy) = y :=
  rfl

theorem roundedPieceOfDomain_roundedPieceDomain (q : (R.roundedRegionPiece j).Piece) :
    R.roundedPieceOfDomain j (R.roundedPieceDomain j q) (R.proj_mem_range_of_mem_piece j q) = q :=
  rfl

/-! ## The projection -/

/-- The bundle projection `π_j : P_j → B_j`. -/
def roundedRegionProj (q : (R.roundedRegionPiece j).Piece) : (R.roundedBaseSurface j).Carrier :=
  show R.roundedBaseComponent j from
    ⟨R.roundedTotalProj (show R.roundedPieceOpens j from q).1,
      (show R.roundedPieceOpens j from q).2⟩

theorem roundedBaseIncl_roundedRegionProj (q : (R.roundedRegionPiece j).Piece) :
    R.roundedBaseIncl j (R.roundedRegionProj j q) = R.proj (R.roundedPieceDomain j q) :=
  rfl

theorem roundedRegionProj_spec (q : (R.roundedRegionPiece j).Piece) :
    ∃ hx : (R.roundedRegionPiece j).map q ∈ R.domain,
      R.roundedBaseIncl j (R.roundedRegionProj j q) = R.proj ⟨_, hx⟩ :=
  ⟨(R.roundedPieceDomain j q).2, rfl⟩

theorem contMDiff_roundedRegionProj :
    ContMDiff (𝓡∂ 3) (SurfaceModel.model (R.roundedBaseSurface j).kind) ∞
      (R.roundedRegionProj j) :=
  contMDiff_roundedBaseSurface_iff.mpr (R.proj_smooth.comp (R.contMDiff_roundedPieceDomain j))

theorem roundedRegionProj_surjective : Surjective (R.roundedRegionProj j) := by
  intro c
  obtain ⟨y, hy⟩ := R.proj_surjective (R.roundedBaseIncl j c)
  have hmem : R.proj y ∈ range (R.roundedBaseIncl j) := hy ▸ mem_range_self c
  exact ⟨R.roundedPieceOfDomain j y hmem, R.roundedBaseIncl_injective j (show
    R.roundedBaseIncl j (R.roundedRegionProj j (R.roundedPieceOfDomain j y hmem)) =
      R.roundedBaseIncl j c from hy)⟩

/-- `∂P_j = π_j⁻¹(∂B_j)`. -/
theorem roundedRegionPiece_boundary_eq :
    (𝓡∂ 3).boundary (R.roundedRegionPiece j).Piece =
      R.roundedRegionProj j ⁻¹'
        (SurfaceModel.model (R.roundedBaseSurface j).kind).boundary
          (R.roundedBaseSurface j).Carrier := by
  ext q
  change (𝓡∂ 3).IsBoundaryPoint q ↔
    (SurfaceModel.model (R.roundedBaseSurface j).kind).IsBoundaryPoint (R.roundedRegionProj j q)
  rw [roundedRegionPiece_isBoundaryPoint_iff, roundedBaseSurface_isBoundaryPoint_iff,
    R.roundedBaseIncl_roundedRegionProj, ← R.roundedFunction_apply, R.roundedPieceDomain_val]

/-! ## The restricted trivializations -/

/-- The projection on the whole piece, as the `projection` field of a fibration. -/
def roundedTopProjection :
    C((⊤ : TopologicalSpace.Opens (R.roundedRegionPiece j).toCarrier.Carrier),
      (R.roundedBaseSurface j).Carrier) :=
  ⟨fun x => R.roundedRegionProj j x.1,
    (R.contMDiff_roundedRegionProj j).continuous.comp continuous_subtype_val⟩

theorem roundedTopProjection_apply
    (x : (⊤ : TopologicalSpace.Opens (R.roundedRegionPiece j).toCarrier.Carrier)) :
    R.roundedTopProjection j x = R.roundedRegionProj j x.1 :=
  rfl

/-- The base neighbourhoods of the fibration: the preimages in `B_j` of those of `R`. -/
def roundedFibreNeighborhood (b : (R.roundedBaseSurface j).Carrier) :
    TopologicalSpace.Opens (R.roundedBaseSurface j).Carrier :=
  ⟨R.roundedBaseIncl j ⁻¹' R.neighborhood (R.roundedBaseIncl j b),
    (R.neighborhood _).isOpen.preimage (R.contMDiff_roundedBaseIncl j).continuous⟩

theorem mem_roundedFibreNeighborhood (b : (R.roundedBaseSurface j).Carrier) :
    b ∈ R.roundedFibreNeighborhood j b :=
  R.mem_neighborhood _

/-- The source of the restricted trivialization at `b`. -/
abbrev RoundedTrivSource (b : (R.roundedBaseSurface j).Carrier) :=
  TopologicalSpace.Opens.comap (R.roundedTopProjection j) (R.roundedFibreNeighborhood j b)

theorem domain_mem_comap (b : (R.roundedBaseSurface j).Carrier) (x : R.RoundedTrivSource j b) :
    R.roundedPieceDomain j x.1.1 ∈
      TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.roundedBaseIncl j b)) :=
  x.2

/-- The forward map of the restricted trivialization at `b`. -/
def roundedTrivFun (b : (R.roundedBaseSurface j).Carrier) (x : R.RoundedTrivSource j b) :
    (R.roundedFibreNeighborhood j b) × Circle :=
  (⟨R.roundedTopProjection j x.1, x.2⟩,
    (R.trivialization (R.roundedBaseIncl j b) ⟨R.roundedPieceDomain j x.1.1,
      R.domain_mem_comap j b x⟩).2)

/-- The point of `R`'s trivialization domain over a point of `N_b × S¹`. -/
def roundedTrivPoint (b : (R.roundedBaseSurface j).Carrier)
    (p : (R.roundedFibreNeighborhood j b) × Circle) :
    TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.roundedBaseIncl j b)) :=
  (R.trivialization (R.roundedBaseIncl j b)).symm (⟨R.roundedBaseIncl j p.1.1, p.1.2⟩, p.2)

theorem proj_roundedTrivPoint (b : (R.roundedBaseSurface j).Carrier)
    (p : (R.roundedFibreNeighborhood j b) × Circle) :
    R.proj (R.roundedTrivPoint j b p).1 = R.roundedBaseIncl j p.1.1 :=
  R.proj_trivialization_symm _ _

theorem proj_roundedTrivPoint_mem (b : (R.roundedBaseSurface j).Carrier)
    (p : (R.roundedFibreNeighborhood j b) × Circle) :
    R.proj (R.roundedTrivPoint j b p).1 ∈ range (R.roundedBaseIncl j) :=
  ⟨p.1.1, (R.proj_roundedTrivPoint j b p).symm⟩

/-- The inverse map of the restricted trivialization at `b`. -/
def roundedTrivInv (b : (R.roundedBaseSurface j).Carrier)
    (p : (R.roundedFibreNeighborhood j b) × Circle) : R.RoundedTrivSource j b :=
  ⟨⟨R.roundedPieceOfDomain j (R.roundedTrivPoint j b p).1 (R.proj_roundedTrivPoint_mem j b p),
      trivial⟩, by
    change R.proj (R.roundedTrivPoint j b p).1 ∈ R.neighborhood (R.roundedBaseIncl j b)
    rw [R.proj_roundedTrivPoint]
    exact p.1.2⟩

theorem roundedRegionProj_roundedTrivInv (b : (R.roundedBaseSurface j).Carrier)
    (p : (R.roundedFibreNeighborhood j b) × Circle) :
    R.roundedRegionProj j (R.roundedTrivInv j b p).1.1 = p.1.1 := by
  apply R.roundedBaseIncl_injective j
  change R.proj (R.roundedTrivPoint j b p).1 = R.roundedBaseIncl j p.1.1
  exact R.proj_roundedTrivPoint j b p

theorem roundedTrivInv_roundedTrivFun (b : (R.roundedBaseSurface j).Carrier)
    (x : R.RoundedTrivSource j b) : R.roundedTrivInv j b (R.roundedTrivFun j b x) = x := by
  set T := R.trivialization (R.roundedBaseIncl j b)
  set y : TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.roundedBaseIncl j b)) :=
    ⟨R.roundedPieceDomain j x.1.1, R.domain_mem_comap j b x⟩ with hy
  have hfst : T y = (⟨R.roundedBaseIncl j (R.roundedTopProjection j x.1),
      (R.roundedTrivFun j b x).1.2⟩, (T y).2) := by
    refine Prod.ext (Subtype.ext ?_) rfl
    exact R.projection_trivialization _ y
  have hpt : R.roundedTrivPoint j b (R.roundedTrivFun j b x) = y := by
    change T.symm (⟨R.roundedBaseIncl j (R.roundedTopProjection j x.1), _⟩, (T y).2) = y
    rw [← hfst, Diffeomorph.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  apply (R.roundedRegionPiece j).injective
  change ((R.roundedTrivPoint j b (R.roundedTrivFun j b x)).1 : W.Carrier) =
    (R.roundedRegionPiece j).map x.1.1
  rw [hpt]
  rfl

theorem roundedTrivFun_roundedTrivInv (b : (R.roundedBaseSurface j).Carrier)
    (p : (R.roundedFibreNeighborhood j b) × Circle) :
    R.roundedTrivFun j b (R.roundedTrivInv j b p) = p := by
  set T := R.trivialization (R.roundedBaseIncl j b)
  refine Prod.ext (Subtype.ext (R.roundedRegionProj_roundedTrivInv j b p)) ?_
  have hpt : (⟨R.roundedPieceDomain j (R.roundedTrivInv j b p).1.1,
      R.domain_mem_comap j b (R.roundedTrivInv j b p)⟩ :
      TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.roundedBaseIncl j b))) =
      R.roundedTrivPoint j b p :=
    Subtype.ext rfl
  change (T ⟨R.roundedPieceDomain j (R.roundedTrivInv j b p).1.1,
    R.domain_mem_comap j b (R.roundedTrivInv j b p)⟩).2 = p.2
  rw [hpt]
  change (T (T.symm (⟨R.roundedBaseIncl j p.1.1, p.1.2⟩, p.2))).2 = p.2
  rw [Diffeomorph.apply_symm_apply]

theorem contMDiff_roundedTrivFun (b : (R.roundedBaseSurface j).Carrier) :
    ContMDiff (R.roundedRegionPiece j).toCarrier.model
      ((SurfaceModel.model (R.roundedBaseSurface j).kind).prod (𝓡 1)) ∞
      (R.roundedTrivFun j b) := by
  have hval : ContMDiff (R.roundedRegionPiece j).toCarrier.model
      (R.roundedRegionPiece j).toCarrier.model ∞
      (fun x : R.RoundedTrivSource j b => (x.1.1 : (R.roundedRegionPiece j).toCarrier.Carrier)) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  refine ContMDiff.prodMk ?_ ?_
  · refine (ContMDiff.subtypeVal_comp_iff (R.roundedFibreNeighborhood j b) _).mp ?_
    exact (R.contMDiff_roundedRegionProj j).comp hval
  · refine contMDiff_snd.comp ((R.trivialization (R.roundedBaseIncl j b)).contMDiff.comp ?_)
    refine (ContMDiff.subtypeVal_comp_iff
      (TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.roundedBaseIncl j b))) _).mp ?_
    exact (R.contMDiff_roundedPieceDomain j).comp hval

theorem contMDiff_roundedTrivInv (b : (R.roundedBaseSurface j).Carrier) :
    ContMDiff ((SurfaceModel.model (R.roundedBaseSurface j).kind).prod (𝓡 1))
      (R.roundedRegionPiece j).toCarrier.model ∞ (R.roundedTrivInv j b) := by
  refine (ContMDiff.subtypeVal_comp_iff (R.RoundedTrivSource j b) _).mp ?_
  refine (ContMDiff.subtypeVal_comp_iff
    (⊤ : TopologicalSpace.Opens (R.roundedRegionPiece j).toCarrier.Carrier) _).mp ?_
  refine contMDiff_roundedPiece_iff.mpr ?_
  have hN : ContMDiff ((SurfaceModel.model (R.roundedBaseSurface j).kind).prod (𝓡 1))
      ((𝓡 2).prod (𝓡 1)) ∞
      (fun p : (R.roundedFibreNeighborhood j b) × Circle =>
        ((⟨R.roundedBaseIncl j p.1.1, p.1.2⟩ : R.neighborhood (R.roundedBaseIncl j b)), p.2)) := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine (ContMDiff.subtypeVal_comp_iff (R.neighborhood (R.roundedBaseIncl j b)) _).mp ?_
    exact (R.contMDiff_roundedBaseIncl j).comp (contMDiff_subtype_val.comp contMDiff_fst)
  have hT := (R.trivialization (R.roundedBaseIncl j b)).symm.contMDiff.comp hN
  exact (contMDiff_subtype_val.comp contMDiff_subtype_val).comp hT

/-- **The restricted trivialization** at `b`: the actual trivialization of the circle region over
`ι b`, restricted to the part of `P_j` over the preimage of its base neighbourhood. -/
def roundedTrivialization (b : (R.roundedBaseSurface j).Carrier) :
    R.RoundedTrivSource j b ≃ₘ⟮(R.roundedRegionPiece j).toCarrier.model,
      (SurfaceModel.model (R.roundedBaseSurface j).kind).prod (𝓡 1)⟯
      ((R.roundedFibreNeighborhood j b) × Circle) where
  toFun := R.roundedTrivFun j b
  invFun := R.roundedTrivInv j b
  left_inv := R.roundedTrivInv_roundedTrivFun j b
  right_inv := R.roundedTrivFun_roundedTrivInv j b
  contMDiff_toFun := R.contMDiff_roundedTrivFun j b
  contMDiff_invFun := R.contMDiff_roundedTrivInv j b

/-! ## The fibration and the Raw presentation -/

/-- **The circle fibration of the piece `P_j`** over the compact surface `B_j`, with the actual
trivializations of the circle region restricted. -/
def roundedRegionFibration : CircleFibration (R.roundedRegionPiece j).toCarrier ⊤ where
  base := R.roundedBaseSurface j
  projection := R.roundedTopProjection j
  surjective c := by
    obtain ⟨q, hq⟩ := R.roundedRegionProj_surjective j c
    exact ⟨⟨q, trivial⟩, hq⟩
  smooth := (R.contMDiff_roundedRegionProj j).comp
    (contMDiff_subtype_val (I := (R.roundedRegionPiece j).toCarrier.model)
      (U := (⊤ : TopologicalSpace.Opens (R.roundedRegionPiece j).toCarrier.Carrier)))
  neighborhood := R.roundedFibreNeighborhood j
  mem_neighborhood := R.mem_roundedFibreNeighborhood j
  trivialization := R.roundedTrivialization j
  projection_trivialization _ _ := rfl

theorem roundedRegionFibration_base :
    (R.roundedRegionFibration j).base = R.roundedBaseSurface j :=
  rfl

theorem roundedRegionFibration_projection
    (x : (⊤ : TopologicalSpace.Opens (R.roundedRegionPiece j).toCarrier.Carrier)) :
    (R.roundedRegionFibration j).projection x = R.roundedRegionProj j x.1 :=
  rfl

/-- The single-piece Raw presentation of `P_j` for a family of boundary tori exhausting `∂P_j`. -/
def roundedRegionRawPresentation {n : ℕ} (E : BoundaryTori (R.roundedRegionPiece j).toCarrier n)
    (hb : (R.roundedRegionPiece j).toCarrier.model.boundary
      (R.roundedRegionPiece j).toCarrier.Carrier = E.image) :
    RawGraphPresentation (R.roundedRegionPiece j).toCarrier :=
  singlePieceRawPresentation _ (R.roundedRegionFibration j) E hb

/-- **Raw piece, closed base component.** If the base component has no boundary, the piece is a
closed circle bundle and is a Raw piece in the `hpiece` format of B3. -/
theorem rawPiece_of_roundedRegionPiece_of_boundary_eq_empty
    (h : (SurfaceModel.model (R.roundedBaseSurface j).kind).boundary
      (R.roundedBaseSurface j).Carrier = ∅) :
    ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (R.roundedRegionPiece j).Piece) := by
  have hb : (R.roundedRegionPiece j).toCarrier.model.boundary
      (R.roundedRegionPiece j).toCarrier.Carrier =
        (BoundaryTori.empty (R.roundedRegionPiece j).toCarrier).image := by
    rw [BoundaryTori.empty_image]
    change (𝓡∂ 3).boundary (R.roundedRegionPiece j).Piece = ∅
    rw [R.roundedRegionPiece_boundary_eq, h, preimage_empty]
  exact ⟨(R.roundedRegionPiece j).toCarrier, ⟨R.roundedRegionRawPresentation j _ hb⟩,
    ⟨show (R.roundedRegionPiece j).toCarrier.Carrier ≃ₘ⟮(R.roundedRegionPiece j).toCarrier.model,
      𝓡∂ 3⟯ (R.roundedRegionPiece j).Piece from
      Diffeomorph.refl (𝓡∂ 3) (R.roundedRegionPiece j).Piece ∞⟩⟩

end CircleRegion

end GC.GraphManifold.Assembly
