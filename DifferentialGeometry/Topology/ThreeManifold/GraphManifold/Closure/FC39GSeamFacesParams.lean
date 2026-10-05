import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesBoundary
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySurfaceEmbedding

/-!
# FC39 GROUP G, target `stub_exists_seams_faces` (lane FC39-G-SF): side parametrizations

Steps G0/G2 of the lane sheet (`build-logs/resume/sheet-FC39-G-SF.md`), in the form recorded in
`build-logs/resume/state-FC39-G-SF.md` (successor design): a side parametrization is NOT obtained
by inverting the piece map at boundary points. Instead:

* every actual model boundary face `m` of a piece is an open (and compact) subset of the boundary
  manifold `BoundaryManifold (𝓡∂ 3) P.Piece` (components of a locally connected space are open), so
  its inclusion `boundaryFaceIncl_GSF P m` is a smooth embedding of a compact boundaryless surface
  (`isSmoothEmbedding_boundaryFaceIncl_GSF`, through the universe-polymorphic form
  `isSmoothEmbedding_coe_of_boundary_opens_GSF` of the boundary-surface lemma of
  `PiecewiseLinear/BoundarySurfaceEmbedding.lean`, there stated for `M : Type`);
* `isSmoothEmbedding_of_interior_GSF`: a smooth map of a boundaryless manifold into `W.interior`
  with injective differential that is a topological embedding is a smooth embedding into `W`
  (route: the recharted interior `interiorSeamModel`);
* `exists_sideParam_GSF`: given a smooth embedding `param : S → W` of a surface with model `𝓡 2`
  onto the image `P.map '' m.1 ⊆ W.interior`, the side parametrization is
  `boundaryFaceIncl ∘ D` with `D` the diffeomorphism of equal ranges
  (`IsSmoothEmbedding.diffeomorphOfRangeEq`) between `param` and `P.map ∘ boundaryFaceIncl`;
  `exists_sideParam_torus_GSF` is the same for `Torus` (model `torusModel`), through the linear
  model change `E¹ × E¹ ≃ E²` (`chartedSpaceTransHomeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance boundaryNonempty_GSF : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty (EuclideanSpace ℝ (Fin 2)) from inferInstance

local instance boundaryCharts_GSF {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

local instance boundarySmooth_GSF {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)

/-! ## Smooth embeddings into the interior of a carrier -/

/-- **Smooth embeddings into the interior of a carrier.** A smooth map from a boundaryless
manifold into a carrier, with values in the interior, injective differential and a topological
embedding, is a smooth embedding (the immersion criterion at interior image points,
`Manifold/ImmersionCriterionInteriorTarget.lean`). -/
theorem isSmoothEmbedding_of_interior_GSF (W : CompactCarrier.{u}) {ES HS : Type*}
    [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES] [Nontrivial ES]
    [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless] {S : Type*}
    [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S] {g : S → W.Carrier}
    (hg : ContMDiff IS W.model ∞ g) (hemb : IsEmbedding g)
    (hmf : ∀ z, Injective (mfderiv IS W.model g z)) (hint : ∀ z, g z ∈ W.interior) :
    IsSmoothEmbedding IS W.model ∞ g :=
  DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
    (by simp) hg hemb hmf hint

/-- A smooth embedding of a compact boundaryless manifold composed with a piece map, landing in
`W.interior`, is a smooth embedding into `W`. -/
theorem isSmoothEmbedding_piece_comp_GSF {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    {ES HS : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
    [Nontrivial ES] [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
    {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S] [CompactSpace S]
    {ζ : S → P.Piece} (hζ : IsSmoothEmbedding IS (𝓡∂ 3) ∞ ζ)
    (hint : ∀ z, P.map (ζ z) ∈ W.interior) :
    IsSmoothEmbedding IS W.model ∞ (P.map ∘ ζ) := by
  have hcont : Continuous (P.map ∘ ζ) := P.continuous_map.comp hζ.contMDiff.continuous
  refine isSmoothEmbedding_of_interior_GSF W (P.smooth.comp hζ.contMDiff)
    (hcont.isClosedEmbedding (P.injective.comp hζ.isEmbedding.injective)).isEmbedding
    (fun z => ?_) hint
  rw [mfderiv_comp z (P.mdifferentiable_map (ζ z)) (hζ.contMDiff.mdifferentiableAt (by simp))]
  exact (P.mfderiv_bijective (ζ z)).injective.comp (hζ.isImmersion.mfderiv_injective (by simp) z)

/-! ## Boundary faces as embedded surfaces -/

/-- Universe-polymorphic form of
`PiecewiseLinear.isSmoothEmbedding_coe_of_boundary_surface_openPartialHomeomorph`
(`PiecewiseLinear/BoundarySurfaceEmbedding.lean:15`, stated there for `M : Type`), for the identity
of an open subset of the boundary manifold. -/
theorem isSmoothEmbedding_coe_of_boundary_opens_GSF
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (U : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) M))
    [Nonempty U] :
    IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (fun x : U => ((x : BoundaryManifold (𝓡∂ 3) M) : M)) := by
  classical
  let F : OpenPartialHomeomorph U (BoundaryManifold (𝓡∂ 3) M) :=
    U.openPartialHomeomorphSubtypeCoe inferInstance
  have hFs : F.source = univ := rfl
  have hF : ContMDiffOn (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ F univ :=
    contMDiff_subtype_val.contMDiffOn
  have hFi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡 2) ∞ F.symm F.target := by
    intro y hy
    have hyU : y ∈ U := by
      have h := hy
      rwa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] at h
    have hfun : (fun z : U => F.symm z) = id := by
      funext z
      exact F.left_inv (mem_univ z)
    have h1 : ContMDiffAt (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡 2) ∞
        (fun z : U => F.symm z) ⟨y, hyU⟩ := by
      rw [hfun]
      exact contMDiffAt_id
    exact (contMDiffAt_subtype_iff.mp h1).contMDiffWithinAt
  refine ⟨?_, IsEmbedding.subtypeVal.comp (F.isOpenEmbedding hFs).isEmbedding⟩
  apply IsImmersionOfComplement.isImmersion (F := ℝ)
  intro x
  set y := F x with hydef
  let b := chartAt (HasSmoothBoundary.boundaryH (I := 𝓡∂ 3)) y
  have hb : b ∈ IsManifold.maximalAtlas (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞
      (BoundaryManifold (𝓡∂ 3) M) := IsManifold.chart_mem_maximalAtlas y
  have hbeq : b = BoundaryManifold.boundaryChart (I := 𝓡∂ 3) y :=
    BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := 𝓡∂ 3) y
  let ψ := chartAt (EuclideanHalfSpace 3) (y : M)
  let α : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin 2)) := F.trans b
  have hαs : α.source = F.source ∩ F ⁻¹' b.source := OpenPartialHomeomorph.trans_source F b
  have hαt : α.target = b.target ∩ b.symm ⁻¹' F.target := OpenPartialHomeomorph.trans_target F b
  have hxα : x ∈ α.source := by
    rw [hαs]
    exact ⟨hFs ▸ mem_univ x, mem_chart_source _ y⟩
  have hbsm : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ b b.source :=
    contMDiffOn_of_mem_maximalAtlas hb
  have hbsi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ b.symm b.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hb
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡 2) ∞ U := by
    refine DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn α ?_ ?_
    · rw [hαs]
      exact hbsm.comp (hF.mono (subset_univ _)) fun z hz => hz.2
    · rw [hαt]
      exact hFi.comp (hbsi.mono inter_subset_left) fun u hu => hu.2
  have hψmax : ψ ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hsrcM : ∀ p : BoundaryManifold (𝓡∂ 3) M, p ∈ b.source → (p : M) ∈ ψ.source := by
    intro p hp
    rw [hbeq] at hp
    exact hp
  refine IsImmersionAtOfComplement.mk_of_charts (normalFirstEquiv 2) α ψ hxα
    (hsrcM y (mem_chart_source _ y)) hαmax hψmax (fun z hz => ?_) fun u hu => ?_
  · rw [hαs] at hz
    exact hsrcM _ hz.2
  · have hu' : u ∈ α.target := hu.2
    rw [hαt] at hu'
    obtain ⟨hwb, hwF⟩ := hu'
    have hFeq : F (α.symm u) = b.symm u := by
      change F (F.symm (b.symm u)) = _
      rw [F.right_inv hwF]
    have hmemψ : ((b.symm u : BoundaryManifold (𝓡∂ 3) M) : M) ∈ ψ.source :=
      hsrcM _ (b.map_target hwb)
    have hincl := BoundaryManifold.inclH_boundaryChart_apply (I := 𝓡∂ 3) y (b.symm u) hmemψ
    rw [← hbeq, b.right_inv hwb] at hincl
    change (𝓡∂ 3) (ψ ((F (α.symm u)) : M)) = normalFirstEquiv 2 (u, 0)
    rw [hFeq, ← hincl]
    exact PiecewiseLinear.inclEuclidean_three_eq_normalFirstEquiv u

section BoundaryFace

variable {W : CompactCarrier.{u}} (P : PieceEmbedding W) (m : ModelBoundaryFace P)

/-- The points of the boundary manifold of a piece lying in the model boundary face `m`. -/
def boundaryFaceSet_GSF : Set (BoundaryManifold (𝓡∂ 3) P.Piece) :=
  {p | (p : P.Piece) ∈ m.1}

theorem boundaryFaceSet_eq_GSF :
    ∃ y : BoundaryManifold (𝓡∂ 3) P.Piece, boundaryFaceSet_GSF P m = connectedComponent y := by
  obtain ⟨x, hx, hm⟩ := m.2
  refine ⟨⟨x, hx⟩, ?_⟩
  ext p
  change (p : P.Piece) ∈ m.1 ↔ _
  rw [hm, connectedComponentIn_eq_image hx]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have : q = p := Subtype.ext hqp
    rw [← this]
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem isOpen_boundaryFaceSet_GSF : IsOpen (boundaryFaceSet_GSF P m) := by
  have _ : LocallyConnectedSpace (BoundaryManifold (𝓡∂ 3) P.Piece) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  obtain ⟨y, hy⟩ := boundaryFaceSet_eq_GSF P m
  rw [hy]
  exact isOpen_connectedComponent

theorem isClosed_boundaryFaceSet_GSF : IsClosed (boundaryFaceSet_GSF P m) := by
  obtain ⟨y, hy⟩ := boundaryFaceSet_eq_GSF P m
  rw [hy]
  exact isClosed_connectedComponent

/-- The face `m` as an open subset of the boundary manifold. -/
def boundaryFaceOpens_GSF : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) P.Piece) :=
  ⟨boundaryFaceSet_GSF P m, isOpen_boundaryFaceSet_GSF P m⟩

/-- The inclusion of the face `m` into the piece. -/
def boundaryFaceIncl_GSF : boundaryFaceOpens_GSF P m → P.Piece :=
  fun x => ((x : BoundaryManifold (𝓡∂ 3) P.Piece) : P.Piece)

instance nonempty_boundaryFaceOpens_GSF : Nonempty (boundaryFaceOpens_GSF P m) := by
  obtain ⟨x, hx, hm⟩ := m.2
  refine ⟨⟨⟨x, hx⟩, ?_⟩⟩
  change x ∈ m.1
  rw [hm]
  exact mem_connectedComponentIn hx

instance compactSpace_boundaryManifold_GSF : CompactSpace (BoundaryManifold (𝓡∂ 3) P.Piece) :=
  (isClosedEmbedding_boundaryInclusion (I := 𝓡∂ 3) (M := P.Piece)).compactSpace

instance compactSpace_boundaryFaceOpens_GSF : CompactSpace (boundaryFaceOpens_GSF P m) :=
  isCompact_iff_compactSpace.mp (isClosed_boundaryFaceSet_GSF P m).isCompact

theorem isSmoothEmbedding_boundaryFaceIncl_GSF :
    IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (boundaryFaceIncl_GSF P m) :=
  isSmoothEmbedding_coe_of_boundary_opens_GSF (boundaryFaceOpens_GSF P m)

theorem range_boundaryFaceIncl_GSF : range (boundaryFaceIncl_GSF P m) = m.1 := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hq
    exact ⟨⟨⟨q, m.subset hq⟩, hq⟩, rfl⟩

end BoundaryFace

/-! ## Side parametrizations -/

/-- **The side parametrization, model `𝓡 2`.** A smooth embedding `param` of a surface onto the
image of a model boundary face, inside `W.interior`, factors through the piece as a smooth
embedding onto the face. -/
theorem exists_sideParam_GSF {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (m : ModelBoundaryFace P) {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {param : S → W.Carrier} (hparam : IsSmoothEmbedding (𝓡 2) W.model ∞ param)
    (hrange : range param = P.map '' m.1) (hint : range param ⊆ W.interior) :
    ∃ ψ : S → P.Piece, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ ψ ∧ range ψ = m.1 ∧
      ∀ z, P.map (ψ z) = param z := by
  have hζ := isSmoothEmbedding_boundaryFaceIncl_GSF P m
  have hrζ := range_boundaryFaceIncl_GSF P m
  have hι : IsSmoothEmbedding (𝓡 2) W.model ∞ (P.map ∘ boundaryFaceIncl_GSF P m) := by
    refine isSmoothEmbedding_piece_comp_GSF P hζ fun z => hint ?_
    rw [hrange, ← hrζ]
    exact ⟨_, ⟨z, rfl⟩, rfl⟩
  have hr : range param = range (P.map ∘ boundaryFaceIncl_GSF P m) := by
    rw [range_comp, hrζ, hrange]
  let D := hparam.diffeomorphOfRangeEq hι hr
  refine ⟨boundaryFaceIncl_GSF P m ∘ D,
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp _ hζ D, ?_,
    fun z => hparam.comp_diffeomorphOfRangeEq hι hr z⟩
  rw [← hrζ]
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨D z, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨D.symm y, ?_⟩
    change boundaryFaceIncl_GSF P m (D (D.symm y)) = _
    rw [Diffeomorph.apply_symm_apply]

/-- The linear model change `E¹ × E¹ ≃ E²` of the torus model. -/
def torusModelLinearEquiv_GSF :
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- The homeomorphism of model spaces of the torus model change. -/
def torusModelHomeomorph_GSF :
    ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  torusModelLinearEquiv_GSF.toHomeomorph

theorem torusModelHomeomorph_compat_GSF
    (y : ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :
    (𝓡 2) (torusModelHomeomorph_GSF y) = torusModelLinearEquiv_GSF (torusModel y) :=
  rfl

/-- **The side parametrization, the torus.** -/
theorem exists_sideParam_torus_GSF {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (m : ModelBoundaryFace P) {param : Torus → W.Carrier}
    (hparam : IsSmoothEmbedding torusModel W.model ∞ param)
    (hrange : range param = P.map '' m.1) (hint : range param ⊆ W.interior) :
    ∃ ψ : Torus → P.Piece, IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ ψ ∧ range ψ = m.1 ∧
      ∀ t, P.map (ψ t) = param t := by
  let _ := DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := Torus)
    torusModelHomeomorph_GSF
  have _ : IsManifold (𝓡 2) ∞ Torus :=
    DifferentialGeometry.Manifold.isManifold_transHomeomorph torusModel (𝓡 2)
      torusModelHomeomorph_GSF torusModelLinearEquiv_GSF torusModelHomeomorph_compat_GSF
  have hparam' : IsSmoothEmbedding (𝓡 2) W.model ∞ param :=
    (DifferentialGeometry.Manifold.isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff
      torusModel (𝓡 2) torusModelHomeomorph_GSF torusModelLinearEquiv_GSF
      torusModelHomeomorph_compat_GSF W.model).mpr hparam
  obtain ⟨ψ, hψ, hψr, hψm⟩ := exists_sideParam_GSF P m hparam' hrange hint
  refine ⟨ψ, ?_, hψr, hψm⟩
  exact (DifferentialGeometry.Manifold.isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff
    torusModel (𝓡 2) torusModelHomeomorph_GSF torusModelLinearEquiv_GSF
    torusModelHomeomorph_compat_GSF (𝓡∂ 3)).mp hψ

end GC.GraphManifold.Assembly.FC39P0
