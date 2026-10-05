import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate

/-!
# FC42 packet T1a: the rounded base of a circle region as a surface with boundary

Review 40 §3.1, route A. For a circle region `R` of the FC39 certificate the rounded base
`B_ρ = {b | R.rounding b ≤ 0}` is a regular sublevel of the smooth function `R.rounding` on the
boundaryless surface `R.Base` (fields `rounding_smooth`, `rounding_regular`, `rounded_compact`).
The tree's `SmoothBoundaryAtlas.regularSublevel` with `n := 1` (`GraphManifold/RegularSublevelAtlas.lean`),
used exactly as for `unitDiscAtlas` (`GraphManifold/SolidTorus.lean`), gives its `𝓡∂ 2` atlas; the map
criteria `SmoothBoundaryAtlas.contMDiff_subtype_val` and `contMDiff_iff_subtype_val`
(`Topology/Manifold/SmoothBoundaryAtlas/Maps.lean`) give the smooth maps out of and into it.

* `CircleRegion.roundedBase`, `CircleRegion.roundedBaseAtlas` and the named instances
  `roundedBase_{chartedSpace,isManifold,compactSpace,locallyConnectedSpace}_ASMTOR`;
* `roundedBase_isBoundaryPoint_iff` (`∂B_ρ = {rounding = 0}`), `roundedBase_isInteriorPoint_iff`;
* the connected components `roundedBaseComponent j` (open and closed, finitely many), each a
  `CompactSurface` `roundedBaseSurface j` of kind `withBoundary` (its boundary may be empty: a closed
  base component is allowed; no orientability is assumed), with the inclusion `roundedBaseIncl j`
  into `R.Base`, the smoothness criteria, and the boundary formula.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The model half-space `ℍⁿ` is locally connected. -/
theorem locallyConnectedSpace_euclideanHalfSpace_of_neZero (n : ℕ) [NeZero n] :
    LocallyConnectedSpace (EuclideanHalfSpace n) := by
  have : LocallyPathConnectedSpace (range (𝓡∂ n)) :=
    (𝓡∂ n).convex_range.locallyPathConnectedSpace
  exact (𝓡∂ n).isClosedEmbedding.isEmbedding.toHomeomorph.locallyConnectedSpace

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- The rounded base `B_ρ = {b | rounding b ≤ 0}` of a circle region. -/
def roundedBase : Set R.Base :=
  {b | R.rounding b ≤ 0}

/-- The `𝓡∂ 2` atlas of the rounded base: the regular sublevel atlas with `n := 1`, exactly as
`unitDiscAtlas`. -/
def roundedBaseAtlas : SmoothBoundaryAtlas (𝓡 2) 2 R.roundedBase :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 2) (n := 1) finrank_euclideanSpace_fin
    R.rounding_smooth 0 R.rounding_regular

instance roundedBase_chartedSpace_ASMTOR : ChartedSpace (EuclideanHalfSpace 2) R.roundedBase :=
  R.roundedBaseAtlas.toChartedSpace

instance roundedBase_isManifold_ASMTOR : IsManifold (𝓡∂ 2) ∞ R.roundedBase :=
  R.roundedBaseAtlas.isManifold

instance roundedBase_compactSpace_ASMTOR : CompactSpace R.roundedBase :=
  isCompact_iff_compactSpace.mp R.rounded_compact

instance roundedBase_locallyConnectedSpace_ASMTOR : LocallyConnectedSpace R.roundedBase := by
  have := locallyConnectedSpace_euclideanHalfSpace_of_neZero 2
  exact ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) R.roundedBase

theorem rounding_le_zero_of_mem (b : R.roundedBase) : R.rounding b ≤ 0 :=
  b.2

variable {R} in
/-- `∂B_ρ = {rounding = 0}`. -/
theorem roundedBase_isBoundaryPoint_iff {b : R.roundedBase} :
    (𝓡∂ 2).IsBoundaryPoint b ↔ R.rounding b = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 2) (n := 1)
    finrank_euclideanSpace_fin R.rounding_smooth 0 R.rounding_regular b

variable {R} in
theorem roundedBase_isInteriorPoint_iff {b : R.roundedBase} :
    (𝓡∂ 2).IsInteriorPoint b ↔ R.rounding b < 0 :=
  SmoothBoundaryAtlas.regularSublevel_isInteriorPoint_iff (𝓡 2) (n := 1)
    finrank_euclideanSpace_fin R.rounding_smooth 0 R.rounding_regular b

theorem contMDiff_roundedBase_val :
    ContMDiff (𝓡∂ 2) (𝓡 2) ∞ (Subtype.val : R.roundedBase → R.Base) :=
  R.roundedBaseAtlas.contMDiff_subtype_val

variable {R} in
theorem contMDiff_roundedBase_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {f : X → R.roundedBase} :
    ContMDiff J (𝓡∂ 2) ∞ f ↔ ContMDiff J (𝓡 2) ∞ (Subtype.val ∘ f) :=
  R.roundedBaseAtlas.contMDiff_iff_subtype_val f

variable {R} in
theorem contMDiffOn_roundedBase_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {f : X → R.roundedBase} {s : Set X} :
    ContMDiffOn J (𝓡∂ 2) ∞ f s ↔ ContMDiffOn J (𝓡 2) ∞ (Subtype.val ∘ f) s :=
  R.roundedBaseAtlas.contMDiffOn_iff_subtype_val f s

/-! ## The components -/

/-- The connected component `j` of the rounded base, as an open subset. -/
def roundedBaseComponent (j : ConnectedComponents R.roundedBase) :
    TopologicalSpace.Opens R.roundedBase :=
  ⟨ConnectedComponents.mk ⁻¹' {j}, (isOpen_discrete {j}).preimage ConnectedComponents.continuous_coe⟩

theorem coe_roundedBaseComponent (j : ConnectedComponents R.roundedBase) :
    (R.roundedBaseComponent j : Set R.roundedBase) = ConnectedComponents.mk ⁻¹' {j} :=
  rfl

variable {R} in
theorem mem_roundedBaseComponent_iff {j : ConnectedComponents R.roundedBase} {b : R.roundedBase} :
    b ∈ R.roundedBaseComponent j ↔ ConnectedComponents.mk b = j :=
  Iff.rfl

theorem isClosed_roundedBaseComponent (j : ConnectedComponents R.roundedBase) :
    IsClosed (R.roundedBaseComponent j : Set R.roundedBase) :=
  (isClosed_discrete {j}).preimage ConnectedComponents.continuous_coe

theorem isConnected_roundedBaseComponent (j : ConnectedComponents R.roundedBase) :
    IsConnected (R.roundedBaseComponent j : Set R.roundedBase) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe j
  change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- The component `j` of the rounded base as a compact connected surface of kind `withBoundary`. -/
def roundedBaseSurface (j : ConnectedComponents R.roundedBase) : CompactSurface.{u} :=
  haveI : CompactSpace (R.roundedBaseComponent j) :=
    isCompact_iff_compactSpace.mp (R.isClosed_roundedBaseComponent j).isCompact
  haveI : SecondCountableTopology (EuclideanHalfSpace 2) :=
    inferInstanceAs (SecondCountableTopology {x : EuclideanSpace ℝ (Fin 2) // 0 ≤ x 0})
  { kind := .withBoundary
    Carrier := R.roundedBaseComponent j
    charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 2) (R.roundedBaseComponent j))
    smooth := (inferInstance : IsManifold (𝓡∂ 2) ∞ (R.roundedBaseComponent j))
    compact := inferInstance
    secondCountable :=
      ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace 2) (R.roundedBaseComponent j)
    connected := Subtype.connectedSpace (R.isConnected_roundedBaseComponent j) }

theorem roundedBaseSurface_kind (j : ConnectedComponents R.roundedBase) :
    (R.roundedBaseSurface j).kind = .withBoundary :=
  rfl

/-- The carrier of a rounded base surface, read as the component. -/
def roundedBaseSurfaceEquiv (j : ConnectedComponents R.roundedBase) :
    (R.roundedBaseSurface j).Carrier ≃ R.roundedBaseComponent j :=
  Equiv.refl _

/-- The inclusion of the component `j` of the rounded base into the base. -/
def roundedBaseIncl (j : ConnectedComponents R.roundedBase) :
    (R.roundedBaseSurface j).Carrier → R.Base :=
  fun b => ((show R.roundedBaseComponent j from b) : R.roundedBase).val

theorem roundedBaseIncl_injective (j : ConnectedComponents R.roundedBase) :
    Injective (R.roundedBaseIncl j) := fun _ _ h =>
  Subtype.val_injective (Subtype.val_injective h)

theorem rounding_roundedBaseIncl_le (j : ConnectedComponents R.roundedBase)
    (b : (R.roundedBaseSurface j).Carrier) : R.rounding (R.roundedBaseIncl j b) ≤ 0 :=
  ((show R.roundedBaseComponent j from b) : R.roundedBase).2

theorem range_roundedBaseIncl (j : ConnectedComponents R.roundedBase) :
    range (R.roundedBaseIncl j) =
      Subtype.val '' (R.roundedBaseComponent j : Set R.roundedBase) := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, (show R.roundedBaseComponent j from b).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(⟨y, hy⟩ : R.roundedBaseComponent j), rfl⟩

variable {R} in
theorem mem_range_roundedBaseIncl_iff {j : ConnectedComponents R.roundedBase} {x : R.Base} :
    x ∈ range (R.roundedBaseIncl j) ↔
      ∃ hx : R.rounding x ≤ 0, ConnectedComponents.mk (⟨x, hx⟩ : R.roundedBase) = j := by
  rw [range_roundedBaseIncl]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hj⟩
    exact ⟨⟨x, hx⟩, hj, rfl⟩

theorem iUnion_range_roundedBaseIncl :
    (⋃ j, range (R.roundedBaseIncl j)) = R.roundedBase := by
  ext x
  simp only [mem_iUnion, mem_range_roundedBaseIncl_iff]
  constructor
  · rintro ⟨j, hx, -⟩
    exact hx
  · intro hx
    exact ⟨_, hx, rfl⟩

theorem pairwise_disjoint_range_roundedBaseIncl :
    Pairwise fun j j' : ConnectedComponents R.roundedBase =>
      Disjoint (range (R.roundedBaseIncl j)) (range (R.roundedBaseIncl j')) := by
  intro j j' hjj'
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨h1, hj⟩ := mem_range_roundedBaseIncl_iff.1 hx
  obtain ⟨h2, hj'⟩ := mem_range_roundedBaseIncl_iff.1 hx'
  exact hjj' (hj.symm.trans hj')

theorem contMDiff_roundedBaseIncl (j : ConnectedComponents R.roundedBase) :
    ContMDiff (SurfaceModel.model (R.roundedBaseSurface j).kind) (𝓡 2) ∞ (R.roundedBaseIncl j) :=
  R.contMDiff_roundedBase_val.comp
    (contMDiff_subtype_val (I := 𝓡∂ 2) (U := R.roundedBaseComponent j))

variable {R} in
/-- Smooth maps into a rounded base surface are the maps whose composition with the inclusion
into the base is smooth. -/
theorem contMDiff_roundedBaseSurface_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {j : ConnectedComponents R.roundedBase} {f : X → (R.roundedBaseSurface j).Carrier} :
    ContMDiff J (SurfaceModel.model (R.roundedBaseSurface j).kind) ∞ f ↔
      ContMDiff J (𝓡 2) ∞ (R.roundedBaseIncl j ∘ f) := by
  change ContMDiff J (𝓡∂ 2) ∞ (show X → R.roundedBaseComponent j from f) ↔ _
  rw [← ContMDiff.subtypeVal_comp_iff (R.roundedBaseComponent j), contMDiff_roundedBase_iff]
  rfl

variable {R} in
theorem contMDiffOn_roundedBaseSurface_iff {F G X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X]
    [ChartedSpace G X] {j : ConnectedComponents R.roundedBase}
    {f : X → (R.roundedBaseSurface j).Carrier} {s : Set X} :
    ContMDiffOn J (SurfaceModel.model (R.roundedBaseSurface j).kind) ∞ f s ↔
      ContMDiffOn J (𝓡 2) ∞ (R.roundedBaseIncl j ∘ f) s := by
  change ContMDiffOn J (𝓡∂ 2) ∞ (show X → R.roundedBaseComponent j from f) s ↔ _
  have h1 : ContMDiffOn J (𝓡∂ 2) ∞ (show X → R.roundedBaseComponent j from f) s ↔
      ContMDiffOn J (𝓡∂ 2) ∞ (Subtype.val ∘ (show X → R.roundedBaseComponent j from f)) s :=
    forall₂_congr fun x _ => (ContMDiffWithinAt.subtypeVal_comp_iff _ _ _ _).symm
  rw [h1, contMDiffOn_roundedBase_iff]
  rfl

variable {R} in
/-- `∂B_j = B_j ∩ {rounding = 0}`. -/
theorem roundedBaseSurface_isBoundaryPoint_iff {j : ConnectedComponents R.roundedBase}
    {b : (R.roundedBaseSurface j).Carrier} :
    (SurfaceModel.model (R.roundedBaseSurface j).kind).IsBoundaryPoint b ↔
      R.rounding (R.roundedBaseIncl j b) = 0 := by
  change (𝓡∂ 2).IsBoundaryPoint (show R.roundedBaseComponent j from b) ↔ _
  rw [ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val]
  exact roundedBase_isBoundaryPoint_iff

variable {R} in
theorem roundedBaseSurface_isInteriorPoint_iff {j : ConnectedComponents R.roundedBase}
    {b : (R.roundedBaseSurface j).Carrier} :
    (SurfaceModel.model (R.roundedBaseSurface j).kind).IsInteriorPoint b ↔
      R.rounding (R.roundedBaseIncl j b) < 0 := by
  change (𝓡∂ 2).IsInteriorPoint (show R.roundedBaseComponent j from b) ↔ _
  rw [ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val]
  exact roundedBase_isInteriorPoint_iff

end CircleRegion

end GC.GraphManifold.Assembly
