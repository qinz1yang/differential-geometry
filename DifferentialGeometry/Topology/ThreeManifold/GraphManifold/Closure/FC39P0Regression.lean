import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Corners
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpace
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskSmale

/-!
# FC39 producer, packet P0 (gate 1), §6: the three regression tests (general form)

Task-47 draft §6 (disposition D9): for each counterexample of review 46 §3.1, the OLD dry link holds
on the data and the conclusion of the old stub fails, and the NEW contract rejects the data. The
dry links are transcribed VERBATIM from `build-logs/scratch/FC39-DRY/FC39Dry.lean:575–606`, on the
row parts they actually read (`DryEdgeLink`, `DrySeamLink`, `DryCircleLink`). The tests are proved
for ALL data of the relevant shape (the S³ instances of the draft are corollaries once the S³
inhabitants exist):

* **A (duplicate handle).** `EdgeLayer.duplicate H h₀` registers the handle `h₀` twice. From ANY
  new registration `EdgeComponentsLink P M H`: the dry `EdgeLink` holds for the duplicated layer
  (`EdgeComponentsLink.dryEdgeLink`, `DryEdgeLink.duplicate`); the old S4 conclusion fails (no
  `CoverLayer`: the two handle images have a common interior point) and the old S9 conclusion fails
  (no `HandleEndLayer`: the two end disks coincide); the new contract has no registration of the
  duplicated layer (`isEmpty_componentsLink_duplicate`: three handles cannot have pairwise disjoint
  end disks over two components — derived from `endDisks_disjoint_of_components`).
* **B (pseudo-seam).** A sphere seam whose side is a vertex with EMPTY model boundary (a closed
  zero piece): the dry `SeamLink` holds when edge piece, region, ports and torus seams are empty;
  no `FaceLayer` exists (`sphereSeam_face` + `face_exhausted`); no `SeamFacesLink` exists (the side
  face would be an actual model boundary component of an empty boundary), and without slim pieces
  every `SeamFacesLink` has no sphere seam at all.
* **C (swapped corner axes).** `swapAxesRegion` and `RimChartLayer.swap` exchange the two
  axes of every corner chart, the first / second labels and the two rim coordinates. The dry
  `CircleLink` survives, `RimChartLayer.swap` is a rim chart layer, the old S11b formula
  (`vertex ⇔ y ≤ 0`) fails at `(x, y) = (-1/2, 1/2)`, and the new contract rejects the swapped data
  (`X = λx` would force `λ = 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsRegression_FC39P0 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}}

/-! ## A — duplicate handle -/

/-- The dry `EdgeLink` (FC39Dry.lean:588), on the edge bundle it reads. -/
def DryEdgeLink (P : EdgeBundle W) (H : EdgeLayer W) : Prop :=
  (⋃ h, range (H.handle h).map) ∪ (⋃ e, range (H.edgeCircle e).piece.map) = P.edgePiece ∧
    (∀ h b, ∃ c ∈ frontier P.cbase, (H.handle h).endDisk b = P.disk c) ∧
    ∀ h (t : Icc (0 : ℝ) 1), ∃ c ∈ P.cbase,
      (fun x : ClosedCell 2 => (H.handle h).map (x, t)) '' diskRim = P.rim c

/-- The layer with the handle `h₀` registered twice (the new index `0` is a copy of `h₀`). -/
def EdgeLayer.duplicate (H : EdgeLayer W) (h₀ : Fin H.handleCount) : EdgeLayer W where
  handleCount := H.handleCount + 1
  handle := Fin.cons (H.handle h₀) H.handle
  edgeCircleCount := H.edgeCircleCount
  edgeCircle := H.edgeCircle

theorem EdgeLayer.duplicate_handle_zero (H : EdgeLayer W) (h₀ : Fin H.handleCount) :
    (H.duplicate h₀).handle (0 : Fin (H.handleCount + 1)) = H.handle h₀ :=
  rfl

theorem EdgeLayer.duplicate_handle_succ (H : EdgeLayer W) (h₀ i : Fin H.handleCount) :
    (H.duplicate h₀).handle i.succ = H.handle i :=
  rfl

theorem EdgeLayer.duplicate_handle_cases (H : EdgeLayer W) (h₀ : Fin H.handleCount)
    (i : Fin (H.duplicate h₀).handleCount) : ∃ j, (H.duplicate h₀).handle i = H.handle j := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact ⟨h₀, rfl⟩
  · exact ⟨j, rfl⟩

/-- The old link holds for every NEW registration. -/
theorem EdgeComponentsLink.dryEdgeLink {P : EdgeBundle W} {M : EdgeComponentModels P}
    {H : EdgeLayer W} (L : EdgeComponentsLink P M H) : DryEdgeLink P H := by
  refine ⟨L.iUnion_ranges_eq_edgePiece, fun h b =>
    ⟨(L.endOfHandle h b).1, (L.endOfHandle h b).2, L.endDisk_eq h b⟩, fun h t =>
    ⟨M.intervalBase (L.handleEquiv h) t, ?_, L.handle_rim h t⟩⟩
  apply ActualComponent.subset
  rw [← M.intervalBase_range]
  exact mem_range_self t

/-- The old link survives the duplication. -/
theorem DryEdgeLink.duplicate {P : EdgeBundle W} {H : EdgeLayer W} (hL : DryEdgeLink P H)
    (h₀ : Fin H.handleCount) : DryEdgeLink P (H.duplicate h₀) := by
  obtain ⟨hu, he, hr⟩ := hL
  refine ⟨?_, fun h b => ?_, fun h t => ?_⟩
  · rw [← hu]
    congr 1
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      obtain ⟨j, hj⟩ := H.duplicate_handle_cases h₀ i
      rw [hj] at hi
      exact mem_iUnion.2 ⟨j, hi⟩
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨j.succ, hj⟩
  · obtain ⟨j, hj⟩ := H.duplicate_handle_cases h₀ h
    rw [hj]
    exact he j b
  · obtain ⟨j, hj⟩ := H.duplicate_handle_cases h₀ h
    rw [hj]
    exact hr j t

/-- The centre of the closed disk. -/
def diskCentre : ClosedCell 2 :=
  ⟨0, by simp⟩

/-- The model-interior point `(0, 1/2)` of a product handle. -/
theorem handleCentre_isInteriorPoint :
    ((𝓡∂ 2).prod (𝓡∂ 1)).IsInteriorPoint
      (diskCentre, (⟨1 / 2, by norm_num, by norm_num⟩ : Icc (0 : ℝ) 1)) := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, handle_isBoundaryPoint_iff]
  rintro (h | h | h)
  · rw [mem_diskRim_iff] at h
    simp [diskCentre] at h
  · have := congrArg Subtype.val h
    norm_num [iccEnd] at this
  · have := congrArg Subtype.val h
    norm_num [iccEnd] at this

/-- **Old S4 fails**: no cover layer for a duplicated handle. -/
theorem not_coverLayer_duplicate (H : EdgeLayer W) (h₀ : Fin H.handleCount) (V : VertexLayer W)
    (circ : CircleRegion W) : ¬ CoverLayer W V (H.duplicate h₀) circ := by
  intro hC
  have hne : (0 : Fin (H.handleCount + 1)) ≠ h₀.succ := (Fin.succ_ne_zero h₀).symm
  have hd : Disjoint (interior (range (H.handle h₀).map)) (interior (range (H.handle h₀).map)) :=
    hC.handle_disjoint hne
  have hx := (H.handle h₀).map_mem_interior_range handleCentre_isInteriorPoint
  exact Set.disjoint_left.1 hd hx hx

/-- **Old S9 fails**: no handle-end layer for a duplicated handle. -/
theorem isEmpty_handleEndLayer_duplicate (H : EdgeLayer W) (h₀ : Fin H.handleCount) {n : ℕ}
    {E : BoundaryTori W n} (V : VertexLayer W) {circ : CircleRegion W} {S : SeamLayer W V circ}
    {O : PortLayer W E V} (F : FaceLayer W E V S O) :
    IsEmpty (HandleEndLayer W V (H.duplicate h₀) F) := by
  refine ⟨fun HE => ?_⟩
  have hne : ((0 : Fin (H.handleCount + 1)), false) ≠ (h₀.succ, false) := by
    simp only [ne_eq, Prod.mk.injEq, and_true]
    exact (Fin.succ_ne_zero h₀).symm
  have hd : Disjoint ((H.handle h₀).endDisk false) ((H.handle h₀).endDisk false) :=
    HE.endDisk_disjoint _ _ _ _ hne
  have hx : (H.handle h₀).map (diskCentre, iccEnd false) ∈ (H.handle h₀).endDisk false :=
    ⟨diskCentre, rfl⟩
  exact Set.disjoint_left.1 hd hx hx

/-- **The new contract rejects the duplicated layer** (for every edge bundle and component export).
-/
theorem isEmpty_componentsLink_duplicate (P : EdgeBundle W) (M : EdgeComponentModels P)
    (H : EdgeLayer W) (h₀ : Fin H.handleCount) :
    IsEmpty (EdgeComponentsLink P M (H.duplicate h₀)) := by
  refine ⟨fun L => ?_⟩
  have hne : ((0 : Fin (H.handleCount + 1)), false) ≠ (h₀.succ, false) := by
    simp only [ne_eq, Prod.mk.injEq, and_true]
    exact (Fin.succ_ne_zero h₀).symm
  have hd : Disjoint ((H.handle h₀).endDisk false) ((H.handle h₀).endDisk false) :=
    L.endDisks_disjoint_of_components hne
  have hx : (H.handle h₀).map (diskCentre, iccEnd false) ∈ (H.handle h₀).endDisk false :=
    ⟨diskCentre, rfl⟩
  exact Set.disjoint_left.1 hd hx hx

/-- **Regression test A.** From any new registration of `H` and any handle `h₀`: the dry link holds
for the duplicated layer, the old S4 and S9 conclusions fail, the new contract rejects it. -/
theorem regressionA {P : EdgeBundle W} {M : EdgeComponentModels P} {H : EdgeLayer W}
    (L : EdgeComponentsLink P M H) (h₀ : Fin H.handleCount) :
    DryEdgeLink P (H.duplicate h₀) ∧
      (∀ (V : VertexLayer W) (circ : CircleRegion W), ¬ CoverLayer W V (H.duplicate h₀) circ) ∧
      (∀ {n : ℕ} {E : BoundaryTori W n} (V : VertexLayer W) {circ : CircleRegion W}
        {S : SeamLayer W V circ} {O : PortLayer W E V} (F : FaceLayer W E V S O),
          IsEmpty (HandleEndLayer W V (H.duplicate h₀) F)) ∧
      IsEmpty (EdgeComponentsLink P M (H.duplicate h₀)) :=
  ⟨L.dryEdgeLink.duplicate h₀, not_coverLayer_duplicate H h₀,
    fun V _ _ _ F => isEmpty_handleEndLayer_duplicate H h₀ V F,
    isEmpty_componentsLink_duplicate P M H h₀⟩

/-! ## B — pseudo-seam inside a vertex with empty model boundary -/

/-- The dry `SeamLink` (FC39Dry.lean:598), on the sets it reads. -/
def DrySeamLink {n : ℕ} (P : EdgeBundle W) (R : CircleBundle W) (E : BoundaryTori W n)
    {V : VertexLayer W} {circ : CircleRegion W} (S : SeamLayer W V circ) : Prop :=
  (∀ c b, (S.torusSide c b).isSome) ∧
    (∀ c, Disjoint (closure (S.torusSeam c).collar.target) (P.edgePiece ∪ R.region)) ∧
    (∀ c, Disjoint (closure (S.sphereSeam c).collar.target) (P.edgePiece ∪ R.region)) ∧
    (∀ i c, Disjoint (E.collar i).target (S.torusSeam c).collar.target) ∧
    (∀ i c, Disjoint (E.collar i).target (S.sphereSeam c).collar.target)

/-- The dry `SeamLink` holds when there is no edge piece, no circle region, no port and no torus
seam. -/
theorem drySeamLink_of_empty (P : EdgeBundle W) (R : CircleBundle W) (E : BoundaryTori W 0)
    {V : VertexLayer W} {circ : CircleRegion W} (S : SeamLayer W V circ)
    (hP : P.edgePiece = ∅) (hR : R.region = ∅) (hT : S.torusSeamCount = 0) :
    DrySeamLink P R E S := by
  have hc : ∀ c : Fin S.torusSeamCount, False := fun c => absurd c.2 (by omega)
  refine ⟨fun c => (hc c).elim, fun c => (hc c).elim, fun c => ?_, fun i => i.elim0,
    fun i => i.elim0⟩
  rw [hP, hR, union_empty]
  exact disjoint_empty _

/-- A point of the standard sphere. -/
def closureSpherePoint : ClosureSphere.{u} :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- **Old S8 fails**: a sphere seam with a side on a vertex with empty model boundary has no face
layer. -/
theorem isEmpty_faceLayer_of_side_boundary_empty {n : ℕ} {E : BoundaryTori W n}
    {V : VertexLayer W} {circ : CircleRegion W} (S : SeamLayer W V circ) (O : PortLayer W E V)
    (c : Fin S.sphereSeamCount) (b : Bool)
    (hk : (𝓡∂ 3).boundary (V.vertex (S.sphereSide c b)).piece.Piece = ∅) :
    IsEmpty (FaceLayer W E V S O) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨f, hfo, hfk⟩ := F.sphereSeam_face c b
  have hface := (F.face_sphereSeam f c b hfk).1
  have hx : (S.sphereSeam c).collar (closureSpherePoint, 0) ∈ F.face f := by
    rw [hface]
    exact ⟨closureSpherePoint, rfl⟩
  have hsub : F.face f ⊆ (V.vertex (F.faceOwner f)).boundaryImage := by
    intro y hy
    rw [← F.face_exhausted (F.faceOwner f)]
    exact mem_iUnion₂.2 ⟨f, rfl, hy⟩
  have hy := hsub hx
  rw [hfo, Vertex.boundaryImage, hk, image_empty] at hy
  exact hy

/-- **The new contract rejects it**: a seam side must be an actual model boundary component. -/
theorem isEmpty_seamFacesLink_of_side_boundary_empty {n : ℕ} {E : BoundaryTori W n}
    (Rw : FC39RowsV2 W E) {V : VertexLayer W} (VL : VertexModelLink Rw V) (O : PortLayer W E V)
    {circ : CircleRegion W} (S : SeamLayer W V circ) (F : FaceLayer W E V S O)
    (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier) (c : Fin S.sphereSeamCount) (b : Bool)
    (hk : (𝓡∂ 3).boundary (V.vertex (S.sphereSide c b)).piece.Piece = ∅) :
    IsEmpty (SeamFacesLink Rw V VL O S F N) := by
  refine ⟨fun L => ?_⟩
  obtain ⟨x, hx, -⟩ := (L.sphereSideFace c b).2
  rw [hk] at hx
  exact hx

/-- Without slim pieces there is no actual shared face, hence no sphere seam in any joint link. -/
theorem SeamFacesLink.sphereSeamCount_eq_zero {n : ℕ} {E : BoundaryTori W n}
    {Rw : FC39RowsV2 W E} {V : VertexLayer W} {VL : VertexModelLink Rw V} {O : PortLayer W E V}
    {circ : CircleRegion W} {S : SeamLayer W V circ} {F : FaceLayer W E V S O}
    {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier} (L : SeamFacesLink Rw V VL O S F N)
    (h : Rw.slim.count = 0) : S.sphereSeamCount = 0 := by
  by_contra hne
  have hσ := (L.sphereEquiv ⟨0, Nat.pos_of_ne_zero hne⟩).1.1.1.1.2
  omega

/-- **Regression test B.** A sphere seam with a side on a vertex with empty model boundary, with
empty edge piece, circle region, ports and torus seams: the dry link holds, the old S8 conclusion
fails, the new contract rejects it. -/
theorem regressionB (P : EdgeBundle W) (R : CircleBundle W) (E : BoundaryTori W 0)
    {V : VertexLayer W} {circ : CircleRegion W} (S : SeamLayer W V circ) (O : PortLayer W E V)
    (hP : P.edgePiece = ∅) (hR : R.region = ∅) (hT : S.torusSeamCount = 0)
    (c : Fin S.sphereSeamCount) (b : Bool)
    (hk : (𝓡∂ 3).boundary (V.vertex (S.sphereSide c b)).piece.Piece = ∅) :
    DrySeamLink P R E S ∧ IsEmpty (FaceLayer W E V S O) ∧
      ∀ (Rw : FC39RowsV2 W E) (VL : VertexModelLink Rw V) (F : FaceLayer W E V S O)
        (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier),
        IsEmpty (SeamFacesLink Rw V VL O S F N) :=
  ⟨drySeamLink_of_empty P R E S hP hR hT, isEmpty_faceLayer_of_side_boundary_empty S O c b hk,
    fun Rw VL F N => isEmpty_seamFacesLink_of_side_boundary_empty Rw VL O S F N c b hk⟩

/-- A closed zero vertex has empty model boundary (the vertex of the draft's test B). -/
theorem closedZero_boundary_eq_empty (C : ClosedZeroPiece W) :
    (𝓡∂ 3).boundary (Vertex.closedZero C).piece.Piece = ∅ :=
  C.boundary_empty

/-! ## C — swapped corner axes -/

/-- The dry `CircleLink` (FC39Dry.lean:575), on the bundles it reads. -/
def DryCircleLink (P : EdgeBundle W) (R : CircleBundle W) (circ : CircleRegion W) : Prop :=
  circ.region = R.region ∧
    ∃ ι : circ.Base → R.Base, Topology.IsOpenEmbedding ι ∧
      (∀ x : circ.domain, ∃ hx : (x : W.Carrier) ∈ R.domain,
        R.proj ⟨x, hx⟩ = ι (circ.proj x)) ∧
      (∀ k, ∃ c ∈ frontier P.cbase, P.rim c = R.fibre (ι (circ.cornerChart k (0, 0)))) ∧
      (∀ c ∈ frontier P.cbase, ∃ k, P.rim c = R.fibre (ι (circ.cornerChart k (0, 0))))

/-- The coordinate swap of `ℝ × ℝ`. -/
def swapPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toPartialEquiv := (Equiv.prodComm ℝ ℝ).toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn

/-- The swap of the two rim coordinates of `Circle × (ℝ × ℝ)`. -/
def rimSwapPartialDiffeomorph :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ))
      (Circle × (ℝ × ℝ)) (Circle × (ℝ × ℝ)) ∞ where
  toPartialEquiv := (Equiv.prodCongr (Equiv.refl Circle) (Equiv.prodComm ℝ ℝ)).toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contMDiff_fst.prodMk
    ((contDiff_snd.prodMk contDiff_fst).contMDiff.comp contMDiff_snd)).contMDiffOn
  contMDiffOn_invFun := (contMDiff_fst.prodMk
    ((contDiff_snd.prodMk contDiff_fst).contMDiff.comp contMDiff_snd)).contMDiffOn

theorem swap_mem_rimBox_iff {r : ℝ} {v : ℝ × ℝ} : v.swap ∈ rimBox r ↔ v ∈ rimBox r :=
  and_comm

theorem image_swap_rimBox (r : ℝ) : Prod.swap '' rimBox r = rimBox r := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact swap_mem_rimBox_iff.2 hw
  · intro hv
    exact ⟨v.swap, swap_mem_rimBox_iff.2 hv, Prod.swap_swap v⟩

theorem standardRimRounding_swap (v : ℝ × ℝ) :
    standardRimRounding v.swap = standardRimRounding v := by
  simp only [standardRimRounding, Prod.fst_swap, Prod.snd_swap,
    DifferentialGeometry.Topology.Manifold.CornerRounding.roundedMin]
  rw [show v.2 - v.1 = -(v.1 - v.2) by ring, Real.smoothAbs.neg (by norm_num [rimRoundingWidth])]
  ring

theorem swapPartialDiffeomorph_source :
    swapPartialDiffeomorph.source = univ :=
  rfl

/-- **The swapped circle region**: every corner chart precomposed with the swap, first and second
labels exchanged; all other data unchanged. -/
def swapAxesRegion (circ : CircleRegion W) : CircleRegion W :=
  { circ with
    cornerChart := fun k => swapPartialDiffeomorph.trans (circ.cornerChart k)
    cornerChart_source := fun k => by
      ext v
      change v ∈ univ ∩ Prod.swap ⁻¹' (circ.cornerChart k).source ↔ v ∈ rimBox 2
      rw [circ.cornerChart_source k, univ_inter, mem_preimage]
      exact swap_mem_rimBox_iff
    cornerChart_disjoint := fun k k' hkk' => by
      change Disjoint ((circ.cornerChart k).target ∩ _) ((circ.cornerChart k').target ∩ _)
      exact (circ.cornerChart_disjoint hkk').mono inter_subset_left inter_subset_left
    cornerFirst := circ.cornerSecond
    cornerSecond := circ.cornerFirst
    corner_ne := fun k => (circ.corner_ne k).symm
    chart_first := fun k v hv => by
      change circ.defining (circ.cornerSecond k) (circ.cornerChart k v.swap) = _
      rw [circ.chart_second k v.swap (swap_mem_rimBox_iff.2 hv)]
      rfl
    chart_second := fun k v hv => by
      change circ.defining (circ.cornerFirst k) (circ.cornerChart k v.swap) = _
      rw [circ.chart_first k v.swap (swap_mem_rimBox_iff.2 hv)]
      rfl
    chart_other := fun k l v hl hl' hv =>
      circ.chart_other k l v.swap hl' hl (swap_mem_rimBox_iff.2 hv)
    corner_center := circ.corner_center
    rounding_chart := fun k v hv => by
      change circ.rounding (circ.cornerChart k v.swap) = _
      rw [circ.rounding_chart k v.swap (swap_mem_rimBox_iff.2 hv), standardRimRounding_swap]
    rounding_agree := by
      have h : ∀ k, (fun v => circ.cornerChart k v.swap) '' rimBox 1 =
          circ.cornerChart k '' rimBox 1 := fun k => by
        rw [← image_swap_rimBox 1, image_image]
        simp only [Prod.swap_swap]
        rw [image_swap_rimBox]
      change {b | circ.rounding b ≤ 0} \ (⋃ k, (fun v => circ.cornerChart k v.swap) '' rimBox 1) =
        circ.cornerBase \ ⋃ k, (fun v => circ.cornerChart k v.swap) '' rimBox 1
      simp only [h]
      exact circ.rounding_agree }

/-- **The swapped rim charts**: every rim chart precomposed with the swap of the two rim
coordinates. -/
def RimChartLayer.swap {H : EdgeLayer W} {circ : CircleRegion W} (K : RimChartLayer W H circ) :
    RimChartLayer W H (swapAxesRegion circ) where
  handleCorner := K.handleCorner
  handleCorner_bijective := K.handleCorner_bijective
  rimChart h b := rimSwapPartialDiffeomorph.trans (K.rimChart h b)
  rim_source h b {p} := by
    change p ∈ univ ∩ _ ⁻¹' (K.rimChart h b).source ↔ _
    rw [univ_inter, mem_preimage, K.rim_source]
    exact swap_mem_rimBox_iff
  rim_proj h b p hp := by
    have hp' : (p.1, p.2.swap) ∈ (K.rimChart h b).source := hp.2
    exact K.rim_proj h b (p.1, p.2.swap) hp'
  rim_label h b := by
    rw [← K.rim_label h b]
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(p.1, p.2.swap), ?_, rfl⟩
      change p.2.swap = (0, 0)
      rw [show p.2 = (0, 0) from hp]
      rfl
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(p.1, p.2.swap), ?_, ?_⟩
      · change p.2.swap = (0, 0)
        rw [show p.2 = (0, 0) from hp]
        rfl
      · change K.rimChart h b (p.1, p.2.swap.swap) = _
        rw [Prod.swap_swap]
  rim_disjoint h b h' b' hne := by
    change Disjoint ((K.rimChart h b).target ∩ _) ((K.rimChart h' b').target ∩ _)
    exact (K.rim_disjoint h b h' b' hne).mono inter_subset_left inter_subset_left

/-- The dry `CircleLink` survives the swap (it only reads the corner centres). -/
theorem DryCircleLink.swapAxes {P : EdgeBundle W} {R : CircleBundle W} {circ : CircleRegion W}
    (h : DryCircleLink P R circ) : DryCircleLink P R (swapAxesRegion circ) :=
  h

/-- **The old S11b formula fails** for the swapped charts: if the original rim chart reads the
vertex side as `y ≤ 0`, the swapped one does not (the point `(x, y) = (-1/2, 1/2)`). -/
theorem not_rimVertex_swap {H : EdgeLayer W} {circ : CircleRegion W} (K : RimChartLayer W H circ)
    (h : Fin H.handleCount) (b : Bool) (V₀ : Set W.Carrier) (θ : Circle)
    (hv : ∀ {p}, p ∈ (K.rimChart h b).source → (K.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) :
    ¬ ∀ {p}, p ∈ (K.swap.rimChart h b).source → (K.swap.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0) := by
  intro hv'
  have hbox : ((1 / 2 : ℝ), (-1 / 2 : ℝ)) ∈ rimBox 2 := by
    refine ⟨?_, ?_⟩ <;> norm_num [abs_lt]
  have hp : (θ, ((1 / 2 : ℝ), (-1 / 2 : ℝ))) ∈ (K.rimChart h b).source := (K.rim_source h b).2 hbox
  have hp' : (θ, ((-1 / 2 : ℝ), (1 / 2 : ℝ))) ∈ (K.swap.rimChart h b).source :=
    (K.swap.rim_source h b).2 (swap_mem_rimBox_iff.1 hbox)
  have h1 : K.rimChart h b (θ, ((1 / 2 : ℝ), (-1 / 2 : ℝ))) ∈ V₀ := (hv hp).2 (by norm_num)
  have h2 := (hv' hp').1 h1
  norm_num at h2

/-- **The new contract rejects the swapped data**: with an original labelled compatibility, the
swapped one would give `X = λ y = λ x` on the rim box, hence `λ = 0`. -/
theorem isEmpty_labelled_swap {n : ℕ} {E : BoundaryTori W n} {Pr : FC39Prepared W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) (h : Fin H.handleCount) :
    IsEmpty (LabelledCornerCompatibility Pr H (swapAxesRegion circ) K.swap) := by
  refine ⟨fun L' => ?_⟩
  have hbox : ((1 : ℝ), (0 : ℝ)) ∈ rimBox 2 := by
    refine ⟨?_, ?_⟩ <;> norm_num [abs_lt]
  have hp : ((1 : Circle), ((1 : ℝ), (0 : ℝ))) ∈ (K.rimChart h false).source :=
    (K.rim_source h false).2 hbox
  have hp' : ((1 : Circle), ((0 : ℝ), (1 : ℝ))) ∈ (K.swap.rimChart h false).source :=
    (K.swap.rim_source h false).2 (swap_mem_rimBox_iff.1 hbox)
  obtain ⟨hx, h1⟩ := L.height_eq h false _ hp
  obtain ⟨hx', h2⟩ := L'.height_eq h false _ hp'
  have hscale := circ.cornerScale_pos (K.handleCorner h false)
  change Pr.rows.edge.height ⟨K.rimChart h false ((1 : Circle), ((1 : ℝ), (0 : ℝ))), hx'⟩ -
      Pr.rows.edge.level = circ.cornerScale (K.handleCorner h false) * 0 at h2
  rw [h1] at h2
  simp only [mul_one, mul_zero] at h2
  exact hscale.ne' h2

/-- **Regression test C.** For any circle region with a rim chart layer carrying a labelled
compatibility and the vertex formula at one rim: the dry link survives the swap, the swapped rim
charts form a rim chart layer, the old S11b formula fails for them, and the new contract rejects
them. -/
theorem regressionC {n : ℕ} {E : BoundaryTori W n} {Pr : FC39Prepared W E} {H : EdgeLayer W}
    {circ : CircleRegion W} (K : RimChartLayer W H circ)
    (L : LabelledCornerCompatibility Pr H circ K) (h : Fin H.handleCount) (b : Bool)
    (V₀ : Set W.Carrier) (θ : Circle)
    (hv : ∀ {p}, p ∈ (K.rimChart h b).source → (K.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) :
    (DryCircleLink Pr.rows.edge Pr.rows.circle circ →
        DryCircleLink Pr.rows.edge Pr.rows.circle (swapAxesRegion circ)) ∧
      Nonempty (RimChartLayer W H (swapAxesRegion circ)) ∧
      (¬ ∀ {p}, p ∈ (K.swap.rimChart h b).source → (K.swap.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) ∧
      IsEmpty (LabelledCornerCompatibility Pr H (swapAxesRegion circ) K.swap) :=
  ⟨DryCircleLink.swapAxes, ⟨K.swap⟩, not_rimVertex_swap K h b V₀ θ hv, isEmpty_labelled_swap L h⟩

end GC.GraphManifold.Assembly.FC39P0
