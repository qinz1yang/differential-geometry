import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersJunction
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersDry

/-!
# FC39 producer, packet P0 (gate 1): the S³ global face functions and the labelled corner
compatibility, parametric in the junctions

Part C of the circle kind of the S³ inhabitant. For EVERY joint junction structure `J` of the S³
configuration (the concrete one is built by another lane):

* `sphereRowsOf J : FC39RowsV2` — the S³ rows with the labelled corner tubes `sphereLabelledTubes J`;
* `sphereGlobalFaces J : GlobalFaceFunctions (sphereRowsOf J)` — base `⊤`, the four adapted
  defining functions `circDefining`, the actual faces `circActualFace` (`ψ`-faces = the vertical
  faces of the two edge components, `r`-faces = the two residual faces); each face is the zero set
  inside `C₁` of its function (`fibre_subset_wholeVertical_iff`, `fibre_subset_residualSet_iff`),
  every double zero is a registered corner, `−X`, `−Y_e` on every corner neighbourhood;
* `spherePrepared J`, `sphereGlobalFaceLink J`, **`sphereLabelledCompatibility J :
  LabelledCornerCompatibility (spherePrepared J) sphereEdgeLayer sphereCircleRegion sphereRimLayer`**
  (`X = x / 16`, `Y_e = y / 16` on the whole rim sources, rim targets = the full preimages of the
  corner targets, inside the raw tubes);
* `sphereRegressionC J h b` — regression test C on the S³ data, the vertex formula at the rim
  DERIVED from the labelled side equality (`circRim_vertex_side`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## Endpoints and components -/

theorem circEndSide_apply (i : Fin 2) (e : Bool) :
    circEndSide (sphereEdgeEndEquiv (i, e)) = finTwoEquiv i := by
  rw [circEndSide, Equiv.symm_apply_apply]

theorem circEndEnd_apply (i : Fin 2) (e : Bool) : circEndEnd (sphereEdgeEndEquiv (i, e)) = e := by
  rw [circEndEnd, Equiv.symm_apply_apply]

theorem circEndLabel_apply (i : Fin 2) (e : Bool) :
    circEndLabel (sphereEdgeEndEquiv (i, e)) = (finTwoEquiv i ^^ e) := by
  rw [circEndLabel, circEndSide_apply, circEndEnd_apply]

/-- The actual edge base component of the handle side `b`: the interval `range (edgeInterval b)`. -/
def circVerticalComponent (b : Bool) : sphereEdgeBundle.EdgeBaseComponent :=
  ⟨range (edgeInterval b), edgeInterval b (iccEnd false), range_edgeInterval_subset b ⟨_, rfl⟩,
    (connectedComponentIn_edgeCbase ⟨_, rfl⟩).symm⟩

theorem component_eq_circVerticalComponent (e : sphereEdgeBundle.EdgeEnd) :
    e.component = circVerticalComponent (circEndSide e) :=
  Subtype.ext (connectedComponentIn_edgeCbase ⟨iccEnd (circEndEnd e), (circEnd_val e).symm⟩)

theorem circVerticalComponent_injective : Injective circVerticalComponent := by
  intro b b' h
  have hm : edgeInterval b (iccEnd false) ∈ (circVerticalComponent b').1 := by
    rw [← h]
    exact ⟨_, rfl⟩
  change edgeInterval b (iccEnd false) ∈ range (edgeInterval b') at hm
  rw [range_edgeInterval, mem_preimage, edgeBaseCoord_interval,
    edgeShift_mem_Icc_iff (mem_Ioo_of_Icc_FC39P0b _)] at hm
  exact hm.1

theorem circVerticalComponent_surjective (C : sphereEdgeBundle.EdgeBaseComponent) :
    ∃ b, circVerticalComponent b = C := by
  obtain ⟨_, x, hx, rfl⟩ := C
  change x ∈ edgeCbase at hx
  rw [edgeCbase_eq] at hx
  rcases hx with hx | hx
  · exact ⟨false, Subtype.ext (connectedComponentIn_edgeCbase hx).symm⟩
  · exact ⟨true, Subtype.ext (connectedComponentIn_edgeCbase hx).symm⟩

/-! ## The actual faces of the four defining functions -/

/-- The actual face of the defining function `(axis, side)`: the `ψ`-face of side `b` is the
vertical face of the component of the handle `b`, the `r`-face of side `σ` is the residual face
`sphereResidual σ`. -/
def circActualFaceFun :
    Bool × Bool → CircleFaceLabel sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent
  | (false, b) => .vertical (circVerticalComponent b)
  | (true, σ) => .horizontal (sphereResidual σ)

theorem circActualFaceFun_bijective : Bijective circActualFaceFun := by
  constructor
  · rintro ⟨_ | _, b⟩ ⟨_ | _, b'⟩ h
    · injection h with h'
      rw [circVerticalComponent_injective h']
    · cases h
    · cases h
    · injection h with h'
      rw [sphereResidual_injective h']
  · rintro (F | C)
    · obtain ⟨σ, rfl⟩ := sphereResidual_surjective F
      exact ⟨(true, σ), rfl⟩
    · obtain ⟨b, rfl⟩ := circVerticalComponent_surjective C
      exact ⟨(false, b), rfl⟩

/-- **The actual faces of the S³ circle base**, indexed by the defining functions `Fin 4`. -/
def circActualFace :
    Fin 4 ≃ CircleFaceLabel sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent :=
  circFaceEquiv.symm.trans (Equiv.ofBijective _ circActualFaceFun_bijective)

theorem circActualFace_apply (p : Bool × Bool) :
    circActualFace (circFaceEquiv p) = circActualFaceFun p := by
  simp [circActualFace]

theorem circActualFace_symm (p : Bool × Bool) :
    circActualFace.symm (circActualFaceFun p) = circFaceEquiv p := by
  rw [Equiv.symm_apply_eq, circActualFace_apply]

/-! ## The horizontal faces of the circle base -/

theorem sphereCircleChart_source_mem_CIRCC (c : sphereCircleBaseOpens) (s : Circle) :
    (c.val, s) ∈ sphereCircleChart.source := by
  rw [sphereCircleChart_source]
  exact ⟨c.2, mem_univ _⟩

/-- The stereographic height on a circle fibre is `q₀(r)`. -/
theorem sphereHeight_chart_base (c : sphereCircleBaseOpens) (s : Circle) :
    sphereHeight (sphereCircleChart (c.val, s)) = circHeight (circCoordL true c.val) := by
  have hp := sphereCircleChart_source_mem_CIRCC c s
  have h := sphereHeight_circDomain ⟨_, sphereCircleChart_mem_domain hp⟩
  have hc : sphereCircleProj ⟨_, sphereCircleChart_mem_domain hp⟩ = c :=
    Subtype.ext (sphereCircleProj_chart hp)
  rw [hc] at h
  exact h

/-- **A circle fibre lies in the residual face `σ` iff the `r`-face function vanishes.** -/
theorem fibre_subset_residualSet_iff {σ : Bool} {c : sphereCircleBaseOpens} :
    sphereCircleBundle.fibre c ⊆ sphereSlimPieces.residualSet (sphereResidual σ) ↔
      circFaceFn true σ c = 0 := by
  rw [residualSet_sphereResidual, sphereCircleBundle_fibre, range_subset_iff]
  have key : (∀ s : Circle, sphereCircleChart (c.val, s) ∈
      {x | sphereHeight x = sphereResidualHeight σ}) ↔
        circHeight (circCoordL true c.val) = sphereResidualHeight σ := by
    constructor
    · intro h
      have h1 := h 1
      rwa [mem_ofPred_eq, sphereHeight_chart_base] at h1
    · intro h s
      rw [mem_ofPred_eq, sphereHeight_chart_base]
      exact h
  rw [key, circFaceFn, neg_eq_zero]
  cases σ
  · change _ = -3 / 5 ↔ circHeight _ + 3 / 5 = 0
    constructor <;> intro h <;> linarith
  · change _ = 3 / 5 ↔ 3 / 5 - circHeight _ = 0
    constructor <;> intro h <;> linarith

/-! ## The vertical faces of the circle base -/

/-- The circle direction of a handle rim point. -/
def circRimDir (b : Bool) (w : E2) : Circle :=
  bif b then circleAntipode_CIRCA (unitOf (Complex.orthonormalBasisOneI.repr.symm w))
  else unitOf (Complex.orthonormalBasisOneI.repr.symm w)

/-- A handle point with `‖w‖ = 1` in circle coordinates. -/
theorem handle_eq_circle (b : Bool) (w : ClosedCell 2) (hw : ‖w.val‖ = 1) (t : Icc (0 : ℝ) 1) :
    (cycleS3Handle b).map (w, t) = sphereCircleChart
      (sphereCircleEquiv.symm (circEndVal b, cycleHandleRadius (handleRadiusParam b t)),
        circRimDir b w.val) := by
  rw [cycleS3Handle_map]
  cases b
  · rw [cycleHandleChart_false_eq_circle, hw]
    rfl
  · have hw0 : w.val ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hw
      exact zero_ne_one hw
    rw [cycleHandleChart_true_eq_circle hw0, hw, div_one]
    rfl

/-- A handle point with `‖w‖ = 1` lies on the vertical face of its component. -/
theorem handle_mem_wholeVertical (b : Bool) (w : ClosedCell 2) (hw : ‖w.val‖ = 1)
    (t : Icc (0 : ℝ) 1) :
    (cycleS3Handle b).map (w, t) ∈ sphereEdgeBundle.wholeVertical (circVerticalComponent b) := by
  obtain ⟨hx, hproj⟩ := cycleS3Handle_proj b w t
  refine ⟨⟨_, hx⟩, ⟨?_, ?_⟩, rfl⟩
  · change edgeProj ⟨_, hx⟩ ∈ range (edgeInterval b)
    rw [hproj]
    exact ⟨t, rfl⟩
  · change edgeHeightR ((cycleS3Handle b).map (w, t)) = 1
    rw [cycleS3Handle_map, edgeHeightR_chart (handle_box w t), hw, one_pow]

theorem wholeVertical_subset_handle (b : Bool) :
    sphereEdgeBundle.wholeVertical (circVerticalComponent b) ⊆ range (cycleS3Handle b).map := by
  rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
  rw [range_cycleS3Handle_eq]
  exact ⟨y, ⟨hy1, le_of_eq hy2⟩, rfl⟩

/-- **A circle fibre over `C₁` lies in the vertical face of the handle `b` iff the `ψ`-face
function of side `b` vanishes.** -/
theorem fibre_subset_wholeVertical_iff {b : Bool} {c : sphereCircleBaseOpens}
    (hc : c ∈ sphereCircleCbase) :
    sphereCircleBundle.fibre c ⊆ sphereEdgeBundle.wholeVertical (circVerticalComponent b) ↔
      circFaceFn false b c = 0 := by
  rw [circFaceFn_eq_zero_iff, sphereCircleBundle_fibre, range_subset_iff]
  constructor
  · intro h
    obtain ⟨⟨w, t⟩, hwt⟩ := wholeVertical_subset_handle b (h 1)
    obtain ⟨y, ⟨-, hy2⟩, hyx⟩ := h 1
    have h2 : edgeHeightR ((cycleS3Handle b).map (w, t)) = 1 := by
      rw [hwt, ← hyx]
      exact hy2
    rw [cycleS3Handle_map, edgeHeightR_chart (handle_box w t)] at h2
    have hn : ‖w.val‖ = 1 := by
      have := norm_nonneg w.val
      nlinarith
    rw [handle_eq_circle b w hn t] at hwt
    have hR := cycleHandleRadius_mem_Icc_CIRCA (handleRadiusParam_mem_Icc b t.2)
    have hsrc : (sphereCircleEquiv.symm (circEndVal b, cycleHandleRadius (handleRadiusParam b t)),
        circRimDir b w.val) ∈ sphereCircleChart.source := by
      rw [sphereCircleChart_source]
      refine ⟨sphereCircleEquiv_symm_mem ?_ ⟨by linarith [hR.1], by linarith [hR.2]⟩, mem_univ _⟩
      cases b <;> constructor <;> norm_num [circEndVal]
    have heq := (sphereCircleChart.left_inv hsrc).symm.trans
      ((congrArg sphereCircleChart.symm hwt).trans
        (sphereCircleChart.left_inv (sphereCircleChart_source_mem_CIRCC c 1)))
    have h1 : sphereCircleEquiv.symm (circEndVal b, cycleHandleRadius (handleRadiusParam b t)) =
        c.val := congrArg Prod.fst heq
    rw [← h1, circCoordL_symm]
    rfl
  · intro hψ s
    obtain ⟨⟨t₀, ht₀⟩, htr, -⟩ := cycleHandleRadius_inverse hc.2
    have htr' : cycleHandleRadius t₀ = (sphereCircleEquiv c.val).2 := htr
    let θ₀ : Circle := bif b then circleAntipode_CIRCA s else s
    have hθ : circRimDir b (planeOfCircle θ₀) = s := by
      cases b
      · exact unitOf_planeOfCircle_CIRCB s
      · change circleAntipode_CIRCA (unitOf (Complex.orthonormalBasisOneI.repr.symm
          (planeOfCircle (circleAntipode_CIRCA s)))) = s
        rw [unitOf_planeOfCircle_CIRCB, circleAntipode_antipode_CIRCA]
    let w : ClosedCell 2 := ⟨planeOfCircle θ₀, (planeOfCircle_norm_CIRCA θ₀).le⟩
    let t : Icc (0 : ℝ) 1 := ⟨handleRadiusParam b t₀, handleRadiusParam_mem_Icc b ht₀⟩
    have hc' : c.val = sphereCircleEquiv.symm
        (circEndVal b, cycleHandleRadius (handleRadiusParam b (handleRadiusParam b t₀))) := by
      rw [handleRadiusParam_involutive_CIRCC, htr', ← hψ]
      exact (sphereCircleEquiv.symm_apply_apply c.val).symm
    have hx : sphereCircleChart (c.val, s) = (cycleS3Handle b).map (w, t) := by
      rw [handle_eq_circle b w (planeOfCircle_norm_CIRCA θ₀) t]
      congr 1
      exact Prod.ext hc' hθ.symm
    rw [hx]
    exact handle_mem_wholeVertical b w (planeOfCircle_norm_CIRCA θ₀) t

/-! ## The global face functions -/

/-- The labels of the zero faces inside `C₁`. -/
theorem circDefining_face_eq (f : Fin 4) :
    {c | c ∈ sphereCircleCbase ∧ circDefining f c = 0} =
      {c | c ∈ sphereCircleCbase ∧ sphereCircleBundle.fibre c ⊆
        circleFaceSet sphereSlimPieces sphereEdgeBundle (circActualFace f)} := by
  obtain ⟨⟨a, σ⟩, rfl⟩ := circFaceEquiv.surjective f
  rw [circDefining_face, circActualFace_apply]
  ext c
  refine and_congr_right fun hc => ?_
  cases a
  · exact (fibre_subset_wholeVertical_iff (b := σ) hc).symm
  · exact (fibre_subset_residualSet_iff (σ := σ) (c := c)).symm

theorem circDefining_ncard_le (c : sphereCircleBaseOpens) :
    Set.ncard {l : Fin 4 | circDefining l c = 0} ≤ 2 := by
  have h : {l : Fin 4 | circDefining l c = 0} =
      ↑(Finset.univ.filter fun l => circDefining l c = 0) := by
    ext l
    simp
  rw [h, Set.ncard_coe_finset]
  exact circDefining_depth c

variable (J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
  sphereSlimPieces sphereEdgeBundle sphereCircleBundle)

/-- **The S³ rows** for the joint junctions `J`, with the labelled corner tubes. -/
def sphereRowsOf : FC39RowsV2 sphereW (BoundaryTori.empty sphereW) where
  zero := sphereZeroDomains
  cusp := sphereCuspCores
  slim := sphereSlimPieces
  edge := sphereEdgeBundle
  edgeModels := sphereEdgeModels
  circle := sphereCircleBundle
  junctions := J
  labelledTubes := sphereLabelledTubes J

/-- **Every double zero is a registered labelled corner.** -/
theorem circDefining_double_registered (c : sphereCircleBaseOpens) (f f' : Fin 4) (hne : f ≠ f')
    (h : circDefining f c = 0) (h' : circDefining f' c = 0) :
    ∃ e : sphereEdgeBundle.EdgeEnd, c = J.rimBase e.1 ∧
      ((circActualFace f = .vertical e.component ∧
          circActualFace f' = .horizontal (J.horizontal e)) ∨
        (circActualFace f = .horizontal (J.horizontal e) ∧
          circActualFace f' = .vertical e.component)) ∧
      ∀ f'', f'' ≠ f → f'' ≠ f' → circDefining f'' c < 0 := by
  obtain ⟨k, rfl⟩ := circCorner_center c f f' hne h h'
  let e := sphereEdgeEndEquiv (finTwoEquiv.symm (circCornerEquiv.symm k).1,
    (circCornerEquiv.symm k).2)
  have hside : circEndSide e = (circCornerEquiv.symm k).1 := by
    rw [circEndSide_apply, Equiv.apply_symm_apply]
  have hend : circEndEnd e = (circCornerEquiv.symm k).2 := circEndEnd_apply _ _
  have hcenter : circCorner k (0, 0) = J.rimBase e.1 := by
    rw [rimBase_eq_circCorner J e, hside, hend]
    rfl
  have h0 := origin_mem_rimBox_CIRCC
  have hother : ∀ l, l ≠ circCornerFirst k → l ≠ circCornerSecond k →
      circDefining l (circCorner k (0, 0)) < 0 := fun l h1 h2 => circCorner_other k l _ h1 h2 h0
  have hmem : ∀ l, circDefining l (circCorner k (0, 0)) = 0 →
      l = circCornerFirst k ∨ l = circCornerSecond k := by
    intro l hl
    by_contra hcon
    exact (hother l (fun h1 => hcon (Or.inl h1)) (fun h2 => hcon (Or.inr h2))).ne hl
  have hlab1 : circActualFace (circCornerFirst k) = .vertical e.component := by
    rw [circCornerFirst, circActualFace_apply, component_eq_circVerticalComponent, hside]
    rfl
  have hlab2 : circActualFace (circCornerSecond k) = .horizontal (J.horizontal e) := by
    rw [circCornerSecond, circActualFace_apply, horizontal_eq_circEndLabel J e, circEndLabel,
      hside, hend]
    rfl
  rcases hmem f h with rfl | rfl <;> rcases hmem f' h' with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨e, hcenter, Or.inl ⟨hlab1, hlab2⟩, fun f'' h1 h2 => hother f'' h1 h2⟩
  · exact ⟨e, hcenter, Or.inr ⟨hlab2, hlab1⟩, fun f'' h1 h2 => hother f'' h2 h1⟩
  · exact absurd rfl hne

/-- **The canonical functions `−X`, `−Y_e` near every corner.** -/
theorem circDefining_canonical (e : sphereEdgeBundle.EdgeEnd) (c : sphereCircleBaseOpens) :
    circDefining (circActualFace.symm (.vertical e.component)) c = -(circTubeChart e c).1 ∧
      circDefining (circActualFace.symm (.horizontal (J.horizontal e))) c =
        -(circTubeChart e c).2 := by
  have h1 : (CircleFaceLabel.vertical e.component : CircleFaceLabel sphereSlimPieces.ResidualFace
      sphereEdgeBundle.EdgeBaseComponent) = circActualFaceFun (false, circEndSide e) := by
    rw [component_eq_circVerticalComponent]
    rfl
  have h2 : (CircleFaceLabel.horizontal (J.horizontal e) : CircleFaceLabel
      sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent) =
        circActualFaceFun (true, circEndLabel e) := by
    rw [horizontal_eq_circEndLabel J e]
    rfl
  rw [h1, h2, circActualFace_symm, circActualFace_symm, circDefining_face, circDefining_face,
    circTubeChart_apply]
  exact ⟨rfl, rfl⟩

/-- **The S³ global face functions** (prepared output) for the joint junctions `J`. -/
def sphereGlobalFaces : GlobalFaceFunctions (sphereRowsOf J) where
  base := ⊤
  cbase_subset _ _ := trivial
  Face := Fin 4
  finite := inferInstance
  actualFace := circActualFace
  fn := circDefining
  smooth f := (circDefining_smooth f).contMDiffOn
  zero_regular f c _ _ := circDefining_regular f c
  base_eq := by
    change sphereCircleCbase =
      {c | c ∈ (⊤ : TopologicalSpace.Opens sphereCircleBaseOpens) ∧ ∀ l, circDefining l c ≤ 0}
    rw [sphereCircleCbase_eq]
    ext c
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  face_eq := circDefining_face_eq
  depth_le_two c _ := circDefining_ncard_le c
  double_independent c _ f f' hne h h' := circDefining_independent c f f' hne h h'
  double_registered c _ f f' hne h h' := circDefining_double_registered J c f f' hne h h'
  canonical_near_corner e c _ := circDefining_canonical J e c

/-- **The S³ prepared rows.** -/
def spherePrepared : FC39Prepared sphereW (BoundaryTori.empty sphereW) where
  rows := sphereRowsOf J
  globalFaces := sphereGlobalFaces J

/-- The global face link of the S³ circle region (`faceIndex = id`). -/
def sphereGlobalFaceLink :
    GlobalFaceLink (sphereGlobalFaces J) sphereCircleRegion sphereCircleRestriction where
  range_subset _ _ := trivial
  faceIndex := Equiv.refl (Fin 4)
  defining_eq _ _ := rfl

/-! ## The labelled corner compatibility -/

/-- The endpoint of a corner: the corner `(b, e)` is the end `e` of the handle `b`. -/
def circEndOfCorner : Fin 4 ≃ sphereEdgeBundle.EdgeEnd :=
  circCornerEquiv.symm.trans
    ((Equiv.prodCongr finTwoEquiv.symm (Equiv.refl Bool)).trans sphereEdgeEndEquiv)

theorem circEndOfCorner_apply (k : Fin 4) :
    circEndOfCorner k = sphereEdgeEndEquiv (finTwoEquiv.symm (circCornerEquiv.symm k).1,
      (circCornerEquiv.symm k).2) :=
  rfl

theorem circEndOfCorner_handle (h : Fin 2) (b : Bool) :
    circEndOfCorner (sphereHandleCorner h b) = sphereEdgeEndEquiv (h, b) := by
  rw [circEndOfCorner_apply, sphereHandleCorner, Equiv.symm_apply_apply]
  dsimp only
  rw [Equiv.symm_apply_apply]

theorem sphere_corner_center (k : Fin 4) : circCorner k (0, 0) = J.rimBase (circEndOfCorner k).1 := by
  rw [rimBase_eq_circCorner J, circEndOfCorner_apply, circEndSide_apply, circEndEnd_apply,
    Equiv.apply_symm_apply]
  rfl

theorem circActualFace_first (h : Fin 2) (b : Bool) :
    circActualFace (circCornerFirst (sphereHandleCorner h b)) =
      .vertical (circVerticalComponent (finTwoEquiv h)) := by
  rw [circCornerFirst, sphereHandleCorner, Equiv.symm_apply_apply, circActualFace_apply]
  rfl

theorem circActualFace_second (h : Fin 2) (b : Bool) :
    circActualFace (circCornerSecond (sphereHandleCorner h b)) =
      .horizontal (J.horizontal (sphereEdgeEndEquiv (h, b))) := by
  rw [horizontal_eq_circEndLabel J, circEndLabel_apply, circCornerSecond, sphereHandleCorner,
    Equiv.symm_apply_apply, circActualFace_apply]
  rfl

/-- A rim chart point is a corner tube point with chart coordinates `(x / 16, y / 16)`. -/
theorem circRim_tube_point (b e : Bool) {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    ∃ hx : circRim b e p ∈ sphereCircleDomain,
      sphereCircleProj ⟨circRim b e p, hx⟩ ∈ circTubeBase (sphereEdgeEndEquiv (finTwoEquiv.symm b, e)) ∧
      circTubeChart (sphereEdgeEndEquiv (finTwoEquiv.symm b, e))
        (sphereCircleProj ⟨circRim b e p, hx⟩) = (1 / 16 * p.2.1, 1 / 16 * p.2.2) := by
  obtain ⟨hx, hproj⟩ := circRim_proj b e hp
  refine ⟨hx, ?_, ?_⟩
  · rw [hproj]
    change circCornerChart b e p.2 ∈ (circCornerChart (circEndSide _) (circEndEnd _)).target
    rw [circEndSide_apply, circEndEnd_apply, Equiv.apply_symm_apply]
    exact (circCornerChart b e).map_source (by rw [circCornerChart_source]; exact hp)
  · rw [hproj, circTubeChart_apply, circEndLabel_apply, circEndSide_apply, Equiv.apply_symm_apply]
    obtain ⟨h1, h2⟩ := circCoordL_circCornerChart b e hp
    rw [h1, h2, circSlack_circCornerInv _ _ hp.1, circSlack_circCornerInv _ _ hp.2]

theorem circTube_height_chart {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}
    (hx : sphereCircleProj x ∈ circTubeBase e) :
    edgeHeightR x.val - 1 = (circTubeChart e (sphereCircleProj x)).1 := by
  rw [circTubeChart_apply, circTube_height (circTube_target hx)]
  ring

/-- **`X = x / 16` on the whole rim source.** -/
theorem circRim_height (b e : Bool) {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    ∃ _ : circRim b e p ∈ edgeSource, edgeHeightR (circRim b e p) - 1 = 1 / 16 * p.2.1 := by
  obtain ⟨_, hbase, hchart⟩ := circRim_tube_point b e hp
  refine ⟨circTube_mem_edgeSource (circTube_target hbase), ?_⟩
  have h1 := circTube_height_chart hbase
  rw [hchart] at h1
  exact h1

/-- **`Y_e = y / 16` on the whole rim source.** -/
theorem circRim_horizontal (h : Fin 2) (b : Bool) {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    sphereSlimPieces.residualFn (J.horizontal (sphereEdgeEndEquiv (h, b)))
      (circRim (finTwoEquiv h) b p) = 1 / 16 * p.2.2 := by
  obtain ⟨hx, -, hchart⟩ := circRim_tube_point (finTwoEquiv h) b hp
  have h2 := circTube_face J (e := sphereEdgeEndEquiv (finTwoEquiv.symm (finTwoEquiv h), b))
    ⟨circRim (finTwoEquiv h) b p, hx⟩
  rw [hchart, Equiv.symm_apply_apply] at h2
  exact h2.symm

/-- The rim target is the full circle preimage of the corner chart target. -/
theorem circRim_target_eq (b e : Bool) :
    (circRim b e).target = Subtype.val '' (sphereCircleProj ⁻¹' (circCornerChart b e).target) := by
  ext x
  rw [mem_circRim_target]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, mem_sphereCircleDomain_iff.2 hx⟩, mem_circCornerChart_target.2 hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨mem_sphereCircleDomain_iff.1 y.2, mem_circCornerChart_target.1 hy⟩

theorem sphereRim_target_full (h : Fin 2) (b : Bool) :
    (circRim (finTwoEquiv h) b).target =
      Subtype.val '' (sphereCircleProj ⁻¹' (circCorner (sphereHandleCorner h b)).target) := by
  rw [circCorner_sphereHandleCorner]
  exact circRim_target_eq _ _

theorem sphereRim_target_in_tube (h : Fin 2) (b : Bool) :
    (circRim (finTwoEquiv h) b).target ⊆
      Subtype.val '' (sphereCircleProj ⁻¹' circTubeBase (sphereEdgeEndEquiv (h, b))) := by
  rw [circRim_target_eq]
  refine image_mono (preimage_mono fun c hc => ?_)
  change c ∈ (circCornerChart (circEndSide _) (circEndEnd _)).target
  rw [circEndSide_apply, circEndEnd_apply]
  exact hc

/-- **The S³ labelled corner compatibility** for the joint junctions `J`. -/
def sphereLabelledCompatibility :
    LabelledCornerCompatibility (spherePrepared J) sphereEdgeLayer sphereCircleRegion
      sphereRimLayer where
  edgeLink := sphereEdgeLink
  circleLink := sphereCircleRestriction
  globalFaces := sphereGlobalFaceLink J
  endOfCorner := circEndOfCorner
  corner_center k := sphere_corner_center J k
  endpoint_label h b := (circEndOfCorner_handle h b).symm
  first_label h b := circActualFace_first h b
  second_label h b := circActualFace_second J h b
  height_eq h b _ hp := circRim_height (finTwoEquiv h) b ((mem_circRim_source _ _).1 hp)
  horizontal_eq h b _ hp := circRim_horizontal J h b ((mem_circRim_source _ _).1 hp)
  target_full h b := sphereRim_target_full h b
  target_in_raw_tube h b := sphereRim_target_in_tube h b

/-! ## Regression test C on the S³ data -/

/-- **The vertex formula at a rim, derived**: on the rim chart of the end `b` of the handle `h`,
the vertex owner of the actual label is `y ≤ 0`. -/
theorem circRim_vertex_side (h : Fin 2) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (sphereRimLayer.rimChart h b).source) :
    sphereRimLayer.rimChart h b p ∈
        sphereSlimPieces.rowSet ((sphereLabelledCompatibility J).handleEndOwner h b) ↔
      p.2.2 ≤ 0 := by
  have hp' := (mem_circRim_source _ _).1 hp
  obtain ⟨hx, -, hchart⟩ := circRim_tube_point (finTwoEquiv h) b hp'
  have hv := circTube_vertex_side J (e := sphereEdgeEndEquiv (finTwoEquiv.symm (finTwoEquiv h), b))
    (x := ⟨circRim (finTwoEquiv h) b p, hx⟩)
  rw [hchart, Equiv.symm_apply_apply] at hv
  refine hv.trans ?_
  change 1 / 16 * p.2.2 ≤ 0 ↔ _
  constructor <;> intro h <;> linarith

/-- **Regression test C on the S³ data** (review 49): for the end `b` of the handle `h`, with the
vertex formula DERIVED from the labelled tubes: the dry link holds for the original and the
swapped data, the swapped rim charts form a rim chart layer, the old S11b formula fails for them,
and the new contract rejects them. -/
theorem sphereRegressionC (h : Fin 2) (b : Bool) :
    DryCircleLink sphereEdgeBundle sphereCircleBundle sphereCircleRegion ∧
      DryCircleLink sphereEdgeBundle sphereCircleBundle (swapAxesRegion sphereCircleRegion) ∧
      Nonempty (RimChartLayer sphereW sphereEdgeLayer (swapAxesRegion sphereCircleRegion)) ∧
      (¬ ∀ {p}, p ∈ (sphereRimLayer.swap.rimChart h b).source →
        (sphereRimLayer.swap.rimChart h b p ∈
            sphereSlimPieces.rowSet ((sphereLabelledCompatibility J).handleEndOwner h b) ↔
          p.2.2 ≤ 0)) ∧
      IsEmpty (LabelledCornerCompatibility (spherePrepared J) sphereEdgeLayer
        (swapAxesRegion sphereCircleRegion) sphereRimLayer.swap) :=
  regressionC_projected sphereRimLayer (sphereLabelledCompatibility J) h b _ 1
    (circRim_vertex_side J h b)

end GC.GraphManifold.Assembly.FC39P0
